#lang racket/base
;; What keeps call knowledge from drifting silently with vostd (design.md 3.7):
;;
;;   (at "COMMIT")                  the vostd commit the file was last reviewed against
;;   (spec-digests (API "HEX") ..)  the fingerprints of the APIs its entries name, at
;;                                  that review (lib/vostd/spec-digest.rkt)
;;   (comment "PATH:LINE" "TEXT")   a vostd reference (also caller, ktest) with the
;;                                  text of the line it cites: its anchor
;;
;; Everything here works on text and forms; reading the checkout is the
;; caller's (lib/vostd/git.rkt).
(require racket/file racket/list racket/string racket/match)
(provide vostd-refs anchor-text relocate splice-meta rewrite-refs knowledge-apis read-digests ref-kinds)

(define ref-kinds '("comment" "caller" "ktest"))

;; vostd-refs : text -> ((START END KIND PATH LINE SNIPPET-or-#f) ...)
;; the references written (KIND "PATH:LINE[..]" ["SNIPPET"]), with their offsets
(define ref-rx (pregexp (format "[(](~a) \"([^\":]+):([0-9]+)[^\"]*\"(?: (\"(?:[^\"\\\\]|\\\\.)*\"))?[)]"
                                (string-join ref-kinds "|"))))
(define (vostd-refs text)
  (for/list ([p (in-list (regexp-match-positions* ref-rx text))])
    (define m (regexp-match ref-rx text (car p) (cdr p)))
    (list (car p) (cdr p) (list-ref m 1) (list-ref m 2) (string->number (list-ref m 3))
          (and (list-ref m 4) (read (open-input-string (list-ref m 4)))))))

;; anchor-text : lines line -> string or #f: the cited line, trimmed, at most 80 characters
(define (anchor-text lines i)
  (and lines (<= 1 i (vector-length lines))
       (let ([l (string-trim (vector-ref lines (sub1 i)))])
         (if (> (string-length l) 80) (substring l 0 80) l))))

;; relocate : lines-or-#f line snippet -> 'same | (moved N) | 'lost | (ambiguous N ...)
;; Where the snippet is now: at the line, else at its only other line, else
;; at the nearest when it is clearly nearer than the next.
(define (relocate lines i snippet)
  (define (has? j) (string-contains? (string-trim (vector-ref lines (sub1 j))) snippet))
  (cond [(not lines) 'lost]
        [(and (<= 1 i (vector-length lines)) (has? i)) 'same]
        [else
         (define hits (for/list ([j (in-range 1 (add1 (vector-length lines)))] #:when (has? j)) j))
         (match hits
           ['() 'lost]
           [(list j) `(moved ,j)]
           [_ (define by (sort hits < #:key (lambda (j) (abs (- j i)))))
              (if (< (abs (- (car by) i)) (abs (- (cadr by) i))) `(moved ,(car by)) `(ambiguous ,@hits))])]))

;; rewrite-refs : text ((REF . NEW-LINE-or-#f) ...) (REF -> SNIPPET-or-#f) -> text
;; Each reference with its line moved (when NEW-LINE) and its snippet added
;; (when it has none and the function gives one); back to front, so earlier
;; offsets stay valid.  The rest of the text, comments included, is kept.
(define (rewrite-refs text placed snippet-for)
  (for/fold ([t text]) ([x (in-list (sort placed > #:key caar))])
    (match-define (list a b kind path line snippet) (car x))
    (define new-line (or (cdr x) line))
    (define new-snippet (or snippet (snippet-for (car x))))
    (define kept (cadr (regexp-match #rx"^[(][a-z]+ \"[^\":]+:[0-9]+([^\"]*)\"" (substring t a b))))
    (if (and (equal? new-line line) (equal? new-snippet snippet))
        t
        (string-append (substring t 0 a)
                       (format "(~a \"~a:~a~a\"~a)" kind path new-line kept (if new-snippet (format " ~s" new-snippet) ""))
                       (substring t b)))))

;; splice-meta : text commit ((API . HEX) ...) -> text, with (at ..) and
;; (spec-digests ..) replaced, or added after the (module ..) form.  The
;; forms are located by read-syntax, so comments elsewhere are kept.
(define (splice-meta text commit digests)
  (define in (open-input-string text))
  (port-count-lines! in)
  (define spans                         ; ((START END HEAD) ...), 0-based offsets
    (let loop ([acc '()])
      (define x (read-syntax 'knowledge in))
      (if (eof-object? x) (reverse acc)
          (let ([d (syntax->datum x)] [a (sub1 (syntax-position x))])
            (loop (cons (list a (+ a (syntax-span x)) (and (pair? d) (car d))) acc))))))
  (define drop (filter (lambda (s) (memq (caddr s) '(at spec-digests))) spans))
  (define meta
    (string-append
     (format "\n(at ~s)\n(spec-digests" commit)
     (apply string-append (for/list ([d (in-list digests)]) (format "\n  (~a ~s)" (car d) (cdr d))))
     ")"))
  ;; the old forms go with the newline before each, back to front
  (define without
    (for/fold ([t text]) ([s (in-list (reverse drop))])
      (string-append (regexp-replace #rx"\n$" (substring t 0 (car s)) "") (substring t (cadr s)))))
  ;; after (module ..), which comes before them, so its offset is unchanged
  (define me (for/first ([s (in-list spans)] #:when (eq? (caddr s) 'module)) (cadr s)))
  (if me
      (string-append (substring without 0 me) meta (substring without me))
      (string-append meta "\n" without)))

;; knowledge-apis : entries -> (API ...): the APIs the entries name
(define (knowledge-apis k)
  (remove-duplicates
   (append* (for/list ([e (in-list k)])
              (match e
                [`(protocol ,_ ,fs ...) (cond [(assq 'calls fs) => cdr] [else '()])]
                [`(,_ ,(? symbol? a) ,_ ...) (list a)]
                [_ '()])))))

;; read-digests : file -> (values (hash API -> HEX) COMMIT-or-#f)
(define (read-digests file)
  (define fs (file->list file))
  (values (for/hash ([x (in-list fs)] #:when (eq? (car x) 'digest)) (values (cadr x) (caddr x)))
          (cond [(assq 'commit fs) => cadr] [else #f])))
