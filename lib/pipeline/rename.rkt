#lang racket/base
;; Names that follow the source across an update of vostd (docs/representation.md
;; step 6).  An entry's NAME is VIR's path (`impl&%8::daddr`), which changes when
;; impls are added or reordered; its key is the source's (`<DmaCoherent<M> as
;; HasDaddr>::daddr`), which does not.  Instead of writing keys into the data
;; (knowledge, issues, digests, audit all name APIs), the keys bridge the two
;; tables: an old name maps to the new name with the same key, and the data is
;; rewritten with that mapping.
;;
;; renames : OLD-APIS-DIR NEW-APIS-DIR -> (values ((OLD . NEW) ...) (OLD ...))
;;   the names whose entry has a new name, and the old names whose key is in no
;;   new entry (gone, or the key itself changed: for a person to look at)
;; rename-file! : FILE ((OLD . NEW) ...) -> count, every symbol OLD in its forms
;;   replaced (the file rewritten only when something changed)
(require racket/file racket/list racket/match racket/string)
(provide renames rename-file!)

(define (keys-of dir)
  (for*/hash ([f (in-list (directory-list dir #:build? #t))]
              #:when (regexp-match? #rx"[.]rktd$" (path->string f))
              [x (in-list (file->list f))]
              #:when (and (pair? x) (eq? (car x) 'fn))
              [k (in-value (let ([s (assq 'source (filter pair? (cddr x)))])
                             (and s (let ([kk (assq 'key (filter pair? (cdr s)))]) (and kk (cadr kk))))))]
              #:when k)
    (values (cadr x) k)))

(define (renames old-dir new-dir)
  (define old (keys-of old-dir))
  (define new (keys-of new-dir))
  (define by-key (for/hash ([(n k) (in-hash new)]) (values k n)))
  (define-values (rs lost)
    (for/fold ([rs '()] [lost '()]) ([(n k) (in-hash old)])
      (define m (hash-ref by-key k #f))
      (cond [(not m) (values rs (cons n lost))]
            [(eq? m n) (values rs lost)]
            [else (values (cons (cons n m) rs) lost)])))
  (values (sort rs symbol<? #:key car) (sort lost symbol<?)))

;; On the text, so that comments stay: a name is a whole token (between
;; whitespace or parentheses), as `write` gives a symbol of these characters.
(define (rename-file! file rs)
  (define h (for/hash ([r (in-list rs)]) (values (symbol->string (car r)) (symbol->string (cdr r)))))
  (define n 0)
  (define text (file->string file))
  (define out
    (regexp-replace* #px"(?<=[\\s(])[^\\s()\"';]+(?=[\\s)])" text
                     (lambda (tok) (cond [(hash-ref h tok #f) => (lambda (new) (set! n (add1 n)) new)]
                                         [else tok]))))
  (when (> n 0)
    (call-with-output-file file #:exists 'truncate (lambda (o) (write-string out o))))
  n)
