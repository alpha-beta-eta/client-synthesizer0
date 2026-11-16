#lang racket/base
;; Golden outputs of what does not need Verus or vostd data, on small inputs
;; written for the tests (tests/inputs/): the spec text of functions, the
;; drift of call knowledge (anchors, metadata), and the listing of trusted
;; code and the check of its verdicts.  A change that is not meant to change
;; behaviour must leave them unchanged.
;;   raco test tests             compare
;;   racket tests/golden.rkt update   rewrite tests/golden/ (after a deliberate change)
(require racket/file racket/pretty racket/port racket/runtime-path rackunit racket/match
         "../lib/model/knowledge.rkt" "../lib/model/knowledge-drift.rkt" "../lib/vostd/spec-digest.rkt"
         "../lib/vostd/trusted.rkt" "../lib/model/audit.rkt")

(define-runtime-path root "..")
(define-runtime-path golden-dir "golden")

(define (in-root f) (build-path root f))

(define (forms->string forms)
  (with-output-to-string (lambda () (for ([f (in-list forms)]) (pretty-write f)))))

;; The spec text of two functions (design.md 3.7) in two versions of a file:
;; the attributes counted by brackets (`#[trigger]` inside `#[verus_spec]`),
;; and a removed `external_body`.
(define (lines-of f)
  (list->vector (map (lambda (l) (regexp-replace #rx"\r$" l "")) (file->lines (in-root f)))))
(define (spec-texts)
  (apply string-append
         (for*/list ([f (in-list '("tests/inputs/spec-v1.rs" "tests/inputs/spec-v2.rs"))]
                     [ls (in-value (lines-of f))]
                     [name (in-list '("reference_count" "size"))])
           (define i (for/first ([j (in-range (vector-length ls))]
                                 #:when (regexp-match? (pregexp (format "\\bfn ~a\\b" name)) (vector-ref ls j)))
                       (add1 j)))
           (format ";; ~a ~a\n~a\n" f name (spec-text ls i i)))))

;; The drift of a knowledge file (design.md 3.7): its references read
;; against a moved and changed source, the line numbers of moved anchors
;; written (as `knowledge --fix`; no anchors are added: anchoring a reference
;; at the line it cites now is right only after it has been read again), and
;; the metadata replaced; comments are kept.
(define (knowledge-drift)
  (define text (file->string (in-root "tests/inputs/knowledge.rktd")))
  (define v2 (lines-of "tests/inputs/spec-v2.rs"))
  (define placed (for/list ([r (in-list (vostd-refs text))])
                   (cons r (if (list-ref r 5) (relocate v2 (list-ref r 4) (list-ref r 5)) 'none))))
  (define fixed (rewrite-refs text
                              (for/list ([x (in-list placed)]) (cons (car x) (and (pair? (cdr x)) (eq? (cadr x) 'moved) (caddr x))))
                              (lambda (r) #f)))
  (string-append (forms->string (for/list ([x (in-list placed)]) (list (list-ref (car x) 4) (cdr x))))
                 (forms->string (knowledge-apis (read-knowledge (in-root "tests/inputs/knowledge.rktd"))))
                 ";; ---- written\n"
                 (splice-meta fixed "2222222" '((Frame::reference_count . "aaaaaaaaaaaa") (Frame::size . "bbbbbbbbbbbb")))))

;; Trusted code (design.md 3.10): the sites of two versions of a file (the
;; lexer, the items' paths, the fingerprints), and the verdicts of the first
;; checked against the second, with demo statuses; then the changed ones accepted.
(define (trusted-scan)
  (apply string-append
         (for/list ([f (in-list '("tests/inputs/trusted-v1.rs" "tests/inputs/trusted-v2.rs"))])
           (string-append (format ";; ~a\n" f) (forms->string (scan-source "t.rs" (file->string (in-root f))))))))
(define (audit-check)
  (define a (read-audit (in-root "tests/inputs/audit.rktd")))
  (define sites (for/list ([s (in-list (scan-source "t.rs" (file->string (in-root "tests/inputs/trusted-v2.rs"))))])
                  (match-define (list kind file item detail line fp) s)
                  `(trusted ,kind ,file ,item ,detail (line ,line) (fp ,fp))))
  (define demos (hash "d.rs" (hash "demo_max" 'verified "demo_forge" 'failed)))
  (define-values (a2 ids) (accept-audit a sites "2222222"))
  (string-append (forms->string (check-audit (list a) sites demos))
                 ";; ---- accepted\n"
                 (forms->string (list ids (findf (lambda (v) (equal? (verdict-id v) "t#1")) (audit-verdicts a2))
                                      `(at ,(audit-at a2))))))

(define cases
  (list
   (list "spec-text" spec-texts)
   (list "knowledge-drift" knowledge-drift)
   (list "trusted-scan" trusted-scan)
   (list "audit-check" audit-check)))

(define update? (member "update" (vector->list (current-command-line-arguments))))

(make-directory* golden-dir)
(for ([c (in-list cases)])
  (define file (build-path golden-dir (string-append (car c) ".txt")))
  (define out ((cadr c)))
  (if update?
      (call-with-output-file file #:exists 'truncate (lambda (o) (write-string out o)))
      (test-equal? (car c) out (file->string file))))
