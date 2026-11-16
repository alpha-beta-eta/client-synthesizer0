#lang racket/base
;; Spec text with holes (docs/representation.md 4.2, 4.5): a clause or claim
;; kept as its source text, each free use of a variable a hole, so that it is
;; substituted on structure, not by a regular expression over the whole text.
;;
;; source->template : text (VAR-SYMBOL ...) -> (tmpl PIECE ...)
;;   PIECE = string | X | (old X) | (final X) | (deref (old X)) | (deref (final X))
;; A use is the variable's name not after `.`, `::` or `'`, not before `::` or
;; `!`, and not bound in the text itself (closure and quantifier parameters,
;; `let`, the names a `matches` pattern binds): a name the text binds is never
;; a hole, even where it would be the variable.  `old(p)`, `final(p)` and their
;; `*` are holes as a whole.  Other names stay as written.
(require racket/list racket/match racket/string)
(provide source->template template-holes template-vars template-map bound-in-text)

;; bound-in-text : text -> (string ...), the names the text binds
(define (bound-in-text text)
  (remove-duplicates
   (append
    ;; |a: T, b| of closures and quantifiers
    (for*/list ([m (in-list (regexp-match* #px"\\|([^|]*)\\|" text #:match-select cadr))]
                [part (in-list (string-split m ","))]
                [n (in-value (regexp-match #px"^\\s*(?:mut\\s+)?([A-Za-z_][A-Za-z0-9_]*)" part))] #:when n)
      (cadr n))
    ;; let x = .., let (a, b) = ..
    (for*/list ([m (in-list (regexp-match* #px"\\blet\\s+(?:mut\\s+)?(?:\\(([^)]*)\\)|([A-Za-z_][A-Za-z0-9_]*))" text #:match-select cdr))]
                [part (in-list (string-split (or (car m) (cadr m)) ","))])
      (string-trim part))
    ;; the names a pattern binds: `matches Some(x)`, `matches Child::Frame(p, l, q)`
    (for*/list ([m (in-list (regexp-match* #px"\\bmatches\\s+[A-Za-z0-9_:]+\\s*\\(([^()]*)\\)" text #:match-select cadr))]
                [part (in-list (string-split m ","))]
                [n (in-value (regexp-match #px"^\\s*(?:ref\\s+)?(?:mut\\s+)?([a-z_][A-Za-z0-9_]*)\\s*$" part))] #:when n)
      (cadr n)))))

(define rx
  (pregexp (string-append
            "(?<![.:'A-Za-z0-9_])"
            "(?:(\\*\\s*)?(old|final)\\(\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*\\)"
            "|([A-Za-z_][A-Za-z0-9_]*))"
            "(?![A-Za-z0-9_]|\\s*::|!)")))

(define (source->template text vars)
  (define bound (bound-in-text text))
  (define holes (filter (lambda (v) (not (member v bound))) (map symbol->string vars)))
  (let loop ([start 0] [acc '()])
    (define m (regexp-match-positions rx text start))
    (cond
      [(not m)
       (define pieces ; adjacent strings joined
         (for/fold ([out '()] #:result (reverse out)) ([p (in-list (reverse (cons (substring text start) acc)))])
           (if (and (string? p) (pair? out) (string? (car out)))
               (cons (string-append (car out) p) (cdr out))
               (cons p out))))
       `(tmpl ,@pieces)]
      [else
       (define (sub k) (let ([p (list-ref m k)]) (and p (substring text (car p) (cdr p)))))
       (define star (sub 1)) (define kw (sub 2)) (define inner (sub 3)) (define name (sub 4))
       (define hole
         (cond [(and inner (member inner holes))
                (define h `(,(string->symbol kw) ,(string->symbol inner)))
                (if star `(deref ,h) h)]
               [(and name (member name holes)) (string->symbol name)]
               [else #f]))
       (define whole (car m))
       (if hole
           (loop (cdr whole) (list* hole (substring text start (car whole)) acc))
           (loop (cdr whole) (cons (substring text start (cdr whole)) acc)))])))

;; template-holes : (tmpl PIECE ...) -> (PIECE ...), the holes
(define (template-holes t) (filter (lambda (p) (not (string? p))) (cdr t)))

;; template-vars : (tmpl PIECE ...) -> (X ...), the variables of its holes
(define (template-vars t)
  (remove-duplicates
   (for/list ([h (in-list (template-holes t))])
     (let loop ([h h]) (match h [(? symbol? x) x] [`(,_ ,a) (loop a)])))))

;; template-map : (tmpl PIECE ...) (X -> PIECE) -> (tmpl PIECE ...)
;; Each hole's variable replaced by f's piece for it, under its old, final and
;; deref: renaming (a callee's parameter to the caller's argument) on the
;; structure, not by a regular expression over the text.
(define (template-map t f)
  `(tmpl ,@(for/list ([p (in-list (cdr t))])
             (if (string? p)
                 p
                 (let loop ([h p])
                   (match h
                     [(? symbol? x) (f x)]
                     [`(,k ,a) `(,k ,(loop a))]))))))
