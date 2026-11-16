#lang racket/base
;; Checking the text of claims and assumptions before Verus does
;; (docs/representation.md 4.5, step 3).  The text is parsed with the source's
;; parser (item-index --exprs, verus_syn as Verus uses it), and the tree is
;; checked for what Verus would reject or what makes the client meaningless:
;;
;;   (parse-error MESSAGE)        the text is not a Verus expression
;;   (unknown-names X ..)         free variables that are none of the API's
;;                                parameters (exec, ghost), `ret`, `gret`
;;   (old-of-non-mut X ..)        old(x) / final(x) of a parameter that is not `&mut`
;;   (matches-on-rhs OP)          `a OP b matches P && c` (or `==> c`): Verus rejects a
;;                                matches with && or ==> as the right operand of a
;;                                binary operator unless it is parenthesized
;;                                (builtin_macros, handle_binary_ops)
;;
;; What it cannot tell: whether the claim is true, whether a method exists on
;; the receiver's type or its trait bounds hold (`self.inv()` on a type whose
;; `Inv` impl needs a bound the API lacks), whether Verus can infer a
;; quantifier's triggers.  Those still come from Verus and from reading.
(require racket/list racket/match racket/string racket/port racket/system
         "../model/api.rkt" "../base/forms.rkt")
(provide parse-texts text-problems closed-uses)

;; parse-texts : exe (string ...) -> (tree-or-(error MSG) ...), one item-index run
(define (parse-texts exe texts)
  (cond
    [(null? texts) '()]
    [else
     (define in (string-join (for/list ([t (in-list texts)]) (regexp-replace* #rx"[\r\n]+" t " ")) "\n"))
     (define out
       (with-output-to-string
         (lambda ()
           (parameterize ([current-input-port (open-input-string (string-append in "\n"))])
             (system* exe "--exprs")))))
     (define trees (for/list ([x (in-port read (open-input-string out))]) x))
     (unless (= (length trees) (length texts))
       (error 'parse-texts "item-index --exprs gave ~a trees for ~a texts" (length trees) (length texts)))
     trees]))

(define ident-rx #px"^[a-z_][A-Za-z0-9_]*$")

;; The names a tree binds anywhere (quantifiers, matches patterns): bound for
;; the whole claim, conservatively (a matches without its own `&& rest` may
;; still bind for an enclosing `==>`).
(define (bound-names t)
  (match t
    [`(,(or 'forall 'exists 'choose) ,bs ,body) (append (map car bs) (bound-names body))]
    [`(pat ,_ ,names ...) names]
    [(? pair?) (append-map bound-names (filter pair? t))]
    [_ '()]))

;; The free single-identifier variables of a tree (not callees, fields, methods).
(define (free-vars t)
  (let loop ([t t])
    (match t
      [`(path ,(? string? p)) (if (regexp-match? ident-rx p) (list p) '())]
      [`(call (path ,_) ,args ...) (append-map loop args)]
      [`(call ,f ,args ...) (append (loop f) (append-map loop args))]
      [`(method ,r ,_ ,_ ,args ...) (append (loop r) (append-map loop args))]
      [`(,(or 'field 'arrow) ,a ,_) (loop a)]
      [`(,(or 'is 'isnt) ,a ,_) (loop a)]
      [`(as ,a ,_) (loop a)]
      [`(,(or 'forall 'exists 'choose) ,_ ,body) (loop body)]
      [`(matches ,a ,_ ,rest ...) (append (loop a) (append-map loop (filter pair? rest)))]
      [`(pat ,_ ...) '()]
      [`(,(or 'lit 'src) ,_) '()]
      [`(op ,_ ,a ,b) (append (loop a) (loop b))]
      [(? pair?) (append-map loop (filter pair? (cdr t)))]
      [_ '()])))

;; old(x) / final(x) of a variable
(define (old-final-vars t)
  (match t
    [`(call (path ,(or "old" "final")) (path ,(? string? x))) (list x)]
    [`(final (path ,(? string? x))) (list x)]
    [(? pair?) (append-map old-final-vars (filter pair? t))]
    [_ '()]))

(define (matches-on-rhs t)
  (match t
    [`(op ,op ,a ,(and b `(matches ,_ ,_ ,(or "&&" "==>") ,_))) (cons op (append (matches-on-rhs a) (matches-on-rhs (cdr b))))]
    [(? pair?) (append-map matches-on-rhs (filter pair? t))]
    [_ '()]))

;; closed-uses : table tree -> (NAME ...)
;; The spec functions a claim calls that the table has as `closed`
;; (docs/representation.md B3): the client cannot see their bodies, so a claim
;; that needs one unfolded fails although it may be true; a note for judging the
;; claim, not a problem of its text.  By the last segment of the name.
(define (closed-uses table tree)
  (define (last-seg s) (let ([ps (string-split s "::")]) (if (null? ps) s (last ps))))
  (define called
    (remove-duplicates
     (let walk ([t tree])
       (match t
         [`(method ,r ,(? string? m) ,_ ,args ...) (cons m (append (walk r) (append-map walk args)))]
         [`(call (path ,(? string? f)) ,args ...) (cons (last-seg (regexp-replace #rx"::<.*$" f "")) (append-map walk args))]
         [(? pair?) (append-map walk (filter pair? t))]
         [_ '()]))))
  (define closed
    (for*/list ([n (in-list (table-names table))]
                [a (in-value (api-ref table n))]
                #:when (and (eq? (api-mode a) 'spec)
                            (let ([src (form-ref a 'source #f)])
                              (and (pair? src) (equal? (assq 'publish (filter pair? src)) '(publish closed))))))
      (regexp-replace #rx"^.*::" (symbol->string n) "")))
  (filter (lambda (m) (member m closed)) called))

;; text-problems : api tree -> (problem ...)
;; The parameters a claim may name: the API's exec and ghost parameters (as the
;; client names them, `self`), `ret` and `gret`.
(define (text-problems api tree)
  (match tree
    [`(error ,msg) (list `(parse-error ,msg))]
    [_
     (define ps (append (api-params api) (api-ghost-params api)))
     (define allowed (append (map (lambda (p) (symbol->string (param-name p))) ps) '("ret" "gret")))
     (define bound (bound-names tree))
     (define unknown (remove-duplicates
                      (filter (lambda (x) (not (or (member x allowed) (member x bound)))) (free-vars tree))))
     (define muts (for/list ([p (in-list ps)] #:when (match (param-type p) [`(&mut ,_) #t] [_ #f]))
                    (symbol->string (param-name p))))
     (define not-mut (remove-duplicates
                      (filter (lambda (x) (and (member x allowed) (not (member x muts)))) (old-final-vars tree))))
     (append (if (null? unknown) '() `((unknown-names ,@unknown)))
             (if (null? not-mut) '() `((old-of-non-mut ,@not-mut)))
             (for/list ([op (in-list (remove-duplicates (matches-on-rhs tree)))]) `(matches-on-rhs ,op)))]))
