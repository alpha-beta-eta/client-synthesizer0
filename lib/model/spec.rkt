#lang racket/base
;; Spec expressions (the E of client.rkt): their variables and names, and
;; the instances of a callee's requires (design.md 结论8, 19).
(require racket/list racket/match racket/string "api.rkt")
(provide expr-vars subst-expr requires-instance panic-condition)

;; panic-condition : E -> E or #f
;; P of a "may panic here" clause `P ==> may_panic()` (`may_panic`
;; uninterpreted: satisfied only where not P holds); nested,
;; `A ==> (B ==> may_panic())` gives `A && B`.  #f for any other clause.
(define (panic-condition c)
  (define (may-panic-call? e)
    (match e
      [`(call ,(? symbol? f)) (regexp-match? #rx"(^|::)may_panic$" (symbol->string f))]
      [_ #f]))
  (match c
    [`(implies ,a ,b)
     (cond [(may-panic-call? b) a]
           [(panic-condition b) => (lambda (p) `(and ,a ,p))]
           [else #f])]
    [_ #f]))

;; expr-vars : E -> (X ...), the variables E mentions.
(define (expr-vars e)
  (match e
    [(or 'true 'false) '()]
    [(? symbol? x) (list x)]
    [`(field ,a ,_) (expr-vars a)]
    [`(arrow ,a ,_) (expr-vars a)]
    [`(method ,a ,_ ,args ...) (append-map expr-vars (cons a args))]
    [`(is ,a ,_) (expr-vars a)]
    [`(call ,_ ,args ...) (append-map expr-vars args)]
    [`(const ,_) '()]
    [`(src ,_) '()]
    ;; a quantifier's bound variables are not the client's
    [`(,(or 'forall 'exists) ,bs ,body) (remove* (map car bs) (expr-vars body))]
    [`(,_ ,args ...) (append-map expr-vars args)]
    [_ '()]))

;; subst-expr : E ((X . E) ...) -> E
;; Variables replaced by the binding, and `old(e)` by `e`: a callee's `old(p)`
;; is the argument as the caller passes it.
(define (subst-expr e binding)
  (let loop ([e e])
    (match e
      [(? symbol? x) (cond [(assq x binding) => cdr] [else x])]
      [`(old ,a) (loop a)]
      [`(field ,a ,f) `(field ,(loop a) ,f)]
      [`(arrow ,a ,f) `(arrow ,(loop a) ,f)]
      [`(method ,a ,m ,args ...) `(method ,(loop a) ,m ,@(map loop args))]
      [`(is ,a ,c) `(is ,(loop a) ,c)]
      [`(call ,f ,args ...) `(call ,f ,@(map loop args))]
      [`(const ,_) e]
      [`(src ,_) e]
      ;; bound variables are not replaced inside (a parameter of the same name is shadowed)
      [`(,(and q (or 'forall 'exists)) ,bs ,body)
       `(,q ,bs ,(subst-expr body (filter (lambda (b) (not (assq (car b) bs))) binding)))]
      [`(,op ,args ...) `(,op ,@(map loop args))]
      [_ e])))

;; requires-instance : api (ARG ...) (GARG ...) [((T . TYPE) ...)] -> (E ...)
;; The callee's requires clauses with its parameter names replaced by the
;; arguments, and its type parameters by their instances where they occur in
;; the type arguments of a called name (`align_of_as_usize::<T>`,
;; `Cursor::<C, G>::..`): the only place a spec expression spells a type.
;; Written in the client's body they mean "the precondition holds now"
;; (assert-requires, 结论19); lifted, they become the client's requires (结论8).
(define (requires-instance api args gargs [types '()])
  (define names (map param-name (append (api-params api) (api-ghost-params api))))
  (define binding
    (for/list ([n (in-list names)] [a (in-list (append args gargs))])
      (cons n (match a ['(none) '(const None)] [`(spec ,e) e] [(? symbol? x) x]))))
  ;; in a template (a clause kept as source text), `None` cannot be simplified
  ;; away and rustc cannot infer its type: written `None::<T>` there
  (define typed-none
    (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
               [a (in-list (append args gargs))]
               #:when (equal? a '(none)))
      (cons (param-name p)
            (match (subst-type (param-type p) types)
              [`(Option ,t) `(const ,(string->symbol (format "None::<~a>" (type->text t))))]
              [_ '(const None)]))))
  (for/list ([r (in-list (api-requires api))])
    (define r* (match r
                 [`(tmpl ,ps ...) `(tmpl ,@(for/list ([p (in-list ps)])
                                             (cond [(and (symbol? p) (assq p typed-none)) => cdr] [else p])))]
                 [_ r]))
    (simplify-none (subst-type-args (subst-expr r* binding) types))))

;; subst-type-args : E ((T . TYPE) ...) -> E
;; In the names of calls and methods, a type parameter is replaced by the Rust
;; spelling of its instance: a whole identifier not after `::` (`Trait::M` is
;; an item), so `<M1 as OwnerOf>::wf`, `M::ReprPerm`, `size_of::<T>` and
;; `Cursor::<C, G>::f` alike.  (Until 2026-11-13 only between `<` or `, ` and
;; `>` or `,`: the source's `<M1 as OwnerOf>::wf` kept M1 where the client's
;; second call has M1_g, E0308.)  All at once: an instance may name another.
(define (subst-type-args e types)
  (define ts (filter (lambda (b) (not (eq? (car b) (cdr b)))) types))
  (define rx (and (pair? ts)
                  (pregexp (format "(?<![A-Za-z0-9_])(?<!::)(~a)(?![A-Za-z0-9_])"
                                   (string-join (map (lambda (b) (regexp-quote (symbol->string (car b)))) ts) "|")))))
  (define (rename f)
    (define s (symbol->string f))
    (if (not rx)
        f
        (string->symbol
         (regexp-replace* rx s (lambda (all x) (type->text (cdr (assq (string->symbol x) ts))))))))
  (let loop ([e e])
    (match e
      [`(method ,a ,m ,args ...) `(method ,(loop a) ,(if (symbol? m) (rename m) m) ,@(map loop args))]
      [`(call ,f ,args ...) `(call ,(if (symbol? f) (rename f) f) ,@(map loop args))]
      [`(const ,_) e]
      [`(src ,_) e]
      ;; the bound variables' types take the instances too
      [`(,(and q (or 'forall 'exists)) ,bs ,body)
       `(,q ,(for/list ([b (in-list bs)]) (list (car b) (subst-type (cadr b) types))) ,(loop body))]
      [`(,op ,args ...) `(,op ,@(map loop args))]
      [_ e])))

;; simplify-none : E -> E
;; A `None` argument makes `x is None` true and `x is Some` false; the
;; disjuncts and conjuncts that become constant are simplified away, so that
;; no `None` is left whose type rustc cannot infer (such as `(None)->0`).
(define (simplify-none e)
  (match e
    [`(is (const None) None) 'true]
    [`(is (const None) Some) 'false]
    [`(and ,as ...)
     (define xs (map simplify-none as))
     (cond [(memq 'false xs) 'false]
           [else (match (filter (lambda (x) (not (eq? x 'true))) xs)
                   ['() 'true] [(list x) x] [ys `(and ,@ys)])])]
    [`(or ,as ...)
     (define xs (map simplify-none as))
     (cond [(memq 'true xs) 'true]
           [else (match (filter (lambda (x) (not (eq? x 'false))) xs)
                   ['() 'false] [(list x) x] [ys `(or ,@ys)])])]
    [`(not ,a) (match (simplify-none a) ['true 'false] ['false 'true] [x `(not ,x)])]
    [`(implies ,a ,b)
     (match* ((simplify-none a) (simplify-none b))
       [('false _) 'true] [('true y) y] [(x y) `(implies ,x ,y)])]
    [_ e]))
