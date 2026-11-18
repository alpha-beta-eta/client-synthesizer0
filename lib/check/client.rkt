#lang racket/base
;; Clients and their well-formedness check (design.md, 结论4-8).
;;
;; A client as written (by hand or by enum.rkt):
;;   (client NAME [(source "...")] [(type-params TP ...)]
;;           (params (X MODE TYPE) ...) [(requires E ...)] (body STMT ...))
;;   TP   = T | (T BOUND ...)    bounds besides those the calls give (结论6), e.g. for
;;                               a type parameter used only in spec expressions
;;   STMT = (let X CALL) | (do CALL) | (ghost X E) | (assert E ["from" [(by MODE)]])
;;        | (proof-text "stmt; ..")                      proof steps, as text (a claim's)
;;        | (assert-requires API (ARG ...) (GARG ...) [(types (T TYPE) ...)])
;;                                                       the callee's requires, here
;;        | (if-let (Ok|Err|Some X) Y STMT ...)          no else branch
;;        | (if-let (Ok|Err|Some X) Y (then STMT ...) (else STMT ...))
;;        | (if-let (Ok X) Y (then STMT ...) (else (Err E) STMT ...))   the else branch binds the Err payload
;;        | (untuple ((X MODE) ...) Y)                   Y, an exec tuple, taken apart (moved); MODE
;;                                                       exec|tracked|ghost per component (`Tracked<T>`)
;;        | (if-not X STMT ...)
;;        | (if XE (then STMT ...) (else STMT ...))      XE: an exec condition (结论22)
;;        | (repeat N (invariant INV ...) STMT ...)       a loop run N times (结论26)
;;   INV  = E | (requires-of API (ARG ...) (GARG ...))
;;   XE   = X | INTEGER | true | false | (const NAME) | (== XE XE) | ... | (not XE) | (and XE ...)
;;   CALL = (call API (ARG ...) (GARG ...) [-> G] [(types (T TYPE) ...)])
;;          receiver is the first ARG; types gives type parameters the arguments do not determine
;;   ARG  = X | (none) | (spec E)
;;   E    = X | INTEGER | true | false | (const NAME) | (src "...")
;;        | (== E E) | (!= E E) | (< E E) | (<= E E) | (> E E) | (>= E E) | (+ E E) | (- E E) | (* E E)
;;        | (% E E) | (/ E E) | (<< E E) | (>> E E) | (bitand E E) | (bitor E E) | (bitxor E E)
;;        | (=~= E E) | (=~~= E E) | (call || E ...) (a tuple)
;;        | (not E) | (and E ...) | (or E ...) | (implies E E)
;;        | (deref E) | (borrow E) | (old E) | (view E) | (field E NAME) | (arrow E NAME) | (method E NAME E ...)
;;        | (is E NAME) | (call NAME E ...) | (as E (const TYPE))      an integer cast
;;
;; check-client turns it into the elaborated form that render.rkt writes out,
;; with everything render.rkt needs decided here:
;;   (client NAME (source S) (generics (T BOUND ...) ...) (params ...)
;;           (requires E ...) (body ESTMT ...))
;;   ESTMT = (call ID BIND API (args A ...) (gargs A ...) (gret G) (subst (T . TYPE) ...))
;;         | (ghost ID X E) | (assert ID E FROM) | (assert-requires ID API (E ...))
;;         | (if-let ID CTOR X Y (then ESTMT ...) (else ESTMT ...) [(err E)]) | (if-not ID X ESTMT ...)
;;         | (untuple ID ((X MODE TYPE) ...) Y)
;;         | (if ID XE (then ESTMT ...) (else ESTMT ...)) | (repeat ID N (invariant E ...) ESTMT ...)
;;   ID    = "s3.2": the 2nd statement in the body of the 3rd; "s3.e1": the 1st of its else branch
;;   A     = (KIND X) | (none) | (spec E)     KIND says how X is passed (结论7)
;; or, when the client is not well-formed,
;;   (ill-formed NAME (source S) (at ID) FACT)
(require racket/list racket/match "../model/api.rkt" "../base/forms.rkt" "../model/spec.rkt")
(provide check-client client-name
         (struct-out st) (struct-out var) (struct-out ill)
         initial-state check-call bind-call check-stmt enter-if-let merge-branches
         usable-vars spec-read unclosed type-param-name lift-clauses liftable?)

;; ================================================================ state

;; var: one variable in scope.
;;   mode    exec | tracked | ghost
;;   state   live | moved | (dead ID)       dead: a borrow it held was invalidated at ID
;;   param?  a parameter of the client
;;   touched? passed by `&mut` or moved since entry (结论8: requires are lifted only before this)
;;   borrows variables it borrows from; mutating or moving any of them kills it
(struct var (mode type state param? touched? borrows) #:transparent)

;; st: the checking state.  env: name -> var; bounds: type param -> bounds;
;; requires: lifted clauses, in order; used: the variables some call took as an
;; argument (any way, a copy too), for lift-clauses' second exception.
(struct st (table env bounds requires used) #:transparent)

;; ill: raised for a client that is not well-formed.
(struct ill (id fact) #:transparent)

(define (fail id . fact) (raise (ill id fact)))

(define (initial-state table type-params params)
  (st table
      (for/hash ([p (in-list params)])
        (values (param-name p) (var (param-mode p) (param-type p) 'live #t #f '())))
      (for/hash ([t (in-list type-params)])
        (if (pair? t) (values (car t) (cdr t)) (values t '())))
      '()
      '()))

(define (type-param-name t) (if (pair? t) (car t) t))

(define (lookup s id x)
  (define v (hash-ref (st-env s) x #f))
  (unless v (fail id 'unbound x))
  (match (var-state v)
    ['moved (fail id 'use-after-move x)]
    [`(dead ,at) (fail id 'use-of-invalidated-borrow x 'invalidated-at at)]
    ['live v]))

;; ================================================================ clients

(define (client-name c) (cadr c))

;; check-client : table client -> elaborated client or ill-formed form
(define (check-client table c)
  (define name (client-name c))
  (define source (let ([s (form-ref c 'source #f)]) (if s (car s) "")))
  (define params (form-ref c 'params))
  (define type-params (form-ref c 'type-params))
  (with-handlers ([ill? (lambda (e) `(ill-formed ,name (source ,source) (at ,(ill-id e)) ,(ill-fact e)))])
    (define-values (body s) (check-body (initial-state table type-params params) (form-ref c 'body) '()))
    ;; (allow-open): only probes of the table (结论31) may end with open values.
    (unless (form-flag? c 'allow-open) (check-closed s (lambda (_) #t)))
    `(client ,name (source ,source)
             (generics ,@(for/list ([t (in-list (map type-param-name type-params))])
                           (cons t (hash-ref (st-bounds s) t))))
             (params ,@params)
             (requires ,@(st-requires s) ,@(form-ref c 'requires))
             (body ,@(match* ((form-ref c 'negate #f) (form-ref c 'antecedent #f))
                       [(#f #f) body]
                       [((list (? string? at)) #f) (negate-at body at)]
                       [(#f (list (? string? at))) (antecedent-at body at)])))))

;; (antecedent ID): the clause ID ("s2/1") of an assert-requires, an
;; implication A ==> B, asserted as not A, the rest unchanged.  A vacuity
;; probe (docs/enumeration.md 8.2): if not A verifies, A cannot hold there and
;; the clause passed vacuously, asking nothing of what came before.
(define (antecedent-at body at)
  (match-define (list _ sid k) (or (regexp-match #px"^(.*)/([0-9]+)$" at) (fail at 'no-clause-at at)))
  (define n (string->number k))
  (define found #f)
  (define out
    (let walk ([x body])
      (match x
        [`(assert-requires ,(== sid) ,api ,clauses)
         #:when (<= 1 n (length clauses))
         `(assert-requires ,sid ,api ,(for/list ([c (in-list clauses)] [i (in-naturals 1)])
                                       (match* ((= i n) c)
                                         [(#t `(implies ,a ,_)) (set! found #t) `(not ,a)]
                                         [(_ _) c])))]
        [(cons a d) (cons (walk a) (walk d))]
        [_ x])))
  (unless found (fail at 'no-implication-at at))
  out)

;; (negate ID): the assertion whose error id is ID ("s7", or "s2/1" for the
;; 1st clause of an assert-requires) asserted negated, the rest unchanged.
;; A refutation probe (analysis/refute.rkt): the client is the same up to
;; that point, so if the negation verifies, the original clause is false on
;; every path reaching it that the facts admit.
(define (negate-at body at)
  (define-values (sid n)
    (match (regexp-match #px"^(.*)/([0-9]+)$" at)
      [(list _ s k) (values s (string->number k))]
      [_ (values at #f)]))
  (define found #f)
  (define out
    (let walk ([x body])
      (match x
        [`(assert ,(== sid) ,e ,more ...)
         #:when (not n)
         (set! found #t)
         `(assert ,sid (not ,e) ,@more)]
        [`(assert-requires ,(== sid) ,api ,clauses)
         #:when (and n (<= 1 n (length clauses)))
         (set! found #t)
         `(assert-requires ,sid ,api ,(for/list ([c (in-list clauses)] [i (in-naturals 1)])
                                       (if (= i n) `(not ,c) c)))]
        [(cons a d) (cons (walk a) (walk d))]
        [_ x])))
  (unless found (fail at 'no-assertion-at at))
  out)

;; check-body : st (STMT ...) path [prefix] -> (values (ESTMT ...) st)
;; path: the id of the enclosing statement, as a reversed list of segments;
;; prefix: "" for a body, "e" for an else branch.
(define (check-body s stmts path [prefix ""])
  (for/fold ([out '()] [s s] #:result (values (reverse out) s))
            ([stmt (in-list stmts)] [i (in-naturals 1)])
    (define-values (e s2) (check-stmt s stmt (stmt-id path (format "~a~a" prefix i))))
    ;; a call or assert-requires preceded by the client's choice not to panic
    (values (match e [`(begin ,es ...) (append (reverse es) out)] [_ (cons e out)]) s2)))

;; ---------------------------------------------------------------- may_panic
;; A clause `P ==> may_panic()` (`may_panic` uninterpreted) says the callee may
;; panic when P holds; it is satisfied only where not P can be proved.  A real
;; caller decides not to call it so that it panics: it checks the alignment, the
;; count, before.  The client does the same, as an assumption at the call
;; (`assume(!P)`) instead of asserting not P (docs/enumeration.md 17): the panic
;; condition is a choice of the caller, not a fact the earlier calls owe it.  If
;; not P cannot hold there, the path is vacuous and the vacuity assertion at its
;; end says so.  An assert-requires assumes it at the clause itself (render.rkt).
(define (with-no-panic id s clauses e)
  (define ps (filter-map panic-condition clauses))
  (if (null? ps)
      e
      `(begin (assume ,(format "~a/np" id) ,(map (lambda (p) `(not ,p)) ps)) ,e)))

(define (check-stmt s stmt id)
  (match stmt
    [`(let ,x ,call)
     (define-values (e s2) (bind-call s id x call))
     (values (with-no-panic id s (call-clauses s id call) e) s2)]
    [`(do ,call)
     (define-values (e s2) (bind-call s id #f call))
     (values (with-no-panic id s (call-clauses s id call) e) s2)]
    ;; with a type when the value's type is known but cannot be inferred
    ;; where it is bound (a spec function's result whose type parameter no
    ;; argument determines: `let ghost r: PageTablePageMeta<C> = self_.into_spec();`)
    [`(ghost ,x ,e ,t ...)
     (define s1 (spec-read s id e))
     (values `(ghost ,id ,x ,e ,@t)
             (bind-new id s1 x (var 'ghost (cond [(pair? t) (car t)] [(symbol? e) (var-type (lookup s id e))] [else '?])
                                    'live #f #f '())))]
    [`(assert ,e) (check-stmt s `(assert ,e "") id)]
    [`(assert ,e ,from)
     (values `(assert ,id ,e ,from) (spec-read s id e #:moved-ok? (equal? from "claim")))]
    ;; proved by a prover mode (a claim's `(by bit_vector)`, docs/representation.md 4.5)
    [`(assert ,e ,from (by ,(and m (or 'bit_vector 'compute 'compute_only 'nonlinear_arith))))
     (values `(assert ,id ,e ,from (by ,m)) (spec-read s id e #:moved-ok? (equal? from "claim")))]
    ;; proof steps a claim names (`lemma_x(a, b);`), as text
    [`(proof-text ,(? string? t)) (values `(proof-text ,id ,t) s)]
    [`(proof-text ,(and t `(tmpl ,_ ...))) (values `(proof-text ,id ,t) (spec-read s id t #:moved-ok? #t))]
    [`(assert-requires ,name ,args ,gargs ,more ...)
     (define api (or (api-ref (st-table s) name) (fail id 'no-such-api name)))
     (unless (and (= (length args) (length (api-params api)))
                  (= (length gargs) (length (api-ghost-params api))))
       (fail id 'arity name))
     ;; the type parameters the arguments do not determine, as a call gives them
     (define types (call-types `(call ,name ,args ,gargs ,@more)))
     (define clauses (clauses-for s api args gargs (append types (arg-types s api args gargs))))
     (values `(assert-requires ,id ,name ,clauses)
             (for/fold ([s s]) ([c (in-list clauses)]) (spec-read s id c)))]
    [`(if-let (,ctor ,x) ,y (then ,tb ...) (else (Err ,e) ,eb ...))
     #:when (and (eq? ctor 'Ok) (symbol? e))
     (define-values (st-then st-else) (enter-if-let s id ctor x y #:err e))
     (define-values (etb s-then) (check-body st-then tb (path-of id)))
     (define-values (eeb s-else) (check-body st-else eb (path-of id) "e"))
     (values `(if-let ,id ,ctor ,x ,y (then ,@etb) (else ,@eeb) (err ,e)) (merge-branches s s-then s-else id))]
    [`(if-let (,ctor ,x) ,y (then ,tb ...) (else ,eb ...))
     (define-values (st-then st-else) (enter-if-let s id ctor x y))
     (define-values (etb s-then) (check-body st-then tb (path-of id)))
     (define-values (eeb s-else) (check-body st-else eb (path-of id) "e"))
     (values `(if-let ,id ,ctor ,x ,y (then ,@etb) (else ,@eeb)) (merge-branches s s-then s-else id))]
    [`(untuple ((,xs ,modes) ...) ,y)
     (define v (lookup s id y))
     (unless (eq? (var-mode v) 'exec) (fail id 'not-exec y))
     (define ts (match (var-type v)
                  [`(tuple ,ts ...) #:when (= (length ts) (length xs)) ts]
                  [t (fail id 'not-a-tuple-of (length xs) t)]))
     (for ([m (in-list modes)]) (unless (memq m '(exec tracked ghost)) (fail id 'bad-mode m)))
     (define s1 (consume s id y v))
     ;; each component borrows what the tuple borrowed (the pointer and the
     ;; permission of `ref_as_raw(&x)` both still borrow x)
     (values `(untuple ,id ,(map list xs modes ts) ,y)
             (for/fold ([s s1]) ([x (in-list xs)] [m (in-list modes)] [t (in-list ts)])
               (bind-new id s x (var m t 'live #f #f (var-borrows v)))))]
    [`(if-let (,ctor ,x) ,y ,body ...)
     (check-stmt s `(if-let (,ctor ,x) ,y (then ,@body) (else)) id)]
    [`(if ,e (then ,tb ...) (else ,eb ...))
     (check-exec-expr s id e)
     (define-values (etb s-then) (check-body s tb (path-of id)))
     (define-values (eeb s-else) (check-body s eb (path-of id) "e"))
     (values `(if ,id ,e (then ,@etb) (else ,@eeb)) (merge-branches s s-then s-else id))]
    [`(repeat ,n (invariant ,invs ...) ,body ...)
     (define v (lookup s id n))
     (unless (and (eq? (var-mode v) 'exec) (eq? (var-type v) 'usize)) (fail id 'not-exec-usize n))
     (define clauses
       (append* (for/list ([inv (in-list invs)])
                  (match inv
                    [`(requires-of ,name ,args ,gargs)
                     (let ([api (or (api-ref (st-table s) name) (fail id 'no-such-api name))])
                       (clauses-for s api args gargs (arg-types s api args gargs)))]
                    [e (list e)]))))
     (define s0 (lift-clauses (for/fold ([s s]) ([c (in-list clauses)]) (spec-read s id c)) clauses))
     (define-values (eb s2) (check-body s0 body (path-of id)))
     ;; The body runs again: it may not move or invalidate what was there before.
     (for ([(k v0) (in-hash (st-env s))] #:when (eq? (var-state v0) 'live))
       (define v1 (hash-ref (st-env s2) k))
       (unless (eq? (var-state v1) 'live) (fail id 'moved-in-loop k (var-state v1))))
     (values `(repeat ,id ,n (invariant ,@clauses) ,@eb) (leave-scope s0 s2 id))]
    [`(if-not ,x ,body ...)
     (define v (lookup s id x))
     (unless (and (eq? (var-mode v) 'exec) (eq? (var-type v) 'bool)) (fail id 'not-exec-bool x))
     (define-values (eb s2) (check-body s body (path-of id)))
     (values `(if-not ,id ,x ,@eb) (leave-scope s s2 id))]
    [_ (fail id 'unknown-statement stmt)]))

;; enter-if-let : st id CTOR X Y -> (values st-then st-else)
;; Both branches see Y moved; the then branch also has X, which borrows what
;; Y borrowed: the CursorMut inside the Option that `cursor_mut_at(&mut list)`
;; returned still borrows the list, so it dies when the list is borrowed
;; again (E0499/E0502 when it is used after; design.md 3.3).
;; With #:err E (ctor Ok), the else branch has E, the Err payload, which
;; borrows what Y borrowed too.
(define (enter-if-let s id ctor x y #:err [e #f])
  (define v (lookup s id y))
  (unless (eq? (var-mode v) 'exec) (fail id 'not-exec y))
  (define inner
    (match* (ctor (var-type v))
      [('Ok `(Result ,t ,_)) t]
      [('Err `(Result ,_ ,e)) e]
      [('Some `(Option ,t)) t]
      [(_ t) (fail id 'pattern-mismatch ctor t)]))
  (define s1 (consume s id y v))
  (define s-else
    (if e
        (match (var-type v)
          [`(Result ,_ ,et) (bind-new id s1 e (var 'exec et 'live #f #f (var-borrows v)))])
        s1))
  (values (bind-new id s1 x (var 'exec inner 'live #f #f (var-borrows v))) s-else))

;; Variables bound inside a nested body go out of scope; whatever the body
;; did to outer variables (moves, invalidated borrows) stays, since the body
;; may have run.  A value of a must-close type may not go out of scope
;; unclosed (结论21).
(define (leave-scope outer inner [id "end"])
  (check-closed inner (lambda (k) (not (hash-ref (st-env outer) k #f))) id)
  (struct-copy st inner
               [env (for/hash ([(k v) (in-hash (st-env inner))] #:when (hash-ref (st-env outer) k #f))
                      (values k v))]))

;; check-closed : st (X -> boolean) -> void
;; Every live variable selected by leaving? whose type is must-close.
;; id: the statement whose body is being left, or "end" for the client's.
(define (check-closed s leaving? [id "end"])
  (for ([k (in-list (unclosed s))] #:when (leaving? k))
    (fail id 'not-closed k (var-type (hash-ref (st-env s) k)))))

;; unclosed : st -> (X ...), live variables of must-close types.
(define (unclosed s)
  (for/list ([(k v) (in-hash (st-env s))]
             #:when (and (eq? (var-state v) 'live) (must-close-type? (st-table s) (var-type v))))
    k))

;; check-exec-expr : st id E -> void
;; A condition of exec code: exec variables of Copy type, constants, comparisons (结论22).
(define (check-exec-expr s id e)
  (let loop ([e e])
    (match e
      [(or 'true 'false) (void)]
      [(? exact-integer?) (void)]
      [`(const ,_) (void)]
      [(? symbol? x)
       (define v (lookup s id x))
       (unless (and (eq? (var-mode v) 'exec) (copy-type? (st-table s) (var-type v)))
         (fail id 'not-exec-copy x))]
      [`(,(or '== '!= '< '<= '> '>= '+ '- '* 'and 'or 'not) ,args ...) (for-each loop args)]
      [_ (fail id 'bad-exec-expression e)])))

;; merge-branches : st st st [id] -> st
;; After an if-let or if with two branches: a variable is moved, invalidated
;; or touched if it is in either branch.  The requires lifted in either branch
;; are kept: the caller cannot choose the branch, so it must meet both (注意19).
(define (merge-branches outer a b [id "end"])
  (define a* (leave-scope outer a id))
  (define b* (leave-scope outer b id))
  (define (worse x y)
    (cond [(eq? (var-state x) 'moved) x]
          [(eq? (var-state y) 'moved) y]
          [(pair? (var-state x)) x]
          [(pair? (var-state y)) y]
          [else x]))
  (struct-copy st a*
               [env (for/hash ([(k va) (in-hash (st-env a*))])
                      (define vb (hash-ref (st-env b*) k))
                      (values k (struct-copy var (worse va vb)
                                             [touched? (or (var-touched? va) (var-touched? vb))])))]
               [bounds (for/hash ([(t bs) (in-hash (st-bounds a*))])
                         (values t (remove-duplicates (append bs (hash-ref (st-bounds b*) t '())))))]
               [requires (remove-duplicates (append (st-requires a*) (st-requires b*)))]
               [used (remove-duplicates (append (st-used a*) (st-used b*)))]))

(define (env-set s x v) (struct-copy st s [env (hash-set (st-env s) x v)]))

;; bind-new : id st X var -> st, a new variable.  A name may not be bound
;; twice: rebinding would hide the outer value (and an open must-close value
;; with it), and these scoping rules do not model shadowing.
(define (bind-new id s x v)
  (when (hash-ref (st-env s) x #f) (fail id 'rebinding x))
  (env-set s x v))

;; ================================================================ calls

;; check-call : st id CALL -> (values api args gargs subst effects)
;; Resolves every argument against the parameter it is passed to (结论7).
;; effects: list of (mut X) / (move X) / (borrow X), applied by bind-call.
(define (check-call s id call)
  (match-define `(call ,name ,args ,gargs ,@_) call)
  (define api (or (api-ref (st-table s) name) (fail id 'no-such-api name)))
  ;; Facts about a call name the API.
  (with-handlers ([ill? (lambda (e) (raise (ill (ill-id e) `(in ,name ,@(ill-fact e)))))])
    (check-call* s id api args gargs (call-types call))))

;; call-types : CALL -> ((T . TYPE) ...), the explicit `(types (T TYPE) ...)`:
;; type parameters the arguments do not determine (e.g. `Frame::<M>::from_raw`).
(define (call-types call)
  (or (for/first ([x (in-list (cddddr call))] #:when (and (pair? x) (eq? (car x) 'types)))
        (map (lambda (p) (cons (car p) (cadr p))) (cdr x)))
      '()))

(define (call-gret call)
  (let loop ([xs (cddddr call)])
    (match xs [(list* '-> g _) g] [(cons _ rest) (loop rest)] ['() #f])))

(define (check-call* s id api args gargs types)
  (define name (api-name api))
  (when (eq? (api-mode api) 'spec) (fail id 'spec-function-called name))
  (define params (api-params api))
  (define gparams (api-ghost-params api))
  (unless (= (length args) (length params)) (fail id 'arity name (length params) (length args)))
  (unless (= (length gargs) (length gparams)) (fail id 'ghost-arity name (length gparams) (length gargs)))
  (define vars (map car (api-generics api)))
  (for ([t (in-list types)]) (unless (memq (car t) vars) (fail id 'not-a-type-parameter (car t))))
  ;; a lifetime for a type parameter (or the reverse) is a syntax error that
  ;; stops rustc before it reports any other client
  (define (lifetime? x) (and (symbol? x) (regexp-match? #rx"^'" (symbol->string x))))
  (for ([t (in-list types)])
    (unless (eq? (lifetime? (car t)) (lifetime? (cdr t))) (fail id 'lifetime-mismatch (car t) (cdr t))))
  (define-values (resolved subst effects)
    (for/fold ([out '()] [subst types] [effects '()] #:result (values (reverse out) subst effects))
              ([p (in-list (append params gparams))] [a (in-list (append args gargs))])
      (define-values (r subst2 eff) (resolve-arg s id p a vars subst))
      (values (cons r out) subst2 (append effects eff))))
  (check-conflicts id effects)
  ;; A table writes every lifetime of a signature as the one `'a` (design.md 3.2, 3.3).
  ;; A lifetime is never written in a call (rustc infers it), unless a bound
  ;; names it: then the bound, lifted to the client, is on the client's own
  ;; `'a`, which outlives the body, and a local borrowed for the call would
  ;; have to live as long (E0597: `get` on a guard from `read` of a local
  ;; `Rcu`, with `P: NonNullPtrRef<'a>`).
  (define (bound-mentions? v)
    (for/or ([b (in-list (api-generics api))])
      (let mentions? ([x (cdr b)]) (if (pair? x) (ormap mentions? x) (eq? x v)))))
  (when (for/or ([v (in-list vars)])
          (define t (assq v subst))
          (and (lifetime? v) t (lifetime? (cdr t)) (not (eq? (cdr t) '|'_|)) (bound-mentions? v)))
    (for ([p (in-list params)] [a (in-list args)]
          #:when (and (symbol? a) (eq? (param-mode p) 'exec) (ref-type? (param-type p))))
      (define v (hash-ref (st-env s) a #f))
      ;; a value held in the body, a parameter too (a guard passed by value)
      (when (and v (not (ref-type? (var-type v))))
        (fail id 'local-borrowed-for-client-lifetime (param-name p) a))))
  ;; The same for any mode, from the source's lifetimes (item-index): a
  ;; reference parameter whose own lifetime is the one the bound names
  ;; (`borrow_perm_as_ref_perm(tracked perm: &'a Self::Permission)` with
  ;; `L: NonNullPtrRef<'a>`) is borrowed for the client's `'a`, so a value held
  ;; in the body cannot be passed (E0597; the permission an untupled `into_raw`
  ;; gave).  `borrow_ref_perm(tracked perm: &Self::RefPermission)`, elided,
  ;; takes it; so does `reader(&'a self)`, whose `'a` no bound names (rustc
  ;; picks a short one).  design.md 3.1.
  (for ([p (in-list params)] [a (in-list args)]
        #:when (and (symbol? a) (ref-type? (param-type p))))
    (define l (param-source-lifetime api (param-name p)))
    (define lv (and l (string->symbol (string-append "'" l))))
    (define t (and lv (assq lv subst)))
    (when (and t (lifetime? (cdr t)) (not (eq? (cdr t) '|'_|)) (bound-mentions? lv))
      (define v (hash-ref (st-env s) a #f))
      (when (and v (not (ref-type? (var-type v))))
        (fail id 'local-borrowed-for-client-lifetime (param-name p) a))))
  ;; The elided `'_` where a bound names the lifetime (`get` on a guard of a
  ;; local: `P: NonNullPtrRef<'_>`): only a higher-ranked bound on the
  ;; client's `P` would do, and the tables cannot write one (design.md 3.3).
  (for ([v (in-list vars)] #:when (lifetime? v))
    (define t (assq v subst))
    (when (and t (eq? (cdr t) '|'_|)
               (for/or ([b (in-list (api-generics api))])
                 (let mentions? ([x (cdr b)]) (if (pair? x) (ormap mentions? x) (eq? x v)))))
      (fail id 'elided-lifetime-in-bound v)))
  (define-values (rargs rgargs) (split-at resolved (length params)))
  (values api rargs rgargs subst effects))

;; resolve-arg : st id param ARG vars subst -> (values A subst effects)
(define (resolve-arg s id p a vars subst)
  (define pt (param-type p))
  (define pname (param-name p))
  (match* ((param-mode p) a)
    [('spec `(spec ,e))
     (spec-read s id e)
     (define et (spec-type s id e))
     (define s2 (if et
                    (or (match-type (strip-ref pt) et vars subst) (fail id 'type-mismatch pname pt et))
                    subst))
     (values `(spec ,e) s2 (for/list ([x (in-list (expr-vars e))]) `(read ,x)))]
    [('spec (? symbol? x))
     (define v (lookup s id x))
     (define s2 (or (match-type (strip-ref pt) (strip-ref (var-type v)) vars subst)
                    (fail id 'type-mismatch pname pt (var-type v))))
     ;; a reference passed for a spec parameter that is not one is passed
     ;; dereferenced (`perm: &BoxPointsToRef` to a lemma's `perm: BoxPointsToRef`);
     ;; a value for one that is, borrowed (`lemma_view_in_vaddr_range(&v0)` for
     ;; `owner: &CursorOwner`)
     (values (cond [(and (ref-type? (var-type v)) (not (ref-type? pt))) `(spec (deref ,x))]
                   [(and (not (ref-type? (var-type v))) (pair? pt) (eq? (car pt) '&)) `(spec (borrow ,x))]
                   [else `(spec ,x)])
             s2 '())]
    [('tracked '(none))
     (match pt
       [`(Option ,_) (values '(none) subst '())]
       [_ (fail id 'none-for-non-option pname pt)])]
    [((and mode (or 'exec 'tracked)) (? symbol? x))
     (define v (lookup s id x))
     (unless (eq? (var-mode v) mode) (fail id 'mode-mismatch pname mode x (var-mode v)))
     (pass s id pname pt x v vars subst)]
    [(mode _) (fail id 'bad-argument pname mode a)]))

;; pass: how variable x of type (var-type v) is passed to a parameter of type pt.
(define (pass s id pname pt x v vars subst)
  (define vt (var-type v))
  (define (m pat typ) (or (match-type pat typ vars subst) (fail id 'type-mismatch pname pt vt)))
  (match* (pt vt)
    ;; `&'static T` (docs/representation.md 5c): only a value that is `&'static`
    ;; itself (a client parameter declared so, or a result such as
    ;; `tracked_borrow_slot`'s); a local or an ordinary reference does not live
    ;; that long (E0521, E0597).  The other way, a `&'static` value goes where
    ;; `&` is taken.
    [(`(&static ,t) `(&static ,u)) (values `(same ,x) (m t u) '())]
    [(`(&static ,_) _) (fail id 'not-static pname x vt)]
    [(`(& ,t) `(&static ,u)) (values `(same ,x) (m t u) '())]
    [(`(& ,t) `(& ,u)) (values `(same ,x) (m t u) `((borrow ,x)))]
    [(`(& ,t) `(&mut ,u)) (values `(reref ,x) (m t u) `((borrow ,x)))]
    [(`(& ,t) u) (values `(ref ,x) (m t u) `((borrow ,x)))]
    [(`(&mut ,t) `(&mut ,u)) (values `(same ,x) (m t u) `((mut ,x)))]
    [(`(&mut ,_) `(& ,_)) (fail id 'mutable-borrow-through-shared-ref pname x vt)]
    [(`(&mut ,t) u) (values `(mutref ,x) (m t u) `((mut ,x)))]
    [(t `(&mut ,u)) #:when (not (copy-type? (st-table s) u))
     (fail id 'move-out-of-borrow `(param ,pname ,t) `(arg ,x ,vt))]
    [(t u)
     (define s2 (m t u))
     (if (copy-type? (st-table s) u)
         (values `(copy ,x) s2 '())
         (values `(move ,x) s2 `((move ,x))))]))

;; A variable moved or mutably borrowed may not be used again in the same call
;; (by an exec argument: a spec argument's reads, `read`, do not count).
(define (check-conflicts id effects)
  (define uses (for/list ([e (in-list effects)] #:unless (eq? (car e) 'read)) (cadr e)))
  (for ([e (in-list effects)] #:when (memq (car e) '(mut move)))
    (when (> (count (lambda (y) (eq? y (cadr e))) uses) 1)
      (fail id 'conflicting-use (cadr e)))))

(define (untouched-param? s x)
  (define v (hash-ref (st-env s) x #f))
  (and v (var-param? v) (not (var-touched? v))))

;; param-invariant? : st E -> boolean; `p.inv()` or `p.wf()` (p possibly
;; dereferenced) of a client parameter p that is still live
(define (param-invariant? s e)
  (match e
    [`(method ,(or (? symbol? x) `(deref ,(? symbol? x))) ,(or 'inv 'wf))
     (define v (hash-ref (st-env s) x #f))
     (and v (var-param? v) (eq? (var-state v) 'live))]
    [_ #f]))

;; call-clauses : st id CALL -> (E ...); the callee's requires for this call,
;; in the state before it
(define (call-clauses s id call)
  (define-values (api _args _gargs subst _effects) (check-call s id call))
  (clauses-for s api (caddr call) (cadddr call) subst))

;; bind-call : st id X-or-#f CALL -> (values ESTMT st)
(define (bind-call s id x call)
  (define-values (api args gargs subst effects) (check-call s id call))
  (define gret (call-gret call))
  (when (and (api-ghost-ret api) (not gret)) (fail id 'ghost-return-not-bound (api-name api)))
  (when (and gret (not (api-ghost-ret api))) (fail id 'no-ghost-return (api-name api)))
  (define ret (api-ret api))
  (when (and x (not ret)) (fail id 'unit-result-bound (api-name api) x))
  (define s1 (add-bounds (lift-requires s api (caddr call) (cadddr call) subst) id api subst))
  (define s2 (mark-used (apply-effects s1 id effects) (append (caddr call) (cadddr call))))
  (define ret-type (and ret (subst-type ret subst)))
  (check-inferred id api subst)
  ;; a mutable borrow of x is recorded also as (mut . x): while the borrower
  ;; lives, a spec use of x ends it, as a shared borrow does (spec-read)
  ;; arguments for parameters whose borrow cannot reach the result (the
  ;; table's no-flow, from the source's lifetimes) are not borrowed by it
  (define no-flow-args
    (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
               [a (in-list (append (caddr call) (cadddr call)))]
               #:when (and (symbol? a) (memq (param-name p) (api-no-flow api))))
      a))
  (define borrowed (remove-duplicates
                    (append* (for/list ([e (in-list effects)]
                                        #:when (and (memq (car e) '(borrow mut)) (not (memq (cadr e) no-flow-args))))
                               (append (list (cadr e))
                                       (if (eq? (car e) 'mut) (list (cons 'mut (cadr e))) '())
                                       (var-borrows (hash-ref (st-env s) (cadr e))))))))
  (define s3
    (if x
        ;; a result that is a reference, or whose type carries the lifetime
        ;; (a `CursorMut<'a, M>` from `&'a mut self`), borrows from the
        ;; arguments passed by reference (注意1, 14); so does an associated
        ;; type of an API with a lifetime (representation.md 5a: `Self::RefPermission`
        ;; of `borrow_perm_as_ref_perm(perm: &'a Self::Permission)` is
        ;; `BoxPointsToRef<'a, T>`; moving perm after is E0505), the table's no-flow
        ;; (from the source, which counts this) saying which ones
        (bind-new id s2 x (var (cond [(api-ret-ghost? api) 'ghost] [(eq? (api-mode api) 'proof) 'tracked] [else 'exec]) ret-type 'live #f #f
                           (if (or (ref-type? ret-type) (carries-lifetime? ret-type)
                                   (and (has-assoc? ret-type)
                                        (for/or ([g (in-list (api-generics api))]) (lifetime-symbol? (car g)))))
                               borrowed '())))
        s2))
  (define s4
    (if gret
        (bind-new id s3 gret (var (car (api-ghost-ret api)) (subst-type (cadr (api-ghost-ret api)) subst)
                              'live #f #f '()))
        s3))
  (values `(call ,id ,x ,(api-name api) (args ,@args) (gargs ,@gargs) (gret ,gret) (subst ,@subst)) s4))

(define (ref-type? t) (and (pair? t) (memq (car t) '(& &mut &static)) #t))

(define (lifetime-symbol? x) (and (symbol? x) (regexp-match? #rx"^'" (symbol->string x))))
(define (carries-lifetime? t)
  (if (pair? t) (ormap carries-lifetime? t) (and (lifetime-symbol? t) (not (eq? t '|'static|)))))
(define (has-assoc? t) (and (pair? t) (or (eq? (car t) 'assoc) (ormap has-assoc? (cdr t)))))

;; param-source-lifetime : api param-name -> "a" or #f
;; The named lifetime of a reference parameter, from the source record
;; (`(p "perm" "&'a Self::Permission" (ref "a" shared) ..)`); #f when elided or unknown.
(define (param-source-lifetime api pname)
  (define src (form-ref api 'source #f))
  (define ps (and (pair? src) (for/first ([x (in-list src)] #:when (and (pair? x) (eq? (car x) 'params))) (cdr x))))
  (for/first ([p (in-list (or ps '()))]
              #:when (and (pair? p) (equal? (cadr p) (symbol->string pname))))
    (match p
      [`(p ,_ ,_ (ref ,(? string? l) ,_) ,_ ...) #:when (not (equal? l "_")) l]
      [_ #f])))

;; Every type parameter of the API must be determined by the arguments.
(define (check-inferred id api subst)
  (for ([g (in-list (api-generics api))])
    (unless (assq (car g) subst) (fail id 'cannot-infer (api-name api) (car g)))))

;; The bounds of the API's type parameters, instantiated, become bounds of
;; the client's type parameters (结论6).  Bounds on concrete types are not
;; checked, except that a trait object (`dyn ..`) satisfies none but
;; `?Sized` (`into_dyn` then `clone`: the methods of `Frame<M>` want
;; `M: Repr<..>`).
(define (add-bounds s id api subst)
  (define (dyn? t)
    (if (pair? t) (ormap dyn? t) (and (symbol? t) (regexp-match? #rx"^dyn " (symbol->string t)))))
  (for/fold ([s s]) ([g (in-list (api-generics api))])
    (define inst (cond [(assq (car g) subst) => cdr] [else #f]))
    (define bs (map (lambda (b) (subst-type b subst)) (cdr g)))
    (when (and inst (dyn? inst) (for/or ([b (in-list bs)]) (not (memq b '(?Sized static)))))
      (fail id 'bound-on-trait-object (api-name api) (car g) inst))
    ;; nor an associated type (`<L as NonNullPtrRef>::Ref` for `into_raw`'s
    ;; `L: NonNullPtr`): the table does not say what it implements, and the
    ;; client cannot add the bound (E0599, the bounds not satisfied)
    (when (and inst (pair? inst) (eq? (car inst) 'assoc) (for/or ([b (in-list bs)]) (not (memq b '(?Sized static)))))
      (fail id 'bound-on-associated-type (api-name api) (car g) inst))
    (if (and (symbol? inst) (hash-ref (st-bounds s) inst #f))
        (struct-copy st s [bounds (hash-update (st-bounds s) inst
                                               (lambda (old) (remove-duplicates (append old bs))))])
        s)))

;; Moving or mutably borrowing x touches it and invalidates every variable
;; borrowing from it.  Borrowing x shared invalidates those that borrow it
;; mutably (`VmWriter::from(slice)` then `VmReader::from(&*slice)`: the
;; writer cannot be used after, E0502).
(define (apply-effects s id effects)
  (define s0
    (for/fold ([s s]) ([e (in-list effects)] #:when (memq (car e) '(borrow read)))
      (define x (cadr e))
      (struct-copy st s
                   [env (for/hash ([(k w) (in-hash (st-env s))])
                          (values k (if (and (member (cons 'mut x) (var-borrows w)) (eq? (var-state w) 'live))
                                        (struct-copy var w [state `(dead ,id)])
                                        w)))])))
  (for/fold ([s s0]) ([e (in-list effects)] #:when (memq (car e) '(mut move)))
    (define x (cadr e))
    (define v (hash-ref (st-env s) x))
    (define s1 (env-set s x (struct-copy var v [touched? #t]
                                         [state (if (eq? (car e) 'move) 'moved (var-state v))])))
    (struct-copy st s1
                 [env (for/hash ([(k w) (in-hash (st-env s1))])
                        (values k (if (and (memq x (var-borrows w)) (eq? (var-state w) 'live))
                                      (struct-copy var w [state `(dead ,id)])
                                      w)))])))

;; if-let moves the scrutinee.
(define (consume s id y v)
  (apply-effects s id (if (copy-type? (st-table s) (var-type v)) '() `((move ,y)))))

;; ================================================================ requires

;; The callee's requires clauses, with its parameter names replaced by the
;; arguments, that mention only client parameters not yet touched become
;; clauses of the client's requires (结论8); the others stay obligations.
;; `old(p)` of the callee becomes the bare argument: render.rkt writes the
;; client's `&mut` parameters as `old(x)` in the client's requires.
(define (lift-requires s api args gargs subst)
  (lift-clauses s (clauses-for s api args gargs subst)))

;; arg-types : st api (ARG ...) (GARG ...) -> subst
;; The API's type parameters as the arguments' types determine them, for
;; requires asserted or used as invariants without a call (assert-requires,
;; requires-of).  Arguments that are not variables, or whose types do not
;; match, determine nothing here.
(define (arg-types s api args gargs)
  (define vars (map car (api-generics api)))
  (for/fold ([subst '()]) ([p (in-list (append (api-params api) (api-ghost-params api)))]
                           [a (in-list (append args gargs))])
    (define v (and (symbol? a) (hash-ref (st-env s) a #f)))
    (or (and v (match-type (strip-ref (param-type p)) (strip-ref (var-type v)) vars subst))
        subst)))

;; clauses-for : st api (ARG ...) (GARG ...) subst -> (E ...)
;; The callee's requires for these arguments and type instances (spec.rkt),
;; with `*x` replaced by `x` where x is not a reference here: the callee may
;; deref a parameter it takes by reference, which the client passes from a
;; value (结论8).
;; And the other way: an argument for a `&` parameter that is a value here,
;; written as an argument of a spec function, is borrowed (`fmt_req(&r, f)`
;; for the callee's `fmt_req(self, f)`, where self is `&Self`); a method
;; receiver needs nothing (auto-ref).
(define (clauses-for s api args gargs subst)
  (define (value-var? x)
    (define v (and (symbol? x) (hash-ref (st-env s) x #f)))
    (and v (not (ref-type? (var-type v)))))
  (define borrowed
    (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
               [a (in-list (append args gargs))]
               #:when (and (pair? (param-type p)) (memq (car (param-type p)) '(& &static)) (value-var? a)))
      a))
  ;; a reference here for a parameter that takes a value (`r: &mut
  ;; MetaSlotStorage` for a lemma's `r: MetaSlotStorage`, passed as `*r`): `*r`
  ;; in the requires too
  (define dereffed
    (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
               [a (in-list (append args gargs))]
               #:when (and (symbol? a) (not (value-var? a)) (hash-ref (st-env s) a #f)
                           (not (ref-type? (param-type p)))))
      a))
  (define (fix e)
    (match e
      [`(deref ,(? symbol? x))
       (if (value-var? x) x e)]
      [(? symbol? x) #:when (memq x dereffed) `(deref ,x)]
      [`(call ,f ,as ...)
       `(call ,f ,@(for/list ([a (in-list as)]) (if (and (symbol? a) (memq a borrowed)) `(borrow ,a) (fix a))))]
      ;; the same for a method's arguments (`self.page_in_range_saturated(range, ..)`
      ;; for `range: &Range<Paddr>`, given `v1`: E0308 without the `&`, 2026-11-11);
      ;; not for its receiver
      [`(method ,recv ,(? symbol? m) ,as ...)
       `(method ,(fix recv) ,m ,@(for/list ([a (in-list as)]) (if (and (symbol? a) (memq a borrowed)) `(borrow ,a) (fix a))))]
      [`(,(and q (or 'forall 'exists)) ,bs ,body) `(,q ,bs ,(fix body))]
      [(? pair?) (map fix e)]
      [_ e]))
  (map fix (requires-instance api args gargs subst)))

;; lift-clauses : st (E ...) -> st; the same rule for any clauses (loop invariants, 结论26).
;; Also an invariant of one client parameter (`p.inv()`, `p.wf()`, design.md
;; 3.4) that a later call requires after p was touched: a real caller holds
;; it from the start (the regions, the owners it threads through), so the
;; client assumes it at entry (`old(p).inv()`) and the call that touched p
;; must keep it.  Not lifting it made every path on which the touching call
;; says nothing (an Err branch) fail at it.
;; And a clause between a parameter no call has used yet and parameters only
;; borrowed `&mut` so far (`p.wf(*regions)` after a call took `&mut regions`):
;; a real caller's p is good at the start, so the client assumes it of the entry
;; values (render writes `&mut` parameters as `old(x)` in its requires), and the
;; call that asks it checks that the calls before kept it (design.md 3.4).
(define (lift-clauses s clauses)
  (define new (for/list ([e (in-list clauses)] #:when (liftable? s e)) e))
  (struct-copy st s [requires (remove-duplicates (append (st-requires s) new))]))

;; liftable? : st E -> boolean, whether lift-clauses makes E a requires of the client.
;; The second exception: every variable a live client parameter, those not borrowed
;; `&mut` yet taken by no call at all (not even copied: `paddr` given to
;; `from_unused` and then to `inc_frame_ref_count` is the same slot, and assuming
;; at the entry what the second call needs would answer the first call's question),
;; and at least one of them.
(define (liftable? s e)
  (define xs (expr-vars e))
  (define (v x) (hash-ref (st-env s) x #f))
  (or (andmap (lambda (x) (untouched-param? s x)) xs)
      (param-invariant? s e)
      (and (pair? xs)
           (for/and ([x (in-list xs)])
             (and (v x) (var-param? (v x)) (eq? (var-state (v x)) 'live)
                  (or (var-touched? (v x)) (not (memq x (st-used s))))))
           (for/or ([x (in-list xs)]) (and (untouched-param? s x) (not (memq x (st-used s)))))
           (not (same-relation-elsewhere? s e)))))

;; same-relation-elsewhere? : st E -> boolean
;; One owner describes one object: a requires already says the same of another
;; object (the clause with its receiver taken out: `self_.0.invariants(*owner, ..)`
;; and `self__g.pt_cursor.0.invariants(*owner, ..)`), so assuming E too would say
;; the owner describes two objects, a contradiction (design.md 3.4).
(define (same-relation-elsewhere? s e)
  (define-values (shape root) (receiver-shape e))
  (and shape
       (for/or ([r (in-list (st-requires s))])
         (define-values (shape2 root2) (receiver-shape r))
         (and shape2 (equal? shape shape2) (not (eq? root root2))))))

;; receiver-shape : E -> (values E-with-the-receiver-taken-out root) or (values #f #f)
(define (receiver-shape e)
  (define (root x)
    (match x
      [(? symbol? v) v]
      [`(,(or 'field 'arrow) ,a ,_) (root a)]
      [`(,(or 'deref 'old) ,a) (root a)]
      [_ #f]))
  (match e
    [`(method ,recv ,m ,args ...) #:when (root recv) (values `(method _ ,m ,@args) (root recv))]
    [_ (values #f #f)]))

;; mark-used : st (A ...) -> st, the variables of a call's arguments as used
(define (mark-used s args)
  (define xs (append* (for/list ([a (in-list args)])
                        (match a
                          [(? symbol? x) (list x)]
                          [`(spec ,e) (expr-vars e)]
                          [`(,_ ,(? symbol? x)) (list x)]
                          [_ '()]))))
  (struct-copy st s [used (remove-duplicates (append (st-used s) xs))]))

;; spec-read : st id E -> st; every variable E mentions must be usable.
;; A spec use of x reads x as a shared borrow does (rustc: E0502 when a
;; value borrowing x mutably is used after `self.wf(owner)` with a CursorMut
;; from `&mut self`): it ends the live values that borrow x mutably, and a
;; later use of one of them is ill-formed (use-of-invalidated-borrow).  Not
;; rejecting the spec use itself: the value may never be used again, and
;; then rustc accepts it (NLL).  design.md 3.3.
;; moved-ok?: an assertion (a claim) may read a variable an earlier call
;; moved, its value when it was moved: Verus accepts `split(self)` followed by
;; a claim about `self_` (r22: 8 such claims compiled; they were text until
;; 2026-11-13, so this was never checked, docs/enumeration.md 7.2).  Not a
;; callee's requires asserted again (assert-requires): a real caller cannot
;; call with a value it gave away (principle 4).  No read of a variable whose
;; borrow was invalidated.
(define (spec-read s id e #:moved-ok? [moved-ok? #f])
  (define xs (expr-vars e))
  (for ([x (in-list xs)])
    (define v (hash-ref (st-env s) x #f))
    (if (and moved-ok? v (eq? (var-state v) 'moved))
        (void)
        (lookup s id x)))
  (apply-effects s id (for/list ([x (in-list xs)]) `(read ,x))))

;; spec-type : st id E -> TYPE or #f
;; The type of a spec expression where it is simple to know: a variable, or
;; a one-parameter spec function of the table applied as a method to an
;; expression of known type.  A receiver of the wrong type is not
;; well-formed; otherwise unknown (#f), and Verus decides (注意2).
(define (spec-type s id e)
  (match e
    [(? symbol? x) (let ([v (hash-ref (st-env s) x #f)]) (and v (strip-ref (var-type v))))]
    [`(method ,a ,m)
     (define at (spec-type s id a))
     ;; the spec methods of that name; the one whose receiver type matches
     (define fs (for*/list ([n (in-list (table-names (st-table s)))]
                            [api (in-value (api-ref (st-table s) n))]
                            #:when (and (eq? (api-mode api) (quote spec)) (equal? (api-call api) (list (quote method) m))
                                        (= 1 (length (api-params api)))))
                  api))
     (define hit
       (and at (for/or ([f (in-list fs)])
                 (define sub (match-type (strip-ref (param-type (car (api-params f)))) at (map car (api-generics f)) (quote ())))
                 (and sub (subst-type (api-ret f) sub)))))
     (cond [(or (not at) (null? fs)) #f]
           [hit hit]
           [else (fail id (quote type-mismatch) m at)])]
    [_ #f]))

;; usable-vars : st -> ((X . var) ...), live variables, by name (for enum.rkt).
(define (usable-vars s)
  (sort (for/list ([(k v) (in-hash (st-env s))] #:when (eq? (var-state v) 'live)) (cons k v))
        symbol<? #:key car))
