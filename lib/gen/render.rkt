#lang racket/base
;; Rendering elaborated clients to a Verus module (design.md, 结论9).
;; All knowledge of the surface syntax is here; client.rkt has already
;; decided how every argument is passed.
;;
;; Every call and assertion is written on a line of its own, and render-module
;; returns a line map, so that run.rkt can attribute Verus's errors (结论10).
(require racket/list racket/match racket/string "../model/api.rkt" (only-in "../model/spec.rkt" panic-condition))
(provide render-module expr->text top->text sanity-name vacuity? vacuity-id? client-module)

(define sanity-name 'client_sanity)

;; render-module : table (elaborated-client ...) -> (values string linemap)
;;   linemap = ((item LINE CLIENT ID) ... (client CLIENT START END) ...)
(define (render-module table clients)
  (define lines '())
  (define lmap '())
  (define (emit! s [item #f])
    (set! lines (cons s lines))
    (when item (set! lmap (cons `(item ,(length lines) ,@item) lmap))))
  (for ([u (in-list (api-table-uses table))]) (emit! u))
  (emit! "")
  (emit! "verus! {")
  (emit! "")
  (emit! "/// Must fail: shows that this module is verified.")
  (emit! (format "fn ~a() {" sanity-name))
  (emit! "    assert(false);" (list sanity-name "s1"))
  (emit! "}")
  (for ([c (in-list clients)])
    (emit! "")
    (define start (add1 (length lines)))
    (render-client table c emit!)
    (set! lmap (cons `(client ,(cadr c) ,start ,(length lines)) lmap)))
  (emit! "")
  (emit! "} // verus!")
  (values (string-append (string-join (reverse lines) "\n") "\n") (reverse lmap)))

(define (render-client table c emit!)
  (match-define `(client ,name (source ,source) (generics ,gens ...) (params ,params ...)
                         (requires ,reqs ...) (body ,body ...)) c)
  (define olds (for/list ([p (in-list params)] #:when (match (param-type p) [`(&mut ,_) #t] [_ #f]))
                 (param-name p)))
  (unless (equal? source "") (emit! (format "/// ~a" source)))
  ;; each client in a solver of its own: Verus otherwise gives the whole client
  ;; module one z3 session, verified serially (design.md 4.1)
  (emit! "#[verifier::spinoff_prover]")
  (emit! (format "fn ~a~a(" name (generics->text gens)))
  ;; A client's shared reference parameter lives as long as its lifetime 'a:
  ;; an API may want it (`cursor(&'a self, guard: &'a G, ..)`, where VIR,
  ;; and so the table, has lost the reference's lifetime: E0621), and the
  ;; body can always borrow it for less.
  (define long? (for/or ([g (in-list gens)]) (eq? (car g) '|'a|)))
  (for ([p (in-list params)])
    (emit! (format "    ~a," (match p
                               [(list x 'exec `(& ,t)) #:when long? (format "~a: &'a ~a" x (type->text t))]
                               [(list x 'tracked `(& ,t)) #:when long? (format "Tracked(~a): Tracked<&'a ~a>" x (type->text t))]
                               [_ (param->text p)]))))
  (emit! ")")
  (unless (null? reqs)
    (emit! "    requires")
    (for ([r (in-list reqs)]) (emit! (format "        ~a," (top->text r olds)))))
  (emit! "{")
  ;; An owned tracked parameter may be lent as `&mut`; Verus does not take
  ;; `Tracked(mut x)` in a parameter list, so it is rebound.
  (for ([p (in-list params)] #:when (and (eq? (param-mode p) 'tracked) (owned? (param-type p))))
    (emit! (format "    let tracked mut ~a = ~a;" (param-name p) (param-name p))))
  (parameterize ([var-types (make-hasheq)])
    (for ([p (in-list params)])
      (bound! table (param-name p) (param-mode p) (param-type p) "    " emit! (list name "s0")))
    (render-body table name body 1 emit! (and (vacuity?) "end")))
  (emit! "}"))

;; The types of the client's variables as rendering goes (an if-let's binder
;; takes its type from the scrutinee's).
(define var-types (make-parameter #f))

;; bound! : table X MODE TYPE pad emit! item -> void
;; A value of a datatype with a type invariant (#[verifier::type_invariant]:
;; guards, FrameRef, Rcu, SpinLock) gets `use_type_invariant` where it is
;; bound, as a real caller would call it: what the invariant gives is not a
;; gap of the specification (docs/representation.md B2).  Exec and tracked
;; values only (a ghost one has no invariant to use); through one reference.
(define (bound! table x mode t pad emit! item)
  (when (var-types) (hash-set! (var-types) x t))
  (when (and (memq mode '(exec tracked)) (use-type-invariants?))
    (define-values (inner arg)
      (match t
        [`(& ,u) (values u (symbol->string x))]
        [`(&static ,u) (values u (symbol->string x))]
        [`(&mut ,u) (values u (format "&*~a" x))]
        [u (values u (format "&~a" x))]))
    (when (and (client-module) (has-type-invariant? table inner (client-module)))
      (emit! (format "~aproof { use_type_invariant(~a); }" pad arg) item))))

;; use-type-invariants? : whether bound! writes use_type_invariant
(define use-type-invariants? (make-parameter #t))
;; client-module : the module the clients are in ("sync::cs_clients" beside sync::spin, the
;; target's), or #f (not known: no use_type_invariant, which needs to see the
;; type's invariant function)
(define client-module (make-parameter #f))

;; vacuity? : whether path ends get the vacuity assertion (结论29).
(define vacuity? (make-parameter #t))

(define (generics->text gens)
  (if (null? gens)
      ""
      (format "<~a>"
              (string-join (for/list ([g (in-list gens)])
                             (cond
                             ;; a const generic
                             [(assq 'const (filter pair? (cdr g)))
                              => (lambda (c) (format "const ~a: ~a" (car g) (type->text (cadr c))))]
                             [(null? (cdr g))
                                 (symbol->string (car g))]
                             [else
                                 (format "~a: ~a" (car g) (string-join (map type->text (cdr g)) " + "))]))
                           ", "))))

(define (param->text p)
  (match-define (list x mode t) p)
  (match mode
    ['exec (format "~a~a: ~a" (if (owned? t) "mut " "") x (type->text t))]
    ['tracked (format "Tracked(~a): Tracked<~a>" x (type->text t))]
    [(or 'ghost 'spec) (format "Ghost(~a): Ghost<~a>" x (type->text t))]))

(define (owned? t) (not (and (pair? t) (memq (car t) '(& &mut &static)))))

;; tail: #f, or the path id when this body ends a path of the client (结论29).
;; The last statement of such a body passes the tail on to its branches if it
;; is an if-let or if; otherwise the body ends with the vacuity assertion.
(define (render-body table name body depth emit! [tail #f])
  (define pad (make-string (* 4 depth) #\space))
  (define (branching? e) (and (pair? e) (memq (car e) '(if-let if)) #t))
  (define last-e (and (pair? body) (last body)))
  (define (child-tail e which) (and tail (eq? e last-e) (format "~a/~a" (cadr e) which)))
  (define (branch-else e eb)
    (define t (child-tail e 'else))
    (unless (and (null? eb) (not t))
      (emit! (format "~a} else {" pad))
      (render-body table name eb (add1 depth) emit! t)))
  (for ([e (in-list body)])
    (match e
      [`(call ,id ,x ,api-name (args ,args ...) (gargs ,gargs ...) (gret ,gret) (subst ,subst ...))
       (define api (api-ref table api-name))
       (when gret (emit! (format "~aproof_decl! { let tracked mut ~a; }" pad gret) (list name id)))
       (define text (let ([t (call->text api args gargs gret subst)])
                      (if (api-unsafe? api) (format "unsafe { ~a }" t) t)))
       (emit! (string-append
               pad
               (cond [(and (eq? (api-mode api) 'proof) x (api-ret-ghost? api))
                      ;; a spec result of a proof function: the call stays in proof
                      ;; code, the result goes into a ghost variable
                      (format "let ghost mut ~a: ~a = vstd::pervasive::arbitrary(); proof { ~a = ~a; }"
                              x (type->text (subst-type (api-ret api) subst)) x text)]
                     [(eq? (api-mode api) 'proof)
                      (if x (format "let tracked mut ~a = ~a;" x text) (format "proof { ~a; }" text))]
                     [x (format "let mut ~a = ~a;" x text)]
                     [else (format "~a;" text)]))
              (list name id))
       (when x
         (bound! table x (if (eq? (api-mode api) 'proof) (if (api-ret-ghost? api) 'ghost 'tracked) 'exec)
                 (subst-type (api-ret api) subst) pad emit! (list name id)))
       (when gret
         (match (api-ghost-ret api)
           [`(,m ,t) (bound! table gret m (subst-type t subst) pad emit! (list name id))]
           [_ (void)]))]
      [`(ghost ,id ,x ,ex) (emit! (format "~alet ghost ~a = ~a;" pad x (expr->text ex)) (list name id))]
      [`(ghost ,id ,x ,ex ,t) (emit! (format "~alet ghost ~a: ~a = ~a;" pad x (type->text t) (expr->text ex)) (list name id))]
      [`(assert ,id ,ex ,from)
       (emit! (format "~aassert(~a);~a" pad (top->text ex) (if (equal? from "") "" (format " // ~a" from)))
              (list name id))]
      [`(assert ,id ,ex ,from (by ,m))
       (emit! (format "~aassert(~a) by (~a);~a" pad (top->text ex) m (if (equal? from "") "" (format " // ~a" from)))
              (list name id))]
      ;; the client's choice not to make the next call panic (check/client.rkt with-no-panic)
      [`(assume ,id (,es ...))
       (for ([ex (in-list es)])
         (emit! (format "~aproof { assume(~a); } // no panic" pad (top->text ex)) (list name id)))]
      [`(proof-text ,id ,t) (emit! (format "~aproof { ~a }" pad (if (string? t) t (top->text t))) (list name id))]
      ;; Each clause on its own line, numbered: "s3/2" is the 2nd clause.
      [`(assert-requires ,id ,api-name (,clauses ...))
       (for ([c (in-list clauses)] [i (in-naturals 1)])
         ;; a "may panic here" clause: the client chooses not P (check/client.rkt with-no-panic)
         (define p (panic-condition c))
         (when p
           (emit! (format "~aproof { assume(~a); } // no panic" pad (expr->text `(not ,p))) (list name id)))
         (emit! (format "~aassert(~a); // requires of ~a" pad (expr->text c) api-name)
                (list name (format "~a/~a" id i))))]
      ;; with the Err payload bound: a match, the arms on their own lines
      [`(if-let ,id Ok ,x ,y (then ,tb ...) (else ,eb ...) (err ,er))
       (define-values (okt errt) (match (and (var-types) (hash-ref (var-types) y #f))
                                   [`(Result ,a ,b) (values a b)] [_ (values #f #f)]))
       (define inner-pad (string-append pad "        "))
       (emit! (format "~amatch ~a {" pad y) (list name id))
       (emit! (format "~a    Ok(mut ~a) => {" pad x) (list name id))
       (when okt (bound! table x 'exec okt inner-pad emit! (list name id)))
       (render-body table name tb (+ depth 2) emit! (child-tail e 'then))
       (emit! (format "~a    }" pad))
       (emit! (format "~a    Err(mut ~a) => {" pad er) (list name id))
       (when errt (bound! table er 'exec errt inner-pad emit! (list name id)))
       (render-body table name eb (+ depth 2) emit! (child-tail e 'else))
       (emit! (format "~a    }" pad))
       (emit! (format "~a}" pad))]
      ;; a tuple taken apart: `let (mut p, Tracked(perm)) = v;`
      [`(untuple ,id ((,xs ,modes ,_) ...) ,y)
       (define pats (for/list ([x (in-list xs)] [m (in-list modes)])
                      (case m [(tracked) (format "Tracked(~a)" x)] [(ghost) (format "Ghost(~a)" x)] [else (format "mut ~a" x)])))
       (emit! (format "~alet (~a~a) = ~a;" pad (string-join pats ", ") (if (= (length pats) 1) "," "") y) (list name id))
       (for ([x (in-list xs)] [m (in-list modes)] [t (in-list (map caddr (caddr e)))])
         (bound! table x m t pad emit! (list name id)))]
      [`(if-let ,id ,ctor ,x ,y (then ,tb ...) (else ,eb ...))
       (emit! (format "~aif let ~a(mut ~a) = ~a {" pad ctor x y) (list name id))
       (match* (ctor (and (var-types) (hash-ref (var-types) y #f)))
         [('Ok `(Result ,a ,_)) (bound! table x 'exec a (string-append pad "    ") emit! (list name id))]
         [('Err `(Result ,_ ,b)) (bound! table x 'exec b (string-append pad "    ") emit! (list name id))]
         [('Some `(Option ,a)) (bound! table x 'exec a (string-append pad "    ") emit! (list name id))]
         [(_ _) (void)])
       (render-body table name tb (add1 depth) emit! (child-tail e 'then))
       (branch-else e eb)
       (emit! (format "~a}" pad))]
      [`(if-not ,id ,x ,inner ...)
       (emit! (format "~aif !~a {" pad x) (list name id))
       (render-body table name inner (add1 depth) emit!)
       (emit! (format "~a}" pad))]
      [`(if ,id ,ex (then ,tb ...) (else ,eb ...))
       (emit! (format "~aif ~a {" pad (expr->text ex)) (list name id))
       (render-body table name tb (add1 depth) emit! (child-tail e 'then))
       (branch-else e eb)
       (emit! (format "~a}" pad))]
      ;; A counted while loop; the invariant clauses are numbered "s3/inv2".
      [`(repeat ,id ,n (invariant ,invs ...) ,inner ...)
       (define i (string-append "i_" (string-replace id "." "_")))
       (emit! (format "~alet mut ~a: usize = 0;" pad i) (list name id))
       (emit! (format "~awhile ~a < ~a" pad i n) (list name id))
       (emit! (format "~a    invariant" pad))
       (emit! (format "~a        ~a <= ~a," pad i n))
       (for ([c (in-list invs)] [k (in-naturals 1)])
         (emit! (format "~a        ~a," pad (expr->text c)) (list name (format "~a/inv~a" id k))))
       (emit! (format "~a    decreases ~a - ~a," pad n i))
       (emit! (format "~a{" pad))
       (render-body table name inner (add1 depth) emit!)
       (emit! (format "~a    ~a = ~a + 1;" pad i i))
       (emit! (format "~a}" pad))]))
  (when (and tail (not (and last-e (branching? last-e))))
    (emit! (format "~aassert(false); // vacuity: must fail" pad) (list name (format "~a/vac" tail)))))

;; call->text : api (A ...) (A ...) G-or-#f subst -> string
;; In a function path, {T} is replaced by the instantiated type parameter T.
(define (call->text api args gargs gret subst)
  (define proof? (eq? (api-mode api) 'proof))
  (define (arg->text a)
    (match a
      [`(spec ,e) (if proof? (expr->text e) (format "Ghost(~a)" (expr->text e)))]
      ['(none) (if proof? "None" "Tracked(None)")]
      [`(,kind ,x) (pass->text kind x)]))
  (define (garg->text a)
    (match a
      [`(spec ,e) (format "Ghost(~a)" (expr->text e))]
      ['(none) "Tracked(None)"]
      [`(,kind ,x) (format "Tracked(~a)" (pass->text kind x))]))
  (define core-args
    (match (api-call api)
      [`(method ,_) (cdr args)]
      [`(function ,_) args]))
  (define trailing (if (eq? (api-ghost-style api) 'arg) (map garg->text gargs) '()))
  (define arg-text (string-join (append (map arg->text core-args) trailing) ", "))
  (define core
    (match (api-call api)
      [`(method ,m) (format "~a.~a~a(~a)" (match (car args) [`(spec ,e) (expr->text e)] [`(,_ ,x) x]) m
                            (turbofish api subst (car (api-params api)) #f)
                            arg-text)]
      [`(function ,p)
       (format "~a~a(~a)"
               (for/fold ([p p]) ([b (in-list subst)])
                 (string-replace p (format "{~a}" (car b)) (type->text (cdr b))))
               (turbofish api subst #f p)
               arg-text)]))
  (define with (if (eq? (api-ghost-style api) 'with) (map garg->text gargs) '()))
  (if (and (null? with) (not gret))
      core
      (format "(#[verus_spec(with ~a~a)] ~a)"
              (string-join with ", ")
              (if gret (format " => Tracked(~a)" gret) "")
              core)))

;; The `::<..>` of a call whose type parameters are not all determined by the
;; arguments (`r.read_once::<T>()`, `disable_preempt::<G>()`).  The function's
;; own type parameters are taken to be those its self type does not mention (the
;; receiver's type, or the {T} of the path); the undetermined ones are written,
;; the others left to inference with `_`.
(define (turbofish api subst receiver path)
  (define (mentions? t x) (if (pair? t) (ormap (lambda (y) (mentions? y x)) t) (eq? t x)))
  (define ps (append (api-params api) (api-ghost-params api)))
  (define own (for/list ([g (in-list (map car (api-generics api)))]
                         ;; lifetimes are left out of a turbofish altogether
                         #:unless (regexp-match? #rx"^'" (symbol->string g))
                         #:unless (if receiver
                                      (mentions? (param-type receiver) g)
                                      (string-contains? path (format "{~a}" g))))
                g))
  (define (free? g) (not (for/or ([p (in-list ps)]) (mentions? (param-type p) g))))
  (if (and (ormap free? own) (andmap (lambda (g) (or (not (free? g)) (assq g subst))) own))
      (format "::<~a>" (string-join (for/list ([g (in-list own)])
                                      (if (free? g) (type->text (cdr (assq g subst))) "_"))
                                    ", "))
      ""))

(define (pass->text kind x)
  (match kind
    [(or 'move 'copy 'same) (symbol->string x)]
    ['ref (format "&~a" x)]
    ['reref (format "&*~a" x)]
    ['mutref (format "&mut ~a" x)]))

;; top->text : E [olds] -> string
;; An expression where it stands alone (a requires clause, an assertion, proof
;; steps): a template without the parentheses expr->text puts around it
;; inside an expression (a claim or an assumption kept as a template renders
;; as its text did, docs/enumeration.md 7.2).
(define (top->text e [olds '()])
  (match e
    [`(tmpl ,ps ...) (apply string-append (for/list ([p (in-list ps)]) (if (string? p) p (expr->text p olds))))]
    [_ (expr->text e olds)]))

;; expr->text : E [olds] -> string
;; olds: the client's `&mut` parameters, written `old(x)` (in requires).
(define (expr->text e [olds '()])
  (let loop ([e e])
    (match e
      [(? symbol? x) (if (memq x olds) (format "old(~a)" x) (symbol->string x))]
      [(? exact-integer? n) (number->string n)]
      [`(const ,n) (format "~a" n)]
      [`(src ,s) s]
      ;; a source clause kept as its text, the parameters' uses filled in
      ;; (vostd/source-spec.rkt source->template)
      [`(tmpl ,ps ...) (format "(~a)" (apply string-append (for/list ([p (in-list ps)]) (if (string? p) p (loop p)))))]
      [`(,(and op (or '== '!= '< '<= '> '>= '+ '- '* '% '/ '<< '>> '=~= '=~~=)) ,a ,b) (format "(~a ~a ~a)" (loop a) op (loop b))]
      [`(,(and op (or 'bitand 'bitor 'bitxor)) ,a ,b)
       (format "(~a ~a ~a)" (loop a) (match op ['bitand "&"] ['bitor "|"] ['bitxor "^"]) (loop b))]
      [`(not ,a) (format "!(~a)" (loop a))]
      ;; from the source's trees (vostd/source-spec.rkt)
      [`(neg ,a) (format "(-~a)" (loop a))]
      [`(index ,a ,i) (format "~a[~a]" (loop a) (loop i))]
      [`(tuple ,as ...) (format "(~a~a)" (string-join (map loop as) ", ") (if (= (length as) 1) "," ""))]
      [`(binop ,(? string? op) ,a ,b) (format "(~a ~a ~a)" (loop a) op (loop b))]
      [`(and ,as ...) (format "(~a)" (string-join (map loop as) " && "))]
      [`(or ,as ...) (format "(~a)" (string-join (map loop as) " || "))]
      [`(implies ,a ,b) (format "(~a ==> ~a)" (loop a) (loop b))]
      [`(deref ,a) (format "(*~a)" (loop a))]
      [`(borrow ,a) (format "(&~a)" (loop a))]
      [`(as ,a (const ,t)) (format "(~a as ~a)" (loop a) t)]
      ;; (a variable in olds is already written old(x))
      [`(old ,(? symbol? a)) (format "old(~a)" a)]
      [`(old ,a) (format "old(~a)" (loop a))]
      [`(view ,a) (format "(~a)@" (loop a))]
      ;; on an arrow, parenthesized: `x->0.0` reads as the float 0.0
      [`(field (arrow ,_ ,_) ,f) (format "(~a).~a" (loop (cadr e)) f)]
      [`(field ,a ,f) (format "~a.~a" (loop a) f)]
      [`(arrow ,a ,f) (format "(~a)->~a" (loop a) f)]
      [`(method ,a ,m ,args ...) (format "~a.~a(~a)" (loop a) m (string-join (map loop args) ", "))]
      [`(is ,a ,c) (format "(~a is ~a)" (loop a) c)]
      ;; the source's triggers: inline `#[trigger] e`, `#![trigger ..]`, `#![auto]`;
      ;; with none, `#![auto]` (Verus chooses, as it did for the source)
      [`(,(and q (or 'forall 'exists)) ,bs ,body)
       (define-values (attrs b)
         (match body
           [`(with-triggers ,gs ... ,b)
            (values (for/list ([g (in-list gs)]) (format "#![trigger ~a]" (string-join (map loop (cdr g)) ", "))) b)]
           [`(quant-attr ,a ,b) (values (list (format "#![~a]" a)) b)]
           [_ (values '() body)]))
       (define inline? (let find ([e b]) (match e [`(trigger ,_) #t] [(? pair?) (ormap find e)] [_ #f])))
       (format "(~a|~a| ~a~a)" q (string-join (for/list ([b (in-list bs)]) (format "~a: ~a" (car b) (type->text (cadr b)))) ", ")
               (cond [(pair? attrs) (string-append (string-join attrs " ") " ")] [inline? ""] [else "#![auto] "])
               (loop b))]
      [`(trigger ,a) (format "(#[trigger] ~a)" (loop a))]
      [`(record ,(? string? p) ,fs ...)
       (format "~a { ~a }" p (string-join (for/list ([f (in-list fs)]) (format "~a: ~a" (car f) (loop (cadr f)))) ", "))]
      [`(quant-attr ,_ ,a) (loop a)]
      [`(with-triggers ,_ ... ,a) (loop a)]
      [`(call ,f ,args ...) (format "~a(~a)" f (string-join (map loop args) ", "))])))

;; vacuity-id? : id -> boolean, the id of a vacuity assertion ("end/vac", "s3/then/vac").
(define (vacuity-id? id) (and (string? id) (regexp-match? #rx"/vac$" id)))
