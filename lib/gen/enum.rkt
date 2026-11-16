#lang racket/base
;; Enumerating clients (design.md, 结论12-14, 18-24).
;;
;; An enumeration spec:
;;   (enum PREFIX [(type-params T ...)] (params (X MODE TYPE) ...)
;;         (apis API ...)          exec APIs a step may call
;;         (providers API ...)     proof APIs that may produce a missing tracked argument
;;         (specs API ...)         spec functions that may form spec arguments
;;         (depth K)               calls on the longest path
;;         [(else-depth E)]        calls after an Err/None or a false condition (default 0)
;;         [(properties NAME ...)] properties every path must satisfy (prop.rkt)
;;         [(explicit-requires)]   assert each later call's requires before it
;;         [(repeat-last)]         at each leaf, assert the last call's requires again
;;         [(conditions (API XE) ...)]  after a call of API, also branch on XE, where
;;                                 `ret` stands for its result (结论22)
;;         [(relations (A B E [(arg I)] [(via)]) ...)]
;;         [(roles (API PARAM ROLE) ...)]   the role of an API's parameter (PARAM may be
;;                                 ret or gret, its outputs), from a knowledge file
;;         [(var-roles (X ROLE) ...)]       the roles of the client's parameters
;;                                 (auto/knowledge/FORMAT.md)
;;         [(max-choices K)]       at each step, at most K continuations per API
;;         [(prefer-produced)]     among the values a parameter may take, those calls
;;                                 produced come before the client's parameters: with
;;                                 max-choices, the continuations kept pass on what an
;;                                 earlier call gave, as a real caller does
;;         [(pair-by-origin)]      an object goes with the ghost value the same call
;;                                 returned: see `paired` below
;;         [(consistent-fresh)]    no requires clause ties a client parameter not used
;;                                 so far to a value a call produced: see `consistent`
;;         [(elided-lifetimes)])   a free lifetime parameter, when the client has none,
;;                                 takes the elided '_ (design.md 3.5): see type-choices
;;                                 when B is called on something A produced, assert E,
;;                                 where `in` is A's receiver (or its argument I) before
;;                                 the call and `out` is B's result (结论24); with (via),
;;                                 also when B is called on A's receiver itself (a
;;                                 container: push the frame, pop it back)
;; Every client produced is well-formed by construction: each step is
;; checked with client.rkt as it is added (结论12).  A client is a tree: a
;; call returning Result/Option is followed by an if-let whose then branch
;; continues the enumeration and whose else branch continues it for at most
;; E calls (结论18); a condition branches the same way.  A path ends only
;; when no value of a must-close type is open (结论21).  Without
;; explicit-requires the obligations are implicit: the requires of every
;; call after the first.
(require racket/list racket/match racket/string file/sha1
         "../model/api.rkt" "../check/client.rkt" "../check/prop.rkt" "../base/forms.rkt"
         (only-in "../model/spec.rkt" expr-vars))
(provide enumerate current-none-vacuous)

;; current-none-vacuous : API-name -> (PARAM ...), the tracked Option
;; parameters for which the probe found the requires with None unsatisfiable
;; (analysis/probe.rkt's none-vacuous facts; none-forces?)
(define current-none-vacuous (make-parameter (hash)))

;; A relation (A B E [(arg I)] [(via)]): which argument of A is `in`, and
;; whether B on A's receiver counts.
(define (relation-arg r) (cond [(assq 'arg (cdddr r)) => cadr] [else 0]))
(define (relation-via? r) (and (assq 'via (cdddr r)) #t))

;; Lifetimes are written |'a| (结论34).
(define (lifetime? x) (regexp-match? #rx"^'" (symbol->string x)))

;; The variables the events of a history mention.
(define (history-vars hist)
  (remove-duplicates (for*/list ([ev (in-list hist)] [r (in-list (caddr ev))]) (cdr r))))

;; The type parameters of api that no parameter's type mentions; the call
;; gives them explicitly (结论27).
(define (free-generics api)
  (define (syms t) (if (pair? t) (append-map syms t) (list t)))
  (define used (append-map (lambda (p) (syms (param-type p))) (append (api-params api) (api-ghost-params api))))
  (for/list ([g (in-list (map car (api-generics api)))] #:unless (memq g used)) g))

;; enumerate : table spec (property ...) -> (client ...)
;; props: the compiled properties the spec may name.
(define (enumerate table spec [all-props '()])
  (define prefix (cadr spec))
  (define type-params (form-ref spec 'type-params))
  (define params (form-ref spec 'params))
  (define apis (form-ref spec 'apis))
  (define providers (form-ref spec 'providers))
  (define specs (form-ref spec 'specs))
  (define depth (car (form-ref spec 'depth '(2))))
  (define else-depth (car (form-ref spec 'else-depth '(0))))
  (define explicit? (form-flag? spec 'explicit-requires))
  (define repeat? (form-flag? spec 'repeat-last))
  (define conditions (form-ref spec 'conditions))
  (define relations (form-ref spec 'relations))
  (define roles (form-ref spec 'roles))
  ;; With (max-choices K), each step keeps the first K continuations (in
  ;; enumeration order, not a sample) of each API: at most (K * #apis)^depth
  ;; bodies, for enumerations that stand for a usage rather than a space.
  (define max-choices (car (form-ref spec 'max-choices '(#f))))
  (define prefer-produced? (form-flag? spec 'prefer-produced))
  (define pair-by-origin? (form-flag? spec 'pair-by-origin))
  (define consistent-fresh? (form-flag? spec 'consistent-fresh))
  (define elided-lifetimes? (form-flag? spec 'elided-lifetimes))

  ;; origins-of : hist -> (values var->call-index call-index->api-name)
  ;; The call that produced each value: its result (unwrapped from Ok/Some)
  ;; and its ghost result; what a provider takes out has the origin of what
  ;; it took it from (the owner in an earlier call's ghost Option).
  (define (origins-of hist)
    (for/fold ([orig (hash)] [apis (hash)]) ([ev (in-list hist)] [k (in-naturals)])
      (match ev
        [`(ev ,a ,binds)
         (define outs (for/list ([b (in-list binds)] #:when (and (memq (car b) '(ret gret)) (symbol? (cdr b)))) (cdr b)))
         (cond
           [(memq a providers)
            (define from (and (pair? binds) (hash-ref orig (cdar binds) #f)))
            (values (if from (for/fold ([o orig]) ([x (in-list outs)]) (hash-set o x from)) orig) apis)]
           [else (values (for/fold ([o orig]) ([x (in-list outs)]) (hash-set o x k)) (hash-set apis k a))])]
        [_ (values orig apis)])))

  ;; consistent : api st hist choices -> choices
  ;; With (consistent-fresh): a choice in which one requires clause of the
  ;; API (with the arguments put in) names both a client parameter not used
  ;; so far and a value that is not a client parameter (a call's result, its
  ;; ghost result, what a provider took out) is dropped, even when none is
  ;; left: then the step is not taken (a protocol whose owner no call gives,
  ;; such as `cursor_front_mut`, which returns no CursorOwner, is not made
  ;; with an unrelated one; design.md 3.5).
  ;; Nothing is known of the parameter, so the clause cannot hold
  ;; (`x1.tracked_slot_perm@.value().wf(*slot_own)`: the frame just allocated
  ;; with an owner no call produced, where a real caller takes the owner out
  ;; of `regions`).  What remains passes produced values on together, or a
  ;; consistent pair of fresh parameters (design.md 3.5).
  (define (consistent api s hist choices)
    (cond
      [(not consistent-fresh?) choices]
      [else
       (define vars (usable-vars s))
       (define used (history-vars hist))
       (define (fresh? a)
         (define v (and (symbol? a) (cond [(assq a vars) => cdr] [else #f])))
         (and v (var-param? v) (not (var-touched? v)) (not (memq a used))))
       (define names (map param-name (append (api-params api) (api-ghost-params api))))
       (define (mixed? choice)
         (match-define (list pre args gargs) choice)
         (define arg-of (map cons names (append args gargs)))
         (for/or ([r (in-list (api-requires api))])
           (define as (for*/list ([x (in-list (expr-vars r))] [a (in-value (assq x arg-of))]
                                  #:when (and a (symbol? (cdr a))))
                        (cdr a)))
           (and (ormap fresh? as) (ormap (lambda (a) (not (fresh? a))) as))))
       (filter (lambda (c) (not (mixed? c))) choices)]))

  ;; paired : api hist choices -> choices
  ;; With (pair-by-origin): when a call gets an exec value that call k
  ;; produced, and call k also returned a ghost value of type T (or
  ;; Option<T>), a tracked parameter of type T gets call k's ghost value
  ;; (itself, or what a provider takes out of it): the writer with the owner
  ;; from the same from_kernel_space, the cursor with the owner from the same
  ;; cursor_mut.  A real caller never pairs an object with another call's
  ;; owner or with a fresh one, and a client that does fails for that alone.
  ;; Choices that break this are dropped, unless none is left.
  (define (paired api hist choices)
    (cond
      [(not pair-by-origin?) choices]
      [else
       (define-values (orig apis) (origins-of hist))
       (define (head t) (let ([b (strip-ref t)]) (if (pair? b) (car b) b)))
       (define (ghost-type k)
         (match (api-ghost-ret (api-ref table (hash-ref apis k)))
           [`(,_ (Option ,t)) t] [`(,_ ,t) t] [_ #f]))
       ;; call k's result, unwrapped from Result/Option
       (define (result-type k)
         (match (api-ret (api-ref table (hash-ref apis k)))
           [`(Result ,t ,_) t] [`(Option ,t) t] [#f #f] [t t]))
       (define ps (append (api-params api) (api-ghost-params api)))
       (define (ok? choice)
         (match-define (list pre args gargs) choice)
         ;; values a provider takes out in this choice
         (define o (for/fold ([o orig]) ([st (in-list pre)])
                     (match st
                       [`(let ,x (call ,_ (,from ,_ ...) ,_ ...)) (if (hash-ref o from #f) (hash-set o x (hash-ref o from)) o)]
                       [_ o])))
         (define as (append args gargs))
         ;; an object produced by call k: an owner of k's ghost type comes from k;
         ;; and the other way, an owner produced by call k: an object of k's
         ;; result type comes from k
         (define (from? x k) (and (symbol? x) (equal? (hash-ref o x #f) k)))
         (and
          (for*/and ([(p a) (in-parallel ps as)]
                     #:when (and (eq? (param-mode p) 'exec) (symbol? a) (hash-ref o a #f))
                     [k (in-value (hash-ref o a))]
                     [t (in-value (ghost-type k))]
                     #:when t
                     [(q b) (in-parallel ps as)]
                     #:when (and (eq? (param-mode q) 'tracked) (eq? (head (param-type q)) (head t))))
            (from? b k))
          (for*/and ([(q b) (in-parallel ps as)]
                     #:when (and (eq? (param-mode q) 'tracked) (symbol? b) (hash-ref o b #f))
                     [k (in-value (hash-ref o b))]
                     [t (in-value (result-type k))]
                     #:when t
                     [(p a) (in-parallel ps as)]
                     #:when (and (eq? (param-mode p) 'exec) (eq? (head (param-type p)) (head t))))
            (from? a k))))
       (define kept (filter ok? choices))
       (if (null? kept) choices kept)]))
  ;; A parameter may have several roles (knowledge merged from two rounds gave
  ;; `read`'s writer_own both writer-owner and owner-of-writer): all of them,
  ;; and two agree when they have one in common (role-check).  Until
  ;; 2026-11-13 the first was taken here and the last for a client
  ;; parameter, so such a parameter took nothing (docs/enumeration.md 7.6).
  (define (param-roles a pname)
    (for/list ([r (in-list roles)] #:when (and (eq? (car r) a) (eq? (cadr r) pname))) (caddr r)))
  (define (param-role a pname) (let ([rs (param-roles a pname)]) (and (pair? rs) rs)))
  ;; A variable has the role of the parameter it was passed as or produced
  ;; by; what a provider takes out has the role of what it took it from.
  (define (var-roles hist)
    (for/fold ([h (for/fold ([h (hash)]) ([r (in-list (form-ref spec 'var-roles))])
                    (hash-update h (car r) (lambda (l) (if (memq (cadr r) l) l (append l (list (cadr r))))) '()))])
              ([ev (in-list hist)])
      (match ev
        [`(ev ,a ,binds)
         (for/fold ([h h]) ([b (in-list binds)] #:when (symbol? (cdr b)))
           (define r (or (param-role a (car b))
                         (and (memq (car b) '(ret gret)) (memq a providers) (pair? binds)
                              (hash-ref h (cdar binds) #f))))
           (if r (hash-set h (cdr b) r) h))]
        [_ h])))
  (define props
    (for/list ([n (in-list (form-ref spec 'properties))])
      (or (findf (lambda (p) (eq? (property-name p) n)) all-props)
          (error 'enum "unknown property ~a" n))))

  ;; A provider is called for each `need`: at most once per tracked parameter.
  (define (may-call? api hist main?)
    (define k (for/sum ([p (in-list (append (api-params api) (api-ghost-params api)))])
                (if (eq? (param-mode p) 'tracked) 1 0)))
    (properties-may-call? props hist (api-name api) providers k main?))

  (define (status s hist main?)
    (properties-status props (for/list ([(k v) (in-hash (st-env s))]) (cons k (var-type v))) hist main?))

  ;; A statement checked against s; #f when it is not well-formed there.
  (define (try-stmt s stmt)
    (with-handlers ([ill? (lambda (_) #f)])
      (let-values ([(_e s2) (check-stmt s stmt "enum")]) s2)))

  ;; gen : st (event ...) remaining last counter main? origins -> (body ...)
  ;; Bodies whose every path is accepted by the properties; a path stops
  ;; only where no accepted continuation exists (maximal paths).
  ;; last: (api args gargs) of the call before, for repeat-last.
  ;; origins: ((X SNAPSHOT API) ...), what each variable was produced by (relations).
  (define (gen s hist remaining last counter main? origins)
    (define bodies
      (if (zero? remaining)
          '()
          (append*
           ;; An API that the properties reject as the next call, whatever its
           ;; arguments, is not expanded: its argument choices are never built
           ;; (each would be checked and then judged dead; time-sinks.md A6).
           (for/list ([name (in-list apis)]
                      #:when (may-call? (api-ref table name) hist main?))
             (define api (api-ref table name))
             (define (all)
               (for*/list ([types (in-list (type-choices api))]
                           [choice (in-list (consistent api s hist (paired api hist (arg-choices table s api providers specs params counter (history-vars hist)
                                                         (role-check api (var-roles hist))
                                                         #:prefer-produced? prefer-produced?))))])
                 (expand s hist remaining api types choice counter main? origins)))
             (if max-choices
                 ;; the first K bodies, expanding no more choices than needed
                 (let loop ([cs (for*/list ([types (in-list (type-choices api))]
                                            [choice (in-list (consistent api s hist (paired api hist (arg-choices table s api providers specs params counter (history-vars hist)
                                                                          (role-check api (var-roles hist))
                                                         #:prefer-produced? prefer-produced?))))])
                                  (cons types choice))]
                            [acc '()])
                   (if (or (null? cs) (>= (length acc) max-choices))
                       (take acc (min max-choices (length acc)))
                       (loop (cdr cs) (append acc (expand s hist remaining api (caar cs) (cdar cs) counter main? origins)))))
                 (append* (all)))))))
    (cond [(pair? bodies) bodies]
          [(and (null? (unclosed s)) (eq? (status s hist main?) 'accepted)) (list (leaf s last))]
          ;; a path that would end with a value still open (a lock guard): released
          ;; as a real caller does, by the API that takes only it by value (its drop),
          ;; whose requires (the lock's invariant restored) is then checked; the path
          ;; is not thrown away for want of depth (representation.md 6.8)
          [(pair? (unclosed s))
           (define-values (closing s2) (close-open s))
           (if (and closing (eq? (status s2 hist main?) 'accepted))
               (list (append closing (leaf s2 last)))
               '())]
          [else '()]))

  ;; close-open : st -> (values (STMT ...) st) or (values #f _)
  (define (close-open s)
    (let loop ([s s] [acc '()] [xs (unclosed s)])
      (cond
        [(null? xs) (values (reverse acc) s)]
        [else
         (define x (car xs))
         (define head (let ([t (var-type (hash-ref (st-env s) x))]) (if (pair? t) (car t) t)))
         (define stmt
           (for*/first ([n (in-list (table-names table))]
                        [a (in-value (api-ref table n))]
                        #:when (and (eq? (api-mode a) 'exec) (null? (api-ghost-params a)) (not (api-ret a))
                                    (= (length (api-params a)) 1)
                                    (let ([t (param-type (car (api-params a)))]) (and (pair? t) (eq? (car t) head))))
                        [st (in-value `(do (call ,n (,x) ())))]
                        #:when (try-stmt s st))
             st))
         (if stmt
             (loop (try-stmt s stmt) (cons stmt acc) (cdr xs))
             (values #f s))])))

  (define (role-check api vroles)
    (lambda (p x)
      (define want (param-roles (api-name api) (param-name p)))
      (define have (hash-ref vroles x #f))
      (or (null? want) (not have) (and (ormap (lambda (w) (memq w have)) want) #t))))

  (define (type-choices api)
    (define free (free-generics api))
    ;; a lifetime parameter takes a lifetime, a type parameter a type
    (apply cartesian-product (for/list ([g (in-list free)])
                               (define ts (for/list ([t (in-list (map type-param-name type-params))]
                                                     #:when (eq? (lifetime? g) (lifetime? t)))
                                            (list g t)))
                               ;; With (elided-lifetimes): a lifetime only in the result
                               ;; (`lock` -> SpinLockGuard<'a, ..>) when the client has none
                               ;; takes the elided '_, which rustc infers (a lifetime is never
                               ;; written in a call).  Not when a bound names it: the bound
                               ;; would be lifted to the client as `P: NonNullPtrRef<'_>`.
                               (if (and elided-lifetimes? (null? ts) (lifetime? g)
                                        (not (for/or ([b (in-list (api-generics api))])
                                               (mentions? (cdr b) g))))
                                   (list (list g '|'_|))
                                   ts))))

  (define (mentions? t x) (if (pair? t) (ormap (lambda (y) (mentions? y x)) t) (eq? t x)))

  (define (leaf s last)
    (match last
      [(list api args gargs)
       #:when repeat?
       (define stmt `(assert-requires ,(api-name api) ,args ,gargs))
       (if (try-stmt s stmt) (list stmt) '())]
      [_ '()]))

  ;; expand : one call (with its providers) -> (body ...)
  (define (expand s hist remaining api types choice counter main? origins)
    (match-define (list pre args gargs) choice)
    (with-handlers ([ill? (lambda (_) '())])
      (define-values (s1 pre-evs)
        (for/fold ([s s] [evs '()] #:result (values s (reverse evs))) ([p (in-list pre)])
          (match-define `(let ,x (call ,pname ,pargs ,pgargs)) p)
          (define-values (_e s2) (bind-call s "enum" x (caddr p)))
          (values s2 (cons (make-event (api-ref table pname) pargs pgargs x #f) evs))))
      ;; Ghost snapshots of the arguments that relations starting here name:
      ;; ((I . SNAP) ...)
      (define snaps
        (remove-duplicates
         (for*/list ([r (in-list relations)] #:when (eq? (car r) (api-name api))
                     [i (in-value (relation-arg r))]
                     #:when (and (< i (length args)) (symbol? (list-ref args i))))
           (cons i (string->symbol (if (= i 0) (format "in~a" counter) (format "in~a_~a" counter i)))))))
      (define snap-stmts (for/list ([p (in-list snaps)]) `(ghost ,(cdr p) ,(list-ref args (car p)))))
      (define s1* (for/fold ([s s1]) ([st (in-list snap-stmts)]) (and s (try-stmt s st))))
      (unless s1* (raise (ill "enum" '(snapshot))))
      (define x (and (api-ret api) (string->symbol (format "v~a" counter))))
      (define gret (and (api-ghost-ret api) (string->symbol (format "o~a" counter))))
      (define call `(call ,(api-name api) ,args ,gargs ,@(if gret `(-> ,gret) '())
                          ,@(if (null? types) '() `((types ,@types)))))
      (define req-stmt `(assert-requires ,(api-name api) ,args ,gargs))
      (define asserts (if (and explicit? (pair? hist) (pair? (api-requires api)) (try-stmt s1* req-stmt))
                          (list req-stmt)
                          '()))
      (define-values (_e s2a) (bind-call s1* "enum" x call))
      (define stmt (if x `(let ,x ,call) `(do ,call)))
      ;; A tuple result is taken apart at once, as a real caller does: the
      ;; components (v3_0, v3_1) are the values later calls get (design.md 3.1).
      (define modes (and x (api-ret-modes api)))
      (define parts (and modes (for/list ([m (in-list modes)] [i (in-naturals)])
                                 (list (string->symbol (format "~a_~a" x i)) m))))
      (define untuple (and parts `(untuple ,parts ,x)))
      (define s2 (if untuple
                     (or (try-stmt s2a untuple) (raise (ill "enum" '(untuple))))
                     s2a))
      (define produced (if parts (map car parts) (list x)))
      (define head (append pre snap-stmts asserts (list stmt) (if untuple (list untuple) '())))
      ;; the event names each component as the call's ret
      (define (call-event ret)
        (define ev (make-event api args gargs ret gret))
        (if (and parts (eq? ret x))
            (match ev [`(ev ,a ,roles)
                       `(ev ,a ,(append* (for/list ([r (in-list roles)])
                                           (if (eq? (car r) 'ret) (map (lambda (c) (cons 'ret c)) produced) (list r)))))])
            ev))
      (define this (list api args gargs))
      ;; Assertions of relations whose first call produced an argument of this
      ;; one (or, with (via), was called on the same receiver).
      ;; origins: ((X SNAP API I) ...)
      (define (relation-asserts out)
        (remove-duplicates
         (for*/list ([r (in-list relations)] #:when (eq? (cadr r) (api-name api))
                     [a (in-list (append args gargs))] #:when (symbol? a)
                     [o (in-list origins)]
                     #:when (and (eq? (car o) a) (eq? (caddr o) (car r)) (= (cadddr o) (relation-arg r))))
           `(assert ,(subst-symbols (caddr r) `((in . ,(cadr o)) (out . ,out)))
                    ,(format "relation ~a, ~a" (car r) (cadr r))))))
      ;; What this call may change (passed as `&mut`) no longer holds what an
      ;; earlier call gave it: its origins are dropped (push_back; push_back;
      ;; pop_back gives the second frame back, not the first).
      (define mutated
        (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
                   [a (in-list (append args gargs))]
                   #:when (and (symbol? a) (match (param-type p) [`(&mut ,_) #t] [_ #f])))
          a))
      (define (with-origins os produced)
        (append
         (for*/list ([r (in-list relations)] #:when (eq? (car r) (api-name api))
                     [snap (in-value (assv (relation-arg r) snaps))] #:when snap
                     [p (in-list (append produced
                                         (if (and (relation-via? r) (symbol? (car args))) (list (car args)) '())))]
                     #:when p)
           (list p (cdr snap) (api-name api) (car snap)))
         (filter (lambda (o) (not (memq (car o) mutated))) os)))
      (define ctor (match (and x (var-type (hash-ref (st-env s2) x)))
                     [`(Result ,_ ,_) 'Ok] [`(Option ,_) 'Some] [_ #f]))
      ;; The Err payload is bound only when some API enumerated here takes a
      ;; value of its type (UniqueFrame::try_from's Err(frame) gives the frame
      ;; back); binding every Error would only change how clients are written.
      (define err-var
        (match (and (eq? ctor 'Ok) (var-type (hash-ref (st-env s2) x)))
          [`(Result ,_ ,et)
           #:when (for*/or ([n (in-list (append apis providers))]
                            [a (in-value (api-ref table n))] #:when a
                            [p (in-list (append (api-params a) (api-ghost-params a)))]
                            #:when (memq (param-mode p) '(exec tracked)))
                    (with-handlers ([exn:fail? (lambda (_) #f)]) (compatible? s2 a (param-type p) et)))
           (string->symbol (format "e~a" counter))]
          [_ #f]))
      (cond
        [ctor
         (define y (string->symbol (format "x~a" counter)))
         (define-values (s-then s-else) (enter-if-let s2 "enum" ctor y x #:err err-var))
         (define rel (filter (lambda (st) (try-stmt s-then st)) (relation-asserts y)))
         (define hist-then (append hist pre-evs (list (make-event api args gargs y gret))))
         (define hist-else (append hist pre-evs (list (make-event api args gargs #f gret #:failed x))))
         (define os (with-origins origins (list y gret)))
         (define tbs (if (eq? (status s-then hist-then main?) 'dead)
                         '()
                         (gen s-then hist-then (sub1 remaining) this (add1 counter) main? os)))
         (define ebs (if (or (null? tbs) (eq? (status s-else hist-else #f) 'dead))
                         '()
                         (gen s-else hist-else (min else-depth (sub1 remaining)) this (add1 counter) #f os)))
         (for*/list ([tb (in-list tbs)] [eb (in-list ebs)])
           (append head (list `(if-let (,ctor ,y) ,x (then ,@rel ,@tb)
                                       (else ,@(if err-var `((Err ,err-var)) '()) ,@eb)))))]
        [else
         (define rel (if (and x (not parts)) (filter (lambda (st) (try-stmt s2 st)) (relation-asserts x)) '()))
         (define hist2 (append hist pre-evs (list (call-event x))))
         (define os (with-origins origins (append produced (list gret))))
         (cond
           [(eq? (status s2 hist2 main?) 'dead) '()]
           [else
            (define plain
              (for/list ([b (in-list (gen s2 hist2 (sub1 remaining) this (add1 counter) main? os))])
                (append head rel b)))
            ;; Branching on the result (结论22).
            (define branched
              (for*/list ([c (in-list conditions)] #:when (and x (eq? (car c) (api-name api)))
                          [xe (in-value (subst-symbols (cadr c) `((ret . ,x))))]
                          #:when (try-stmt s2 `(if ,xe (then) (else)))
                          [tb (in-list (gen s2 (append hist2 `((ev if-true ((on . ,x)))))
                                            (sub1 remaining) this (add1 counter) main? os))]
                          [eb (in-list (gen s2 (append hist2 `((ev if-false ((on . ,x)))))
                                            (min else-depth (sub1 remaining)) this (add1 counter) #f os))])
                (append head rel (list `(if ,xe (then ,@tb) (else ,@eb))))))
            (append plain branched)])])))

  (define s0 (initial-state table type-params params))
  (for/list ([body (in-list (gen s0 '() depth #f 0 #t '()))] #:unless (null? body))
    (define name (string->symbol
                  (format "~a_~a" prefix (substring (sha1 (open-input-string (format "~s" body))) 0 8))))
    `(client ,name
             (source ,(format "enum ~a: ~a" prefix (string-join (map symbol->string (calls-of body)) "; ")))
             (type-params ,@type-params)
             (params ,@params)
             (body ,@body))))

;; The APIs called along the body, in order (then branches before else).
(define (calls-of body)
  (append* (for/list ([st (in-list body)])
             (match st
               [`(let ,_ (call ,a ,_ ...)) (list a)]
               [`(do (call ,a ,_ ...)) (list a)]
               [`(if-let ,_ ,_ (then ,tb ...) (else ,eb0 ...))
                (define eb (match eb0 [`((Err ,_) ,r ...) r] [_ eb0])) ; the Err binder is no call
                (append (calls-of tb) (if (null? eb) '() (cons '|else:| (calls-of eb))))]
               [`(if ,_ (then ,tb ...) (else ,eb ...))
                (append (list '|if:|) (calls-of tb) (if (null? eb) '() (cons '|else:| (calls-of eb))))]
               [_ '()]))))

;; arg-choices : ... -> ((pre-steps args gargs) ...)
;; role-ok? : param var -> whether their roles (when both known) agree.
(define (arg-choices table s api providers specs params counter used [role-ok? (lambda (p x) #t)]
                     #:prefer-produced? [prefer-produced? #f])
  (define vars (usable-vars s))
  (define names (map param-name (append (api-params api) (api-ghost-params api))))
  (define (cands p)
    (match (param-mode p)
      ['spec (append (map car vars) (spec-exprs table s specs (param-type p)))]
      [mode
       ;; A variable named after another parameter of this API is not passed
       ;; here (owner_r is not the writer's owner_w).
       (define direct0 (for/list ([v (in-list vars)]
                                  #:when (and (eq? (var-mode (cdr v)) mode)
                                              (compatible? s api (param-type p) (var-type (cdr v)))
                                              (or (eq? (car v) (param-name p)) (not (memq (car v) names)))
                                              (role-ok? p (car v))))
                         v))
       (define-values (produced fresh) (partition (lambda (v) (not (var-param? (cdr v)))) direct0))
       (cond
         [prefer-produced?
          ;; what calls produced; else what a provider takes out of it (the
          ;; owner in the ghost Option an earlier call returned); the client's
          ;; parameters last
          (append (map car produced)
                  (if (and (eq? mode 'tracked) (null? produced)) `((need ,(param-type p))) '())
                  (map car fresh)
                  (if (and (eq? mode 'tracked) (match (param-type p) [`(Option ,_) #t] [_ #f])) '((none)) '()))]
         [else
          (append (map car direct0)
                  (if (and (eq? mode 'tracked) (match (param-type p) [`(Option ,_) #t] [_ #f])) '((none)) '())
                  (if (and (eq? mode 'tracked) (null? direct0)) `((need ,(param-type p))) '()))])]))
  (define per-param (map cands (append (api-params api) (api-ghost-params api))))
  ;; A missing tracked argument is provided for the receiver of this call:
  ;; the spec arguments of the provider are formed from the receiver only
  ;; (结论14).
  (append*
   (for/list ([combo (in-list (canonical-combos per-param vars params used))])
     (define focus (and (pair? combo) (symbol? (car combo)) (car combo)))
     (define expanded
       (apply cartesian-product
              (for/list ([a (in-list combo)])
                (match a
                  [`(need ,typ) (if focus (provided table s providers specs params typ focus counter) '())]
                  [_ (list a)]))))
     (for*/list ([c (in-list expanded)]
                [plain (in-value (map (lambda (a) (if (and (pair? a) (eq? (car a) 'provided)) (caddr a) a)) c))]
                #:unless (none-forces? api plain))
       (define pre (append* (for/list ([a (in-list c)] #:when (and (pair? a) (eq? (car a) 'provided))) (cadr a))))
       (define-values (args gargs) (split-at plain (length (api-params api))))
       (list pre args gargs)))))

;; none-forces? : api (ARG ...) -> boolean
;; Whether passing None for a tracked Option parameter makes a requires clause
;; false, or false unless the client gives up some condition P (the clause
;; becomes !P).  `get_slot(paddr)` requires `valid_frame_paddr(paddr) ==>
;; slot_perm is Some && ..`: with None the client can only call it on an invalid
;; paddr, the clause `valid_frame_paddr(paddr) ==> false` is lifted into the
;; client's requires, and every Ok of get_slot (which ensures
;; `valid_frame_paddr(paddr) == res is Ok`) is vacuous (2026-11-12: 29 chains
;; verified only on vacuous paths).  Such a None is not taken; a None the
;; requires do not object to is.  Where the objection is inside a spec
;; function (`raw_item_well_formed((.., Tracked(None)))`), only Verus sees it:
;; the probe's none-vacuous facts (current-none-vacuous).
(define (none-forces? api args)
  (define ps (append (api-params api) (api-ghost-params api)))
  (define nones (for/list ([p (in-list ps)] [a (in-list args)] #:when (equal? a '(none))) (param-name p)))
  (and (pair? nones)
       (or (for/or ([n (in-list nones)]) (and (memq n (hash-ref (current-none-vacuous) (api-name api) '())) #t))
           (for/or ([r (in-list (api-requires api))])
             (define v (simplify-none r nones))
             (or (eq? v #f)
                 (match v [`(not ,x) (not (mentions-none? x))] [_ #f]))))))

(define (mentions-none? e) (cond [(eq? e 'NONE) #t] [(pair? e) (ormap mentions-none? e)] [else #f]))

;; The clause with the parameters in nones as None, simplified as far as None
;; decides it: #t, #f, or an expression.
(define (simplify-none e nones)
  (let s ([e e])
    (match e
      [(? symbol? x) (cond [(memq x nones) 'NONE] [(eq? x 'true) #t] [(eq? x 'false) #f] [else x])]
      [`(is ,a ,v)
       (define a* (s a))
       (if (eq? a* 'NONE) (eq? v 'None) `(is ,a* ,v))]
      [`(not ,a) (match (s a) [#t #f] [#f #t] [x `(not ,x)])]
      [`(and ,as ...)
       (define xs (map s as))
       (cond [(memq #f xs) #f]
             [else (match (filter (lambda (x) (not (eq? x #t))) xs) ['() #t] [(list x) x] [ys `(and ,@ys)])])]
      [`(or ,as ...)
       (define xs (map s as))
       (cond [(memq #t xs) #t]
             [else (match (filter (lambda (x) (not (eq? x #f))) xs) ['() #f] [(list x) x] [ys `(or ,@ys)])])]
      [`(implies ,a ,b)
       (define a* (s a)) (define b* (s b))
       (cond [(or (eq? a* #f) (eq? b* #t)) #t]
             [(eq? a* #t) b*]
             [(eq? b* #f) (match a* [`(not ,x) x] [_ `(not ,a*)])]
             [else `(implies ,a* ,b*)])]
      [(? pair?) (map s e)]
      [_ e])))

;; Client parameters that are still unused (not touched, and in no event so
;; far) and interchangeable (same mode and type) are used in declaration
;; order: in an argument tuple, the fresh ones, in order of first use, are a
;; prefix of that order.  Using metadata2 before metadata1 gives the same
;; client up to renaming; two(a1, a2) and two(a1, a1) are both kept (结论13).
;;
;; canonical-combos : the argument tuples of (apply cartesian-product per-param)
;; that canonical-combo? accepts, in the same order, built argument by argument:
;; the condition is checked from the left and a rejected prefix has no accepted
;; extension, so rejected tuples are never built.  The full product was built
;; and then filtered before: a protocol whose calls' probes give several
;; interchangeable parameters per type (vm_space's `ktest-flusher`: three
;; cursor calls, each with seven parameters) gave tens of thousands of tuples
;; per call and step, nearly all rejected, and its generation did not end.
(define (canonical-combos per-param vars params used)
  (define (fresh? x)
    (define v (cond [(assq x vars) => cdr] [else #f]))
    (and v (var-param? v) (not (var-touched? v)) (not (memq x used))))
  (define (key x) (let ([v (cdr (assq x vars))]) (list (var-mode v) (var-type v))))
  (define memo (make-hasheq))
  (define (fresh?* x) (hash-ref! memo x (lambda () (fresh? x))))
  (define order (for/list ([y (in-list (map param-name params))] #:when (fresh?* y)) (cons y (key y))))
  ;; may x come next, the fresh parameters in seen used so far?  (as canonical-combo?)
  (define (next-ok? x seen)
    (cond
      [(and (symbol? x) (fresh?* x) (not (memq x seen)))
       (define k (key x))
       (define next (for/first ([o (in-list order)] #:when (and (equal? (cdr o) k) (not (memq (car o) seen))))
                      (car o)))
       (and (eq? next x) (cons x seen))]
      [else seen]))
  ;; in the order of cartesian-product
  (let loop ([ps per-param] [seen '()])
    (if (null? ps)
        '(())
        (for*/list ([a (in-list (car ps))]
                    [seen2 (in-value (next-ok? a seen))] #:when seen2
                    [rest (in-list (loop (cdr ps) seen2))])
          (cons a rest)))))

(define (canonical-combo? combo vars params used)
  (define (fresh? x)
    (define v (cond [(assq x vars) => cdr] [else #f]))
    (and v (var-param? v) (not (var-touched? v)) (not (memq x used))))
  (define (key x) (let ([v (cdr (assq x vars))]) (list (var-mode v) (var-type v))))
  (define order (filter fresh? (map param-name params)))
  (let loop ([as combo] [seen '()])
    (match as
      ['() #t]
      [(cons (? symbol? x) rest)
       #:when (and (fresh? x) (not (memq x seen)))
       ;; the first fresh parameter of its kind not used yet
       (define next (for/first ([y (in-list order)]
                                #:when (and (equal? (key y) (key x)) (not (memq y seen))))
                      y))
       (and (eq? next x) (loop rest (cons x seen)))]
      [(cons _ rest) (loop rest seen)])))

;; A rough filter on candidates (client.rkt decides): the outermost type
;; constructor must agree, unless the parameter's type is one of the API's
;; type parameters.  Such a parameter takes only a value whose type is a type
;; parameter of the client (behind as many references as the parameter's
;; type has): the bounds then become the client's (结论6) and rustc checks
;; them, while on a concrete type they are not checked (注意3) and the client
;; would not compile (a VmSpace as the `guard: &G` with `G: InAtomicMode`,
;; `&M` as `Link::new`'s `M: AnyFrameMeta`); and a value of a concrete type
;; in a generic container (a lock guard as `RwLock::new`'s data) is not how
;; the API is used.
(define (compatible? s api pt vt)
  (define (head t) (let ([b (strip-ref t)]) (if (pair? b) (car b) b)))
  (cond [(not (assq (strip-ref pt) (api-generics api))) (equal? (head pt) (head vt))]
        [else (let ([b (if (equal? (strip-ref pt) pt) vt (strip-ref vt))])
                (and (symbol? b) (hash-has-key? (st-bounds s) b)))]))

;; spec-exprs : spec functions applied to one variable (focus, or any), with
;; result type typ.
(define (spec-exprs table s specs typ [focus #f])
  (for*/list ([name (in-list specs)]
              [api (in-value (api-ref table name))]
              #:when (and (= (length (api-params api)) 1) (equal? (api-ret api) typ))
              [v (in-list (usable-vars s))]
              #:when (or (not focus) (eq? (car v) focus))
              #:when (match-type (strip-ref (param-type (car (api-params api))))
                                 (strip-ref (var-type (cdr v)))
                                 (map car (api-generics api)) '()))
    (match (api-call api)
      [`(method ,m) `(spec (method ,(car v) ,m))]
      [`(function ,f) `(spec (call ,(string->symbol f) ,(car v)))])))

;; provided : one provider call producing a fresh tracked variable whose
;; type matches typ; as (provided (STMT) X).  Its spec arguments are spec
;; functions of focus; its tracked arguments are existing variables.
(define (provided table s providers specs params typ focus counter)
  (define vars (usable-vars s))
  (for*/list ([name (in-list providers)]
              [api (in-value (api-ref table name))]
              ;; the provider's own type parameters may be bound (Option::tracked_unwrap's T)
              #:when (let ([r (api-ret api)])
                       (and r (match-type (strip-ref r) (strip-ref typ) (map car (api-generics api)) '()) #t))
              [combo (in-list
                      (apply cartesian-product
                             (for/list ([p (in-list (api-params api))])
                               (match (param-mode p)
                                 ['spec (spec-exprs table s specs (param-type p) focus)]
                                 [mode (for/list ([v (in-list vars)]
                                                  #:when (and (eq? (var-mode (cdr v)) mode)
                                                              (compatible? s api (param-type p) (var-type (cdr v)))))
                                         (car v))]))))])
    (define x (string->symbol (format "g~a" counter)))
    `(provided ((let ,x (call ,name ,combo ()))) ,x)))
