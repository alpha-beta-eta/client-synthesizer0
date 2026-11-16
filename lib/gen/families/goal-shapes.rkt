#lang racket/base
;; The goal family's parts (docs/enumeration.md 4, 7, 9): how a plan of
;; goal.rkt becomes clients.  The question of every goal client is G's
;; requires, asserted clause by clause where a real caller would call G, with
;; only what G's arguments depend on before it.
;;   make-enum-goal   the enumeration (enum.rkt) seeded with the first API's
;;                    probe, its main path the plan's calls in order, G last
;;   after-err-client H fails (Err/None), then G on what H took by `&mut`
;;   again-client     G again on new parameters, where nothing produces what
;;                    the first call took
;;   producers-of, mutators-of, produces?, outputs+, outputs*  the dependencies
;;                    of G's arguments, read off the types
;;   tied-clauses, consistent-fresh?  a clause tying a new parameter to a
;;                    produced value (noise: the client knows nothing of it)
;; Up to 2026-11-14 this file also listed the dependency shapes by hand
;; (generate-goals); the single goal regression of goal.rkt replaced it.
(require racket/list racket/match racket/string "../../model/api.rkt" "../../base/forms.rkt" "../../check/client.rkt"
         "../probe.rkt" "../enum.rkt" "../../check/prop.rkt" "../../model/knowledge.rkt"
         "common.rkt" "flow.rkt" (only-in "../../model/spec.rkt" expr-vars))
(provide producers-of mutators-of tied-clauses
         ;; for goal.rkt
         make-enum-goal produces? outputs+ outputs* mentioned? consumed-params consistent-fresh?
         after-err-client again-client main-calls shares? tuple-ret?)

(define (all-params a) (append (api-params a) (api-ghost-params a)))

;; produces? : output (KIND TYPE), parameter p of b -> boolean
;; flows? (a datatype into a parameter of a datatype, in the same mode), or,
;; for a parameter b's requires mention, any value of the type: an integer
;; (`paddr_to_vaddr(pa)` with pa from `start_paddr()`), into a spec parameter
;; any output (a lemma's arguments).  Only where a clause mentions it: else
;; every call returning a usize would produce for every usize parameter.
;; An integer is produced for an integer parameter only when the source writes
;; both with the same type that is not the bare integer (`Paddr` from
;; `start_paddr()` for `pa: Paddr`): VIR has `usize` for Paddr, Vaddr and
;; usize alike, and an integer producer by the type alone gave a virtual
;; address (`paddr_to_vaddr`'s) to a lemma's `pa: Paddr`, an end address to a
;; size (docs/enumeration.md 7.9).  The output's source text is its third
;; element (outputs+).
(define (produces? o p b)
  (or (flows? (take o 2) p b)
      (and (mentioned? p b)
           (match-let ([(list kind t more ...) o])
             (and (match (param-mode p)
                    ['spec #t]
                    ['tracked (eq? kind 'gret)]
                    [_ (not (eq? kind 'gret))])
                  (not (memq (let ([pt (strip-ref (param-type p))]) (if (pair? pt) (car pt) pt))
                             (map car (api-generics b))))
                  (match-type (strip-ref (param-type p)) (strip-ref t) (map car (api-generics b)) '())
                  (or (not (memq (strip-ref (param-type p)) primitive))
                      (let ([ot (and (pair? more) (car more))] [pt (source-param-text b (param-name p))])
                        (and ot pt (not (memq (string->symbol (norm-type ot)) primitive))
                             (equal? (norm-type ot) (norm-type pt)))))
                  #t)))))

(define (norm-type s) (regexp-replace* #px"\\s+" s ""))

;; the source's text of an API's parameter's type, or #f
(define (source-param-text a name)
  (define src (form-ref a 'source #f))
  (define ps (and (list? src) (for/first ([x (in-list src)] #:when (and (pair? x) (eq? (car x) 'params))) (cdr x))))
  (for/first ([p (in-list (or ps '()))]
              #:when (and (pair? p) (eq? (car p) 'p) (equal? (cadr p) (symbol->string name))))
    (caddr p)))

;; the source's text of an API's result type, or #f
(define (source-ret-text a)
  (define src (form-ref a 'source #f))
  (define r (and (list? src) (for/first ([x (in-list src)] #:when (and (pair? x) (eq? (car x) 'ret))) x)))
  (and r (= (length r) 3) (string? (caddr r)) (caddr r)))

;; the type arguments of `Name<A, B>` as text, at the top level
(define (generic-args s)
  (define m (regexp-match #px"^\\s*[A-Za-z_:]+\\s*<(.*)>\\s*$" s))
  (and m (let ([parts (tuple-parts (string-append "(" (cadr m) ")"))]) parts)))

;; outputs+ : api -> ((KIND TYPE TEXT-or-#f) ...), outputs with the source's
;; text of each (inside Ok/Some for those)
(define (outputs+ a)
  (define rt (source-ret-text a))
  (for/list ([o (in-list (outputs a))])
    (match-define (list kind t) o)
    (list kind t
          (and rt (match kind
                    ['ret rt]
                    [(or 'ok 'some) (let ([as (generic-args rt)]) (and as (pair? as) (car as)))]
                    [_ #f])))))

(define (mentioned? p b)
  (for/or ([r (in-list (api-requires b))]) (and (memq (param-name p) (expr-vars r)) #t)))

;; producers-of : (api ...) api -> (api ...), the APIs with an output that can be an argument of b
(define (producers-of steps b)
  (for/list ([a (in-list steps)]
             #:when (for*/or ([o (in-list (outputs+ a))] [p (in-list (all-params b))]) (produces? o p b)))
    a))

;; mutators-of : (api ...) api -> (api ...), the APIs taking by `&mut` an object
;; (a datatype) that is also an argument of g, in the same mode
(define (mutators-of steps g)
  (for/list ([h (in-list steps)]
             #:when (for*/or ([ph (in-list (all-params h))] [pg (in-list (all-params g))])
                      (match (param-type ph)
                        [`(&mut ,t)
                         (and (datatype? t) (eq? (param-mode ph) (param-mode pg))
                              (match-type (strip-ref (param-type pg)) t (map car (api-generics g)) '())
                              #t)]
                        [_ #f])))
    h))

;; make-enum-goal : table knowledge elided? -> (enum-goal seq G accept? [#:relations R] -> (client ...))
;; The enumeration (enum.rkt, as for chain) seeded with the first API's
;; probe, whose main path calls the APIs in order (providers between),
;; the last G; the clients accept? keeps, with only G's requires asserted.
;; enum.rkt takes a tuple result apart and keeps every step well-formed.
(define (make-enum-goal table k elided?)
  (define providers (if (api-ref table 'Option::tracked_unwrap) '(Option::tracked_unwrap) '()))
  (define roles (knowledge-roles k))
  (define (assumed api) (knowledge-assumptions k api))
  (define prov (if (null? providers) 'empty `(alt ,@(for/list ([p (in-list providers)]) `(call ,p)))))
  (lambda (seq g accept? #:relations [rels (quote ())])
    (define f (car seq))
    (define probe (probe-client f))
    (define path (compile-property
                  `(property goal (forall) (paths main)
                             (seq ,@(add-between (for/list ([a (in-list seq)]) `(call ,(api-name a))) `(* ,prov))))))
    (define spec
      `(enum ,(safe (format "goal_~a" (string-join (map (lambda (a) (format "~a" (api-name a))) seq) "_")))
             (type-params ,@(form-ref probe 'type-params))
             (params ,@(form-ref probe 'params))
             (apis ,@(remove-duplicates (map api-name seq)))
             (providers ,@providers)
             (depth ,(length seq))
             (properties goal)
             (explicit-requires)
             (prefer-produced) (pair-by-origin) (consistent-fresh)
             ,@(if elided? '((elided-lifetimes)) '())
             (roles ,@roles)
             (var-roles ,@(knowledge-var-roles k f))
             ,@(if (null? rels) (quote ()) `((relations ,@rels)))))
    (define as (assumed f))
    (for/list ([c (in-list (enumerate table spec (list path)))] #:when (accept? (main-calls c)))
      (append (only-requires-of c (api-name g))
              (if (null? as) '() `((requires ,@as))) '((allow-open))))))

(define (shares? xs ys) (and (for/or ([x (in-list xs)]) (memq x ys)) #t))

;; outputs* : api -> outputs (common.rkt's), with a tuple result's parts too, in
;; the modes the source gives them (`(NonNull<..>, Tracked<..>)`: exec, tracked)
(define (outputs* a)
  (append (outputs+ a)
          (match (api-ret a)
            [`(tuple ,ts ..1)
             (define modes (or (api-ret-modes a) (map (lambda (_) 'exec) ts)))
             (define texts (let* ([rt (source-ret-text a)] [ps (and rt (tuple-parts (string-trim rt)))])
                             (if (and ps (= (length ps) (length ts))) ps (map (lambda (_) #f) ts))))
             (for/list ([t (in-list ts)] [m (in-list modes)] [tx (in-list texts)] #:unless (eq? m 'ghost))
               (list (if (eq? m 'tracked) 'gret 'ret) t tx))]
            [_ '()])))

(define (tuple-ret? a) (match (api-ret a) [`(tuple ,_ ..1) #t] [_ #f]))

;; after-err-client : table H G assumptions -> client or #f
;; goal_err_<H>_<G>: H called as in its probe; in its Err (None) branch, G's
;; requires asserted, G taking H's parameter where the type and mode are the
;; same (the state H left), a new parameter elsewhere; only when G takes at
;; least one variable H took by `&mut`.  #f when H's result is no Result/Option.
(define (after-err-client table h g as)
  (define probe (probe-client h))
  (define call-stmt (for/first ([s (in-list (form-ref probe 'body))] #:when (match s [`(let ,_ ,_) #t] [_ #f])) s))
  (define ctor (match (api-ret h) [`(Result ,_ ,_) 'Ok] [`(Option ,_) 'Some] [_ #f]))
  (define hparams (form-ref probe 'params))
  (define (local x) (if (eq? x 'self) 'self_ x))
  (define gps (all-params g))
  (define used '())
  (define args
    (for/list ([q (in-list gps)])
      (define want (param-type q))
      (define hit (for/first ([hp (in-list hparams)]
                              #:when (and (not (memq (car hp) used))
                                          (eq? (cadr hp) (match (param-mode q) ['spec 'ghost] [m m]))
                                          (equal? (caddr hp) want)))
                    (car hp)))
      (cond [hit (set! used (cons hit used)) hit]
            [else (string->symbol (format "~a_g" (local (param-name q))))])))
  ;; G's type parameters must be the client's (H's probe's), by name
  (define tp-names (map (lambda (t) (if (pair? t) (car t) t)) (form-ref probe 'type-params)))
  (define generics-ok?
    (for/and ([v (in-list (map car (api-generics g)))])
      (or (regexp-match? #rx"^'" (symbol->string v)) (memq v tp-names))))
  (define fresh (for/list ([q (in-list gps)] [a (in-list args)] #:unless (memq a (map car hparams)))
                  (list a (match (param-mode q) ['spec 'ghost] [m m]) (param-type q))))
  (define takes-mut?
    (for/or ([hp (in-list hparams)]) (and (match (caddr hp) [`(&mut ,_) #t] [_ #f]) (memq (car hp) args) #t)))
  (match call-stmt
    [`(let ,r ,_)
     #:when (and ctor takes-mut? generics-ok? (null? (free-generics g)))
     (define-values (gargs gghost) (split-at args (length (api-params g))))
     `(client ,(safe (format "goal_err_~a_~a" (api-name h) (api-name g)))
              (source ,(format "goal: ~a after ~a failed" (api-name g) (api-name h)))
              ;; with the lifetimes the new parameters' types name and H's probe has
              ;; not (`self_g: &mut CursorMut<'a, M>` after `pop_back`: E0261 in r23)
              (type-params ,@(form-ref probe 'type-params)
                           ,@(let* ([have (map (lambda (t) (if (pair? t) (car t) t)) (form-ref probe 'type-params))]
                                    [lts (remove-duplicates
                                          (let walk ([t (map caddr fresh)])
                                            (cond [(pair? t) (append-map walk t)]
                                                  [(and (symbol? t) (regexp-match? #rx"^'" (symbol->string t))) (list t)]
                                                  [else '()])))])
                               (filter (lambda (l) (not (memq l have))) lts)))
              (params ,@hparams ,@fresh)
              ;; G asserted, then called: the call lifts the clauses about the new
              ;; parameters only into the client's requires (client.rkt lifts at
              ;; calls); asserted without the call, they failed for that alone
              ;; (r24: 269 of the after-error failures)
              (body ,call-stmt
                    (if-let (,ctor x) ,r (then)
                            (else (assert-requires ,(api-name g) ,gargs ,gghost)
                                  ,(let ([c `(call ,(api-name g) ,gargs ,gghost ,@(if (api-ghost-ret g) '(-> gr_g) '()))])
                                     (if (api-ret g) `(let w_g ,c) `(do ,c))))))
              ,@(if (null? as) '() `((requires ,@as)))
              (allow-open))]
    [_ #f]))

;; again-client : table G assumptions -> client or #f
;; goal_again_<G>: G called as in its probe, then its requires asserted again
;; with a new parameter for each argument the call consumed (by value, not
;; Copy): `write_meta(self, metadata, ..)` twice needs a second metadata.
;; (repeat.rkt asserts them on the moved value itself, which no caller can
;; pass again.)  #f when G consumes nothing: (b) covers it.
(define (again-client table g as)
  (define probe (probe-client g))
  (define ps (all-params g))
  (define consumed (consumed-params table g))
  (define (local x) (if (eq? x 'self) 'self_ x))
  (define (again-name x) (string->symbol (format "~a_2" (local x))))
  (define call-stmt (for/first ([s (in-list (form-ref probe 'body))] #:when (match s [`(,(or 'let 'do) ,_ ...) #t] [_ #f])) s))
  (match call-stmt
    [(or `(let ,_ (call ,_ ,cas ,cgs ,more ...)) `(do (call ,_ ,cas ,cgs ,more ...)))
     #:when (pair? consumed)
     (define (re a p) (if (and (symbol? a) (memq (param-name p) consumed)) (again-name (param-name p)) a))
     (define-values (aps gps) (split-at ps (length cas)))
     (define types (for/list ([m (in-list more)] #:when (and (pair? m) (eq? (car m) 'types))) m))
     `(client ,(safe (format "goal_again_~a" (api-name g)))
              (source ,(format "goal: ~a again, with new values for what it consumed" (api-name g)))
              (type-params ,@(form-ref probe 'type-params))
              (params ,@(form-ref probe 'params)
                      ,@(for/list ([p (in-list (form-ref probe 'params))]
                                   #:when (memq (let ([n (car p)]) (if (eq? n 'self_) 'self n)) consumed))
                          (cons (again-name (if (eq? (car p) 'self_) 'self (car p))) (cdr p))))
              ;; asserted, then called (as after-err-client: the call lifts the
              ;; clauses about the new values only; r24: 35 failures for that alone,
              ;; and Verus crashed on one such assertion, `(x@.f)@ is Some ==> x.inv()`)
              (body ,call-stmt
                    (assert-requires ,(api-name g) ,(map re cas aps) ,(map re cgs gps) ,@types)
                    ,(let* ([more2 (let loop ([m more])
                                     (match m
                                       [(list '-> g2 rest ...) (list* '-> (string->symbol (format "~a_2" g2)) rest)]
                                       [(cons x rest) (cons x (loop rest))]
                                       ['() '()]))]
                            [c `(call ,(api-name g) ,(map re cas aps) ,(map re cgs gps) ,@more2)])
                       (match call-stmt
                         [`(let ,x ,_) `(let ,(string->symbol (format "~a_2" x)) ,c)]
                         [_ `(do ,c)])))
              ,@(if (null? as) '() `((requires ,@as)))
              (allow-open))]
    [_ #f]))

;; consistent-fresh? : a flow client, G -> boolean
;; No requires clause of G ties a parameter G gets fresh (flow.rkt names them
;; X_g) to one it gets from the calls before (the produced value, what is
;; shared with F): nothing makes such a clause hold, and the client fails for
;; that alone (`item_from_raw(pa_g, level_g, prop_g, ..) == r` with r from
;; `clone`; `self_g.wf_region(*owner, *regions)` with the owner from
;; `pop_back`).  flow.rkt checks this for tracked parameters only; this is
;; enum.rkt's consistent-fresh for every mode (design.md 3.5).
;; The noise is a clause's, not the client's: a client is dropped only when
;; every clause about what came from the calls before is so tied (it then
;; asks nothing about the produced value; the first version dropped a client
;; for any such clause and lost `split`'s `self.inv()` because `offset <
;; self.size()` tied a fresh offset to the produced segment).  The tied
;; clauses' failures are noise of the client, not facts about G (tied-clauses).
(define (consistent-fresh? c g)
  (define ks (clause-kinds c g))
  (or (not ks) (memq 'produced ks) (not (memq 'tied ks))))

;; tied-clauses : a flow client, G -> the numbers (from 1) of G's clauses tying
;; a fresh parameter to a produced or shared one, or '()
(define (tied-clauses c g)
  (define ks (clause-kinds c g))
  (if ks (for/list ([k (in-list ks)] [i (in-naturals 1)] #:when (eq? k 'tied)) i) '()))

;; for each requires clause of G in the client: fresh (only fresh parameters:
;; lifted), produced (only values from before), tied (both), none; or #f
(define (clause-kinds c g)
  ;; flow.rkt's and after-err-client's new parameters are X_g, again-client's X_2
  (define fresh? (lambda (x) (and (symbol? x) (regexp-match? #rx"_(g|2)$" (symbol->string x)))))
  (define stmt (let find ([x (form-ref c 'body)])
                 (match x [`(assert-requires ,(== (api-name g)) ,_ ...) x] [(? pair?) (ormap find x)] [_ #f])))
  (match stmt
    [`(assert-requires ,_ ,as ,gs ,_ ...)
     (define binding (for/list ([p (in-list (all-params g))] [a (in-list (append as gs))]) (cons (param-name p) a)))
     (for/list ([r (in-list (api-requires g))])
       (define args (filter symbol? (map (lambda (v) (cond [(assq v binding) => cdr] [else #f])) (expr-vars r))))
       (define f (ormap fresh? args)) (define o (ormap (lambda (a) (not (fresh? a))) args))
       (cond [(and f o) 'tied] [o 'produced] [f 'fresh] [else 'none]))]
    [_ #f]))

;; the calls on a client's main path (then branches), each (API ARG-VARS BOUND-VARS):
;; the variables it binds are its result, the Ok/Some inside it, its ghost result
(define (main-calls c)
  (let loop ([ss (form-ref c 'body)] [acc '()])
    (match ss
      ['() (reverse acc)]
      [(cons s rest)
       (match s
         [(or `(let ,_ (call ,api ,as ,gs ,_ ...)) `(do (call ,api ,as ,gs ,_ ...)))
          (define bound (append (match s [`(let ,x ,_) (list x)] [_ '()])
                                (match s [`(,_ ... (call ,_ ,_ ,_ -> ,g ,_ ...)) (list g)] [_ '()])))
          (loop rest (cons (list api (filter symbol? (append as gs)) bound) acc))]
         [`(if-let (,_ ,x) ,y (then ,ts ...) ,_ ...)
          (define acc* (for/list ([e (in-list acc)]) (if (memq y (caddr e)) (list (car e) (cadr e) (cons x (caddr e))) e)))
          (loop (append ts rest) acc*)]
         [`(if-let (,_ ,x) ,y ,ts ...)
          (define acc* (for/list ([e (in-list acc)]) (if (memq y (caddr e)) (list (car e) (cadr e) (cons x (caddr e))) e)))
          (loop (append ts rest) acc*)]
         ;; a tuple result taken apart: its parts are the call's too
         [`(untuple ((,xs ,_) ...) ,y)
          (define acc* (for/list ([e (in-list acc)]) (if (memq y (caddr e)) (list (car e) (cadr e) (append xs (caddr e))) e)))
          (loop rest acc*)]
         [_ (loop rest acc)])])))

;; the client with only g's requires asserted (a producer's or mutator's are its own goal)
(define (only-requires-of c g)
  (define (keep stmts)
    (for/list ([s (in-list stmts)]
               #:unless (match s [`(assert-requires ,a ,_ ...) (not (eq? a g))] [_ #f]))
      (match s
        [`(if-let ,p ,y (then ,ts ...) (else ,es ...)) `(if-let ,p ,y (then ,@(keep ts)) (else ,@(keep es)))]
        [`(if-let ,p ,y ,ts ...) `(if-let ,p ,y ,@(keep ts))]
        [`(if ,xe (then ,ts ...) (else ,es ...)) `(if ,xe (then ,@(keep ts)) (else ,@(keep es)))]
        [_ s])))
  (for/list ([f (in-list c)]) (match f [`(body ,ss ...) `(body ,@(keep ss))] [_ f])))

;; consumed-params : table api -> (name ...), the parameters a call takes by
;; value and does not give back (not a reference, not spec, not Copy)
(define (consumed-params table g)
  (for/list ([p (in-list (all-params g))]
             #:unless (match (param-type p) [`(,(or '& '&mut '&static) ,_) #t] [_ #f])
             #:unless (eq? (param-mode p) 'spec)
             #:unless (copy-type? table (param-type p)))
    (param-name p)))
