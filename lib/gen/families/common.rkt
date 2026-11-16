#lang racket/base
;; What the families of clients share (design.md 3.6): the outputs of an
;; API, which outputs can flow to which parameters, pure calls, and the
;; round-trip relations asserted on chains.
(require racket/list racket/match "../../model/api.rkt" "../../base/forms.rkt"
         (only-in "../rw.rkt" source-ensures source-ret-name))
(provide primitive safe local outputs datatype? flows? free-generics pure? relations)

(define primitive '(bool char u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize int nat))

(define (safe s) (string->symbol (regexp-replace* #rx"[^A-Za-z0-9_]" (format "~a" s) "_")))

(define (local x) (if (eq? x 'self) 'self_ x))

;; outputs : api -> ((KIND TYPE) ...), KIND = ret | ok | some | gret
(define (outputs f)
  (append
   (match (api-ret f)
     [#f '()]
     [`(Result ,t ,_) `((ok ,t))]
     [`(Option ,t) `((some ,t))]
     [t `((ret ,t))])
   (match (api-ghost-ret f) [`(,_ ,t) `((gret ,t))] [_ '()])))

(define (datatype? t)
  (define b (strip-ref t))
  (define h (if (pair? b) (car b) b))
  (and (symbol? h) (not (memq h primitive)) (not (memq h '(tuple slice assoc)))))

;; Whether output (KIND TYPE) of f can be parameter p of g: modes agree
;; (exec values to exec parameters, ghost results to tracked ones) and the
;; types match with g's type parameters bindable.
(define (flows? out p g)
  (match-define (list kind t) out)
  (define pt (strip-ref (param-type p)))
  (and (datatype? t)
       ;; the parameter names a datatype: a bare type parameter would take anything
       (datatype? pt)
       (not (memq (if (pair? pt) (car pt) pt) (map car (api-generics g))))
       (eq? (param-mode p) (if (eq? kind 'gret) 'tracked 'exec))
       (let ([sigma (match-type (strip-ref (param-type p)) (strip-ref t) (map car (api-generics g)) '())])
         (and sigma (not (dyn-under-bounds? sigma g))))
       #t))

;; Whether a type parameter of g with bounds would be bound to a type with a
;; `dyn` in it: the bounds (such as `Repr<MetaSlotStorage>` on `Frame<M>`'s
;; methods) do not hold for a trait object, and the client would not compile
;; (`into_dyn` then `start_paddr`).  Bounds on concrete types are not checked
;; in general (注意3); this case is cheap to see.
(define (dyn-under-bounds? sigma g)
  (define (dyn? t)
    (if (pair? t) (ormap dyn? t) (and (symbol? t) (regexp-match? #rx"^dyn " (symbol->string t)))))
  (for/or ([b (in-list sigma)])
    (define bounds (cond [(assq (car b) (api-generics g)) => cdr] [else '()]))
    (and (pair? bounds) (dyn? (cdr b)))))

;; The type parameters of api that no parameter's type mentions (as in enum.rkt).
(define (free-generics api)
  (define (syms t) (if (pair? t) (append-map syms t) (list t)))
  (define used (append-map (lambda (q) (syms (param-type q))) (append (api-params api) (api-ghost-params api))))
  (for/list ([g (in-list (map car (api-generics api)))] #:unless (memq g used)) g))

;; pure? : an exec call that changes nothing the client holds: no `&mut`
;; argument, no argument moved (each is a shared reference or Copy), no
;; ghost result.
(define (pure? table a)
  (and (eq? (api-mode a) 'exec)
       (not (api-ghost-ret a))
       (for/and ([p (in-list (append (api-params a) (api-ghost-params a)))])
         (define t (param-type p))
         (or (eq? (param-mode p) 'spec)
             (match t [`(& ,_) #t] [`(&static ,_) #t] [`(&mut ,_) #f] [_ (copy-type? table t)])))))

;; relations : (api ...) identity-forms -> ((A B E [(arg I)] [(via)]) ...)
;; Round trips, each asserting that one identity function of the type has
;; the same value on what went in and what came back:
;;   derived: B takes an output of A (as flow? decides) and gives back (after
;;     Ok/Some) a value of the type of A's argument I (into_raw, from_raw;
;;     from_unique, try_from_shared): `in` is argument I before A, `out` is B's
;;     result;
;;   declared: (roundtrip A B [(arg I)] [(via)]), for what is not derivable
;;     (push_back then pop_back on the same list gives the frame back; push_front
;;     then pop_back does not, which only the one who writes it can tell).
;; Which spec functions identify a value of a type is declared:
;; (identity TYPE SPEC-FN ...), e.g. (identity Frame start_paddr_spec).
;; With #:ensures? (goal-plan), a derived round trip also asserts what A's and
;; B's own ensures (the source's) equate on a value of the type: X.f() == Y or
;; Y == X.f() gives f, X == Y the value itself (into_raw: r == self.range()
;; gives range on Segment and Range itself; from_raw: r.range() == range).
;; Then a clause like from_raw's r.range() == range is asked by the round trip
;; even where no identity is declared (docs/enumeration.md 11).
(define (relations steps identity #:ensures? [ensures? #f])
  (define (head t) (let ([b (strip-ref t)]) (if (pair? b) (car b) b)))
  (define (ids-of t)
    (append* (for/list ([f (in-list identity)] #:when (and (eq? (car f) 'identity) (eq? (cadr f) (head t))))
               (cddr f))))
  ;; the identities for head h that a's and b's ensures give: spec method names, or 'self.
  ;; Only an equation linking a call's result and the argument of the round trip
  ;; counts (a's argument i, b's argument the value flows to), each side a value
  ;; or one spec method of it; the h-typed side of each is an identity, and both
  ;; calls must have one (slice then clone, limit then skip: no such equation, so
  ;; not a round trip whatever the types say).
  (define (ensures-ids a i b j h)
    (define (sname p) (let ([s (symbol->string (param-name p))]) (if (equal? s "self_") "self" s)))
    (define (type-of api name)
      (cond [(equal? name (source-ret-name api)) (api-ret api)]
            [(findf (lambda (p) (equal? (sname p) name)) (append (api-params api) (api-ghost-params api))) => param-type]
            [else #f]))
    (define (unparen e) (match e [`(paren ,x) (unparen x)] [_ e]))
    ;; (BASE . ID) or #f
    (define (side e)
      (match (unparen e)
        [`(method (path ,(? string? x)) ,(? string? f) ,_) (cons x (string->symbol f))]
        [`(path ,(? string? x)) (cons x 'self)]
        [_ #f]))
    (define (ids api arg)
      (define ret (source-ret-name api))
      (for*/list ([e (source-ensures api)]
                  #:when (match e [`(op "==" ,_ ,_) #t] [_ #f])
                  [l (in-value (side (caddr e)))] [r (in-value (side (cadddr e)))]
                  #:when (and l r ret arg)
                  [pair (list (cons l r) (cons r l))]
                  #:when (and (equal? (car (car pair)) ret) (equal? (car (cdr pair)) arg))
                  [s (list (car pair) (cdr pair))]
                  #:when (let ([t (type-of api (car s))]) (and t (eq? (head (unwrapped t)) h))))
        (cdr s)))
    (define ia (ids a (and i (< i (length (api-params a))) (sname (list-ref (api-params a) i)))))
    (define ib (ids b (and j (sname (list-ref (append (api-params b) (api-ghost-params b)) j)))))
    (if (and (pair? ia) (pair? ib)) (remove-duplicates (append ia ib)) '()))
  (define (unwrapped t) (match t [`(Result ,u ,_) u] [`(Option ,u) u] [u u]))
  (define (asserting a b t opts [extra '()])
    (for/list ([fn (in-list (remove-duplicates (append (ids-of t) extra)))])
      `(,(api-name a) ,(api-name b) ,(if (eq? fn 'self) '(== in out) `(== (method in ,fn) (method out ,fn))) ,@opts)))
  (define derived
    (for*/list ([a (in-list steps)] [out (in-list (outputs a))]
                [b (in-list steps)]
                #:when (and (api-ret b)
                            (for/or ([q (in-list (append (api-params b) (api-ghost-params b)))]) (flows? out q b)))
                [(p i) (in-indexed (api-params a))]
                #:when (eq? (head (param-type p)) (head (unwrapped (api-ret b))))
                [j (in-value (for/first ([(q j) (in-indexed (append (api-params b) (api-ghost-params b)))] #:when (flows? out q b)) j))]
                [r (in-list (asserting a b (param-type p) `((arg ,i))
                                       (if ensures? (ensures-ids a i b j (head (param-type p))) '())))])
      r))
  (define declared
    (for*/list ([f (in-list identity)] #:when (eq? (car f) 'roundtrip)
                [a (in-value (findf (lambda (x) (eq? (api-name x) (cadr f))) steps))]
                [b (in-value (findf (lambda (x) (eq? (api-name x) (caddr f))) steps))]
                #:when (and a b (api-ret b))
                [r (in-list (asserting a b (unwrapped (api-ret b)) (cdddr f)))])
      r))
  (remove-duplicates (append derived declared)))
