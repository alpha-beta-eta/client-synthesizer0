#lang racket/base
;; Properties of call sequences (design.md, 结论15-18).
;;
;;   (property NAME (forall (V TYPE-PATTERN) ...) G)
;;
;; G is a grammar (deriv.rkt) whose letters are event predicates:
;;   LETTER = any | (call API-or-_ (ROLE V-or-_) ...)
;;          | (ev-not LETTER) | (ev-and LETTER ...) | (ev-or LETTER ...)
;; A ROLE is a parameter name of the API (`self`, `regions`, ...) or `ret`
;; (the result; for a call whose Result/Option is unwrapped, the unwrapped
;; value) or `gret`.
;;
;; Semantics (parametric, as in trace slicing): for every binding of the
;; variables V to distinct objects (client variables) whose types match, the
;; slice of the history (the events that mention a bound object) is in the
;; language of G.  With no variables the slice is the whole history.
;;
;; An event is (ev API ((ROLE . X) ...)).
(require racket/list racket/match "../model/api.rkt" "../base/deriv.rkt" "../base/forms.rkt")
(provide compile-property property-name
         make-event properties-status properties-may-call?)

;; paths: all (every root-to-leaf path of the client) or main (only the path
;; through then branches; for properties that select clients) (结论18).
;; name-only?: no variables, and no letter looks at roles: whether an event
;; matches a letter depends on its API alone (properties-may-call?).
(struct property (name params paths start name-only?) #:transparent)

(define (letter? r)
  (or (eq? r 'any) (and (pair? r) (memq (car r) '(call ev-not ev-and ev-or)) #t)))

;; compile-property : form -> property
(define (compile-property form)
  (match form
    [`(property ,name (forall (,vs ,ts) ...) (paths ,(and paths (or 'all 'main))) ,g)
     (property name (map cons vs ts) paths (compile-grammar g letter?)
               (and (null? vs) (name-only-form? g)))]
    [`(property ,name (forall (,vs ,ts) ...) ,g)
     (compile-property `(property ,name (forall ,@(map list vs ts)) (paths all) ,g))]
    [_ (error 'property "bad property ~s" form)]))

;; Whether no letter of the grammar form g constrains roles.
(define (name-only-form? g)
  (define (letter-ok? l)
    (match l
      ['any #t]
      [`(call ,_) #t]
      [`(call ,_ ,_ ,_ ...) #f]
      [`(,(or 'ev-not 'ev-and 'ev-or) ,ls ...) (andmap letter-ok? ls)]))
  (let walk ([g g])
    (cond [(letter? g) (letter-ok? g)]
          [(pair? g) (andmap (lambda (x) (or (not (pair? x)) (walk x)))
                             (match g [`(grammar ,_ (,_ ,bodies) ...) bodies] [_ (cdr g)]))]
          [else #t])))

;; make-event : api args gargs ret gret [#:failed X] -> event
;; Arguments that are variables become roles named after the parameters.
;; On the else branch of a Result/Option the call has no `ret` but a role
;; `failed` (the Result/Option variable).
(define (make-event api args gargs ret gret #:failed [failed #f])
  (define roles
    (append
     (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
                [a (in-list (append args gargs))]
                #:when (symbol? a))
       (cons (param-name p) a))
     (if ret (list (cons 'ret ret)) '())
     (if gret (list (cons 'gret gret)) '())
     (if failed (list (cons 'failed failed)) '())))
  `(ev ,(api-name api) ,roles))

;; ================================================================ bindings

;; bindings : property ((X . TYPE) ...) -> (((V . X) ...) ...), distinct objects
(define (bindings prop objects)
  (let loop ([params (property-params prop)] [used '()])
    (match params
      ['() '(())]
      [(cons (cons v pat) rest)
       (for*/list ([o (in-list objects)]
                   #:when (and (not (memq (car o) used)) (type-matches? pat (strip-ref (cdr o))))
                   [b (in-list (loop rest (cons (car o) used)))])
         (cons (cons v (car o)) b))])))

;; The event as one binding sees it: bound objects are replaced by their
;; variable names, the others by `_`.  It is also the memo key of derive.
(define (view ev b)
  (match-define `(ev ,api ,roles) ev)
  (define inv (map (lambda (p) (cons (cdr p) (car p))) b))
  (list api (for/list ([r (in-list roles)])
              (cons (car r) (cond [(assq (cdr r) inv) => cdr] [else '_])))))

(define (in-slice? ev b)
  (or (null? b)
      (match-let ([`(ev ,_ ,roles) ev])
        (for/or ([r (in-list roles)]) (and (memq (cdr r) (map cdr b)) #t)))))

(define (match-letter pred v)
  (match-define (list api roles) v)
  (let m ([p pred])
    (match p
      ['any #t]
      [`(call ,a ,cs ...)
       (and (or (eq? a '_) (eq? a api))
            (for/and ([c (in-list cs)])
              (match-define (list role x) c)
              (define r (assq role roles))
              (and r (or (eq? x '_) (eq? (cdr r) x)))))]
      [`(ev-not ,q) (not (m q))]
      [`(ev-and ,qs ...) (andmap m qs)]
      [`(ev-or ,qs ...) (ormap m qs)])))

;; residual : property binding (event ...) -> node
(define (residual prop b history)
  (for/fold ([n (property-start prop)]) ([ev (in-list history)] #:when (in-slice? ev b))
    (derive n (view ev b) match-letter)))

;; properties-status : (property ...) ((X . TYPE) ...) (event ...) main? -> 'dead | 'accepted | 'open
;;   dead      some binding's residual is surely empty: no extension can satisfy it
;;   accepted  every binding's residual is nullable
;; main?: the history is on the main path; otherwise `(paths main)` properties are ignored.
(define (properties-status props objects history [main? #t])
  (define rs (for*/list ([p (in-list props)]
                         #:when (or main? (eq? (property-paths p) 'all))
                         [b (in-list (bindings p objects))])
               (residual p b history)))
  (cond [(not (andmap maybe-nonempty? rs)) 'dead]
        [(andmap nullable? rs) 'accepted]
        [else 'open]))

;; properties-may-call? : (property ...) (event ...) api-name inserted k main? -> boolean
;; Whether a call of api-name may come next: #f only when some property
;; surely rejects every history (event ...) ++ PRE ++ (a call of api-name),
;; PRE being at most k calls of the APIs in `inserted` (the providers that
;; may be called for the call's tracked arguments), in any order.  Only
;; name-only properties are consulted: for them the call's arguments and
;; results do not matter, so the answer agrees with what properties-status
;; says after the call.  The enumerator asks it before building the call's
;; argument choices (time-sinks.md A6).
(define (properties-may-call? props history api inserted k [main? #t])
  (define ps (for/list ([p (in-list props)]
                        #:when (and (property-name-only? p) (or main? (eq? (property-paths p) 'all))))
               p))
  (define (ev a) (list a '()))
  (or (null? ps)
      (let loop ([rs (for/list ([p (in-list ps)]) (residual p '() history))] [k k])
        (or (andmap maybe-nonempty? (for/list ([r (in-list rs)]) (derive r (ev api) match-letter)))
            (and (> k 0)
                 (for/or ([a (in-list inserted)])
                   (define rs2 (for/list ([r (in-list rs)]) (derive r (ev a) match-letter)))
                   ;; a dead residual stays dead
                   (and (andmap maybe-nonempty? rs2) (loop rs2 (sub1 k)))))))))
