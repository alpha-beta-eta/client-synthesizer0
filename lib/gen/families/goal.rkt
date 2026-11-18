#lang racket/base
;; goal: for every API G, can a caller who got G's arguments from real calls
;; satisfy each clause of G's requires?  One bounded goal regression
;; (the predecessor's docs/enumeration.md 9, 15; design.md 3.4).  A plan is a sequence of calls ending
;; in G with causal links; the question is G's requires.  Its obligations are G's
;; parameters a requires clause mentions (a parameter no clause mentions asks
;; nothing; it comes from the client's parameters).  Three relevances:
;;   R1 produce: an output of A can be the argument (goal-shapes.rkt's produces?);
;;      link A -out-> B.  A's own parameters come from the client (lifted),
;;      except one A's ensures mention together with A's result: its source
;;      bears on G's clause (`clone(self)` then the lemma on what it gave),
;;      so it is an obligation again (depth at most 2).
;;   R2 touch: H takes by `&mut` a value G takes; link H -touch-> G.  On H's
;;      success (or either way) only where H may change what G's clauses read
;;      (lib/gen/rw.rkt: neither given nor framed by H's ensures); after H's
;;      error always (the question is then whether the state is usable, 8.3).
;;      At most one touch.
;;   R3 again: a call took G's argument by value; G again on a value from a
;;      producer (R1), or on a new parameter where nothing produces it.
;;   R4 defs: what P's ensures write of an output or a `&mut` argument is read
;;      by some reader's requires (all-defs).
;; Round trips: derived from the types and the ensures (common.rkt's relations).
;; A plan is realized by goal-shapes.rkt's enum-goal, its acceptance read off
;; the links.
(require racket/list racket/match racket/set "../../model/api.rkt" "../../base/forms.rkt" "../../check/client.rkt"
         "../../model/knowledge.rkt" "common.rkt" "flow.rkt" "goal-shapes.rkt" (prefix-in rw: "../rw.rkt"))
(provide generate-goals plan-shape)

(define (all-params a) (append (api-params a) (api-ghost-params a)))

;; accept : (api ...) links -> (main-calls -> boolean)
;; links: (out I J): the I-th call's bound values are among the J-th's arguments;
;; (touch I J): the I-th and J-th calls share an argument.  The calls are found on
;; the main path in order, the first being the seed.
;; pick : (api ...) calls -> the calls of seq, in order on the main path (the first the seed, G last), or #f
(define (pick seq cs)
  (define names (map api-name seq))
  (define picked
    (let loop ([cs cs] [ns names] [first? #t] [acc '()])
      (cond [(null? ns) (reverse acc)]
            [(null? cs) #f]
            [(eq? (car (car cs)) (car ns)) (loop (cdr cs) (cdr ns) #f (cons (car cs) acc))]
            [first? #f]
            [else (loop (cdr cs) ns #f acc)])))
  (and picked (pair? cs) (eq? (car (last cs)) (last names)) picked))

(define (accept seq links)
  (lambda (cs)
    (define picked (pick seq cs))
    (and picked
         (for/and ([l links])
           (match l
             [`(out ,i ,j) (shares? (caddr (list-ref picked i)) (cadr (list-ref picked j)))]
             [`(touch ,i ,j) (shares? (cadr (list-ref picked i)) (cadr (list-ref picked j)))])))))

;; the parameters of b its requires mention
(define (asked b) (filter (lambda (p) (mentioned? p b)) (all-params b)))

;; connection : P w G p -> #f, 'any (any producer F of w), or a type T (F must
;; also take an argument of type T)
;; Does the source of P's argument w bear on G's clause about p (P's result)?
;; - P's ensures mention both its result and w: yes, from any producer.
;; - P has no ensures (external, trait: `item_into_raw`, `complement`): only
;;   through G, when a clause of G mentions p and another parameter s of w's
;;   type; then w must be related to s, so F takes an argument of that type
;;   (`clone(self)`, `item_into_raw`, then the lemma on self and the parts: the
;;   long chain of 7.6).  Without the condition every producer of every
;;   argument of an opaque P is an obligation (page_prop: 852 clients).
(define (strip t) (match t [`(,(or '& '&mut) ,x) (strip x)] [_ t]))
(define (connection pa w g p)
  (define ret (rw:source-ret-name pa))
  (define wn (symbol->string (param-name w)))
  (define ens (rw:source-ensures pa))
  (cond
    [(pair? ens)
     (and ret
          (for/or ([e ens])
            (define names (let walk ([x e]) (match x [`(path ,(? string? s)) (list s)] [(? pair?) (append-map walk x)] [_ '()])))
            (and (member ret names) (member wn names) #t))
          'any)]
    [else
     (for*/first ([r (api-requires g)] #:when (memq (param-name p) (expr-vars* r))
                  [s (all-params g)] #:when (and (not (eq? s p)) (memq (param-name s) (expr-vars* r))
                                                 (equal? (strip (param-type s)) (strip (param-type w)))))
       (strip (param-type w)))]))
(define (expr-vars* r) (let walk ([x r]) (cond [(symbol? x) (list x)] [(pair? x) (append-map walk x)] [else '()])))
(define (takes-type? f t) (for/or ([q (all-params f)]) (equal? (strip (param-type q)) t)))

;; plan-shape : client -> symbol, for reports: which rule instance gave it
(define (plan-shape c) (let ([s (assq 'plan (filter pair? (cddr c)))]) (if s (cadr s) 'other)))
(define (tag c shape) (and c (append c `((plan ,shape)))))

;; the branch of H's result G is called on in client c: ok, err, or any
(define (branch-of c gn)
  (or (let find ([x (cdr (or (assq 'body (filter pair? (cddr c))) '(body)))] [b 'any])
        (match x
          [`(assert-requires ,(== gn) ,_ ...) b]
          [`(if-let (,(or 'Some 'Ok) ,_) ,_ (then ,ts ...) (else ,es ...)) (or (find ts 'ok) (find es 'err))]
          [`(if-let (,(or 'Some 'Ok) ,_) ,_ ,ts ...) (find ts 'ok)]
          [(? pair?) (for/or ([y x]) (find y b))]
          [_ #f]))
      'any))

;; the calls on c's main path with their whole argument lists: (API (ARG ...)), args not only variables
(define (main-calls* c)
  (let loop ([ss (cdr (or (assq 'body (filter pair? (cddr c))) '(body)))] [acc '()])
    (match ss
      ['() (reverse acc)]
      [(cons s rest)
       (match s
         [(or `(let ,_ (call ,api ,as ,gs ,_ ...)) `(do (call ,api ,as ,gs ,_ ...))) (loop rest (cons (list api (append as gs)) acc))]
         [`(if-let ,_ ,_ (then ,ts ...) ,_ ...) (loop (append ts rest) acc)]
         [`(if-let ,_ ,_ ,ts ...) (loop (append ts rest) acc)]
         [_ (loop rest acc)])])))

;; does H, the i-th call of seq in c, touch something G (the last) reads and may change it?
(define (touch-matters? table c seq h g i)
  (define picked (pick seq (main-calls* c)))
  (define (mut? p) (match (param-type p) [`(&mut ,_) #t] [_ #f]))
  (and picked
       (let* ([hcall (list-ref picked i)] [gcall (last picked)]
              [hbind (for/list ([p (all-params h)] [a (cadr hcall)] #:when (and (symbol? a) (mut? p))) (cons a (param-name p)))]
              [shared (for*/list ([(p a) (in-parallel (all-params g) (cadr gcall))] [hb (in-value (and (symbol? a) (assq a hbind)))] #:when hb)
                        (cons (param-name p) (cdr hb)))])
         (pair? (rw:interferes? h g (branch-of c (api-name g)) shared)))))

;; generate-goals : table (name ...) #:knowledge #:identity #:elided-lifetimes? -> (client ...)
(define (generate-goals table names #:knowledge [k '()] #:identity [identity '()] #:elided-lifetimes? [elided? #f])
  (define steps (for/list ([n names] #:when (memq (api-mode (api-ref table n)) '(exec proof))) (api-ref table n)))
  (define targets (filter (lambda (g) (pair? (api-requires g))) steps))
  (define roles (knowledge-roles k))
  (define (assumed api) (knowledge-assumptions k api))
  (define (keep c) (and c (eq? (car (check-client table c)) 'client) c))
  (define enum-goal (make-enum-goal table k elided?))
  (define (realize seq links shape) (map (lambda (c) (tag c shape)) (enum-goal seq (last seq) (accept seq links))))
  ;; producers of a parameter p of b: (A output) for every output, a tuple's parts too
  (define (producers p b)
    (for*/list ([a steps] [o (outputs* a)] #:when (produces? o p b)) (list a o)))
  (define plans
    (append*
     (for/list ([g targets])
       (define qs (asked g))
       ;; R1, depth 1: a producer of an asked parameter (flow's client where the
       ;; output is whole; enum-goal for a tuple's part)
       (define r1
         (append*
          (for*/list ([p qs] [fo (producers p g)])
            (match-define (list f o) fo)
            (define i (index-of (all-params g) p))
            (if (member (take o 2) (map (lambda (x) (take x 2)) (outputs+ f)))
                (let ([c (or (keep (flow-client table f (take o 2) g p i #t roles #:assumed assumed))
                             (keep (flow-client table f (take o 2) g p i #f roles #:assumed assumed)))])
                  (if (and c (consistent-fresh? c g)) (list (tag c 'produce)) '()))
                (realize (list f g) '((out 0 1)) 'produce-part)))))
       ;; R1, depth 2: P produces an asked parameter of G; P's parameter w that
       ;; P's ensures connect to its result is an obligation; F produces w
       (define r1-2
         (append*
          (for*/list ([p qs] [po (producers p g)] #:unless (eq? (car po) g)
                      [pa (in-value (car po))] [w (all-params pa)] [conn (in-value (connection pa w g p))] #:when conn
                      [fo (producers w pa)] #:unless (eq? (car fo) pa)
                      #:when (or (eq? conn 'any) (takes-type? (car fo) conn)))
            (realize (list (car fo) pa g) '((out 0 1) (out 1 2)) 'produce-2))))
       ;; R1 twice: a clause mentions two asked parameters no single call
       ;; produces together (two holes, X6: 21 clauses); both from producers,
       ;; else the clause relating them is never asked with both from real calls
       (define r1x2
         (append*
          (for*/list ([r (api-requires g)]
                      [ps (in-value (filter (lambda (p) (memq (param-name p) (expr-vars* r))) qs))]
                      [p ps] [q ps] #:when (< (index-of ps p) (index-of ps q))
                      [pp (in-value (producers p g))] [qp (in-value (producers q g))]
                      #:when (and (pair? pp) (pair? qp) (null? (set-intersect (map car pp) (map car qp))))
                      [fp (remove-duplicates (map car pp))] [fq (remove-duplicates (map car qp))])
            (realize (list fp fq g) '((out 0 2) (out 1 2)) 'produce-two))))
       ;; R2: a touch by H, on its success (or either way) where it matters, after its error always
       (define hs (mutators-of steps g))
       (define r2
         (append*
          (for/list ([h hs])
            (filter (lambda (c) (touch-matters? table c (list h g) h g 0)) (realize (list h g) '((touch 0 1)) 'touch)))))
       (define r1+r2
         (append*
          (for*/list ([p qs] [fo (producers p g)] [h hs])
            (filter (lambda (c) (touch-matters? table c (list (car fo) h g) h g 1))
                    (realize (list (car fo) h g) '((out 0 2) (touch 1 2)) 'produce+touch)))))
       (define r2-err
         (for*/list ([h hs] [c (in-value (let ([c (after-err-client table h g (assumed h) roles)]) (and c (keep c))))] #:when c)
           (tag c 'touch-err)))
       ;; R3: G took an argument; G again on a produced value, else a new parameter
       (define cps (consumed-params table g))
       (define r3
         (if (null? cps) '()
             (let* ([fs (remove-duplicates
                         (for*/list ([p (all-params g)] #:when (memq (param-name p) cps) [fo (producers p g)]) (car fo)))]
                    [via (append* (for/list ([f fs]) (realize (list g f g) '((touch 0 2) (out 1 2)) 'again)))])
               (if (pair? via) via
                   (let ([c (again-client table g (assumed g))]) (if (and c (keep c)) (list (tag c 'again-new)) '()))))))
       (append r1 r1-2 r1x2 r2 r1+r2 r2-err r3))))
  ;; R4 defs (all-defs, docs/enumeration.md 15): what P's ensures write of an output or of a
  ;; `&mut` argument is asked by some reader's requires.  The rules above go back from a goal
  ;; among the module's own APIs, so an output only another module's API reads (DMA's
  ;; `reader` read by io's `read`) is never handed on, and a frame of a `&mut` argument
  ;; (`final(self).end == old(self).end`) is left out by R2's filter, which asks only where H
  ;; may change what G reads.  One client per output of P (per `&mut` argument): the
  ;; reader reading most of P's clauses about it (then by name), unless an own goal reads it
  ;; already (an output: R1 has the client) or none does.
  (define all-steps
    (remove-duplicates
     (append steps
             (for*/list ([n (table-names table)] [a (in-value (api-ref table n))]
                         #:when (and a (memq (api-mode a) '(exec proof)) (pair? (api-requires a)))) a))
     eq?))
  (define (reader-score g q paths) ; how many of the clauses (each a list of paths) g's requires read at q
    (define rds (for*/list ([c (api-requires g)] [rd (rw:requires-reads c)] #:when (eq? (car rd) (param-name q))) (cadr rd)))
    (for/sum ([ps paths]) (if (for*/or ([wp ps] [rp rds]) (rw:path-match? wp rp)) 1 0)))
  (define (best cands) ; ((score g q) ...) -> the best (g q), or #f
    (define ok (filter (lambda (x) (> (car x) 0)) cands))
    (and (pair? ok)
         (cdr (argmax car (sort ok symbol<? #:key (lambda (x) (api-name (cadr x))))))))
  (define r4
    (append*
     (for/list ([pa steps])
       (define ret (or (rw:source-ret-name pa) "r"))
       (define gout (rw:source-ghost-out pa))
       (define ws (for/list ([t (rw:source-ensures pa)]) (rw:clause-writes t ret gout)))
       (define (paths-of kind [var #f])
         (filter pair? (for/list ([w ws]) (for/list ([x w] #:when (and (eq? (car x) kind) (or (not var) (equal? (cadr x) var)))) (caddr x)))))
       (append
        ;; the outputs
        (append*
         (for/list ([o (outputs* pa)])
           (define paths (paths-of (if (eq? (car o) 'gret) 'gret 'ret)))
           (define (cands among) (for*/list ([g among] #:unless (eq? g pa) [q (all-params g)] #:when (produces? o q g))
                                   (list (reader-score g q paths) g q)))
           (define own (best (cands steps)))
           (define pick (and (pair? paths) (not own) (best (cands all-steps))))
           (if (not pick) '()
               (match-let ([(list g q) pick])
                 (define i (index-of (all-params g) q))
                 (if (member (take o 2) (map (lambda (x) (take x 2)) (outputs+ pa)))
                     (let ([c (or (keep (flow-client table pa (take o 2) g q i #t roles #:assumed assumed))
                                  (keep (flow-client table pa (take o 2) g q i #f roles #:assumed assumed)))])
                       (if c (list (tag c 'defs)) '()))
                     (realize (list pa g) '((out 0 1)) 'defs))))))
        ;; the `&mut` arguments: a touch, not filtered
        (append*
         (for/list ([v (all-params pa)] #:when (match (param-type v) [`(&mut ,t) (datatype? t)] [_ #f]))
           (define paths (paths-of 'final (symbol->string (param-name v))))
           (define pick
             (and (pair? paths)
                  (best (for*/list ([g all-steps] #:unless (eq? g pa) [q (all-params g)]
                                    #:when (and (eq? (param-mode q) (param-mode v))
                                                (match-type (strip-ref (param-type q)) (strip-ref (param-type v)) (map car (api-generics g)) '())))
                          (list (reader-score g q paths) g q)))))
           (if pick (realize (list pa (car pick)) '((touch 0 1)) 'defs-touch) '())))))))
  ;; round trips, as goal.rkt's (f)
  (define round-trips
    (append*
     (for*/list ([r (relations steps identity #:ensures? #t)]
                 [a (in-value (api-ref table (car r)))] [b (in-value (api-ref table (cadr r)))]
                 #:when (and a b (memq a steps) (memq b steps)))
       (map (lambda (c) (tag c 'round-trip))
            (enum-goal (if (eq? a b) (list a) (list a b)) b #:relations (list r)
                       (lambda (cs) (match cs
                                      [(list (list (== (api-name a)) aa ab) _ ... (list (== (api-name b)) ba _)) (shares? (append ab aa) ba)]
                                      [_ #f])))))))
  (remove-duplicates
   #:key (lambda (c) (list (form-ref c 'type-params) (form-ref c 'params) (form-ref c 'body)))
   (append plans round-trips r4)))
