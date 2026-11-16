#lang racket/base
;; Derivatives of grammars (design.md, 结论16): Brzozowski derivatives
;; extended to recursive grammars as in "parsing with derivatives" (Might,
;; Darais, Spiewak 2011), with intersection and complement.
;;
;; A grammar is a graph of nodes; recursion is a cycle through `ref` nodes.
;; Letters are opaque predicates, decided by a function given by the caller,
;; so this file knows nothing about calls or events.
;;
;;   R = eps | empty | LETTER | (seq R ...) | (alt R ...) | (and R ...) | (not R)
;;     | (* R) | (+ R) | (opt R) | (contains R ...) | N
;;   (contains R1 ... Rn) = any* R1 any* ... Rn any*
;;   G = R | (grammar START (N R) ...)      a nested grammar is also an R
;;
;; `not` may only be applied to an expression that mentions no nonterminal
;; of an enclosing grammar (a nested grammar of its own is fine): its
;; nullability is then computed by a separate fixpoint, and the outer
;; fixpoint stays monotone (结论16).
(require racket/list racket/match)
(provide compile-grammar derive nullable? maybe-nonempty?)

;; node: kind is one of empty eps letter alt seq and not star ref.
;;   letter: x = predicate; alt/seq/and: x, y; not/star: x; ref: x = target (#f while pending)
(struct node (kind [x #:mutable] y))

(define EMPTY (node 'empty #f #f))
(define EPS (node 'eps #f #f))

;; resolve: follow refs whose targets are set.
(define (resolve n)
  (if (and (eq? (node-kind n) 'ref) (node-x n)) (resolve (node-x n)) n))

(define (empty-node? n) (eq? (node-kind (resolve n)) 'empty))
(define (eps-node? n) (eq? (node-kind (resolve n)) 'eps))

(define (mk-alt a b)
  (cond [(empty-node? a) b] [(empty-node? b) a] [(eq? (resolve a) (resolve b)) a] [else (node 'alt a b)]))
(define (mk-seq a b)
  (cond [(or (empty-node? a) (empty-node? b)) EMPTY] [(eps-node? a) b] [(eps-node? b) a] [else (node 'seq a b)]))
(define (mk-and a b)
  (cond [(or (empty-node? a) (empty-node? b)) EMPTY] [else (node 'and a b)]))
(define (mk-not a)
  (define r (resolve a))
  (if (eq? (node-kind r) 'not) (node-x r) (node 'not a #f)))

;; ================================================================ compiling

;; compile-grammar : G letter? -> node
;; letter? : S-expression -> boolean, tells letters from regex forms.
(define (compile-grammar g letter?)
  (match g
    [`(grammar ,start (,names ,bodies) ...)
     (define refs (for/hash ([n (in-list names)]) (values n (node 'ref #f #f))))
     (for ([n (in-list names)] [b (in-list bodies)])
       (set-node-x! (hash-ref refs n) (compile-re b refs letter?)))
     (or (hash-ref refs start #f) (error 'grammar "start ~a is not defined" start))]
    [_ (compile-re g (hash) letter?)]))

(define (compile-re r refs letter?)
  (define (c r) (compile-re r refs letter?))
  (define any* (node 'star (node 'letter 'any #f) #f))
  (match r
    ['eps EPS]
    ['empty EMPTY]
    [(? letter?) (node 'letter r #f)]
    [`(seq) EPS]
    [`(seq ,a ,bs ...) (for/fold ([n (c a)]) ([b (in-list bs)]) (mk-seq n (c b)))]
    [`(alt ,a ,bs ...) (for/fold ([n (c a)]) ([b (in-list bs)]) (mk-alt n (c b)))]
    [`(and ,a ,bs ...) (for/fold ([n (c a)]) ([b (in-list bs)]) (mk-and n (c b)))]
    [`(not ,a)
     (unless (closed? a refs) (error 'grammar "not: nonterminal under not: ~s" a))
     (mk-not (c a))]
    [`(* ,a) (node 'star (c a) #f)]
    [`(+ ,a) (let ([n (c a)]) (mk-seq n (node 'star n #f)))]
    [`(opt ,a) (mk-alt EPS (c a))]
    [`(contains ,as ...) (for/fold ([n any*]) ([a (in-list as)]) (mk-seq n (mk-seq (c a) any*)))]
    ;; A nested grammar has its own nonterminals; it cannot see the outer ones.
    [`(grammar ,_ ...) (compile-grammar r letter?)]
    [(? symbol? n) (or (hash-ref refs n #f) (error 'grammar "unknown nonterminal ~a" n))]
    [_ (error 'grammar "bad expression ~s" r)]))

(define (closed? r refs)
  (match r
    [`(grammar ,_ ...) #t]
    [(? symbol? n) (not (hash-ref refs n #f))]
    [(list _ rs ...) (andmap (lambda (x) (closed? x refs)) rs)]
    [_ #t]))

;; ================================================================ derivatives

;; derive : node key match? -> node
;; key identifies the letter being consumed (an event as seen by one
;; binding); match? : predicate key -> boolean.  Results are memoized by
;; (node, key); a recursive call on the same pair while it is being
;; computed gets a pending ref, which is set when the computation ends
;; (this is how derivatives of recursive grammars terminate).
;; A strong table: its keys are fresh pairs, which a weak table would lose at
;; every collection.
(define memo (make-hash))

(define (derive n key match?)
  (define mk (cons n key))
  (define hit (hash-ref memo mk #f))
  (cond
    [hit (when (pair? hit) (set-box! (cadr hit) #t))
         (if (pair? hit) (caddr hit) hit)]
    [else
     (define placeholder (node 'ref #f #f))
     (define used (box #f))
     (hash-set! memo mk (list 'pending used placeholder))
     (define r (derive* (resolve n) key match?))
     (cond [(unbox used) (set-node-x! placeholder r) (hash-set! memo mk placeholder) placeholder]
           [else (hash-set! memo mk r) r])]))

(define (derive* n key match?)
  (define (d m) (derive m key match?))
  (match (node-kind n)
    [(or 'empty 'eps) EMPTY]
    ['letter (if (match? (node-x n) key) EPS EMPTY)]
    ['alt (mk-alt (d (node-x n)) (d (node-y n)))]
    ['seq (mk-alt (mk-seq (d (node-x n)) (node-y n))
                  (if (nullable? (node-x n)) (d (node-y n)) EMPTY))]
    ['and (mk-and (d (node-x n)) (d (node-y n)))]
    ['not (mk-not (d (node-x n)))]
    ['star (mk-seq (d (node-x n)) n)]
    ['ref (if (node-x n) (d (node-x n)) (error 'derive "pending ref"))]))

;; ================================================================ fixpoints

;; A least fixpoint over the nodes reachable from n.  step computes a node's
;; value from its children's current values.
(define (fixpoint n step)
  (define nodes (reachable n))
  (define val (make-hasheq))
  (for ([m (in-list nodes)]) (hash-set! val m #f))
  (define (get m) (hash-ref val m #f))
  (let loop ()
    (define changed
      (for/fold ([ch #f]) ([m (in-list nodes)])
        (define v (step m get))
        (cond [(eq? v (get m)) ch] [else (hash-set! val m v) #t])))
    (when changed (loop)))
  (get n))

(define (reachable n)
  (define seen (make-hasheq))
  (let walk ([m n])
    (unless (hash-ref seen m #f)
      (hash-set! seen m #t)
      (match (node-kind m)
        [(or 'alt 'seq 'and) (walk (node-x m)) (walk (node-y m))]
        [(or 'star 'not) (walk (node-x m))]
        ['ref (when (node-x m) (walk (node-x m)))]
        [_ (void)])))
  (hash-keys seen))

(define nullable-memo (make-weak-hasheq))

;; nullable? : node -> boolean, whether the empty sequence is in the language.
(define (nullable? n)
  (hash-ref! nullable-memo n
             (lambda ()
               (fixpoint n (lambda (m get)
                             (match (node-kind m)
                               ['empty #f] ['eps #t] ['letter #f] ['star #t]
                               ['alt (or (get (node-x m)) (get (node-y m)))]
                               [(or 'seq 'and) (and (get (node-x m)) (get (node-y m)))]
                               ['not (not (nullable? (node-x m)))]
                               ['ref (and (node-x m) (get (node-x m)))]))))))

;; maybe-nonempty? : node -> boolean.  #f only when the language is surely
;; empty; intersections and complements are over-approximated (结论17).
(define (maybe-nonempty? n)
  (fixpoint n (lambda (m get)
                (match (node-kind m)
                  ['empty #f] [(or 'eps 'letter 'star 'not) #t]
                  ['alt (or (get (node-x m)) (get (node-y m)))]
                  [(or 'seq 'and) (and (get (node-x m)) (get (node-y m)))]
                  ['ref (and (node-x m) (get (node-x m)))]))))
