#lang racket/base
;; A requires (or lemma ensures) clause from the source's tree instead of
;; VIR's (docs/representation.md 10): structure and spelling from the source,
;; meaning from VIR, the two aligned node by node by their spans.
;;
;; The tree is item-index --full-spans's: every node (@ "SPAN" NODE).  VIR's
;; clause of the same span gives, by span (extract.rkt's align-info):
;;   (fn NAME)               the function a call calls, as a client writes its path
;;   (ctor NAME)             the constructor a call or path names
;;   (const NAME)            the constant a path names
;;   (binders ((x T) ..))    a quantifier's bound variables with their types
;;   (wrapped Tracked|Ghost) a variable read whose type is Tracked<T> (Ghost<T>)
;; So no name is resolved by its spelling and no type is guessed.  A node VIR
;; has merged or dropped (`*final(x)` is one VIR node, an automatic `*` or `&`,
;; most `as int`, the `&&&` of a block) is printed as the source writes it:
;; the client is written in the same language, rustc and Verus do the same
;; there.  Methods are the source's: a method call resolves by its receiver's
;; type, which is the same in the client.  A name or binder VIR says nothing
;; of fails the clause (the caller keeps VIR's translation), with the reason
;; in current-source-failure.
(require racket/list racket/match racket/string "../model/template.rkt")
(provide source->aligned source->template strip-spans current-source-failure)

(struct fail (why))

;; current-source-failure : box, set to why the last source->aligned gave #f:
;; (name TEXT) a name VIR's node does not give, (form HEAD) a form not translated
(define current-source-failure (make-parameter (box #f)))

;; strip-spans : spanned tree -> tree (the form item-index --full prints)
(define (strip-spans t)
  (match t
    [(list '@ (? string?) node (? string?) ...) (strip-spans node)]
    [(? pair?) (map strip-spans t)]
    [_ t]))

;; source->aligned : spanned-tree info (VAR-SYMBOL ...) [rename] #:types -> E or #f
;; info: ((SPAN INFO ..) ..) for VIR's clause; vars: the variables' names as the
;; tree writes them; rename: ((NAME . SYMBOL) ..), the ones the table names
;; otherwise (a trait declaration's parameters by the impl's), not where a
;; quantifier binds the name; types: ((SYMBOL . TYPE) ..), the table's types of
;; the variables: one VIR reads as Tracked<T> where the table's type is T (the
;; table unwraps it) is written p for `p@`, Tracked(p) alone.
(define (source->aligned tree info vars [rename '()] #:types [types '()])
  (define (no why) (raise (fail why)))
  ;; at : the node's spans (without its attributes, then with them) -> VIR's INFO of kind k
  (define (at-info sps k)
    (for*/first ([sp (in-list (if (string? sps) (list sps) sps))]
                 [i (in-list (cond [(assoc sp info) => cdr] [else '()]))]
                 #:when (eq? (car i) k))
      i))
  (define (at sps k) (let ([i (at-info sps k)]) (and i (cadr i))))
  (with-handlers ([fail? (lambda (f) (set-box! (current-source-failure) (fail-why f)) #f)])
    (let loop ([t tree] [vars (map symbol->string vars)] [ren rename] [in-quant? #f])
      (define (sub t) (loop t vars ren in-quant?))
      (define (var p) (and (member p vars) (cond [(assoc p ren) => cdr] [else (string->symbol p)])))
      ;; the wrapper of a variable the table unwraps, or #f
      (define (unwrapped sp p)
        (define w (at sp 'wrapped))
        (define v (var p))
        (and w v
             (not (match (cond [(assq v types) => cdr] [else #f]) [(list (== w) _) #t] [_ #f]))
             w))
      (match t
        ;; a group or a block of one expression: the inner node is the expression
        [(list '@ _ (and inner (list '@ _ ...)) _ ...) (sub inner)]
        [(list '@ (? string? sp0) node alt ...)
         (define sp (cons sp0 alt))
         (match node
           ;; parentheses are no node of VIR's: VIR's span of the inner node may be theirs
           [`(paren ,a) (sub (add-spans a sp))]
           [`(path ,(? string? p))
            (cond [(var p) => (lambda (v) (let ([w (unwrapped sp p)]) (if w `(call ,w ,v) v)))]
                  [(member p '("true" "false")) (string->symbol p)]
                  [(or (at sp 'const) (at sp 'ctor)) => (lambda (n) `(const ,(spell p n)))]
                  [else (no `(name ,p))])]
           [`(view (@ ,vsp (path ,(? string? p)) ,valt ...)) #:when (unwrapped (cons vsp valt) p) (var p)]
           [`(call (@ ,_ (path "old") ,_ ...) ,a) `(old ,(sub a))]
           [`(call (@ ,_ (path ,(? string? f)) ,_ ...) ,args ...)
            (when (var f) (no '(form var-call)))
            (cond
              [(or (at sp 'fn) (at sp 'ctor)) => (lambda (n) `(call ,(spell f n) ,@(map sub args)))]
              ;; Verus's wrappers, no node of VIR's: written the same anywhere
              [(member f '("Tracked" "Ghost")) `(call ,(string->symbol f) ,@(map sub args))]
              [else (no `(name ,f))])]
           [`(,(and q (or 'forall 'exists)) ((,(? string? xs) ,_) ...) ,body)
            (define bs (or (at sp 'binders) (no `(form ,q))))
            (define typed (for/list ([x (in-list xs)]) (or (assq (string->symbol x) bs) (no `(form ,q)))))
            (define (unbound l) (filter (lambda (r) (not (member (car r) xs))) l))
            `(,q ,typed ,(loop body (append xs vars) (unbound ren) #t))]
           ;; a method VIR calls through its trait (a trait argument the receiver's
           ;; type does not determine): the trait's path, the receiver as VIR passes it
           [`(method ,r ,(? string?) ,_ ,args ...)
            #:when (at-info sp 'trait-fn)
            (match-define (list _ n w) (at-info sp 'trait-fn))
            (define rv (sub r))
            `(call ,n ,(case w [(deref) `(deref ,rv)] [(borrow) `(borrow ,rv)] [else rv]) ,@(map sub args))]
           [`(op ,(? cmp? o) ,(app strip-1 `(op ,(? cmp? _) ,_ ,_)) ,_)
            (define-values (terms ops) (chain node))
            `(and ,@(for/list ([x (in-list terms)] [y (in-list (cdr terms))] [o (in-list ops)])
                      `(,(string->symbol o) ,(sub x) ,(sub y))))]
           [_ (structural node sub no)])]
        [`(with-triggers (group ,gss ...) ... ,body)
         `(with-triggers ,@(for/list ([gs (in-list gss)]) `(group ,@(map sub gs))) ,(sub body))]
        [`(quant-attr ,(? string? a) ,body) `(quant-attr ,a ,(sub body))]
        ;; outside a quantifier a trigger means nothing (and Verus rejects it)
        [`(trigger ,a) (if in-quant? `(trigger ,(sub a)) (sub a))]
        [_ (no `(form ,(if (pair? t) (car t) t)))]))))

;; spell : the source's path text, VIR's name (symbol) of the item -> symbol
;; How a client writes the item VIR names, as close to the source as the
;; client's scope allows.  VIR's name says which item (its qualifier is what a
;; client in another module needs: `<C as crate::mm::PagingConstsTrait>::`
;; for the source's `C::`, the self type for `Self::`); the source says the
;; rest:
;;   - an absolute path outside the crate (`core::mem::size_of::<T>`) is
;;     written as it is: it names the same item anywhere (VIR's is vstd's spec
;;     of it, `vstd::layout::size_of_as_usize`);
;;   - the last segment is the source's where VIR's is its spec twin (Verus's
;;     `when_used_as_spec`: `frame_to_meta` used in a spec is `frame_to_meta_spec`);
;;   - the turbofish of the last segment is the source's (VIR spells every type
;;     argument out; the source's inference works the same in the client).
(define (spell text vir)
  (define v (symbol->string vir))
  (cond
    [(regexp-match? #px"^(core|alloc|std|vstd)::" text) (string->symbol text)]
    [else
     (define-values (vq vl vtf) (split-last v))
     (define-values (_sq sl stf) (split-last text))
     (define last (if (or (equal? vl sl) (equal? vl (string-append sl "_spec"))) sl vl))
     (string->symbol (string-append (if (equal? vq "") "" (string-append vq "::")) last stf))]))

;; split-last : path -> (values QUALIFIER LAST TURBOFISH), at the last `::`
;; outside angle brackets; TURBOFISH is "::<..>" or ""
(define (split-last p)
  (define segs
    (let loop ([i 0] [depth 0] [start 0] [acc '()])
      (cond
        [(>= i (string-length p)) (reverse (cons (substring p start) acc))]
        [else
         (define c (string-ref p i))
         (cond
           [(char=? c #\<) (loop (add1 i) (add1 depth) start acc)]
           [(char=? c #\>) (loop (add1 i) (max 0 (sub1 depth)) start acc)]
           [(and (zero? depth) (char=? c #\:) (< (add1 i) (string-length p)) (char=? (string-ref p (add1 i)) #\:))
            (loop (+ i 2) depth (+ i 2) (cons (substring p start i) acc))]
           [else (loop (add1 i) depth start acc)])])))
  ;; a turbofish is a last segment `<..>` after the name
  (define-values (name-segs tf)
    (if (and (>= (length segs) 2) (regexp-match? #px"^<.*>$" (last segs)))
        (values (drop-right segs 1) (string-append "::" (last segs)))
        (values segs "")))
  (values (string-join (drop-right name-segs 1) "::") (last name-segs) tf))

;; the forms whose meaning is their parts': loop translates a subtree
(define (structural t loop no)
  (match t
    [`(lit ,(? string? l))
     (cond [(regexp-match? #px"^[0-9]+$" l) (string->number l)]
           [(member l '("true" "false")) (string->symbol l)]
           [else `(const ,(string->symbol l))])]
    [`(op ,(? string? o) ,a ,b)
     (define A (loop a)) (define B (loop b))
     (match o
       [(or "==" "!=" "<" "<=" ">" ">=" "+" "-" "*" "/" "%" "<<" ">>" "=~=" "=~~=") `(,(string->symbol o) ,A ,B)]
       ["&&" `(and ,@(flat 'and A) ,@(flat 'and B))]
       ["||" `(or ,@(flat 'or A) ,@(flat 'or B))]
       ["==>" `(implies ,A ,B)]
       ["&" `(bitand ,A ,B)] ["|" `(bitor ,A ,B)] ["^" `(bitxor ,A ,B)]
       [(or "<==>" "===" "!==" "!~=" "!~~=") `(binop ,o ,A ,B)]
       [_ (no `(form ,o))])]
    [`(has ,a ,b) `(binop "has" ,(loop a) ,(loop b))]
    [`(not ,a) `(not ,(loop a))]
    [`(neg ,a) `(neg ,(loop a))]
    [`(deref ,a) `(deref ,(loop a))]
    [`(method ,r ,(? string? m) ,tf ,args ...)
     (define tft (and (string? tf) (string-trim tf)))
     `(method ,(loop r) ,(string->symbol (cond [(not tft) m]
                                               [(string-prefix? tft "::") (string-append m tft)]
                                               [else (string-append m "::" tft)]))
              ,@(map loop args))]
    [`(field ,a ,(? string? f)) `(field ,(loop a) ,(string->symbol f))]
    [`(arrow ,a ,(? string? f)) `(arrow ,(loop a) ,(string->symbol f))]
    [`(index ,a ,i) `(index ,(loop a) ,(loop i))]
    [`(as ,a ,(? string? ty)) `(as ,(loop a) (const ,(string->symbol ty)))]
    [`(ref ,a) `(borrow ,(loop a))]
    [`(tuple ,as ...) `(tuple ,@(map loop as))]
    [`(view ,a) `(view ,(loop a))]
    [`(is ,a ,(? string? v)) `(is ,(loop a) ,(string->symbol v))]
    [`(isnt ,a ,(? string? v)) `(not (is ,(loop a) ,(string->symbol v)))]
    [`(big-and ,as ...) `(and ,@(append-map (lambda (a) (flat 'and (loop a))) as))]
    [`(big-or ,as ...) `(or ,@(append-map (lambda (a) (flat 'or (loop a))) as))]
    [_ (no `(form ,(if (pair? t) (car t) t)))]))

;; add-spans : spanned node, more spans -> the node with them as alternatives
;; (through a trigger: `(#[trigger] f(x))`)
(define (add-spans t sps)
  (match t
    [(list '@ (? string? sp) node alt ...) `(@ ,sp ,node ,@alt ,@sps)]
    [`(trigger ,a) `(trigger ,(add-spans a sps))]
    [_ t]))

(define (strip-1 t) (match t [(list '@ (? string?) n _ ...) n] [_ t]))

(define (flat op e) (match e [`(,(== op) ,xs ...) xs] [_ (list e)]))

(define (cmp? o) (and (member o '("<" "<=" ">" ">=")) #t))

;; chain : a left-nested comparison -> (values (TERM ...) (OP ...)), TERM_i OP_i TERM_i+1
;; Verus's `a <= b < c` is `a <= b && b < c`; the parser nests it to the left;
;; a parenthesized `(a <= b) < c` has a paren node, so it is not a chain.
(define (chain t)
  (match (strip-1 t)
    [`(op ,(? cmp? o) ,l ,r)
     (define-values (ts os) (chain l))
     (values (append ts (list r)) (append os (list o)))]
    [_ (values (list t) '())]))
