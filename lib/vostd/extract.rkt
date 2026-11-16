#lang racket/base
;; Extracting API tables from VIR (design.md, 结论34).
;;
;; For every exec or proof function visible outside its module (and every spec method) of the
;; selected modules, an entry of the API table (api.rkt), one table per
;; owning module, and a target (run.rkt) that puts the client module inside
;; that module.  What comes from where:
;;   mode, generics and their bounds, parameters (mode, type), return, unsafe,
;;   method or function                                  VIR
;;   ghost parameters written with `#[verus_spec(with ..)]`: those of the
;;   `_VERUS_VERIFIED_` twin that the plain twin lacks;   VIR
;;   the self type of an associated function without self  item-index (verus_syn),
;;                                                         else VIR (macro output)
;;   requires                                              VIR expressions, translated;
;;                                                         a trait impl's, from the trait
;;   lifetime parameters of datatypes and traits           the source (not in VIR)
;; A requires clause that cannot be translated (quantifiers, match, closures,
;; ...) is left out and counted in `(skipped-requires N WHY ...)`; `probe` then
;; reports the entry as requires-weaker, so such entries are not trusted.
;; A function whose signature cannot be expressed is left out, with the reason.
(require racket/list racket/match racket/string racket/file racket/pretty racket/system racket/port
         "vir.rkt" "git.rkt" "../base/forms.rkt" (only-in "../model/api.rkt" type->text) "source-spec.rkt")
(provide extract-tables)

(define vprefix "_VERUS_VERIFIED_")
;; the clients' module, beside the module under test (placement)
(define client-module "cs_clients")

(define (fn-path f) (format "~a" (field (field f 'name) 'path)))
;; A trait default method an impl does not override is, in VIR, a copy named
;; `default%impl&%N%%%m` whose own type parameters are `def_typ_param%T` (and whose
;; requires and ensures are empty: they are the declaration's, taken by decl-of).
;; Named as the impl's method `impl&%N::m`, with the declaration's parameter names.
(define (inherited-as-impl f)
  (define (inherited? f)
    (match (field (field f 'name) 'path)
      [p (regexp-match? #rx"default%impl&%[0-9]+%%%" (format "~a" p))]))
  (define (fix s) (regexp-replace* #rx"def_typ_param%" (regexp-replace* #rx"default%(impl&%[0-9]+)%%%" s "\\1::") ""))
  (if (inherited? f)
      (let loop ([e f])
        (cond [(string? e) (fix e)]
              [(symbol? e) (let ([s (symbol->string e)]) (if (regexp-match? #rx"%" s) (string->symbol (fix s)) e))]
              [(pair? e) (cons (loop (car e)) (loop (cdr e)))]
              [else e]))
      f))
(define (plain p) (string-replace p vprefix ""))
(define (attr f k) (eq? (field (field f 'attrs) k) 'true))
(define (var-name v) (match v [(list 'VarIdent (? string? s) _ ...) s] [_ #f]))
(define (params f) (let ([ps (field f 'params)]) (if (list? ps) (map unwrap ps) '())))
(define (segments p) (string-split (format "~a" p) "::"))
(define (last-seg p) (last (segments p)))
;; The standard library's paths go through private modules too: VIR gives the
;; defining one (`core::ops::range::Range`), the client writes the public
;; re-export (`core::ops::Range`; E0603 otherwise, and rustc suggests an import,
;; which repair does not take).
(define (ostd-path->crate p)
  (define s (format "~a" p))
  (cond [(string-prefix? s "ostd::") (string-append "crate::" (substring s 6))]
        [(regexp-match #px"^(core|alloc|std)::ops::range::(.*)$" s) => (lambda (m) (format "~a::ops::~a" (cadr m) (caddr m)))]
        [else s]))

;; How a trait is named in the client: ostd's by their crate path, the standard
;; library's by their name (its paths go through private modules, and its
;; traits are in the prelude), others (vstd) by their path.
(define (trait-ref p)
  (define s (format "~a" p))
  (cond [(string-prefix? s "ostd::") (ostd-path->crate s)]
        [(regexp-match? #rx"^(core|alloc|std)::" s) (last-seg s)]
        [else s]))

(struct no (what) #:transparent)
(define (fail what) (raise (no what)))

;; ================================================================ types

;; typ : VIR type -> TYPE (api.rkt).  Tracked and Ghost decorations are
;; dropped: the parameter's mode says it.
(define (typ t)
  (match t
    [(list 'Typ 'Bool) 'bool]
    [(list 'Typ 'Int (list 'IntRange 'USize)) 'usize]
    [(list 'Typ 'Int (list 'IntRange 'ISize)) 'isize]
    [(list 'Typ 'Int (list 'IntRange 'U n)) (string->symbol (format "u~a" n))]
    [(list 'Typ 'Int (list 'IntRange 'I n)) (string->symbol (format "i~a" n))]
    [(list 'Typ 'Int (or 'Int (list 'IntRange 'Int))) 'int]
    [(list 'Typ 'Int (or 'Nat (list 'IntRange 'Nat))) 'nat]
    ;; a const generic argument (`[T; 512]`'s 512, `Foo<5>`) and others written as they are
    [(list 'Typ 'ConstInt (? exact-integer? n)) (string->symbol (number->string n))]
    [(list 'Typ 'Primitive (list 'Primitive 'StrSlice) _ ...) 'str]
    [(list 'Typ 'Dyn p _ ...) (string->symbol (format "dyn ~a" (last-seg p)))]
    [(list 'Typ 'TypParam (? string? s)) (string->symbol (string-replace s "Self%" "Self"))]
    [(list 'Typ 'MutRef inner) `(&mut ,(typ inner))]
    [(list 'Typ 'Decorate (list 'TypDecoration 'Ref) _ inner) `(& ,(typ inner))]
    [(list 'Typ 'Decorate (list 'TypDecoration (or 'Tracked 'Ghost)) _ inner) (typ inner)]
    [(list 'Typ 'Decorate (list 'TypDecoration d) _ inner) `(,d ,(typ inner))]
    [(list 'Typ 'Datatype (list 'Dt 'Tuple _) ts _ ...) `(tuple ,@(map typ ts))]
    [(list 'Typ 'Datatype (list 'Dt 'Path p) ts0 _ ...)
     (define n (datatype-name p))
     ;; the default allocator argument (`Vec<T, Global>`) is left implicit
     (define ts (filter (lambda (t) (not (match t [(list 'Typ 'Datatype (list 'Dt 'Path 'alloc::alloc::Global) _ ...) #t]
                                                 [_ #f])))
                        ts0))
     (define args (append (lifetime-args (hash-ref (current-lifetimes) (format "~a" p) 0)) (map typ ts)))
     (if (null? args) n (cons n args))]
    [(list 'Typ 'Projection _ ...)
     (define targs (or (field (cdr t) 'trait_typ_args) '()))
     (define name (field (cdr t) 'name))
     (unless (and (pair? targs) name) (fail 'projection))
     (define self (typ (car targs)))
     (define trait (field (cdr t) 'trait_path))
     ;; `C::E` for a type parameter C; `<KernelPtConfig as PageTableConfig>::E` otherwise.
     ;; A trait with type arguments is named with them even for a type parameter:
     ;; M may be bounded by two instances (`Repr<MetaSlotSmall>` and `Repr<
     ;; MetaSlotStorage>` from two APIs of a protocol), and `M::ReprPerm` is then
     ;; ambiguous (E0221).  Only when the arguments mention no type parameter (the
     ;; trait is written as text, which instantiation does not reach).
     (define targ-texts
       (and trait (pair? (cdr targs))
            (with-handlers ([no? (lambda (_) #f)])
              (define (has-param? v) (match v [(list 'Typ 'TypParam _ ...) #t] [(? pair?) (ormap has-param? v)] [_ #f]))
              (and (not (ormap has-param? (cdr targs)))
                   (for/list ([a (in-list (cdr targs))]) (type->text (typ a)))))))
     (cond
       [(and targ-texts (match (car targs) [(list 'Typ 'TypParam _) #t] [_ #f]))
        `(assoc ,self ,(string->symbol name) ,(format "~a<~a>" (trait-ref trait) (string-join targ-texts ", ")))]
       [(or (not trait) (match (car targs) [(list 'Typ 'TypParam _) #t] [_ #f]))
        `(assoc ,self ,(string->symbol name))]
       [else `(assoc ,self ,(string->symbol name) ,(trait-ref trait))])]
    [(list 'Typ 'Primitive (list 'Primitive 'Slice) (list t0) _ ...) `(slice ,(typ t0))]
    [_ (fail 'type)]))

;; Lifetimes are not in VIR.  A datatype or trait declared with lifetime
;; parameters (`Cursor<'rcu, C, A>`, `NonNullPtrRef<'a>`) gets them all as
;; one lifetime 'a, which the entry then declares: in a signature, a cursor
;; and its owner have the same lifetime.
;; current-lifetimes : VIR path (datatype) or trait name -> number of lifetime parameters
(define current-lifetimes (make-parameter (hash)))
;; current-lifetime-used : box, set when a type or bound of the entry got 'a
(define current-lifetime-used (make-parameter (box #f)))
(define lifetime '|'a|)

(define (lifetime-args k)
  (when (> k 0) (set-box! (current-lifetime-used) #t))
  (for/list ([_ (in-range k)]) lifetime))

;; The number of lifetime parameters NAME is declared with in text.
(define (declared-lifetimes text name)
  (match (regexp-match (pregexp (format "(?:struct|enum|union|trait)\\s+~a\\s*<((?:\\s*'[A-Za-z_]+\\s*(?::[^,>]*)?,?)+)"
                                        (regexp-quote name)))
                       text)
    [(list _ ls) (length (regexp-match* #px"'[A-Za-z_]+" ls))]
    [_ 0]))

(define (unit? t) (equal? t '(tuple)))

;; The decoration of a parameter's type: Tracked, Ghost or #f.
(define (decoration t)
  (match t
    [(list 'Typ 'Decorate (list 'TypDecoration (and d (or 'Tracked 'Ghost))) _ _) d]
    [_ #f]))

;; A const generic (`const L: usize`) is the bound (const usize).
(define (generics f)
  (define bounds (or (field f 'typ_bounds) '()))
  (for/list ([tp (in-list (or (field f 'typ_params) '()))])
    (define const-t (for/or ([b (in-list bounds)])
                      (match b [(list 'GenericBound 'ConstTyp (list 'Typ 'TypParam (== tp)) t) t] [_ #f])))
    (if const-t
        (list (string->symbol tp) (list 'const (typ const-t)))
    (cons (string->symbol (string-replace tp "Self%" "Self"))
          (for*/list ([b (in-list bounds)]
                      #:when (match b
                               [(list 'GenericBound 'Trait (list 'TraitId 'Path _) (cons (list 'Typ 'TypParam (== tp)) _)) #t]
                               [_ #f]))
            (match-define (list 'GenericBound 'Trait (list 'TraitId 'Path tpath) (cons _ rest)) b)
            (define n (string->symbol (last-seg tpath)))
            ;; closure parameters are not supported (design.md 结论23)
            (when (memq n '(Fn FnMut FnOnce)) (fail 'closure-bound))
            (define args (append (lifetime-args (hash-ref (current-lifetimes) (last-seg tpath) 0)) (map typ rest)))
            (if (null? args) n (cons n args)))))))

;; ================================================================ expressions

;; expr : VIR expression -> E (client.rkt), or raises no.
;; method? : callee path -> whether calls to it are written as methods.
;; ptypes : callee path -> the VIR types of its parameters, or #f when unknown.
(define (expr e method? ptypes)
  (define (x e) (expr e method? ptypes))
  (match (unwrap e)
    [(list '> 'ReadPlace p _ ...) (place p method? ptypes)]
    [(list '> 'Old a) `(old ,(x a))]
    [(list '> 'Const (list 'Constant 'Bool b)) (if (eq? b 'true) 'true 'false)]
    [(list '> 'Const (list 'Constant 'Int n)) (if (number? n) n (or (string->number (format "~a" n)) (fail 'int)))]
    [(list '> 'ConstVar (list 'Fun ':path p) _ ...) `(const ,(string->symbol (ostd-path->crate p)))]
    [(list '> 'Binary (list 'BinaryOp 'Arith (list 'ArithOp op _ ...)) a b) `(,(arith op) ,@(widen x a b))]
    [(list '> 'Binary (list 'BinaryOp 'Inequality (list 'InequalityOp op)) a b) `(,(ineq op) ,@(widen x a b))]
    [(list '> 'Binary (list 'BinaryOp 'Bitwise (list 'BitwiseOp op _ ...) _ ...) a b)
     `(,(match op ['BitAnd 'bitand] ['BitOr 'bitor] ['BitXor 'bitxor] ['Shl '<<] ['Shr '>>] [_ (fail 'Bitwise)])
       ,(x a) ,(x b))]
    [(list '> 'Binary (list 'BinaryOp op _ ...) a b) `(,(binop op) ,(x a) ,(x b))]
    ;; `a =~= b`, `a =~~= b`
    [(list '> 'BinaryOpr (list 'BinaryOpr 'ExtEq deep _ ...) a b)
     `(,(if (eq? deep 'true) '=~~= '=~=) ,(x a) ,(x b))]
    ;; usize::MAX (VIR: the unsigned maximum of the architecture's word width)
    [(list '> 'UnaryOpr (list 'UnaryOpr 'IntegerTypeBound (list 'IntegerTypeBoundKind 'UnsignedMax) _ ...)
           (app unwrap (list '> 'UnaryOpr (list 'UnaryOpr 'IntegerTypeBound (list 'IntegerTypeBoundKind 'ArchWordBits) _ ...) _)))
     '(const usize::MAX)]
    [(list '> 'Logical (list 'LogicalOp op) a b)
     (match op ['And `(and ,(x a) ,(x b))] ['Or `(or ,(x a) ,(x b))] ['Implies `(implies ,(x a) ,(x b))]
       [_ (fail 'logical)])]
    [(list '> 'Unary (list 'UnaryOp 'Not) a) `(not ,(x a))]
    ;; `forall|i: int| ..`, `exists|..| ..`: the bound variables with their types
    ;; (the source's triggers are dropped: Verus chooses, render.rkt)
    ;; a block of spec `let`s and an expression (`{ let idx = meta_to_index(p); P(idx) }`,
    ;; often in a quantifier's body): the lets are substituted, as they are pure
    [(list '> 'Block (? list? stmts) tail)
     (define binds
       (for/list ([s (in-list stmts)])
         (define u (unwrap s))
         (unless (and (pair? u) (eq? (car u) 'Stmt) (pair? (cdr u)) (eq? (cadr u) 'Decl)) (fail 'Block))
         (define pat (field u 'pattern))
         (define init (field u 'init))
         (define name (let find ([t pat])
                        (match t [(list 'VarIdent (? string? n) _ ...) n] [(? pair?) (ormap find t)] [_ #f])))
         (unless (and name init (regexp-match? #rx"Pattern Var" (format "~s" pat))) (fail 'Block))
         (cons (string->symbol name)
               (match (unwrap init) [(list 'Place _ ...) (place init method? ptypes)] [_ (x init)]))))
     (for/fold ([body (x tail)]) ([b (in-list (reverse binds))])
       (let-subst body (car b) (cdr b)))]
    ;; a boolean `if c { a } else { b }`: (c ==> a) && (!c ==> b)
    [(list '> 'If c a b) #:when (equal? (node-typ e) '(Typ Bool))
     (define cx (x c))
     `(and (implies ,cx ,(x a)) (implies (not ,cx) ,(x b)))]
    ;; `#![trigger f(i), g(i)]`: (with-triggers (group f(i) g(i)) .. BODY)
    [(list '> 'WithTriggers _ ...)
     (define ts (field (unwrap e) 'triggers))
     `(with-triggers ,@(for/list ([g (in-list (if (list? ts) ts '()))]) `(group ,@(map x (if (list? g) g (list g)))))
                     ,(x (or (field (unwrap e) 'body) (fail 'WithTriggers))))]
    [(list '> 'Quant (list (and q (or 'Forall 'Exists))) binders body)
     `(,(if (eq? q 'Forall) 'forall 'exists)
       ,(for/list ([b (in-list binders)])
          (match (unwrap b)
            [(list '-> v t) (list (string->symbol (or (var-name v) (fail 'Quant))) (typ t))]
            [_ (fail 'Quant)]))
       ,(x body))]
    ;; an integer cast (`idx as int`): kept, since a spec function's parameter
    ;; type does not coerce (`s.spec_index(idx as int)`)
    [(list '> 'Unary (and op (list 'UnaryOp 'Clip _ ...)) a)
     (define t (with-handlers ([no? (lambda (_) #f)]) (typ `(Typ Int ,(field op 'range)))))
     (if t `(as ,(x a) (const ,t)) (x a))]
    ;; triggers are kept (Verus cannot always infer them: `#![auto]` alone fails
    ;; where the source annotates): `#[trigger] e`, `#![auto]`, `#![all_triggers]`
    [(list '> 'Unary (list 'UnaryOp 'Trigger (list 'TriggerAnnotation 'Trigger _ ...)) a) `(trigger ,(x a))]
    [(list '> 'Unary (list 'UnaryOp 'Trigger (list 'TriggerAnnotation 'AutoTrigger _ ...)) a) `(quant-attr "auto" ,(x a))]
    [(list '> 'Unary (list 'UnaryOp 'Trigger (list 'TriggerAnnotation 'AllTriggers _ ...)) a) `(quant-attr "all_triggers" ,(x a))]
    [(list '> 'Unary (list 'UnaryOp (or 'Trigger 'CoerceMode 'HeightTrigger 'StrIsAscii) _ ...) a) (x a)]
    ;; VIR reads through a Tracked/Ghost wrapper without a node: a variant check
    ;; of a field of type Tracked<Option<T>> (`f.tracked_metadata_perm@ is Some`)
    ;; needs its `@` back
    [(list '> 'UnaryOpr (and op (list 'UnaryOpr 'IsVariant _ ...)) a)
     (define (peel e)
       (match (unwrap e)
         [(list '> 'Unary (list 'UnaryOp (or 'Trigger 'CoerceMode) _ ...) b) (peel b)]
         [_ e]))
     ;; (a local is unwrapped in the table, `Tracked(perm): Tracked<T>`, unless
     ;; its type there is Tracked<T> itself; see current-tracked-typed)
     (define local
       (match (unwrap (peel a))
         [(list '> 'ReadPlace (app unwrap (list 'Place 'Local _)) _ ...) (x a)]
         [_ #f]))
     (define a* (match (or (read-place-typ (peel a)) (node-typ (peel a)))
                  [(list 'Typ 'Decorate (list 'TypDecoration (or 'Tracked 'Ghost)) _ _)
                   #:when (or (not local) (memq local (current-tracked-typed)))
                   `(view ,(x a))]
                  [_ (x a)]))
     `(is ,a* ,(string->symbol (or (field op 'variant) (fail 'variant))))]
    [(list '> 'UnaryOpr (list 'UnaryOpr (or 'Box 'Unbox) _ ...) a) (x a)]
    [(list '> 'Multi (list 'MultiOp 'Chained ops) args)
     (define as (map x args))
     `(and ,@(for/list ([op (in-list ops)] [l (in-list as)] [r (in-list (cdr as))])
               (match op
                 [(list 'ChainedOp 'Inequality (list 'InequalityOp o)) `(,(ineq o) ,l ,r)]
                 [_ (fail 'chained)])))]
    [(list '> 'Call ':target (list 'CallTarget 'Fun kind (list 'Fun ':path p) typs _ ...) ':args args _ ...)
     ;; VIR leaves out the dereference of a shared reference passed where the
     ;; callee takes the value (`x.wf(*owner)`); it is put back, except on a receiver
     (define resolved (let ([r (field kind 'resolved)]) (and r (field r 'path))))
     (define pts (or (and resolved (ptypes resolved)) (ptypes p typs) '()))
     (define as (for/list ([a (in-list args)] [i (in-naturals)])
                  (define pt (and (< i (length pts)) (list-ref pts i)))
                  (define receiver? (and (zero? i) (method? p)))
                  (cond
                    [(and (not receiver?) pt (ref-typ? (node-typ a)) (not (ref-typ? pt)) (not (typ-param? pt)))
                     `(deref ,(x a))]
                    ;; and the other way: a value passed where the callee takes a shared reference
                    [(and (not receiver?) pt (node-typ a) (not (ref-typ? (node-typ a))) (ref-typ? pt)
                          (not (typ-param? (node-typ a))))
                     `(borrow ,(x a))]
                    ;; Rust's auto-ref (`frames.len()` on a `Vec` in a spec): the argument
                    ;; is a reference, the place it reads is not
                    [(and (not receiver?) pt (ref-typ? pt) (ref-typ? (node-typ a))
                          (let ([pl (read-place-typ a)]) (and pl (not (ref-typ? pl)) (not (typ-param? pl)))))
                     `(borrow ,(x a))]
                    ;; a bounded integer passed for an int (or nat) parameter: the widening VIR leaves out
                    [(and pt (match* (pt (node-typ a))
                               [((list 'Typ 'Int (or 'Int 'Nat (list 'IntRange (or 'Int 'Nat)))) (list 'Typ 'Int (list 'IntRange (or 'U 'I 'USize 'ISize) _ ...))) #t]
                               [(_ _) #f]))
                     `(as ,(x a) (const ,(match pt [(list _ _ (or 'Nat (list 'IntRange 'Nat))) 'nat] [_ 'int])))]
                    [else (x a)])))
     (cond
       ;; `x->0` of an Option (or any `arrow_N`/`arrow_Name` accessor, vstd's
       ;; OptionAdditionalFns::arrow_0 among them) is written back as `x->0`:
       ;; called by the trait's path it would want `&x` (E0308)
       [(and (pair? as) (null? (cdr as)) (regexp-match #rx"^arrow_(.+)$" (last-seg p)))
        => (lambda (m) `(arrow ,(match (car as) [`(borrow ,e) e] [e e]) ,(string->symbol (cadr m))))]
       ;; a method of vstd's std_specs traits by the trait's path, as for the
       ;; entries: XSpec and XSpecImpl are both in scope
       [(and (method? p) (pair? as) (regexp-match? #rx"^vstd::std_specs::" (format "~a" p)))
        (define segs (segments p))
        ;; no auto-ref through the trait's path: `spec_index(&self, ..)` on a Vec value gets `&frames`
        (define pt0 (and (pair? pts) (car pts)))
        (define rt (node-typ (car args)))
        ;; (vstd's functions are not in the crate's VIR: without the parameter's type,
        ;; a reference read from a place that is not one is the auto-ref)
        (define pl (read-place-typ (car args)))
        (define recv (if (or (and pt0 rt (ref-typ? pt0) (not (ref-typ? rt)) (not (typ-param? rt)))
                             (and (or (not pt0) (ref-typ? pt0)) rt (ref-typ? rt) pl (not (ref-typ? pl)) (not (typ-param? pl))))
                         `(borrow ,(car as))
                         (car as)))
        `(call ,(string->symbol (format "~a::~a" (regexp-replace #rx"SpecImpl$" (string-join (drop-right segs 1) "::") "Spec")
                                        (last segs)))
               ,recv ,@(cdr as))]
       ;; a method of a trait with type arguments (`TreeNodeValue<L>::la_inv`): through
       ;; the trait, `<EntryOwner<C> as TreeNodeValue<L>>::la_inv(self, lv)`; as a
       ;; method call the trait's arguments are not inferred (E0284)
       [(and (method? p) (pair? as) (list? typs) (> (length typs) 1)
             (let ([segs (segments p)])
               (and (>= (length segs) 2)
                    (hash-ref (current-traits) (regexp-replace #rx"^crate::" (string-join (drop-right segs 1) "::") "ostd::") #f)))
             ;; only when a trait argument has a type parameter the self type has not
             ;; (`VmIo<DmaCoherentVmIoOwner<M>>` on `DmaCoherent<M>` is inferred)
             (let* ([names (lambda (t) (let f ([t t]) (match t [(list 'Typ 'TypParam (? string? n)) (list n)] [(? pair?) (append-map f t)] [_ '()])))]
                    [in-self (names (car typs))])
               (for/or ([n (in-list (names (cdr typs)))]) (not (member n in-self)))))
        ;; the receiver as the trait function's first parameter takes it
        (define recv (car as))
        (define pt0 (and (pair? pts) (car pts)))
        (define rt (node-typ (car args)))
        (define recv* (cond [(and pt0 rt (ref-typ? rt) (not (ref-typ? pt0)) (not (typ-param? pt0))) `(deref ,recv)]
                            [(and pt0 rt (not (ref-typ? rt)) (ref-typ? pt0)) `(borrow ,recv)]
                            [else recv]))
        `(call ,(string->symbol (call-path (ostd-path->crate p) kind typs)) ,recv* ,@(cdr as))]
       [(and (method? p) (pair? as))
        ;; `addr%returns_clause_autospec` is VIR's name for the spec meaning of `addr()`;
        ;; Verus 68d80057 (namespaced paths, design.md 4.2) writes it `returns_clause_autospec%addr`
        (define m (regexp-replace #rx"^returns_clause_autospec%|%returns_clause_autospec$" (last-seg p) ""))
        ;; the method's own type parameters that no parameter mentions are written
        ;; (`self.fill_panic_condition::<T>()`, E0282); they are its last ones
        (define free ((current-free-tparams) p))
        (define tf (and (pair? free) (list? typs) (>= (length typs) (length free))
                        (with-handlers ([no? (lambda (_) #f)])
                          (map (lambda (t) (type->text (typ t))) (take-right typs (length free))))))
        `(method ,(car as) ,(string->symbol (if tf (format "~a::<~a>" m (string-join tf ", ")) m)) ,@(cdr as))]
       [else
         (let ([s (ostd-path->crate p)])
           (if (regexp-match? #rx"impl&%" s)
               `(call ,(string->symbol (or ((current-impl-path) p typs) (fail 'impl-function))) ,@as)
               `(call ,(string->symbol (call-path s kind typs)) ,@as)))])]
    ;; a tuple `(a, b)`, a variant `core::option::Option::None` or one with
    ;; positional fields `...::Some(x)`
    ;; a struct (or variant) with named fields, `MappedItem { frame: frame, prop: prop }`:
    ;; (record "PATH" ("field" E) ...), the path and the names as strings (not variables)
    [(list '> 'Ctor (list 'Dt 'Path p) (? string? variant) (? pair? binders) _ ...)
     #:when (for/and ([b (in-list binders)])
              (match (unwrap b) [(list '-> (? symbol? n) _) (not (string->number (symbol->string n)))] [_ #f]))
     `(record ,(if (equal? variant (last-seg p))
                   (format "~a" (ostd-path->crate p))
                   (format "~a::~a" (ostd-path->crate p) variant))
              ,@(for/list ([b (in-list binders)])
                  (match (unwrap b) [(list '-> n e) (list (symbol->string n) (x e))])))]
    [(list '> 'Ctor dt (? string? variant) binders _ ...)
     ;; a local of type Tracked<T> as a field (a trait declaration's
     ;; `(paddr, level, prop, perm)` with `perm: Tracked<T>`, renamed to the
     ;; impl's parameter, which the table and the client bind unwrapped:
     ;; `Tracked(perm): Tracked<T>`) is put back in its wrapper; elsewhere
     ;; (`ptr_perm_match(ptr, perm@)`) VIR already passes the contents
     (define (field-expr e)
       (match* ((unwrap e) (read-place-typ e))
         [((list '> 'ReadPlace (app unwrap (list 'Place 'Local _)) _ ...)
           (list 'Typ 'Decorate (list 'TypDecoration 'Tracked) _ _))
          (define v (x e))
          (if (memq v (current-tracked-typed)) v `(call Tracked ,v))]
         [(_ _) (x e)]))
     (define fields0
       (for/list ([b (in-list binders)])
         (match (unwrap b)
           [(list '-> (? number?) e) (cons e (field-expr e))]
           [(list '-> (? symbol? n) e) #:when (string->number (symbol->string n)) (cons e (field-expr e))]
           [_ (fail 'Ctor)])))
     ;; a tuple whose field is Tracked<T> built from a value of type T (a proof
     ;; function's tracked parameter, unwrapped: `(paddr, level, prop, permission)`
     ;; for `(Paddr, PagingLevel, PageProperty, Tracked<Option<Perm>>)`): wrapped
     (define ftyps (match (node-typ e) [(list 'Typ 'Datatype (list 'Dt 'Tuple _) ts _ ...) ts] [_ #f]))
     (define (tracked-typ? t) (match t [(list 'Typ 'Decorate (list 'TypDecoration 'Tracked) _ _) #t] [_ #f]))
     ;; the type of what is read, through a mode coercion (`permission` coerced to the field's mode)
     (define (inner-typ e)
       (match (unwrap e)
         [(list '> 'Unary (list 'UnaryOp 'CoerceMode _ ...) a) (inner-typ a)]
         [_ (node-typ e)]))
     (define fields
       (for/list ([fe (in-list fields0)] [i (in-naturals)])
         (define ft (or (and ftyps (< i (length ftyps)) (list-ref ftyps i)) (node-typ (car fe))))
         (if (and ft (tracked-typ? ft) (inner-typ (car fe)) (not (tracked-typ? (inner-typ (car fe))))
                  (not (match (cdr fe) [`(call Tracked ,_) #t] [_ #f])))
             `(call Tracked ,(cdr fe))
             (cdr fe))))
     (match dt
       [(list 'Dt 'Tuple _) `(call || ,@fields)]
       [(list 'Dt 'Path p)
        ;; a tuple struct's one variant has the struct's name: `PageTableOwner(x)`,
        ;; not `PageTableOwner::PageTableOwner(x)` (E0599)
        (define v (string->symbol (if (equal? variant (last-seg p))
                                      (format "~a" (ostd-path->crate p))
                                      (format "~a::~a" (ostd-path->crate p) variant))))
        (if (null? fields) `(const ,v) `(call ,v ,@fields))]
       [_ (fail 'Ctor)])]
    [u (fail (if (pair? u) (if (eq? (car u) '>) (cadr u) (car u)) 'expr))]))

;; let-subst : E X E -> E, x replaced by v (not under a quantifier binding x)
(define (let-subst e x v)
  (let loop ([e e])
    (match e
      [(== x) v]
      [`(,(and q (or 'forall 'exists)) ,bs ,body) (if (assq x bs) e `(,q ,bs ,(loop body)))]
      [`(src ,_) e]
      [`(const ,_) e]
      ;; names of methods, fields, functions are not variables
      [`(method ,a ,m ,args ...) `(method ,(loop a) ,m ,@(map loop args))]
      [`(,(and k (or 'field 'arrow)) ,a ,f) `(,k ,(loop a) ,f)]
      [`(call ,f ,args ...) `(call ,f ,@(map loop args))]
      [`(,op ,args ...) `(,op ,@(map loop args))]
      [_ e])))

;; current-impl-path : (callee-path VIR-typs -> string or #f), how a call of an
;; associated function of an impl (a path with impl&%) is written, through
;; its self type: `Cursor::<C, G>::cursor_new_input_valid`.
(define current-impl-path (make-parameter (lambda (p typs) #f)))

;; A datatype is written by its last segment, which the client's imports
;; resolve (`use super::*`, the uses rustc suggests: ostd's own paths go
;; through private modules).  Where several datatypes have that name
;; (vstd's `simple_pptr::PointsTo`, `cell::PointsTo`, `pcell_maybe_uninit::
;; PointsTo`, vstd_extra's `array_ptr::PointsTo`) the one meant is not the one
;; found: one outside ostd and the standard library is then written with its
;; module (`pcell_maybe_uninit::PointsTo<u16>`) and the module is imported.
;; current-ambiguous-types : name -> #t, the names of more than one datatype
(define current-ambiguous-types (make-parameter (hash)))
;; current-type-uses : box of the `use` lines the entry's types need
(define current-type-uses (make-parameter (box '())))
(define (datatype-name p)
  (define segs (segments p))
  (define n (last segs))
  (cond
    [(and (hash-ref (current-ambiguous-types) n #f) (>= (length segs) 3)
          (not (member (car segs) '("ostd" "core" "alloc" "std"))))
     (set-box! (current-type-uses)
               (remove-duplicates (cons (format "use ~a;" (string-join (drop-right segs 1) "::")) (unbox (current-type-uses)))))
     (string->symbol (format "~a::~a" (list-ref segs (- (length segs) 2)) n))]
    [else (string->symbol n)]))

;; A trait method is called as a method, unless the self type has an inherent
;; method of the same name, which a method call would resolve to (`Frame::
;; into_raw` for `<Frame<M> as NonNullPtr>::into_raw`): then through the trait.
;; current-shadowed? : function -> boolean
(define current-shadowed? (make-parameter (lambda (f) #f)))
;; current-free-tparams : callee path -> the callee's trailing type parameters
;; that none of its parameters' types mentions (a method's turbofish), or '()
(define current-free-tparams (make-parameter (lambda (p) '())))
;; current-traits : VIR path of a trait -> #t (call-path)
(define current-traits (make-parameter (hash)))
;; current-datatype-arity : VIR path of a datatype -> its number of type parameters (call-path)
(define current-datatype-arity (make-parameter (hash)))
;; the parameters (of a proof function) whose type in the table is Tracked<T>
;; itself (see `entry`): they are not unwrapped, so not put back in a wrapper
(define current-tracked-typed (make-parameter (quote ())))

;; How a call that is not a method is written.  The type arguments are spelled
;; out, since a spec function's type parameter often appears in no argument
;; (`size_of_as_usize::<T>()`); a trait function is called on its Self type,
;; the first type argument (`<C as PagingConstsTrait>::NR_LEVELS_spec()`).
;; Type arguments that cannot be written are left to inference.
(define (call-path s kind typs)
  (define ts (with-handlers ([no? (lambda (_) #f)]) (map (lambda (t) (type->text (typ t))) (if (list? typs) typs '()))))
  (define segs (segments s))
  ;; a call through a trait, or a trait's function named by its path
  ;; (`Self::obeys_vmio_read_requires()` in a trait's requires): the segment
  ;; before the name is a trait, written in CamelCase, where a function's is a module
  ;; whether the parent is a trait: by VIR's list of traits (`vstd::set::Set::empty`
  ;; is a struct's function, `Set::<T>::empty()`, not `<T as Set>::empty()`);
  ;; without the list, by CamelCase
  (define parent (and (>= (length segs) 2) (string-join (drop-right segs 1) "::")))
  (define (norm p) (regexp-replace #rx"^crate::" p "ostd::"))
  (define trait? (or (match kind [(list 'CallTargetKind (or 'Dynamic 'DynamicResolved) _ ...) #t] [_ #f])
                     (and parent
                          (if (hash-empty? (current-traits))
                              (regexp-match? #px"^[A-Z]" (last (drop-right segs 1)))
                              (hash-ref (current-traits) (norm parent) #f)))))
  (cond
    [(not ts) s]
    ;; the rest of the type arguments are taken to be the trait's (`VmIo<P>`)
    [(and trait? (pair? ts))
     (format "<~a as ~a~a>::~a" (car ts) (trait-ref (string-join (drop-right segs 1) "::"))
             (if (null? (cdr ts)) "" (format "<~a>" (string-join (cdr ts) ", ")))
             (last segs))]
    [(null? ts) s]
    ;; a datatype's function (`vstd::set::Set::empty`): its first type arguments
    ;; are the datatype's (`Set::<TreePath<512>>::empty()`), the rest the function's
    [(and parent (hash-ref (current-datatype-arity) (norm parent) #f))
     => (lambda (k)
          (define-values (dt own) (split-at ts (min k (length ts))))
          (format "~a~a::~a~a" parent (if (null? dt) "" (format "::<~a>" (string-join dt ", ")))
                  (last segs) (if (null? own) "" (format "::<~a>" (string-join own ", ")))))]
    [else (format "~a::<~a>" s (string-join ts ", "))]))

;; The operands of an arithmetic operation or comparison, translated by x.
;; VIR leaves out the widening of a bounded integer to int (`size_of::<T>() as
;; int`); when one operand is int or nat and the other bounded, the cast is put back.
(define (widen x a b)
  (define (kind e) (match (node-typ e)
                     [(list 'Typ 'Int (or 'Int 'Nat (list 'IntRange (or 'Int 'Nat)))) 'unbounded]
                     [(list 'Typ 'Int _) 'bounded]
                     [_ #f]))
  (define (cast e) `(as ,(x e) (const int)))
  (match* ((kind a) (kind b))
    [('unbounded 'bounded) (list (x a) (cast b))]
    [('bounded 'unbounded) (list (cast a) (x b))]
    [(_ _) (list (x a) (x b))]))

(define (binop op)
  (match op ['Eq '==] ['Ne '!=] ['And 'and] ['Or 'or] ['Implies 'implies] [_ (fail op)]))
(define (arith op)
  (match op ['Add '+] ['Sub '-] ['Mul '*] ['EuclideanMod '%] ['EuclideanDiv '/] [_ (fail op)]))
(define (ineq op)
  (match op ['Le '<=] ['Lt '<] ['Ge '>=] ['Gt '>] [_ (fail op)]))

(define (place p method? ptypes)
  (match (unwrap p)
    [(list 'Place 'Local v) (string->symbol (or (var-name v) (fail 'local)))]
    [(list 'Place 'DerefMut q) `(deref ,(place q method? ptypes))]
    ;; a temporary that borrows a place which is not a reference is the
    ;; source's explicit `&p` (`untracked_range_slots_in_regions(&pa_range, ..)`
    ;; with `pa_range: Range`): kept, or the callee would get the value (E0308)
    [(list 'Place 'Temporary e)
     (match (unwrap e)
       [(list '> 'ReadPlace pl kind _ ...)
        #:when (and (pair? kind) (member '(ReadKind ImmutBor) kind)
                    (node-typ pl) (not (ref-typ? (node-typ pl))) (not (typ-param? (node-typ pl))))
        `(borrow ,(expr e method? ptypes))]
       [_ (expr e method? ptypes)])]
    [(list 'Place 'Field fo q)
     (when (eq? (field fo 'get_variant) 'true) (fail 'variant-field))
     (define f (field fo 'field))
     `(field ,(place q method? ptypes) ,(string->symbol (format "~a" (or f (fail 'field)))))]
    [u (fail (if (pair? u) (cadr u) 'place))]))

;; The type annotation of an expression node (@@ SPAN NODE TYPE), or #f.
(define (node-typ e) (and (pair? e) (eq? (car e) '@@) (= (length e) 4) (cadddr e)))

;; The type of the place a ReadPlace node reads, or #f.
(define (read-place-typ e)
  (match (unwrap e)
    [(list '> 'ReadPlace pl _ ...) (node-typ pl)]
    [_ #f]))

;; A shared reference, under Tracked/Ghost decorations.
(define (ref-typ? t)
  (match t
    [(list 'Typ 'Decorate (list 'TypDecoration 'Ref) _ _) #t]
    [(list 'Typ 'Decorate (list 'TypDecoration (or 'Tracked 'Ghost)) _ inner) (ref-typ? inner)]
    [_ #f]))

(define (typ-param? t)
  (match t
    [(list 'Typ 'TypParam _) #t]
    [(list 'Typ 'Decorate _ _ inner) (typ-param? inner)]
    [_ #f]))

;; ================================================================ alignment

;; align-info : VIR clause method? ptypes -> ((SPAN INFO ...) ...)
;; What VIR says of the nodes of a clause, by their spans, for the source's
;; tree of the same clause (docs/representation.md 10, source-spec.rkt's
;; source->aligned): meaning from VIR, structure and spelling from the source.
;;   (fn NAME)               a call of a function: its path as a client writes it
;;   (ctor NAME)             a constructor (a variant, a tuple struct)
;;   (const NAME)            a constant
;;   (binders ((x T) ..))    a quantifier's bound variables, with their types
;;   (wrapped Tracked|Ghost) a read of a local whose type is Tracked<T> (Ghost<T>)
;; Called where entry is (the current-* parameters say how paths are written).
(define (align-info e method? ptypes)
  (define h (make-hash))
  (define (add! sp i)
    (define s (vir-clause-span sp))
    (when s (hash-update! h s (lambda (l) (if (member i l) l (append l (list i)))) '())))
  (let walk ([e e])
    (match e
      [(list (or '@ '@@) sp node more ...)
       (for ([i (in-list (with-handlers ([no? (lambda (_) '())]) (node-info e (unwrap e) (lambda (x) (expr x method? ptypes)))))]) (add! sp i))
       (walk node)]
      [(? pair?) (for-each walk e)]
      [_ (void)]))
  (for/list ([(k v) (in-hash h)]) (cons k v)))

(define (node-info e u x)
  (define (wrapped t)
    (match t
      [(list 'Typ 'Decorate (list 'TypDecoration (and d (or 'Tracked 'Ghost))) _ _) (list `(wrapped ,d))]
      [_ '()]))
  (match u
    [(list '> 'Call ':target (list 'CallTarget 'Fun kind (list 'Fun ':path p) typs _ ...) ':args _ ...)
     (cond
       [(regexp-match? #rx"^arrow_" (last-seg p)) '()]
       [else
        (define s (regexp-replace #rx"(::)returns_clause_autospec%|%returns_clause_autospec$" (ostd-path->crate p) "\\1"))
        (append
         (list `(fn ,(string->symbol (if (regexp-match? #rx"impl&%" s)
                                         (or ((current-impl-path) p typs) (fail 'impl-function))
                                         (call-path s kind typs)))))
         ;; a method of a trait with type arguments the self type does not
         ;; determine (`TreeNodeValue<L>::la_inv` on `EntryOwner<C>`): written as a
         ;; method call it is ambiguous in a client (E0284), so through the trait,
         ;; as expr writes it: (trait-fn NAME RECEIVER-WRAPPER)
         (match (with-handlers ([no? (lambda (_) #f)]) (x e))
           [`(call ,(? symbol? n) ,recv ,_ ...)
            #:when (regexp-match? #px"^<.* as [^ ]*<.*>>::[^:<>]*$" (symbol->string n))
            (list `(trait-fn ,n ,(match recv [`(deref ,_) 'deref] [`(borrow ,_) 'borrow] [_ #f])))]
           [_ '()]))])]
    [(list '> 'Ctor (list 'Dt 'Path p) (? string? variant) _ ...)
     (list `(ctor ,(string->symbol (if (equal? variant (last-seg p))
                                       (format "~a" (ostd-path->crate p))
                                       (format "~a::~a" (ostd-path->crate p) variant)))))]
    [(list '> 'ConstVar (list 'Fun ':path p) _ ...) (list `(const ,(string->symbol (ostd-path->crate p))))]
    ;; an integer type's bound (`usize::MAX`): a constant to the source, not to VIR
    [(list '> 'UnaryOpr (list 'UnaryOpr 'IntegerTypeBound _ ...) _ ...)
     (match (x e) [`(const ,n) (list `(const ,n))] [_ '()])]
    [(list '> 'Quant (list (or 'Forall 'Exists)) binders _)
     (list `(binders ,(for/list ([b (in-list binders)])
                        (match (unwrap b)
                          [(list '-> v t) (list (string->symbol (or (var-name v) (fail 'Quant))) (typ t))]
                          [_ (fail 'Quant)]))))]
    [(list '> 'ReadPlace (app unwrap (list 'Place 'Local _)) _ ...) (wrapped (or (read-place-typ e) (node-typ e)))]
    [(list 'Place 'Local _) (wrapped (node-typ e))]
    [_ '()]))

;; ================================================================ functions

;; entry : function twins items -> fn form, or raises no
(define (entry f plain-of item-of method? ptypes decl-requires)
  (define path (plain (fn-path f)))
  (define twin? (string-contains? (fn-path f) vprefix))
  (define plain-f (and twin? (hash-ref plain-of path #f)))
  (define plain-names (if plain-f (map (lambda (p) (var-name (field p 'name))) (params plain-f)) #f))
  (define mode (field f 'mode))
  (define ps (params f))
  (define self? (and (pair? ps) (equal? (var-name (field (car ps) 'name)) "self")))
  (define (pmode p)
    (define vm (field p 'mode))
    (define d (decoration (field p 'typ)))
    (cond [(eq? vm 'Spec) 'spec]
          [(eq? vm 'Proof) 'tracked]
          [(eq? d 'Tracked) 'tracked]
          [(eq? d 'Ghost) 'spec]
          [else 'exec]))
  (define described
    (for/list ([p (in-list ps)])
      (list (string->symbol (or (var-name (field p 'name)) (fail 'param)))
            (pmode p)
            ;; a spec parameter of a proof function declared `perm: Tracked<T>`
            ;; is a value of type Tracked<T>: the decoration is its type, not its mode
            (match (and (not (eq? mode 'Exec)) (eq? (field p 'mode) 'Spec) (field p 'typ))
              [(list 'Typ 'Decorate (list 'TypDecoration (and d (or 'Tracked 'Ghost))) _ inner) `(,d ,(typ inner))]
              [_ (typ (field p 'typ))])
            ;; with: a parameter of `#[verus_spec(with ..)]`
            (and plain-names (not (member (var-name (field p 'name)) plain-names))))))
  (define-values (main ghost)
    (if (eq? mode 'Exec)
        (partition (lambda (d) (and (eq? (cadr d) 'exec) (not (cadddr d)))) described)
        (values described '())))
  (define style (cond [(null? ghost) 'with] [(andmap cadddr ghost) 'with]
                      [(ormap cadddr ghost) (fail 'mixed-ghost)] [else 'arg]))
  ;; ghost parameters written as arguments must come after the exec ones
  (when (and (eq? style 'arg) (not (equal? (take described (length main)) main))) (fail 'ghost-order))
  (when (eq? mode 'Exec)
    (for ([d (in-list main)]) (unless (eq? (cadr d) 'exec) (fail 'exec-param-mode))))
  (define-values (ret gret)
    (let* ([r (field f 'outer_ret)] [r (and r (unwrap r))])
      (cond
        [(not r) (values #f #f)]
        [(and twin? (equal? (var-name (field r 'name)) "_VERUS_ret_ident"))
         (match (field r 'typ)
           [(list 'Typ 'Datatype (list 'Dt 'Tuple 2) (list t0 t1) _ ...)
            (values (let ([t (typ t0)]) (and (not (unit? t)) t)) (typ t1))]
           [_ (fail 'return-tuple)])]
        [else (let ([t (typ (field r 'typ))]) (values (and (not (unit? t)) t) #f))])))
  (define name (string->symbol (string-replace path "ostd::" "" #:all? #f)))
  ;; a proof function whose result is a spec value (`-> (res: Seq<..>)`, not
  ;; `-> (tracked res: ..)`): bound as ghost (client.rkt, render.rkt)
  (define ret-ghost?
    (and (eq? mode 'Proof) ret
         (let ([r (field f 'outer_ret)]) (and r (eq? (field (unwrap r) 'mode) 'Spec)))))
  (define trait (impl-trait f))
  (define any-trait (impl-trait f #t))
  (define call
    (cond
      ;; a spec method of a vstd trait: by the trait's path, since vstd puts
      ;; several traits with the same methods in scope (IteratorSpec and
      ;; IteratorSpecImpl), or none; XSpecImpl is used through XSpec.  The
      ;; trait's type arguments (`PartialEqSpec<Rhs>`) are inferred.
      [(and self? (eq? mode 'Spec) any-trait (string-prefix? any-trait "vstd::"))
       `(function ,(string-append (regexp-replace #rx"SpecImpl$" any-trait "Spec") "::" (last-seg path)))]
      [(and self? trait ((current-shadowed?) f) (let ([it (item-of f)]) (and it (item-self it))))
       (define tps (map (lambda (tp) (string-replace tp "Self%" "Self")) (or (field f 'typ_params) '())))
       `(function ,(unbrace tps (format "<~a as ~a>::~a" (self-type->text (item-self (item-of f))) (trait-ref trait) (last-seg path))))]
      ;; a method of a trait whose type arguments name a type parameter the self
      ;; type does not (`impl<L> TreeNodeValue<L> for EntryOwner<C>`): a method
      ;; call cannot infer L (E0284), so through the trait, as rustc suggests
      [(and self? (trait-with-args f) (let ([it (item-of f)]) (and it (item-self it)))
            (let ([tw (trait-with-args f)] [st (self-type->text (item-self (item-of f)))])
              (for/or ([m (in-list (regexp-match* #px"\\{([A-Za-z0-9_]+)\\}" tw #:match-select cadr))])
                (not (regexp-match? (pregexp (format "\\b~a\\b" m)) st)))))
       (define tps (map (lambda (tp) (string-replace tp "Self%" "Self")) (or (field f 'typ_params) '())))
       `(function ,(unbrace tps (format "<~a as ~a>::~a" (self-type->text (item-self (item-of f))) (trait-with-args f) (last-seg path))))]
      [self? `(method ,(string->symbol (last-seg path)))]
      [(regexp-match? #rx"impl&%" path)
       (define it (item-of f))
       (unless (and it (item-self it)) (fail 'self-type))
       ;; a trait's associated function on its Self type, so that an inherent
       ;; function of the same name (`Box::from_raw`) does not shadow it
       ;; {X} is for type parameters; a concrete argument (`VmWriter<Infallible>`) is written as it is
       (define tps (map (lambda (tp) (string-replace tp "Self%" "Self")) (or (field f 'typ_params) '())))
       ;; a trait with type arguments too (`<EntryOwner<{C}> as TreeNodeValue<{L}>>::f`):
       ;; on the self type, L would be taken as the function's own (E0107)
       (define tr (or (and trait (trait-ref trait)) (trait-with-args f)))
       `(function ,(unbrace tps
                    (if tr
                        (format "<~a as ~a>::~a" (self-type->text (item-self it)) tr (last-seg path))
                        (string-append (self-type->path (item-self it)) "::" (last-seg path)))))]
      [else `(function ,(string-append "super::" (last-seg path)))]))
  ;; skipped: why each clause left out could not be translated
  ;; req-spans: for each clause kept, VIR's span of it (its own clauses), or #f
  ;; (a trait declaration's, whose parameters are renamed): where the source's
  ;; tree may stand in for it (source-requires)
  (define own-count (length (or (field f 'require) '())))
  ;; req-align: for each clause kept, what VIR says of its nodes (align-info)
  (define-values (reqs req-spans req-align skipped)
    (for/fold ([ok '()] [spans '()] [aligns '()] [skipped '()]
               #:result (values (reverse ok) (reverse spans) (reverse aligns) (reverse skipped)))
              ([r (in-list (append (or (field f 'require) '()) (decl-requires f)))] [i (in-naturals)])
      (with-handlers ([no? (lambda (e) (values ok spans aligns (cons (no-what e) skipped)))])
        (values (cons (parameterize ([current-tracked-typed
                                      (for/list ([d (in-list described)]
                                                 #:when (match (caddr d) [(list 'Tracked _) #t] [_ #f]))
                                        (car d))])
                        (expr r method? ptypes))
                      ok)
                (cons (and (pair? r) (memq (car r) '(@ @@))
                           (let ([sp (vir-clause-span (cadr r))])
                             (and sp (if (< i own-count) sp (list 'decl sp)))))
                      spans)
                (cons (align-info r method? ptypes) aligns)
                skipped))))
  ;; A lemma (a proof function of spec parameters only, with no result): its
  ;; ensures too, and the (lemma) mark, so that retry can insert it and the
  ;; probe checks the declared ensures (docs/representation.md 4.3); a clause
  ;; that cannot be translated is left out (fewer facts, never wrong ones).
  (define lemma?
    (and (eq? mode 'Proof) (null? ghost) (not ret) (not gret)
         (andmap (lambda (d) (eq? (cadr d) 'spec)) main)))
  (define-values (enss ens-spans ens-align)
    (if lemma?
        (for/fold ([ok '()] [spans '()] [aligns '()] #:result (values (reverse ok) (reverse spans) (reverse aligns)))
                  ;; VIR's ensure: (tuple ENSURES ..), the ordinary ones first
                  ([r (in-list (match (field f 'ensure) [`(tuple ,(? list? a) ,_ ...) a] [(? list? a) a] [_ '()]))])
          (with-handlers ([no? (lambda (_) (values ok spans aligns))])
            (values (cons (expr r method? ptypes) ok)
                    (cons (and (pair? r) (memq (car r) '(@ @@)) (vir-clause-span (cadr r))) spans)
                    (cons (align-info r method? ptypes) aligns))))
        (values '() '() '())))
  (define gens (generics f))
  ;; the `&mut` parameters whose borrow cannot reach the result (item-index:
  ;; `regions: Tracked<&mut MetaRegionOwners>` of `cursor`, with its own elided
  ;; lifetime, beside `Cursor<'a, G>`); the checker otherwise takes a result
  ;; with a lifetime to borrow from every reference argument (client.rkt)
  (define no-flow
    (let ([it (item-of f)] [names (map car described)])
      (if it
          (for/list ([m (in-list (item-muts it))]
                     #:when (and (not (cadr m)) (memq (string->symbol (car m)) names)))
            (string->symbol (car m)))
          '())))
  `(fn ,name
       (vir-path ,(fn-path f))
       ,@(if (eq? mode 'Exec) '() `((mode ,(if (eq? mode 'Proof) 'proof 'spec))))
       ,call
       ,@(if (attr f 'is_unsafe) '((unsafe)) '())
       (generics ,@(if (unbox (current-lifetime-used)) (list (list lifetime)) '()) ,@gens)
       (params ,@(map (lambda (d) (take d 3)) main))
       ,@(if (null? ghost) '() `((ghost ,style ,@(map (lambda (d) (take d 3)) ghost))))
       ,@(if ret `((ret ,ret)) '())
       ,@(if ret-ghost? '((ret-ghost)) '())
       ,@(if gret `((ghost-ret tracked ,gret)) '())
       ,@(if (null? no-flow) '() `((no-flow ,@no-flow)))
       ,@(if (null? reqs) '() `((requires ,@reqs)))
       ,@(if (null? skipped) '() `((skipped-requires ,(length skipped) ,@skipped)))
       ,@(if lemma? '((lemma)) '())
       ,@(if (null? enss) '() `((ensures ,@enss)))
       ;; taken out again by source-requires
       (req-spans ,@req-spans)
       (req-align ,@req-align)
       ,@(if (null? enss) '() `((ens-spans ,@ens-spans) (ens-align ,@ens-align)))))

;; The trait of a method in a trait impl, when the trait has no type
;; parameters of its own (or any? is given), or #f.
(define (impl-trait f [any? #f])
  (define k (field f 'kind))
  (and (match k [(list 'FunctionKind 'TraitMethodImpl _ ...) #t] [_ #f])
       (let ([targs (field k 'trait_typ_args)])
         (and (list? targs) (or any? (= (length targs) 1))))
       (format "~a" (field k 'trait_path))))

;; The trait of a method in a trait impl, with its type arguments
;; (`vstd_extra::ghost_tree::TreeNodeValue<{L}>`, {L} for a type parameter), or #f.
(define (trait-with-args f)
  (define k (field f 'kind))
  (and (match k [(list 'FunctionKind 'TraitMethodImpl _ ...) #t] [_ #f])
       (let ([targs (field k 'trait_typ_args)])
         (and (list? targs) (> (length targs) 1)
              (with-handlers ([no? (lambda (_) #f)])
                (format "~a<~a>" (trait-ref (field k 'trait_path))
                        (string-join (for/list ([a (in-list (cdr targs))])
                                       (match a
                                         [(list 'Typ 'TypParam (? string? n)) (format "{~a}" (string-replace n "Self%" "Self"))]
                                         ;; type parameters inside (`From<UniqueFrame<{M}>>`) braced too, to be instantiated
                                         [_ (for/fold ([t (type->text (typ a))])
                                                      ([n (in-list (or (field f 'typ_params) '()))])
                                              (regexp-replace* (pregexp (format "\\b~a\\b" (regexp-quote (string-replace n "Self%" "Self"))))
                                                               t (format "{~a}" (string-replace n "Self%" "Self"))))]))
                                     ", ")))))))

;; "Frame<M>" -> "Frame<{M}>", as a type in a path
(define (self-type->text s)
  (define p (self-type->path s))
  (string-replace p "::<" "<" #:all? #f))

;; {X} is for the type parameters tps; any other braced name is written as it is
(define (unbrace tps s)
  (regexp-replace* #px"\\{([A-Za-z0-9_]+)\\}" s (lambda (all x) (if (member x tps) all x))))

;; "Frame<M>" -> "Frame::<{M}>"; "FrameAllocOptions" -> "{FrameAllocOptions}" (see unbrace)
(define (self-type->path s)
  (match (regexp-match #px"^([A-Za-z_][A-Za-z0-9_]*)(<(.*)>)?$" (string-trim s))
    ;; braced too: the self type may be a type parameter (`impl<C> Trait for C`)
    [(list _ n #f _) (format "{~a}" n)]
    [(list _ n _ args)
     ;; lifetimes are left to inference
     (define as (filter (lambda (a) (not (string-prefix? a "'"))) (map string-trim (string-split args ","))))
     (unless (andmap (lambda (a) (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" a)) as) (fail 'self-type-args))
     (if (null? as) n (format "~a::<~a>" n (string-join (map (lambda (a) (format "{~a}" a)) as) ", ")))]
    [_ (fail 'self-type-form)]))

;; ================================================================ item-index

;; muts: (("x" FLOWS?) ...), the `&mut` parameters and whether the borrow can
;; flow into the return value (item-index)
(struct item (file name start end self muts) #:transparent)

(define (load-items exe root files)
  (define out
    (parameterize ([current-directory root])
      (with-output-to-string (lambda () (apply system* exe files)))))
  (for/list ([x (in-port read (open-input-string out))])
    (define (g k) (cadr (assq k (cdr x))))
    (define m (assq 'muts (cdr x)))
    (item (g 'file) (g 'name) (g 'start) (g 'end) (g 'self) (if m (cdr m) '()))))

;; ================================================================ the source (item-index --full)

;; What the source says of the entries (docs/representation.md, step 2: added,
;; not yet used): `item-index --full` on the files of the chosen functions,
;; matched to VIR by span.
;; load-full : exe root files -> (form ...), the fn, const, datatype, drop-impl
;; records, every node of their trees (@ "SPAN" NODE) (--full-spans; strip-spans
;; gives --full's)
(define (load-full exe root files)
  (define out
    (parameterize ([current-directory root] [current-error-port (open-output-nowhere)])
      (with-output-to-string (lambda () (apply system* exe "--full-spans" files)))))
  (define forms (for/list ([x (in-port read (open-input-string out))]) x))
  ;; an item-index older than --full-spans ignores the flag and prints its plain
  ;; (item ..) records: every clause then silently comes from VIR (2026-11-16:
  ;; requires-from-source 0 with env.local.rktd's stale build).  Refused.
  (when (or (and (pair? files) (null? forms))
            (for/or ([x (in-list forms)]) (and (pair? x) (eq? (car x) 'item))))
    (error 'extract "~a does not support --full-spans (an old build?): rebuild tools/item-index" exe))
  forms)

(define (rec-ref r k [default #f]) (cond [(assq k (cdr r)) => cdr] [else default]))
(define (rec-1 r k) (let ([v (rec-ref r k)]) (and (pair? v) (car v))))

;; "FILE:L1:C1: L2:C2" -> (values FILE L1 L2)
(define (span-lines s)
  (match (regexp-match #px"^(.*):([0-9]+):[0-9]+: ([0-9]+):[0-9]+" s)
    [(list _ f a b) (values f (string->number a) (string->number b))]
    [_ (values #f #f #f)]))

;; A clause span of VIR, with its file normalised and without the hygiene mark,
;; as item-index writes spans.
(define (vir-clause-span s)
  (match (and (string? s) (regexp-match #px"^(.*):([0-9]+:[0-9]+: [0-9]+:[0-9]+) \\(#[0-9]+\\)$" s))
    [(list _ f rest) (format "~a:~a" (car (span-file+line (format "~a:1:1: 1:1 (#0)" f))) rest)]
    [_ #f]))

;; The readable name of a function (docs/representation.md 4.1): the module, then
;; `<Self as Trait>::name`, `Self::name`, or `name`.
(define (source-key module r)
  (define self (rec-1 r 'self))
  (define tr (rec-1 r 'trait))
  (define in-trait (rec-1 r 'in-trait))
  (define name (rec-1 r 'name))
  (define local
    (cond [(and self tr) (format "<~a as ~a>::~a" self tr name)]
          [self (format "~a::~a" self name)]
          [in-trait (format "~a::~a" in-trait name)]
          [else name]))
  (if (equal? module "") local (format "~a::~a" module local)))

;; current-vir-reasons : why -> count, for the clauses kept from VIR
(define current-vir-reasons (make-parameter (make-hash)))

;; the table's variables of an entry with their types: ((NAME . TYPE) ..)
(define (entry-var-types e)
  (for/list ([p (in-list (append (form-ref e 'params '()) (cddr (or (assq 'ghost (cddr e)) '(ghost with)))))]
             #:when (and (pair? p) (pair? (cdr p)) (pair? (cddr p))))
    (cons (car p) (caddr p))))

;; source-requires : entry record-or-#f stats-box decl-rename clause-trees -> entry
;; Each requires clause (req-spans) that the source has with the same span is
;; taken from the source's tree, aligned with VIR's by span (source-spec.rkt's
;; source->aligned, with the entry's req-align); the others stay VIR's.
;; clause-trees: span -> the source's spanned tree, every function's requires
;; and recommends (a spec function's recommends are VIR's requires).  A trait
;; declaration's clause (decl SPAN) is the declaration's tree, its parameters
;; renamed to the impl's (decl-rename: ((DECL-NAME . IMPL-SYMBOL) ..)), as
;; VIR's decl-requires does.  stats: (from-source . from-vir).
(define (source-requires e r stats decl-rename clause-trees)
  (define spans (form-ref e 'req-spans '()))
  (define aligns (form-ref e 'req-align '()))
  (define reqs (form-ref e 'requires '()))
  (define vars (map car (entry-var-types e)))
  (define types (entry-var-types e))
  (define dvars (map (lambda (p) (string->symbol (car p))) decl-rename))
  (define same? (and (= (length spans) (length reqs)) (= (length aligns) (length reqs))))
  (define new-reqs
    (for/list ([q (in-list reqs)] [s (in-list (if same? spans (map (lambda (_) #f) reqs)))]
               [info (in-list (if same? aligns (map (lambda (_) '()) reqs)))])
      (define decl? (and (pair? s) (eq? (car s) 'decl)))
      (define tree (cond [decl? (hash-ref clause-trees (cadr s) #f)]
                         [(and r s) (hash-ref clause-trees s #f)]
                         [else #f]))
      (define t (and tree (if decl?
                              (and (pair? decl-rename) (source->aligned tree info dvars decl-rename #:types types))
                              (source->aligned tree info vars #:types types))))
      (unless t
        (define why (cond [decl? (if tree 'decl-tree 'decl-no-clause)]
                          [(not r) 'no-source]
                          [(not s) 'not-own]
                          [(not tree) 'no-clause]
                          [else (match (unbox (current-source-failure)) [`(name ,_) 'name] [`(form ,h) h] [_ '?])]))
        (hash-update! (current-vir-reasons) why add1 0)
        (when (getenv "CS_DEBUG_VIR")
          (eprintf "VIRCLAUSE ~s ~s ~s ~s\n" why (cadr e) (unbox (current-source-failure)) s)))
      (set-box! stats (if t (cons (add1 (car (unbox stats))) (cdr (unbox stats))) (cons (car (unbox stats)) (add1 (cdr (unbox stats))))))
      (or t q)))
  ;; Source clauses VIR's translation left out (skipped-requires: match,
  ;; closures, blocks): kept as templates of their text (source->template),
  ;; after the others so that the numbering of those stays (docs/representation.md 4.2)
  ;; a declaration's clause (decl SPAN) covers SPAN: an inherited trait default
  ;; method's record is the declaration's, whose clauses are those, in its Self
  (define covered (if (= (length spans) (length reqs))
                      (map (lambda (s) (if (and (pair? s) (eq? (car s) 'decl)) (cadr s) s)) spans)
                      #f))
  (define recovered
    (if (and r covered)
        (for/list ([c (in-list (rec-ref r 'requires '()))]
                   #:when (and (pair? c) (eq? (car c) 'c) (not (member (cadr c) covered))))
          (source->template (caddr c) vars))
        '()))
  (set-box! stats (cons (+ (car (unbox stats)) (length recovered)) (cdr (unbox stats))))
  (define e* (if (and (pair? recovered) (not (assq 'requires (filter pair? e)))) (append e '((requires))) e))
  (for*/list ([fld (in-list e*)]
              #:unless (and (pair? fld) (memq (car fld) '(req-spans req-align)))
              [out (in-value
                    (match fld
                      [`(requires ,_ ...) `(requires ,@new-reqs ,@recovered)]
                      ;; what is still left out
                      [`(skipped-requires ,n ,why ...)
                       (define left (- n (length recovered)))
                       (and (> left 0) `(skipped-requires ,left ,@why))]
                      [_ fld]))]
              #:when out)
    out))

;; source-ensures : entry ens-trees -> entry
;; A lemma's ensures as its requires (source-requires): each clause the source
;; has with the same span from the source's tree, aligned; the others VIR's.
(define (source-ensures e ens-trees)
  (define spans (form-ref e 'ens-spans '()))
  (define aligns (form-ref e 'ens-align '()))
  (define enss (form-ref e 'ensures '()))
  (define vars (map car (entry-var-types e)))
  (define same? (and (= (length spans) (length enss)) (= (length aligns) (length enss))))
  (define new
    (for/list ([q (in-list enss)] [s (in-list (if same? spans (map (lambda (_) #f) enss)))]
               [info (in-list (if same? aligns (map (lambda (_) '()) enss)))])
      (define tree (and s (hash-ref ens-trees s #f)))
      (or (and tree (source->aligned tree info vars #:types (entry-var-types e))) q)))
  (for/list ([fld (in-list e)] #:unless (and (pair? fld) (memq (car fld) '(ens-spans ens-align))))
    (if (and (pair? fld) (eq? (car fld) 'ensures)) `(ensures ,@new) fld)))

;; source-no-flow : entry record-or-#f -> entry
;; no-flow from the source's lifetimes for every reference parameter, shared
;; ones too (item-index --full's flows; docs/representation.md step 5a): a
;; result borrows only the parameters whose lifetime reaches it (`cursor(&'a
;; self, guard: &'a G, va: &Range<Vaddr>)` borrows self and guard, not va).
;; Without a record (generated functions), the entry's own (from the item
;; index: `&mut` parameters only).
(define (source-no-flow e r)
  (define flows (and r (rec-ref r 'flows #f)))
  (cond
    [(not flows) e]
    [else
     (define names (map car (append (form-ref e 'params '()) (cddr (or (assq 'ghost (cddr e)) '(ghost with))))))
     (define nf (for/list ([fl (in-list flows)]
                           #:when (and (pair? fl) (eq? (caddr fl) #f) (memq (string->symbol (car fl)) names)))
                  (string->symbol (car fl))))
     (define without (filter (lambda (fld) (not (and (pair? fld) (eq? (car fld) 'no-flow)))) e))
     (if (null? nf)
         without
         ;; where the old field was, or before requires
         (let loop ([fs without] [acc '()])
           (cond [(null? fs) (append (reverse acc) (list `(no-flow ,@nf)))]
                 [(and (pair? (car fs)) (memq (caar fs) '(requires skipped-requires req-spans)))
                  (append (reverse acc) (list `(no-flow ,@nf)) fs)]
                 [else (loop (cdr fs) (cons (car fs) acc))])))]))

;; source-static : entry record-or-#f -> entry
;; VIR erases lifetimes, `&'static` among them (docs/representation.md 5c): a
;; reference the source declares `&'static X` is written (&static X), in the
;; parameters (exec and ghost), the result and the ghost result.  Each
;; `&'static X` of the source's type text is matched to a (& X) of the table's
;; type whose X is written the same (whitespace and module paths left out).
(define (norm-type-text s)
  (regexp-replace* #px"(?:[A-Za-z_][A-Za-z0-9_]*::)+" (regexp-replace* #px"\\s+" s "") ""))
(define (static-targets text)
  (let loop ([i 0] [acc '()])
    (define m (regexp-match-positions #px"&'static\\s+" text i))
    (cond
      [(not m) (reverse acc)]
      [else
       (define start (cdar m))
       ;; the type after it, up to a delimiter at depth 0
       (define end
         (let scan ([j start] [d 0])
           (cond [(>= j (string-length text)) j]
                 [else (define c (string-ref text j))
                       (cond [(memv c '(#\< #\( #\[)) (scan (add1 j) (add1 d))]
                             [(and (memv c '(#\> #\) #\] #\,)) (= d 0)) j]
                             [(memv c '(#\> #\) #\])) (scan (add1 j) (sub1 d))]
                             [else (scan (add1 j) d)])])))
       (define ty (substring text start end))
       (loop end (if (regexp-match? #px"^mut\\s" ty) acc (cons (norm-type-text ty) acc)))])))
(define (mark-static typ targets)
  (let walk ([t typ])
    (match t
      [`(& ,x) #:when (member (norm-type-text (type->text x)) targets) `(&static ,(walk x))]
      [(? pair?) (map walk t)]
      [_ t])))
(define (source-static e r)
  (cond
    [(not r) e]
    [else
     (define (texts-of k) (for/list ([p (in-list (rec-ref r k '()))] #:when (and (pair? p) (eq? (car p) 'p))) (cons (cadr p) (caddr p))))
     (define by-name (append (texts-of 'params) (texts-of 'with-in)))
     (define ret-text (let ([v (rec-ref r 'ret '())]) (and (= (length v) 2) (string? (cadr v)) (cadr v))))
     (define out-texts (map cdr (texts-of 'with-out)))
     ;; `&'static self`: `Self` is the impl's self type (`PageTable<KernelPtConfig>`)
     (define self-text (rec-1 r 'self))
     (define (targets-of text)
       (for/list ([t (in-list (static-targets text))])
         (if (and (equal? t "Self") self-text) (norm-type-text self-text) t)))
     (define (param p)
       (define t (assoc (symbol->string (car p)) by-name))
       (define targets (if t (targets-of (cdr t)) '()))
       (if (null? targets) p (list* (car p) (cadr p) (mark-static (caddr p) targets) (cdddr p))))
     (for/list ([fld (in-list e)])
       (match fld
         [`(params ,ps ...) `(params ,@(map param ps))]
         [`(ghost ,style ,ps ...) `(ghost ,style ,@(map param ps))]
         [`(ret ,t) (let ([tg (if ret-text (static-targets ret-text) '())]) (if (null? tg) fld `(ret ,(mark-static t tg))))]
         [`(ghost-ret ,m ,t) (let ([tg (append* (map static-targets out-texts))]) (if (null? tg) fld `(ghost-ret ,m ,(mark-static t tg))))]
         [_ fld]))]))

;; source-field : VIR function, its source record or #f, its module -> the (source ..) field
(define (source-field f r module)
  (cond
    [(not r) '(source none)]
    [else
     (define vir-spans
       (for*/list ([k '(require ensure)]
                   [v (in-value (field f k))]
                   [c (in-list (cond [(and (pair? v) (eq? (car v) 'tuple)) (append* (filter list? (cdr v)))]
                                     [(list? v) v] [else '()]))]
                   [s (in-value (and (pair? c) (memq (car c) '(@ @@)) (vir-clause-span (cadr c))))]
                   #:when s)
         s))
     (define (clauses k)
       (for/list ([c (in-list (rec-ref r k '()))])
         ;; (c SPAN TEXT AST): marked (vir) when VIR has a clause with this span
         (match c
           [(list 'c span text tree) `(c ,span ,text ,tree ,@(if (member span vir-spans) '((vir)) '()))]
           [_ c])))
     `(source
       (key ,(source-key module r))
       (span ,(rec-1 r 'span))
       (sig ,(rec-1 r 'sig))
       (mode ,(rec-1 r 'mode)) (publish ,(rec-1 r 'publish)) (attrs ,@(rec-ref r 'attrs '()))
       (lifetimes ,@(rec-ref r 'lifetimes '()))
       (outer-generics ,@(rec-ref r 'outer-generics '())) (outer-lifetimes ,@(rec-ref r 'outer-lifetimes '()))
       (params ,@(rec-ref r 'params '()))
       (with-in ,@(rec-ref r 'with-in '()))
       (with-out ,@(rec-ref r 'with-out '()))
       (ret ,@(rec-ref r 'ret '()))
       (requires ,@(clauses 'requires))
       (ensures ,@(clauses 'ensures))
       ,@(let ([rs (clauses 'returns)]) (if (null? rs) '() `((returns ,@rs)))))]))

;; ================================================================ tables

;; extract-tables : fasl-or-vir module-regex vostd item-index-exe out-dir -> summary
;; Writes out-dir/apis/<module>.rktd and out-dir/targets/<module>.rktd.
(define (extract-tables vir-file module-rx vostd item-index out-dir)
  ;; the checkout's commit, which the VIR is taken to be of: each table records it
  (define commit (git-head vostd))
  (define items (load-vir vir-file))
  (define fns (for/list ([x (in-list items)] #:when (eq? (car (unwrap x)) 'Function)) (inherited-as-impl x)))
  (define by-path (for/hash ([f (in-list fns)]) (values (fn-path f) f)))
  (define plain-of (for/hash ([f (in-list fns)] #:unless (string-contains? (fn-path f) vprefix))
                     (values (fn-path f) f)))
  (define (method? p)
    (define f (or (hash-ref by-path (format "~a" p) #f)
                  (hash-ref by-path (string-append (format "~a" p)) #f)))
    (cond [f (or (attr f 'print_as_method)
                 (let ([ps (params f)]) (and (pair? ps) (equal? (var-name (field (car ps) 'name)) "self"))))]
          ;; not in this VIR: a trait method of a dependency, called on its receiver
          [else (regexp-match? #rx"::[A-Z][A-Za-z0-9_]*::[a-z_0-9]+$" (format "~a" p))]))
  ;; with the call's type arguments, a parameter whose type is one of the
  ;; callee's type parameters gets its instance (`Repr::wf(r: R, ..)` called
  ;; with R = MetaSlotStorage takes a value: `*slot` for `slot: &MetaSlotStorage`)
  (define (ptypes p [typs #f])
    (define f (hash-ref by-path (format "~a" p) #f))
    (define tps (and f (or (field f 'typ_params) '())))
    (define inst
      (if (and typs (list? typs) tps (= (length typs) (length tps)))
          (for/hash ([n (in-list tps)] [t (in-list typs)]) (values n t))
          (hash)))
    (and f (for/list ([q (in-list (params f))])
             (match (field q 'typ)
               [(list 'Typ 'TypParam (? string? n)) #:when (hash-ref inst n #f) (hash-ref inst n)]
               [t t]))))
  ;; A method of a trait impl has the requires of the trait's declaration
  ;; (Verus allows none on the impl): those, with the declaration's parameter
  ;; names replaced by the impl's and Self by the impl's self type.
  ;; the trait's declaration of a trait impl's method, or #f
  (define (decl-of f)
    (define k (field f 'kind))
    (define m (and (match k [(list 'FunctionKind 'TraitMethodImpl _ ...) #t] [_ #f])
                   (field (field k 'method) 'path)))
    (define targs (and m (field k 'trait_typ_args)))
    (and m (list? targs) (pair? targs)
         (let* ([s (segments m)]
                [twin (string-join (append (drop-right s 1) (list (string-append vprefix (last s)))) "::")])
           (if (string-contains? (fn-path f) vprefix)
               (or (hash-ref by-path twin #f) (hash-ref by-path (format "~a" m) #f))
               (hash-ref by-path (format "~a" m) #f)))))
  ;; the declaration's parameter names by the impl's: ((DECL-NAME . IMPL-SYMBOL) ...)
  (define (decl-rename f)
    (define d (decl-of f))
    (define dnames (if d (map (lambda (p) (var-name (field p 'name))) (params d)) '()))
    (define inames (map (lambda (p) (var-name (field p 'name))) (params f)))
    (if (and d (= (length dnames) (length inames)))
        (for/list ([a (in-list dnames)] [b (in-list inames)] #:when (and a b)) (cons a (string->symbol b)))
        '()))
  (define (decl-requires f)
    (define k (field f 'kind))
    (define targs (field k 'trait_typ_args))
    (define d (decl-of f))
    (cond
      [(not d) '()]
      [else
       (define dnames (map (lambda (p) (var-name (field p 'name))) (params d)))
       (define inames (map (lambda (p) (var-name (field p 'name))) (params f)))
       (if (not (= (length dnames) (length inames)))
           '()
           (let* ([names (for/hash ([a (in-list dnames)] [b (in-list inames)]) (values a b))]
                  ;; Self and the trait's type parameters (the declaration's first ones) by the impl's arguments
                  [dtps (or (field d 'typ_params) '())]
                  [tsub (for/hash ([n (in-list dtps)] [t (in-list targs)]) (values n t))])
             (let loop ([e (or (field d 'require) '())])
               (match e
                 [(list 'Typ 'TypParam (? string? n)) #:when (hash-ref tsub n #f) (hash-ref tsub n)]
                 [(list 'VarIdent (? string? s) rest ...) `(VarIdent ,(hash-ref names s s) ,@rest)]
                 [(? pair?) (cons (loop (car e)) (loop (cdr e)))]
                 [_ e]))))]))
  (define (module-of f) (format "~a" (field f 'owning_module)))
  ;; pub, or restricted to a strict ancestor of the owning module (pub(crate),
  ;; pub(super), pub(in crate::mm)): callable from other modules, so it has
  ;; callers outside its module, and the client module (a child of the owning
  ;; module) sees it.  Private functions (restricted to the owning module) are
  ;; helpers, not APIs (design.md 3.2).  VIR prints the crate root (pub(crate))
  ;; as `ostd::`.
  (define (visible-outside? f)
    (define r (field (field f 'visibility) 'restricted_to))
    (or (eq? r 'None)
        (let ([rs (regexp-replace #rx"::$" (format "~a" r) "")] [ms (module-of f)])
          (string-prefix? ms (string-append rs "::")))))
  (define (selected? f)
    (and (regexp-match? module-rx (module-of f))
         (not (regexp-match? (regexp (string-append "::" client-module "$|::clients$")) (module-of f)))
         (memq (field f 'mode) '(Exec Proof Spec))
         (match (field f 'kind) [(list 'FunctionKind (or 'Static 'TraitMethodImpl) _ ...) #t] [_ #f])
         ;; statics and consts are values, not functions
         (match (field f 'item_kind) [(list 'ItemKind (or 'Static 'Const) _ ...) #f] [_ #t])
         ;; a broadcast lemma without parameters cannot be called, only `broadcast use`d
         (not (and (attr f 'broadcast_forall) (null? (params f))))
         ;; a trait default method an impl inherits is taken as that impl's method (its
         ;; requires come from the declaration, as an overriding method's do): it is
         ;; callable on the impl's type, and its requires may be false there (T2)
         (visible-outside? f)
         ;; the twin is taken; the plain function only when it has none
         (or (string-contains? (fn-path f) vprefix)
             (not (hash-ref by-path (let* ([s (segments (fn-path f))])
                                      (string-join (append (drop-right s 1) (list (string-append vprefix (last s)))) "::"))
                            #f)))
         ;; spec functions only as methods (for spec arguments and type checks)
         (or (not (eq? (field f 'mode) 'Spec))
             (let ([ps (params f)]) (and (pair? ps) (equal? (var-name (field (car ps) 'name)) "self"))))))
  (define chosen (filter selected? fns))
  ;; item-index for associated functions without self
  ;; (and for the associated functions requires call, anywhere in ostd)
  (define need (for/list ([f (in-list fns)]
                          ;; (and for every chosen function: which `&mut` borrows reach the result)
                          #:when (or (memq f chosen)
                                     (and (regexp-match? #rx"^ostd::.*impl&%" (fn-path f))
                                          (not (eq? (field f 'mode) 'Exec))))) f))
  (define files (remove-duplicates (filter values (map (lambda (f) (car (or (fn-span f) '(#f)))) need))))
  (define its (if (null? files) '() (load-items item-index vostd files)))
  (define (item-of f)
    (define it
      (match (fn-span f)
        [(cons file line)
         (define n (last-seg (plain (fn-path f))))
         (for/first ([it (in-list its)]
                     #:when (and (equal? (item-file it) file) (equal? (item-name it) n)
                                 (<= (item-start it) line (item-end it))))
           it)]
        [_ #f]))
    (if (and it (item-self it)) it (let ([s (vir-self f)]) (if s (item #f #f #f #f s (if it (item-muts it) '())) it))))
  ;; The self type from VIR, for impls item-index does not see (macro output
  ;; such as bitflags!): a trait impl's Self, or the type of `self` in another
  ;; method of the same impl.
  (define (vir-self f)
    (define k (field f 'kind))
    (define impl (let ([m (regexp-match #rx"^(.*impl&%[0-9]+)::" (fn-path f))]) (and m (cadr m))))
    (define t
      (or (match k
            [(list 'FunctionKind 'TraitMethodImpl _ ...)
             (let ([targs (field k 'trait_typ_args)]) (and (pair? targs) (car targs)))]
            [_ #f])
          (and impl
               (for*/first ([g (in-list fns)]
                            #:when (string-prefix? (fn-path g) (string-append impl "::"))
                            [ps (in-value (params g))]
                            #:when (and (pair? ps) (equal? (var-name (field (car ps) 'name)) "self")))
                 (match (field (car ps) 'typ)
                   [(list 'Typ 'Decorate (list 'TypDecoration 'Ref) _ inner) inner]
                   [(list 'Typ 'MutRef inner) inner]
                   [t t])))))
    (and t (with-handlers ([no? (lambda (_) #f)]) (type->text (typ t)))))
  (define (impl-path p typs)
    (define f (hash-ref by-path (format "~a" p) #f))
    (define it (and f (item-of f)))
    (define names (and f (map (lambda (tp) (string-replace tp "Self%" "Self")) (or (field f 'typ_params) '()))))
    (define texts (with-handlers ([no? (lambda (_) #f)])
                    (map (lambda (t) (type->text (typ t))) (if (list? typs) typs '()))))
    (and it (item-self it) texts (= (length names) (length texts))
         (with-handlers ([no? (lambda (_) #f)])
           (define self (self-type->path (item-self it)))
           ;; the impl's type parameters are named in the self type; the rest are the function's own
           (define-values (in-self own)
             (partition (lambda (nt) (string-contains? self (format "{~a}" (car nt)))) (map cons names texts)))
           (format "~a::~a~a"
                   (unbrace '() (for/fold ([s self]) ([nt (in-list in-self)]) (string-replace s (format "{~a}" (car nt)) (cdr nt))))
                   (last-seg (plain (format "~a" p)))
                   (if (null? own) "" (format "::<~a>" (string-join (map cdr own) ", ")))))))
  ;; lifetime parameters: datatypes by their declaration's span, traits by
  ;; their declaration in ostd's sources (VIR's trait items have no span)
  (define source-lines (make-hash))
  (define (lines-of file)
    (hash-ref! source-lines file
               (lambda () (let ([p (build-path vostd file)]) (if (file-exists? p) (list->vector (file->lines p)) (vector))))))
  (define lifetimes
    (let* ([dts (for*/list ([x (in-list items)]
                            #:when (eq? (car (unwrap x)) 'Datatype)
                            [p (in-value (match (field x 'name) [(list 'Dt 'Path p) (format "~a" p)] [_ #f]))]
                            [s (in-value (fn-span x))]
                            #:when (and p s))
                  (define ls (lines-of (car s)))
                  (define text (string-join (for/list ([i (in-range (sub1 (cdr s)) (min (vector-length ls) (+ (cdr s) 4)))])
                                              (vector-ref ls i))
                                            " "))
                  (cons p (declared-lifetimes text (last-seg p))))]
           [rs (for/list ([f (in-directory (build-path vostd "ostd" "src"))]
                          #:when (regexp-match? #rx"[.]rs$" (path->string f)))
                 f)]
           [trs (for*/list ([f (in-list rs)]
                            [m (in-list (regexp-match* #px"trait\\s+([A-Za-z_][A-Za-z0-9_]*)\\s*<\\s*'[^{]*"
                                                       (file->string f) #:match-select values))])
                  (cons (cadr m) (declared-lifetimes (car m) (cadr m))))])
      (for/hash ([pk (in-list (append dts trs))] #:when (> (cdr pk) 0)) (values (car pk) (cdr pk)))))
  ;; datatype names with more than one path (datatype-name); the standard
  ;; library's are not counted: its types are not in scope unless imported
  ;; (`core::iter::Map` beside vstd's `Map`)
  (define ambiguous
    (let ([paths (make-hash)])
      (for* ([x (in-list items)] #:when (eq? (car (unwrap x)) 'Datatype)
             [p (in-value (match (field x 'name) [(list 'Dt 'Path p) (format "~a" p)] [_ #f]))]
             #:when (and p (not (regexp-match? #rx"^(core|alloc|std)::" p))))
        (hash-update! paths (last-seg p) (lambda (s) (if (member p s) s (cons p s))) '()))
      (for/hash ([(n ps) (in-hash paths)] #:when (> (length ps) 1)) (values n #t))))
  ;; trait methods shadowed by an inherent method of their self type (current-shadowed?)
  (define (trait-impl? f) (match (field f 'kind) [(list 'FunctionKind 'TraitMethodImpl _ ...) #t] [_ #f]))
  (define (self-datatype f)
    (define ps (params f))
    (and (pair? ps) (equal? (var-name (field (car ps) 'name)) "self")
         (let loop ([t (field (car ps) 'typ)])
           (match t
             [(list 'Typ 'Decorate _ _ inner) (loop inner)]
             [(list 'Typ 'MutRef inner) (loop inner)]
             [(list 'Typ 'Datatype (list 'Dt 'Path p) _ ...) (format "~a" p)]
             [_ #f]))))
  (define inherent
    (for*/hash ([f (in-list fns)] #:when (and (not (trait-impl? f)) (regexp-match? #rx"impl&%" (fn-path f)))
                [d (in-value (self-datatype f))] #:when d)
      (values (cons d (last-seg (plain (fn-path f)))) #t)))
  (define (shadowed? f)
    (and (trait-impl? f)
         (let ([d (self-datatype f)]) (and d (hash-ref inherent (cons d (last-seg (plain (fn-path f)))) #f)))))
  (define traits
    (for/hash ([x (in-list items)] #:when (eq? (car (unwrap x)) 'trait))
      (values (regexp-replace #rx"^crate::" (format "~a" (cadr (unwrap x))) "ostd::") #t)))
  (define datatype-arity
    (for*/hash ([x (in-list items)] #:when (eq? (car (unwrap x)) 'Datatype)
                [p (in-value (match (field x 'name) [(list 'Dt 'Path p) (format "~a" p)] [_ #f]))] #:when p)
      (values (regexp-replace #rx"^crate::" p "ostd::") (length (or (field x 'typ_params) '())))))
  (define (free-tparams p)
    (define f (hash-ref by-path (format "~a" p) #f))
    ;; inherent functions only: a trait's method has the trait's type
    ;; parameters among its own (`la_inv` of `TreeNodeValue<L>`)
    (define tps (if (and f (match (field f 'kind) [(list 'FunctionKind 'Static _ ...) #t] ['(FunctionKind Static) #t] [_ #f]))
                    (or (field f 'typ_params) '())
                    '()))
    (define (mentions? t n) (match t [(list 'Typ 'TypParam (== n)) #t] [(? pair?) (ormap (lambda (u) (mentions? u n)) t)] [_ #f]))
    (define used (for/list ([n (in-list tps)]) (for/or ([q (in-list (if f (params f) '()))]) (mentions? (field q 'typ) n))))
    ;; only a trailing run of unused ones (the method's own)
    (let loop ([ns (reverse tps)] [us (reverse used)] [acc '()])
      (if (and (pair? ns) (not (car us))) (loop (cdr ns) (cdr us) (cons (car ns) acc)) acc)))
  ;; the source records (item-index --full) of the chosen functions' files and
  ;; the files of the datatypes; a function is matched as in docs/representation.md 6.1:
  ;; same file, VIR's span starts inside the record's, same name
  (define vir-datatypes
    (for*/list ([x (in-list items)]
                #:when (eq? (car (unwrap x)) 'Datatype)
                [p (in-value (match (field x 'name) [(list 'Dt 'Path p) (format "~a" p)] [_ #f]))]
                [s (in-value (fn-span x))]
                #:when (and p s (regexp-match? #rx"^ostd::" p)))
      (list p (car s) (cdr s))))
  (define full-files
    (remove-duplicates (append (filter values (map (lambda (f) (car (or (fn-span f) '(#f)))) chosen))
                               ;; the traits' declarations, whose clauses trait impls take
                               (filter values (map (lambda (f) (let ([d (decl-of f)]) (and d (car (or (fn-span d) '(#f)))))) chosen))
                               (map cadr vir-datatypes))))
  ;; the records with spanned trees (item-index --full-spans) for the clauses,
  ;; and without spans (as --full prints them) for everything else, the tables among it
  (define full-spanned (if (null? full-files) '() (load-full item-index vostd full-files)))
  (define full (map strip-spans full-spanned))
  (define full-by-file (make-hash))
  (for ([r (in-list full)] #:when (memq (car r) '(fn const datatype)))
    (hash-update! full-by-file (rec-1 r 'file) (lambda (l) (cons r l)) '()))
  ;; every clause of the source by its span: requires and recommends (a trait
  ;; declaration's too, for its impls), and ensures (lemmas)
  (define (clause-trees ks)
    (for*/hash ([r (in-list full-spanned)] #:when (eq? (car r) 'fn)
                [k (in-list ks)]
                [c (in-list (rec-ref r k '()))] #:when (and (pair? c) (eq? (car c) 'c)))
      (values (cadr c) (cadddr c))))
  (define req-trees (clause-trees '(requires recommends)))
  (define ens-trees (clause-trees '(ensures)))
  (define (record-of f)
    (match (fn-span f)
      [(cons file line)
       (define n (regexp-replace #rx"^.*%%%" (last-seg (plain (fn-path f))) ""))
       (define cands
         (for/list ([r (in-list (hash-ref full-by-file file '()))]
                    #:when (eq? (car r) 'fn)
                    #:when (equal? (rec-1 r 'name) n)
                    #:when (let-values ([(_f a b) (span-lines (rec-1 r 'span))]) (and a (<= a line b))))
           r))
       ;; the innermost
       (and (pair? cands)
            (argmin (lambda (r) (let-values ([(_f a b) (span-lines (rec-1 r 'span))]) (- b a))) cands))]
      [_ #f]))
  (define (module-rel f) (regexp-replace #rx"^ostd(::|$)" (module-of f) ""))
  ;; (datatype PATH (span ..) (kind ..) (lifetimes ..) (type-params ..) (fields ..) (variants ..)
  ;;           [(type-invariant "FN")] [(drop)]), by module
  (define datatypes-of (make-hash))
  (for ([d (in-list vir-datatypes)])
    (match-define (list p file line) d)
    (define n (last-seg p))
    (define r (for/first ([r (in-list (hash-ref full-by-file file '()))]
                          #:when (and (eq? (car r) 'datatype) (equal? (rec-1 r 'name) n)
                                      (let-values ([(_f a b) (span-lines (rec-1 r 'span))]) (and a (<= a line b)))))
                r))
    (when r
      (define (head t) (car (regexp-match #px"^[A-Za-z_][A-Za-z0-9_]*" (string-trim t))))
      (define inv
        (for/first ([x (in-list (hash-ref full-by-file file '()))]
                    #:when (and (eq? (car x) 'fn) (member "type_invariant" (rec-ref x 'attrs '()))
                                (rec-1 x 'self) (equal? (head (rec-1 x 'self)) n)))
          (rec-1 x 'name)))
      (define drop? (for/or ([x (in-list full)])
                      (and (eq? (car x) 'drop-impl) (equal? (head (rec-1 x 'type)) n))))
      (define m (string-join (drop-right (segments p) 1) "::"))
      (hash-update! datatypes-of m
                    (lambda (l)
                      (cons `(datatype ,(string->symbol (regexp-replace #rx"^ostd::" p "crate::"))
                                       (span ,(rec-1 r 'span)) (kind ,(rec-1 r 'kind))
                                       (lifetimes ,@(rec-ref r 'lifetimes '()))
       (type-params ,@(rec-ref r 'type-params '()))
                                       (fields ,@(rec-ref r 'fields '())) (variants ,@(rec-ref r 'variants '()))
                                       ,@(if inv `((type-invariant ,inv)) '())
                                       ,@(if drop? '((drop)) '()))
                            l))
                    '())))
  (define by-module (make-hash))
  (define uses-of (make-hash))
  (define skipped (make-hash))
  (define left-out (box (quote ())))
  ;; requires clauses from the source / kept from VIR (source-requires)
  (define req-stats (box (cons 0 0)))
  (for ([f (in-list chosen)])
    (with-handlers ([no? (lambda (e) (hash-update! skipped (no-what e) add1 0)
                           (set-box! left-out (cons (list (fn-path f) (no-what e)) (unbox left-out))))])
      (define uses (box '()))
      (define e (parameterize ([current-impl-path impl-path]
                               [current-lifetimes lifetimes]
                               [current-lifetime-used (box #f)]
                               [current-ambiguous-types ambiguous]
                               [current-type-uses uses]
                               [current-shadowed? shadowed?]
                               [current-traits traits]
                               [current-free-tparams free-tparams]
                               [current-datatype-arity datatype-arity])
                  (entry f plain-of item-of method? ptypes decl-requires)))
      (hash-update! uses-of (module-of f) (lambda (l) (remove-duplicates (append l (unbox uses)))) '())
      (define rec (record-of f))
      (define e+ (append (source-ensures (source-requires (source-static (source-no-flow e rec) rec) rec req-stats (decl-rename f) req-trees) ens-trees) (list (source-field f rec (module-rel f)))))
      (hash-update! by-module (module-of f) (lambda (l) (cons (cons f e+) l)) '())))
  (make-directory* (build-path out-dir "apis"))
  (make-directory* (build-path out-dir "targets"))
  (define written
    (for/list ([(m fes) (in-hash by-module)]
               #:when (module-file m (map car fes)))
      (define mod (string-replace m "ostd::" "" #:all? #f))
      (define base (string-replace mod "::" "."))
      (define file (module-file m (map car fes)))
      (define place (placement vostd mod file))
      (define sibling? (eq? (cadr (assq 'placement place)) 'sibling))
      (define place-uses (cadr (assq 'uses place)))
      ;; a module's free function by its absolute path, `crate::mm::frame::meta::get_slot`:
      ;; right from the clients' module wherever it is, and from another module's clients
      ;; (a protocol's) that can reach it; `super::f` was right only from inside the module
      (define (relocate e)
        (let walk ([x e])
          (match x
            [`(function ,(? string? s)) #:when (string-prefix? s "super::")
             `(function ,(string-append "crate::" mod "::" (substring s 7)))]
            [(? pair?) (cons (walk (car x)) (walk (cdr x)))]
            [_ x])))
      ;; an import the module makes itself already (by the name it imports) is not
      ;; made twice (E0252: `pcell_maybe_uninit` is defined multiple times)
      (define (imported? u)
        (match (regexp-match #px"^use .*::([A-Za-z_][A-Za-z0-9_]*);$" u)
          [(list _ n) (for/or ([p (in-list place-uses)]) (regexp-match? (pregexp (format "\\b~a\\b" n)) p))]
          [_ #f]))
      (write-table (build-path out-dir "apis" (string-append base ".rktd")) m (map relocate (reverse (map cdr fes))) commit
                   (filter (lambda (u) (not (imported? u))) (sort (hash-ref uses-of m '()) string<?))
                   (sort (hash-ref datatypes-of m '()) symbol<? #:key cadr)
                   place-uses)
      (write-forms (build-path out-dir "targets" (string-append base ".rktd"))
                   `((package "ostd")
                     ,@(filter (lambda (x) (not (eq? (car x) 'uses))) place)
                     (mod-anchor end) (mod-line ,(format "mod ~a;" client-module))))
      (list mod (length fes) (cadr (assq 'placement place)))))
  (write-forms (build-path out-dir "left-out.rktd") (sort (unbox left-out) string<? #:key car))
  (list (sort written string<? #:key car)
        (sort (hash->list skipped) > #:key cdr)
        `(requires-from-source ,(car (unbox req-stats))
                               (kept-from-vir ,(cdr (unbox req-stats))
                                              ,@(sort (hash->list (current-vir-reasons)) > #:key cdr)))
        ;; datatypes that hold a tracked resource (a Tracked field) and have no Drop
        ;; recorded: candidates for (must-close ..), which a person decides
        ;; (guards are; a Frame may be dropped; docs/representation.md 4.3)
        `(must-close-candidates
          ,@(sort (for*/list ([ds (in-hash-values datatypes-of)] [d (in-list ds)]
                              #:when (and (not (assq 'drop (filter pair? (cddr d))))
                                          (for/or ([fl (in-list (cdr (assq 'fields (filter pair? (cddr d)))))])
                                            (and (pair? fl) (>= (length fl) 4) (regexp-match? #px"^Tracked<" (cadddr fl))))))
                    (cadr d))
                  symbol<?))))

(define (path->string* p) (if (path? p) (path->string p) p))

(define (fn-span f)
  (define s (and (pair? (unwrap-span f)) (cadr (unwrap-span f))))
  (and (string? s) (span-file+line s)))

;; The (@ SPAN node) wrapper of a top-level item.
(define (unwrap-span f) (if (and (pair? f) (memq (car f) '(@ @@))) f #f))

;; The file that defines module m: the file of its functions, when its name
;; agrees with the module (mod.rs/lib.rs or NAME.rs); inline modules are left out.
(define (module-file m fs)
  (define segs (cdr (segments m)))
  (define files (remove-duplicates (filter values (map (lambda (f) (and (fn-span f) (car (fn-span f)))) fs))))
  (for/first ([file (in-list files)]
              #:when (let* ([parts (string-split file "/")] [stem (last parts)])
                       (cond [(null? segs) (equal? stem "lib.rs")]
                             [(member stem '("mod.rs")) (equal? (list-ref parts (- (length parts) 2)) (last segs))]
                             [else (equal? stem (string-append (last segs) ".rs"))])))
    file))

;; placement : vostd module-path ("mm::frame::segment") file -> ((placement P) (module ..) (file ..) (mod-file ..) (uses U))
;; Where a module's clients go (design.md 3.8).  Beside it: a module
;; `cs_clients` of its parent (`mm::frame::cs_clients`, the file
;; `mm/frame/cs_clients.rs`, declared in the parent's file).  Verus shows a
;; closed spec function's body and private fields to the defining module and
;; its children; a client inside the module saw them, a real caller elsewhere
;; does not, and the clients missed every result described only by closed
;; functions (docs/enumeration.md 17.3, 20: `Segment::split`).  The sibling
;; sees what the tables hold (everything at least `pub(super)`).  It sees the
;; parent's closed bodies still: one level up, not none.  Its imports: the
;; table's own, `use super::NAME::*;` (the module's items), and the module's
;; top-level `use` statements verbatim (their `super` is the sibling's too);
;; not one behind `#[cfg(..)]`.  Where the parent's file is not found (a module
;; mounted by `#[path]`), the clients go inside the module as before:
;; (placement child).
(define (placement vostd mod file)
  (define segs (string-split mod "::"))
  (define name (last segs))
  ;; the directory of the parent's child modules: x/y/ for x/y/z.rs and x/y/z/mod.rs
  (define dir (regexp-replace #rx"[^/]+/?$" (regexp-replace #rx"(/mod)?[.]rs$" file "") ""))
  ;; a top-level module's parent is the crate root (lib.rs): the sibling is `cs_clients`
  (define parent-file
    (and (not (member (last (string-split file "/")) '("lib.rs")))
         (let ([d (regexp-replace #rx"/$" dir "")])
           (for/first ([c (list (string-append d "/mod.rs") (string-append d ".rs") (string-append d "/lib.rs"))]
                       #:when (file-exists? (build-path vostd c)))
             c))))
  (cond
    [(and parent-file (file-exists? (build-path vostd file)))
     (define src (regexp-replace* #px"/\\*.*?\\*/"
                                  (regexp-replace* #px"//[^\n]*" (file->string (build-path vostd file)) "")
                                  ""))
     (define own-uses
       (for/list ([p (in-list (regexp-match-positions* #px"(?m:^use [^;]*;)" src))]
                  #:unless (regexp-match? #px"#\\[cfg\\([^\n]*\\)\\]\\s*$" (substring src 0 (car p))))
         (regexp-replace* #px"\\s+" (substring src (car p) (cdr p)) " ")))
     ;; the module's child modules, and which of them the sibling may name (not private)
     (define children
       (for/list ([m (in-list (regexp-match* #px"(?m:^\\s*(pub(?:\\([^)]*\\))?\\s+)?mod\\s+([A-Za-z_][A-Za-z0-9_]*)\\s*;)" src
                                             #:match-select cdr))])
         (cons (cadr m) (and (car m) #t))))
     ;; `use self::x..` and `use x..` for a child x of the module are through the
     ;; module from the sibling; through a private child, not at all (rustc's
     ;; import suggestions supply what is missing)
     (define (relocate-use u)
       (match (regexp-match #px"^use (?:self::)?([A-Za-z_][A-Za-z0-9_]*)(::.*)$" u)
         [(list _ first rest)
          (define c (assoc first children))
          (cond [(not c) (if (regexp-match? #px"^use self::" u) #f u)]
                [(cdr c) (format "use super::~a::~a~a" name first rest)]
                [else #f])]
         [_ u]))
     ;; the types the module declares and the sibling may name: inside the module its
     ;; own definition outranks every glob import; beside it the module's items come
     ;; by a glob too, and collide with a glob the module makes (vm_space's `Cursor`
     ;; and `crate::mm::page_table::*`'s: E0659).  An explicit import outranks globs.
     (define own-types
       (remove-duplicates
        (for/list ([m (in-list (regexp-match* #px"(?m:^\\s*pub(\\([^)]*\\))?\\s+(?:struct|enum|union|trait|type)\\s+([A-Za-z_][A-Za-z0-9_]*))" src
                                              #:match-select cdr))]
                   #:unless (equal? (car m) "(self)"))
          (cadr m))))
     `((placement sibling)
       (module ,(string-join (append (drop-right segs 1) (list client-module)) "::"))
       (file ,(string-append dir client-module ".rs"))
       (mod-file ,parent-file)
       (uses ,(remove-duplicates
               (append (list (format "use super::~a::*;" name))
                       (if (null? own-types) '()
                           (list (format "use super::~a::{~a};" name (string-join own-types ", "))))
                       (filter values (map relocate-use own-uses))))))]
    [else
     `((placement child)
       (module ,(string-append mod "::" client-module))
       (file ,(client-file file))
       (mod-file ,file)
       (uses ()))]))

;; mod.rs -> the same directory; NAME.rs -> NAME/
(define (client-file file)
  (define parts (string-split file "/"))
  (define stem (last parts))
  (define dir (if (member stem '("mod.rs" "lib.rs"))
                  (drop-right parts 1)
                  (append (drop-right parts 1) (list (substring stem 0 (- (string-length stem) 3))))))
  (string-join (append dir (list (string-append client-module ".rs"))) "/"))

;; type-uses: the modules of types written with their module (datatype-name)
;; datatypes: the (datatype ..) forms of the module (docs/representation.md 4.3)
;; place-uses: the imports of the clients' placement (placement)
(define (write-table file m entries commit [type-uses '()] [datatypes '()] [place-uses '()])
  (call-with-output-file file #:exists 'truncate
    (lambda (o)
      (fprintf o ";; API table extracted from VIR (extract.rkt) for ~a.\n;; Check it with `racket cli.rkt probe` before use.\n" m)
      ;; the checkout the VIR was exported from (run.rkt checks it, design.md 3.2)
      (pretty-write `(at ,commit) o)
      ;; inside the module, `use super::*` is the module's items; beside it (place-uses
      ;; given) it would be the parent's, whose names collide with the module's
      ;; (vm_space's `Cursor` and page_table's: E0659): the module's own imports instead
      (pretty-write `(uses "use vstd::prelude::*;" "use vstd_extra::prelude::*;"
                           ,@(if (null? place-uses) '("use super::*;") place-uses) ,@type-uses) o)
      (pretty-write '(copy bool char u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize int nat) o)
      (for ([d (in-list datatypes)]) (pretty-write d o))
      (for ([e (in-list entries)]) (pretty-write e o)))))
