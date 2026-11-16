#lang racket/base
;; The API table (design.md, 结论3) and types (结论2).
;;
;; A table file is a sequence of forms:
;;   (base FILE)              entries of FILE first; later entries with the same name replace them
;;   (uses "use ...;" ...)    import lines of the client module, emitted verbatim
;;   (at "COMMIT")            the vostd commit the table was made or checked for;
;;                            lib/vostd/run.rkt refuses to verify against another
;;                            checkout (design.md 3.2)
;;   (copy TYPE-NAME ...)     datatypes that are Copy (references `(& T)` always are)
;;   (must-close TYPE-NAME ...)  datatypes whose values must be passed on by value before
;;                            they go out of scope (guards, 结论21)
;;   (observe NAME ((V TYPE-PATTERN) ...) E [numeric] [(consts C ...)])
;;   (observe-bool NAME ((V TYPE-PATTERN) ...) E)
;;                            observations of objects, for postcondition candidates (结论32)
;;   (datatype PATH ..)       a datatype as the source declares it (extract.rkt; not used yet)
;;   (fn NAME FIELD ...)      one API
;;
;;   FIELD = (mode exec|proof|spec)
;;         | (method NAME) | (function "PATH")            how a call is written; in PATH,
;;                                                         {T} is the instantiated type parameter T
;;         | (unsafe)                                      the call is written in `unsafe { }`
;;         | (generics (T BOUND ...) ...)                 BOUND = TYPE, or `static` for 'static
;;         | (params (NAME MODE TYPE) ...)                 receiver first, named `self`
;;         | (ghost with|arg (NAME MODE TYPE) ...)          `#[verus_spec(with ..)]` or trailing args
;;         | (ret TYPE) | (ghost-ret MODE TYPE)
;;         | (requires E ...)                              spec AST over the parameter names
;;         | (ensures E ...)                               only for lemmas (结论25), over the
;;                                                         parameter names
;;         | (lemma)                                       may be inserted by `retry` (结论25)
;;         | (source ..) | (source none)                 what the source says (extract.rkt, from
;;                                                         item-index --full); not used yet
;;   MODE  = exec | tracked | spec
;;   TYPE  = SYMBOL | (& T) | (&mut T) | (&static T) | (assoc T NAME) | (assoc T NAME "TRAIT") | (slice T)
;;         | (tuple T ...) | (NAME T ...)
;;   (assoc T NAME "TRAIT") is `<T as TRAIT>::NAME`, for a T that is not a type parameter
(require racket/list racket/match racket/string racket/file racket/runtime-path "../base/forms.rkt")

;; the providers from vstd that come with the tool (lib/providers/vstd.rktd)
(define-runtime-path vstd-providers "../providers/vstd.rktd")
(provide vstd-providers read-api-table table-commits api-table-uses api-ref api-table-lemmas table-names table-observers
         api-name api-mode api-call api-unsafe? api-generics api-params api-ghost-style api-ghost-params
         api-ret api-ret-modes tuple-parts api-ghost-ret api-requires api-ensures api-no-flow api-ret-ghost?
         param-name param-mode param-type
         copy-type? must-close-type? has-type-invariant? type-param? strip-ref match-type subst-type type->text)

(struct table (uses copy must-close fns observers invariants) #:transparent)

;; read-api-table : path -> table
(define (read-api-table file)
  (define-values (uses copy must-close fns observers invariants) (read-forms file))
  (table uses copy must-close fns observers invariants))

(define (read-forms file)
  (define dir (let-values ([(d _n _x) (split-path (path->complete-path file))]) d))
  (for/fold ([uses '()] [copy '()] [mc '()] [fns (hash)] [obs '()] [invs '()]) ([form (in-list (file->list file))])
    (match form
      ;; (base FILE entries): another module's table, without its imports (they are
      ;; relative to where that module's clients go, extract.rkt's placement)
      [`(base ,f ,more ...)
       (define-values (u c m fs o i) (read-forms (if (absolute-path? f) f (build-path dir f))))
       (values (append uses (if (memq 'entries more) '() u)) (append copy c) (append mc m)
               (for/fold ([h fns]) ([(k v) (in-hash fs)]) (hash-set h k v)) (append obs o) (append invs i))]
      [`(uses ,line ...) (values (append uses line) copy mc fns obs invs)]
      [`(at ,_) (values uses copy mc fns obs invs)]
      [`(copy ,name ...) (values uses (append copy name) mc fns obs invs)]
      [`(must-close ,name ...) (values uses copy (append mc name) fns obs invs)]
      [`(,(or (quote observe) (quote observe-bool)) ,_ ...) (values uses copy mc fns (append obs (list form)) invs)]
      ;; what the source says of the module's datatypes (docs/representation.md 4.3):
      ;; the types with a type invariant (use_type_invariant, B2), by their last segment
      [`(datatype ,path ,more ...)
       (values uses copy mc fns obs
               (if (for/or ([x (in-list more)]) (and (pair? x) (eq? (car x) 'type-invariant)))
                   (cons (format "~a" path) invs)
                   invs))]
      [`(fn ,name ,_ ...) (values uses copy mc (hash-set fns name form) obs invs)])))

;; has-type-invariant? : table TYPE [client-module] -> boolean: a value of TYPE (not a
;; reference to one; strip-ref first) is of a datatype with a #[verifier::type_invariant]
;; (by the last segment of its path), whose invariant function is visible from
;; client-module ("sync::cs_clients"): only inside the datatype's own
;; module (a protocol's type from another module is not; Verus: "type invariant
;; function .. is not visible to this program point").
(define (has-type-invariant? t ty [client-module #f])
  (define h (if (pair? ty) (car ty) ty))
  (and (symbol? h)
       (for/or ([p (in-list (table-invariants t))])
         (define segs (string-split p "::"))
         (and (equal? (last segs) (symbol->string h))
              (or (not client-module)
                  (let ([m (string-join (drop-right (if (equal? (car segs) "crate") (cdr segs) segs) 1) "::")])
                    (string-prefix? client-module (string-append m "::"))))))
       #t))

;; table-commits : path -> (COMMIT ...): the (at ..) of the file and of its
;; bases, recursively.  A table of several modules (a protocol's other
;; modules) has several; lib/providers/vstd.rktd (providers from vstd) has none.
(define (table-commits file)
  (define dir (let-values ([(d _n _x) (split-path (path->complete-path file))]) d))
  (remove-duplicates
   (append* (for/list ([form (in-list (file->list file))])
              (match form
                [`(at ,c) (list c)]
                [`(base ,f ,_ ...) (table-commits (if (absolute-path? f) f (build-path dir f)))]
                [_ '()])))))

(define (api-table-uses t) (remove-duplicates (table-uses t)))

;; api-ref : table symbol -> fn form or #f
(define (api-ref t name) (hash-ref (table-fns t) name #f))

;; api-table-lemmas : table -> (api ...), the entries marked (lemma), by name
(define (api-table-lemmas t)
  (sort (for/list ([(k v) (in-hash (table-fns t))] #:when (field v 'lemma)) v)
        symbol<? #:key api-name))

(define (field api key [default #f]) (form-ref api key default))

(define (api-name api) (cadr api))
(define (api-mode api) (car (field api 'mode '(exec))))
;; api-call : api -> (list 'method NAME) | (list 'function PATH)
(define (api-call api)
  (cond [(field api 'method) => (lambda (v) (list 'method (car v)))]
        [(field api 'function) => (lambda (v) (list 'function (car v)))]
        [else (error 'api-call "~a: neither method nor function" (api-name api))]))
;; api-generics : api -> ((T BOUND ...) ...)
(define (api-generics api) (field api 'generics '()))
(define (api-params api) (field api 'params '()))
;; api-ret-ghost? : api -> boolean, a proof function's result is a spec value
(define (api-ret-ghost? api) (and (field api 'ret-ghost) #t))
;; api-no-flow : api -> (NAME ...), `&mut` parameters whose borrow the result cannot hold
(define (api-no-flow api) (field api 'no-flow '()))
(define (api-ghost-style api) (let ([g (field api 'ghost)]) (if g (car g) 'with)))
(define (api-ghost-params api) (let ([g (field api 'ghost)]) (if g (cdr g) '())))
;; api-ret : api -> TYPE or #f (unit)
(define (api-ret api) (let ([r (field api 'ret)]) (and r (car r))))
;; api-ret-modes : api -> (exec|tracked|ghost ...) or #f
;; For a tuple result, each component's mode, from the source's return type
;; (`(NonNull<Self::Target>, Tracked<Self::Permission>)`): the table's type has
;; the Tracked/Ghost wrappers taken off.  #f without a source, or when the
;; source's components do not match the table's.
(define (api-ret-modes api)
  (define r (api-ret api))
  (define src (field api 'source))
  (define text (and (pair? src)
                    (for/first ([x (in-list src)] #:when (and (pair? x) (eq? (car x) 'ret) (= (length x) 3))) (caddr x))))
  (match r
    [`(tuple ,ts ..1)
     #:when (string? text)
     (define parts (tuple-parts (string-trim text)))
     (and parts (= (length parts) (length ts))
          (for/list ([p (in-list parts)])
            (cond [(regexp-match? #px"^Tracked\\s*<" p) 'tracked]
                  [(regexp-match? #px"^Ghost\\s*<" p) 'ghost]
                  [else 'exec])))]
    [_ #f]))
;; "(A<B, C>, Tracked<D>)" -> ("A<B, C>" "Tracked<D>"); #f if not a parenthesized tuple
(define (tuple-parts s)
  (and (string-prefix? s "(") (string-suffix? s ")")
       (let loop ([cs (string->list (substring s 1 (sub1 (string-length s))))] [depth 0] [cur '()] [acc '()])
         (define (piece) (string-trim (list->string (reverse cur))))
         (cond [(null? cs) (let ([p (piece)]) (reverse (if (equal? p "") acc (cons p acc))))]
               [(memv (car cs) '(#\< #\( #\[)) (loop (cdr cs) (add1 depth) (cons (car cs) cur) acc)]
               [(memv (car cs) '(#\> #\) #\])) (loop (cdr cs) (sub1 depth) (cons (car cs) cur) acc)]
               [(and (char=? (car cs) #\,) (= depth 0)) (loop (cdr cs) depth '() (cons (piece) acc))]
               [else (loop (cdr cs) depth (cons (car cs) cur) acc)]))))
;; api-ghost-ret : api -> (MODE TYPE) or #f
(define (api-ghost-ret api) (field api 'ghost-ret))
(define (api-requires api) (field api 'requires '()))
(define (api-ensures api) (field api 'ensures '()))
(define (api-unsafe? api) (and (field api 'unsafe) #t))

(define (param-name p) (car p))
(define (param-mode p) (cadr p))
(define (param-type p) (caddr p))

;; ================================================================ types

(define (copy-type? t typ)
  (match typ
    [`(,(or (quote &) (quote &static)) ,_) #t]
    [(? symbol? s) (and (memq s (table-copy t)) #t)]
    [`(,name ,_ ...) (and (memq name (table-copy t)) #t)]))

(define (must-close-type? t typ)
  (match typ
    [(? symbol? s) (and (memq s (table-must-close t)) #t)]
    [`(,(or '& '&mut '&static) ,_) #f]
    [`(,name ,_ ...) (and (memq name (table-must-close t)) #t)]))

(define (type-param? typ generics) (and (symbol? typ) (assq typ generics) #t))

(define (strip-ref typ)
  (match typ [`(& ,t) (strip-ref t)] [`(&mut ,t) (strip-ref t)] [`(&static ,t) (strip-ref t)] [_ typ]))

;; match-type : pattern type vars subst -> subst or #f
;; One-way matching: symbols in vars are the callee's type parameters and
;; get bound; everything else must be equal.  The caller's type parameters
;; are rigid (结论2).
(define (match-type pat typ vars subst)
  (cond [(and (symbol? pat) (memq pat vars))
         (define bound (assq pat subst))
         (cond [(not bound) (cons (cons pat typ) subst)]
               [(equal? (cdr bound) typ) subst]
               [else #f])]
        [(symbol? pat) (and (equal? pat typ) subst)]
        ;; a trait written as text (`(assoc M ReprPerm "..Repr<MetaSlotStorage>")`)
        [(string? pat) (and (equal? pat typ) subst)]
        [(and (pair? pat) (pair? typ) (= (length pat) (length typ)))
         (for/fold ([s subst]) ([p (in-list pat)] [x (in-list typ)])
           (and s (match-type p x vars s)))]
        [else #f]))

(define (subst-type typ subst)
  (cond [(symbol? typ) (cond [(assq typ subst) => cdr] [else typ])]
        [(pair? typ) (map (lambda (x) (subst-type x subst)) typ)]
        [else typ]))

;; type->text : TYPE -> string, the Rust spelling
(define (type->text typ)
  (match typ
    ['static "'static"]
    [(? symbol? s) (symbol->string s)]
    ;; VIR erases a reference's own lifetime; a shared reference to a type
    ;; with a lifetime argument gets that lifetime (`get(&'a self)` on
    ;; `RcuOptionReadGuard<'a, P>` needs `&'a`, and `&'a T<'a>` can always be
    ;; reborrowed shorter)
    [`(& (,name ,l ,_ ...))
     #:when (and (symbol? l) (regexp-match? #rx"^'" (symbol->string l)) (not (eq? l 'static)))
     (format "&~a ~a" l (type->text (cadr typ)))]
    [`(& ,t) (string-append "&" (type->text t))]
    ;; a reference the source declares `&'static` (docs/representation.md 5c)
    [`(&static ,t) (string-append "&'static " (type->text t))]
    [`(&mut ,t) (string-append "&mut " (type->text t))]
    [`(assoc ,t ,n) (format "~a::~a" (type->text t) n)]
    [`(assoc ,t ,n ,trait) (format "<~a as ~a>::~a" (type->text t) trait n)]
    [`(slice ,t) (format "[~a]" (type->text t))]
    [`(tuple ,t) (format "(~a,)" (type->text t))]
    [`(tuple ,ts ...) (format "(~a)" (string-join (map type->text ts) ", "))]
    [`(,name ,args ...) (format "~a<~a>" name (string-join (map type->text args) ", "))]))

;; table-names : table -> (symbol ...), every API name, sorted
(define (table-names t) (sort (hash-keys (table-fns t)) symbol<?))
