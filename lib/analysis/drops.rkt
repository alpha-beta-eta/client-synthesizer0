#lang racket/base
;; What a wrapper drops (design.md 3.9, representation.md step 7): facts the
;; functions F calls (G) ensure, that F's body proves but F's ensures does not
;; give its callers.  This file makes the candidates (step 1), puts them into
;; F's ensures (insert-candidates) and reads Verus's errors back to candidates
;; (blame); lib/pipeline/drops.rkt runs the steps: Verus in a copy of the
;; checkout keeps those F proves (step 2), claim clients those F's callers
;; cannot get (step 3).
;;
;; A candidate is G's ensures clause (the source's tree) moved into F:
;;   - G's parameters become F's, where the argument of the call is that
;;     parameter itself (a read, a borrow or a dereference of it); G's shared
;;     or owned parameter that is F's `&mut` one becomes `final(p)`;
;;   - G's result becomes F's, when their types are written the same, or
;;     F's inside Ok/Some: `r is Ok ==> (P[r.unwrap()])`;
;;   - G's ghost results (`with .. -> x: T`) become F's of the same type, or
;;     the content of F's Tracked<Option<T>>: `p@ is Some ==> (P[p@->0])`;
;; a clause that still names something of G's (a local, an unmapped
;; parameter), that names nothing but constants, that has a quantifier (the
;; tree has no triggers yet) or text the tree does not parse (`(src ..)`), or
;; that F's ensures already has, is not a candidate.  The move does not
;; follow data flow: a wrong candidate is one F does not prove, and step 2
;; drops it.
(require racket/list racket/match racket/string racket/port racket/system
         "../vostd/vir.rkt")
(provide drop-candidates print-tree load-records insert-candidates blame vir-calls)

;; ================================================================ source records

;; load-records : item-index-exe vostd -> (record ...), item-index --full on ostd's sources
(define (load-records exe vostd)
  (define files
    (parameterize ([current-directory vostd])
      (sort (for/list ([f (in-directory "ostd")]
                       #:when (and (regexp-match? #rx"[.]rs$" (path->string f))
                                   (regexp-match? #rx"^ostd/(src|specs|libs)/" (path->string f))))
              (path->string f))
            string<?)))
  (define out (parameterize ([current-directory vostd] [current-error-port (open-output-nowhere)])
                (with-output-to-string (lambda () (apply system* exe "--full" files)))))
  (for/list ([x (in-port read (open-input-string out))] #:when (eq? (car x) 'fn)) x))

(define (rec-ref r k [d '()]) (cond [(assq k (cdr r)) => cdr] [else d]))
(define (rec-1 r k) (let ([v (rec-ref r k #f)]) (and (pair? v) (car v))))

(define (span-lines s)
  (match (regexp-match #px"^(.*):([0-9]+):[0-9]+: ([0-9]+):[0-9]+" s)
    [(list _ f a b) (values f (string->number a) (string->number b))]
    [_ (values #f #f #f)]))

;; ================================================================ printing trees

;; print-tree : tree rename -> string or #f
;; The tree back as Verus text, with single-identifier paths renamed by
;; rename (an assoc list of strings).  #f for a tree with (src ..) or a
;; quantifier.  The trees keep the source's parentheses (paren nodes), so
;; printing adds none: precedence, chained comparisons and all, is the source's.
(struct no ())
(define (print-tree t rename)
  (define (ren p) (cond [(assoc p rename) => cdr] [else p]))
  (with-handlers ([no? (lambda (_) #f)])
    (let pr ([t t])
      (match t
        [`(paren ,a) (format "(~a)" (pr a))]
        ;; `#[trigger] e` (item-index since 2026-11-13); quantifiers are not printed
        [`(trigger ,a) (pr a)]
        [`(path ,(? string? p)) (if (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" p) (ren p) p)]
        [`(lit ,(? string? l)) l]
        [`(op ,(? string? o) ,a ,b) (format "~a ~a ~a" (pr a) o (pr b))]
        [`(not ,a) (format "!~a" (pr a))]
        [`(neg ,a) (format "-~a" (pr a))]
        [`(deref ,a) (format "*~a" (pr a))]
        [`(ref ,a) (format "&~a" (pr a))]
        [`(ref-mut ,a) (format "&mut ~a" (pr a))]
        [`(call ,f ,args ...) (format "~a(~a)" (pr f) (string-join (map pr args) ", "))]
        [`(method ,r ,(? string? m) ,tf ,args ...)
         (format "~a.~a~a(~a)" (pr r) m (if (string? tf) (let ([s (string-trim tf)]) (if (string-prefix? s "::") s (string-append "::" s))) "")
                 (string-join (map pr args) ", "))]
        [`(field ,a ,(? string? f)) (format "~a.~a" (pr a) f)]
        [`(arrow ,a ,(? string? f)) (format "~a->~a" (pr a) f)]
        [`(index ,a ,i) (format "~a[~a]" (pr a) (pr i))]
        [`(as ,a ,(? string? ty)) (format "~a as ~a" (pr a) ty)]
        [`(tuple ,as ...) (format "(~a~a)" (string-join (map pr as) ", ") (if (= (length as) 1) "," ""))]
        [`(view ,a) (format "~a@" (pr a))]
        [`(final ,a) (format "final(~a)" (pr a))]
        [`(is ,a ,(? string? v)) (format "~a is ~a" (pr a) v)]
        [`(isnt ,a ,(? string? v)) (format "~a !is ~a" (pr a) v)]
        [`(has ,a ,b) (format "~a has ~a" (pr a) (pr b))]
        [`(big-and ,as ...) (format "(~a)" (string-join (map pr as) " && "))]
        [`(big-or ,as ...) (format "(~a)" (string-join (map pr as) " || "))]
        [`(if ,c ,a ,b) (format "(if ~a { ~a } else { ~a })" (pr c) (pr a) (if b (pr b) "()"))]
        ;; matches binds names (the pattern's), which are not renamed
        [`(matches ,a (pat ,(? string? text) ,_ ...) ,rest ...)
         (match rest
           ['() (format "~a matches ~a" (pr a) text)]
           [(list (? string? op) b) (format "~a matches ~a ~a ~a" (pr a) text op (pr b))])]
        [_ (raise (no))]))))

;; the single-identifier paths of a tree (its free names, conservatively:
;; the names a matches pattern binds are left out)
(define (tree-names t)
  (define bound (let b ([t t]) (match t [`(pat ,_ ,ns ...) ns] [(? pair?) (append-map b (filter pair? t))] [_ '()])))
  (remove* bound
           (let walk ([t t])
             (match t
               [`(path ,(? string? p)) (if (regexp-match? #px"^[a-z_][A-Za-z0-9_]*$" p) (list p) '())]
               [`(call (path ,_) ,args ...) (append-map walk args)]
               [`(pat ,_ ...) '()]
               [(? pair?) (append-map walk (filter pair? t))]
               [_ '()]))))

;; ================================================================ candidates

(define (norm-type s) (regexp-replace* #px"(?:[A-Za-z_][A-Za-z0-9_]*::)+" (regexp-replace* #px"\\s+" s "") ""))
(define (norm-text s) (regexp-replace* #px"\\s+" s ""))

;; The calls in a VIR body: ((callee-path (arg ...)) ...)
(define (vir-calls body)
  (define out '())
  (let walk ([e body])
    (when (pair? e)
      (match e
        [(list '> 'Call ':target (list 'CallTarget 'Fun _ fun _ ...) ':args args _ ...)
         (set! out (cons (list (format "~a" (field fun 'path)) (if (list? args) args '())) out))]
        [_ (void)])
      (for-each walk (if (list? e) e (list (car e) (cdr e))))))
  (reverse out))

;; The local variable an argument is, through reads, borrows and dereferences; or #f.
(define (arg-var a)
  (let loop ([a a] [depth 0])
    (define n (unwrap a))
    (match n
      [(list 'Place 'Local (list 'VarIdent (? string? s) _ ...) _ ...) s]
      [(list 'Place 'Local (list 'VarIdent (? string? s) _ ...)) s]
      [(list '> (or 'ReadPlace 'Borrow 'TwoPhaseBorrowMut 'Unary 'UnaryOpr 'Loc 'VarLoc) x _ ...) #:when (< depth 6) (loop x (add1 depth))]
      [(list 'Place (or 'DerefMut 'Deref 'Temporary) x _ ...) #:when (< depth 6) (loop x (add1 depth))]
      [(list '> 'Var (list 'VarIdent (? string? s) _ ...)) s]
      [_ #f])))

;; arg-place : argument -> (VAR FIELD ...) or #f
;; The local variable and the fields an argument projects, through the same
;; reads, borrows and dereferences: `&mut self.0` is ("self" "0"), the
;; wrappers of vm_space over the page table's cursor.
(define (arg-place a)
  (let loop ([a a] [depth 0] [fields '()])
    (define n (unwrap a))
    (match n
      [(list 'Place 'Field (list 'FieldOpr _ ... ':field (? string? f) _ ...) x _ ...)
       #:when (< depth 8) (loop x (add1 depth) (cons f fields))]
      [(list 'Place 'Local (list 'VarIdent (? string? s) _ ...) _ ...) (cons s fields)]
      [(list 'Place 'Local (list 'VarIdent (? string? s) _ ...)) (cons s fields)]
      [(list '> (or 'ReadPlace 'Borrow 'TwoPhaseBorrowMut 'Unary 'UnaryOpr 'Loc 'VarLoc) x _ ...) #:when (< depth 8) (loop x (add1 depth) fields)]
      [(list 'Place (or 'DerefMut 'Deref 'Temporary) x _ ...) #:when (< depth 8) (loop x (add1 depth) fields)]
      [(list '> 'Var (list 'VarIdent (? string? s) _ ...)) (cons s fields)]
      [_ #f])))

;; drop-candidates : VIR-items records module-regex -> (candidate ...)
;; candidate = (cand F-PATH F-NAME F-FILE INSERT-AFTER G-PATH G-CLAUSE-SPAN TEXT CLAIM-TEXT)
;;   INSERT-AFTER: the span of F's last ensures clause (the candidate goes after it)
;;   TEXT: in F's names (for F's ensures); CLAIM-TEXT: with F's result as `ret` (a claim)
(define (drop-candidates items records module-rx)
  (define fns (for/list ([x (in-list items)] #:when (field x 'require)) x))
  (define (path-of f) (format "~a" (field (field f 'name) 'path)))
  (define by-file (make-hash))
  (for ([r (in-list records)]) (hash-update! by-file (rec-1 r 'file) (lambda (l) (cons r l)) '()))
  (define (record-of f)
    (match (let ([s (and (pair? f) (memq (car f) '(@ @@)) (cadr f))]) (and (string? s) (span-file+line s)))
      [(cons file line)
       (define n (regexp-replace #rx"^.*%%%" (regexp-replace #rx"^_VERUS_VERIFIED_" (last (string-split (path-of f) "::")) "") ""))
       (define cands (for/list ([r (in-list (hash-ref by-file file '()))]
                                #:when (equal? (rec-1 r 'name) n)
                                #:when (let-values ([(_f a b) (span-lines (rec-1 r 'span))]) (and a (<= a line b))))
                       r))
       (and (pair? cands) (argmin (lambda (r) (let-values ([(_f a b) (span-lines (rec-1 r 'span))]) (- b a))) cands))]
      [_ #f]))
  (define by-path (for/hash ([f (in-list fns)]) (values (path-of f) f)))
  (define (twin p) ; the _VERUS_VERIFIED_ twin, which has the ghost parameters
    (define s (string-split p "::"))
    (define t (string-join (append (drop-right s 1) (list (string-append "_VERUS_VERIFIED_" (regexp-replace #rx"^_VERUS_VERIFIED_" (last s) "")))) "::"))
    (hash-ref by-path t #f))
  (define (param-names r) (for/list ([p (in-list (append (rec-ref r 'params) (rec-ref r 'with-in)))]) (cadr p)))
  (define (mut-names r) ; the `&mut` parameters
    (for/list ([p (in-list (append (rec-ref r 'params) (rec-ref r 'with-in)))]
               #:when (or (regexp-match? #px"^&\\s*(?:'[A-Za-z_]+\\s+)?mut\\b" (caddr p))
                          (and (> (length p) 3) (match (cadddr p) [`(ref ,_ mut) #t] [_ #f]))))
      (cadr p)))
  (append*
   (for/list ([f (in-list fns)]
              #:when (regexp-match? module-rx (format "~a" (field f 'owning_module)))
              #:when (memq (field f 'mode) '(Exec Proof))
              ;; the function whose source the record is: its twin if any
              #:unless (and (not (regexp-match? #rx"_VERUS_VERIFIED_" (path-of f))) (twin (path-of f)))
              [fr (in-value (record-of f))]
              #:when (and fr (pair? (rec-ref fr 'ensures))))
     (define f-params (param-names fr))
     (define f-muts (mut-names fr))
     (define f-ret (let ([v (rec-ref fr 'ret)]) (and (pair? v) (car v))))
     (define f-ret-type (let ([v (rec-ref fr 'ret)]) (and (= (length v) 2) (cadr v))))
     (define f-outs (for/list ([p (in-list (rec-ref fr 'with-out))]) (cons (cadr p) (caddr p))))
     (define f-ens (map (lambda (c) (norm-text (caddr c))) (rec-ref fr 'ensures)))
     (define last-span (cadr (last (rec-ref fr 'ensures))))
     (define body (field f 'body))
     (remove-duplicates
      (for*/list ([call (in-list (if body (vir-calls body) '()))]
                  [g (in-value (hash-ref by-path (car call) #f))]
                  #:when g
                  #:unless (equal? (path-of g) (path-of f))
                  [gr (in-value (record-of g))]
                  #:when (and gr (pair? (rec-ref gr 'ensures)))
                  [rename (in-value
                           (let* ([g-params (param-names gr)]
                                  [args (map arg-place (cadr call))]
                                  ;; G's shared or owned parameter that is F's `&mut` one: its value
                                  ;; when F returns (stage 2 finds where F changes it after the call).
                                  ;; An argument that is a field of F's parameter (`&mut self.0`):
                                  ;; (field VAR ".0" F-MUT?), placed by transport
                                  [pmap (for/list ([gp (in-list g-params)] [pl (in-list args)]
                                                   #:when (and pl (member (car pl) f-params)))
                                          (define a (car pl))
                                          (define fmut (and (member a f-muts) (not (member gp (mut-names gr))) #t))
                                          (cons gp (cond [(pair? (cdr pl))
                                                          (list 'field a (apply string-append (map (lambda (f) (string-append "." f)) (cdr pl)))
                                                                (and (member a f-muts) #t))]
                                                         [fmut (format "final(~a)" a)]
                                                         [else a])))]
                                  [g-ret (let ([v (rec-ref gr 'ret)]) (and (pair? v) (car v)))]
                                  [g-ret-type (let ([v (rec-ref gr 'ret)]) (and (= (length v) 2) (cadr v)))]
                                  [rmap (cond
                                          [(not (and g-ret f-ret g-ret-type f-ret-type)) '()]
                                          [(equal? (norm-type g-ret-type) (norm-type f-ret-type)) (list (cons g-ret f-ret))]
                                          ;; F returns Result<T, _> / Option<T> of G's T: through Ok/Some
                                          [(wrapped-in (norm-type f-ret-type) (norm-type g-ret-type))
                                           => (lambda (ctor) (list (cons g-ret (list 'unwrap f-ret ctor))))]
                                          [else '()])]
                                  [omap (for*/list ([go (in-list (rec-ref gr 'with-out))]
                                                    [gt (in-value (norm-type (caddr go)))]
                                                    [fo (in-value (filter (lambda (o) (equal? (norm-type (cdr o)) gt)) f-outs))]
                                                    ;; F's Tracked<Option<T>> of G's Tracked<T>: `p@ is Some ==> P[p@->0]`
                                                    [fs (in-value (filter (lambda (o) (equal? (norm-type (cdr o)) (tracked-option gt))) f-outs))]
                                                    #:when (or (= (length fo) 1) (and (null? fo) (= (length fs) 1))))
                                          (if (= (length fo) 1)
                                              (cons (cadr go) (caar fo))
                                              (cons (cadr go) (list 'some (caar fs)))))])
                             (append pmap rmap omap)))]
                  [c (in-list (rec-ref gr 'ensures))]
                  [tree (in-value (cadddr c))]
                  [names (in-value (tree-names tree))]
                  ;; a fact of constants alone is no wrapper's to give
                  #:when (pair? names)
                  #:when (andmap (lambda (n) (assoc n rename)) names)
                  [wraps (in-value (remove-duplicates (for*/list ([n (in-list names)] [v (in-value (cdr (assoc n rename)))]
                                                                  #:when (and (pair? v) (memq (car v) '(unwrap some))))
                                                        v)))]
                  [text (in-value (transport tree rename wraps #f))]
                  #:when text
                  #:unless (member (norm-text text) f-ens))
        (define claim (and f-ret (transport tree rename wraps f-ret)))
        `(cand ,(path-of f) ,(rec-1 fr 'name) ,(rec-1 fr 'file) ,last-span ,(path-of g) ,(cadr c) ,text ,(or claim text)))))))

;; transport : tree rename wraps (F's result name, for a claim's `ret`, or #f) -> text or #f
;; A wrapped name gets a guard: G's result in F's Ok/Some, `r is Ok ==> (P[r.unwrap()])`;
;; G's ghost result in F's Tracked<Option<..>>, `p@ is Some ==> (P[p@->0])`, where G's text
;; can only use it through its view (`g@`).  G's parameter that is a field of
;; F's (field VAR SUFFIX MUT?): `old(g)`, `final(g)`, `*final(g)` become
;; `old(VAR)SUFFIX`, `final(VAR)SUFFIX`; a bare `g` is `final(VAR)SUFFIX` when
;; VAR is F's `&mut` parameter, else `VARSUFFIX`.
(define (transport tree rename wraps ret)
  (define (as-ret v) (if (and ret (equal? v ret)) "ret" v))
  (define (ph v) (format "DROPSPH_~a" v))
  (define (pf g) (format "DROPSPF_~a" g))
  (define plain
    (for/list ([p (in-list rename)])
      (match (cdr p)
        [`(unwrap ,v ,_) (cons (car p) (format "~a.unwrap()" (as-ret v)))]
        [`(some ,v) (cons (car p) (ph v))]
        [`(field ,_ ,_ ,_) (cons (car p) (pf (car p)))]
        [v (cons (car p) (as-ret v))])))
  (define body
    (for/fold ([s (print-tree tree plain)]) ([p (in-list rename)] #:when (and (pair? (cdr p)) (eq? (cadr p) 'field)))
      (match-define `(field ,v ,suf ,fmut) (cdr p))
      (define q (regexp-quote (pf (car p))))
      (and s
           (let* ([s (regexp-replace* (pregexp (format "\\*\\s*(old|final)\\(\\s*~a\\s*\\)" q)) s (lambda (_ k) (format "~a(~a)~a" k v suf)))]
                  [s (regexp-replace* (pregexp (format "\\b(old|final)\\(\\s*~a\\s*\\)" q)) s (lambda (_ k) (format "~a(~a)~a" k v suf)))])
             (regexp-replace* (pregexp q) s (if fmut (format "final(~a)~a" v suf) (string-append v suf)))))))
  (define body2
    (and body
         (for/fold ([s body]) ([w (in-list wraps)] #:when (eq? (car w) 'some))
           (define v (cadr w))
           (define s2 (and s (regexp-replace* (pregexp (format "~a@" (ph v))) s (format "~a@->0" v))))
           (and s2 (not (regexp-match? (regexp (ph v)) s2)) s2))))
  (and body2
       (for/fold ([s body2]) ([w (in-list (reverse wraps))])
         (match w
           [`(unwrap ,v ,ctor) (format "~a is ~a ==> (~a)" (as-ret v) ctor s)]
           [`(some ,v) (format "~a@ is Some ==> (~a)" v s)]))))

;; "Tracked<VmIoOwner>" -> "Tracked<Option<VmIoOwner>>"
(define (tracked-option t)
  (if (string-prefix? t "Tracked<")
      (string-append "Tracked<Option<" (substring t 8) ">")
      (string-append "Option<" t ">")))

;; "Result<VmWriter<'a,Infallible>,Error>" with "VmWriter<'a,Infallible>" -> "Ok"; Option -> "Some"; else #f
(define (wrapped-in outer inner)
  (cond [(and (string-prefix? outer "Result<") (string-prefix? (substring outer 7) (string-append inner ","))) "Ok"]
        [(and (string-prefix? outer "Result<") (equal? (substring outer 7) (string-append inner ">"))) "Ok"]
        [(and (string-prefix? outer "Option<") (equal? (substring outer 7) (string-append inner ">"))) "Some"]
        [else #f]))

;; ================================================================ step 2: into F's ensures, and back

;; insert-candidates : (line ...) ((LINE COL ID TEXT) ...) -> (line ...)
;; Each candidate after the clause that ends at LINE:COL (1-based, exclusive: an
;; INSERT-AFTER span's end), as ",\n<indent>/*DROP:ID*/ TEXT", so that a line of
;; Verus's errors names the candidate.  Several after one clause: in ID order.
(define (insert-candidates lines ins)
  (define v (list->vector lines))
  (define (later? a b) ; bottom-up, right to left: earlier positions stay valid
    (match* (a b)
      [((list la ca ia _) (list lb cb ib _))
       (or (> la lb) (and (= la lb) (or (> ca cb) (and (= ca cb) (> ia ib)))))]))
  (for ([i (in-list (sort ins later?))])
    (match-define (list l col id text) i)
    (define s (vector-ref v (sub1 l)))
    (define at (sub1 col))
    (define indent (car (regexp-match #px"^\\s*" s)))
    (vector-set! v (sub1 l)
                 (string-append (substring s 0 at) ",\n" indent "/*DROP:" (number->string id) "*/ " text (substring s at))))
  (append* (for/list ([s (in-vector v)]) (string-split s "\n" #:trim? #f))))

;; blame : (error ...) (file line -> string) verified? -> (values ((KIND ID ...) ...) (error ...))
;; errors as parse-verus gives them (MESSAGE FILE LINE CALLEE LOCS ..); line-of
;; reads the copy as the round left it.  An error blames every candidate whose
;; /*DROP:ID*/ line is one of its locations; KIND is unproved (a postcondition
;; not satisfied), or compile when Verus did not get to verify (verified? #f),
;; else other.  An rlimit error names no candidate (it is in a body: the added
;; facts made its proof slower): it blames, as rlimit, the candidates in the
;; nearest ensures above it, the enclosing function's (or the previous one's,
;; when that function has none: a candidate too many is only lost, the next
;; round verifies the rest).  The second value: errors that name no candidate.
(define drop-rx #px"/\\*DROP:([0-9]+)\\*/")
(define (blame errors line-of verified?)
  (define by-kind (make-hash))
  (define (ids-above file l)
    (let up ([l l])
      (cond [(< l 1) '()]
            [(regexp-match? drop-rx (line-of file l))
             (let block ([l l] [acc '()])
               (define m (and (>= l 1) (regexp-match drop-rx (line-of file l))))
               (if m (block (sub1 l) (cons (string->number (cadr m)) acc)) acc))]
            [else (up (sub1 l))])))
  (define unblamed
    (for/fold ([un '()]) ([e (in-list errors)])
      (define rlimit? (regexp-match? #px"rlimit|resource limit" (car e)))
      (define direct
        (remove-duplicates
         (for*/list ([loc (in-list (list-ref e 4))]
                     [m (in-value (regexp-match drop-rx (line-of (car loc) (cdr loc))))]
                     #:when m)
           (string->number (cadr m)))))
      (define ids (if (and (null? direct) rlimit? (list-ref e 1)) (ids-above (list-ref e 1) (list-ref e 2)) direct))
      (define kind (cond [(regexp-match? #px"postcondition not satisfied" (car e)) 'unproved]
                         [rlimit? 'rlimit]
                         [(not verified?) 'compile]
                         [else 'other]))
      (for ([i (in-list ids)]) (hash-update! by-kind kind (lambda (s) (if (memv i s) s (cons i s))) '()))
      (if (null? ids) (cons e un) un)))
  (values (for/list ([k (in-list '(compile unproved rlimit other))] #:when (hash-ref by-kind k #f))
            (cons k (sort (hash-ref by-kind k) <)))
          (reverse unblamed)))
