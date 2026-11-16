#lang racket/base
;; Spec-level read and write sets (docs/enumeration.md 8.3, 9): does a call H,
;; taking a variable by `&mut`, possibly change what a requires clause of G
;; reads of it?  Syntax only, never the logic (Verus decides): an
;; over-approximation of interference, used only to leave out a client that
;; cannot ask anything (8.3: of 461 mutator pairs, the 130 found harmless had
;; no failure), never to say that one fails.
;;
;; reads: G's clause (the table's requires tree, VIR's form: `(method R NAME
;;   ARG ..)`, `(call F ARG ..)`, `(field E F)`, `(old E)`, `(deref E)`) reads,
;;   of a variable v, the access paths it applies a predicate at: for
;;   `owner.value().is_frame()` the path (value is_frame); for v an argument
;;   of a predicate (`self.wf_region(*owner, ..)`, `f(.., owner)`) the path
;;   (wf_region) and (f).
;; gives: H's ensures (the source's trees, (source (ensures (c SPAN TEXT
;;   TREE ..)))), on a branch of H's result (ok: unconditional and under
;;   `r is Some/Ok ==>`; err: unconditional and under `r is None/Err ==>`), give
;;   a path of v when a conjunct applies it to `final(v)` (`final(v).P(..)`,
;;   `P(.., final(v), ..)`, as receiver chain or argument), or frames it
;;   (`final(v).P(..) == old(v).P(..)`, a field path likewise); `*final(v) ==
;;   *old(v)` frames all of v.  A comparison or a disjunction gives nothing
;;   (it may change the value: `final(self).remain_spec() == old(..) - n`).
;; Known approximation: the predicate's arguments are not compared, only its
;; name and the path to it.
(require racket/list racket/match racket/string "../model/api.rkt" "../base/forms.rkt")
(provide clause-reads h-covers? interferes? source-ensures source-ret-name
         source-ghost-out clause-writes requires-reads path-match?)

;; ---------------------------------------------------------------- reads (VIR's form)
(define (sym->name s) (let ([str (if (symbol? s) (symbol->string s) s)]) (last (string-split str "::"))))

;; the variable and the path of an access, or #f: x, x.f, x.m(), old(x), *x
(define (access e)
  (match e
    [(? symbol?) (cons e '())]
    [`(old ,x) (access x)] [`(deref ,x) (access x)]
    [`(field ,x ,f) (let ([a (access x)]) (and a (cons (car a) (append (cdr a) (list (sym->name f))))))]
    [`(method ,r ,name) (let ([a (access r)]) (and a (cons (car a) (append (cdr a) (list (sym->name name))))))]
    [_ #f]))

;; clause-reads : requires tree -> ((VAR PATH RECV) ...): RECV #f for a
;; receiver chain or a spec function's argument, else the receiver's variable
;; (or 'other) for v an argument of a method: `self.wf_region(*owner, ..)`
;; reads owner at (wf_region) with receiver self
(define (clause-reads c)
  (remove-duplicates
   (let walk ([e c])
     (match e
       [`(method ,r ,name ,args ...)
        (define ra (access r))
        (define self (if ra (list (list (car ra) (append (cdr ra) (list (sym->name name))) #f)) '()))
        (define as (for*/list ([x args] [a (in-value (access x))] #:when a)
                     (list (car a) (list (sym->name name)) (if (and ra (null? (cdr ra))) (car ra) 'other))))
        (append self as (if ra '() (walk r)) (append-map walk args))]
       [`(call ,f ,args ...)
        (append (for*/list ([x args] [a (in-value (access x))] #:when a) (list (car a) (list (sym->name f)) #f))
                (append-map walk args))]
       [(? pair?) (append-map walk (cdr e))]
       [_ '()]))))

;; ---------------------------------------------------------------- gives (the source's trees)
(define (source-of a) (let ([s (form-ref a 'source #f)]) (if (list? s) s '())))
(define (source-ensures a)
  (define e (assq 'ensures (filter pair? (source-of a))))
  (if e (for/list ([c (cdr e)] #:when (and (pair? c) (eq? (car c) 'c) (> (length c) 3))) (cadddr c)) '()))
(define (source-ret-name a)
  (define r (assq 'ret (filter pair? (source-of a))))
  (and r (pair? (cdr r)) (string? (cadr r)) (cadr r)))

(define (strip e) (match e [`(paren ,x) (strip x)] [_ e]))
;; the conjuncts of an ensures clause that hold on a branch ('ok or 'err) of the result named ret
(define (conjuncts e branch ret)
  (define (guard g) ; 'ok, 'err, or #f (some other condition)
    (match (strip g)
      [`(is (path ,(== ret)) ,(or "Some" "Ok")) 'ok]
      [`(is (path ,(== ret)) ,(or "None" "Err")) 'err]
      [_ #f]))
  ;; branch 'any: the caller does not look at the result; only what holds either way
  (let loop ([e (strip e)])
    (match e
      [`(big-and ,xs ...) (append-map loop xs)]
      [`(op "&&" ,a ,b) (append (loop a) (loop b))]
      [`(op "==>" ,g ,b) (if (and (not (eq? branch 'any)) (eq? (guard g) branch)) (loop b) '())]
      [`(matches (path ,(== ret)) (pat ,p ,_ ...) "==>" ,b)
       (if (and (not (eq? branch 'any)) (eq? branch (if (regexp-match? #rx"^(Some|Ok)" p) 'ok 'err))) (loop b) '())]
      [`(matches ,_ ...) '()]
      [_ (list e)])))

;; a source access: (VAR-STRING WHEN . PATH), WHEN final or old, or #f
(define (saccess e)
  (match (strip e)
    [`(final (path ,v)) (list v 'final)]
    [`(call (path "old") (path ,v)) (list v 'old)]
    [`(deref ,x) (saccess x)]
    [`(field ,x ,f) (let ([a (saccess x)]) (and a (append a (list f))))]
    [`(method ,r ,name #f) (let ([a (saccess r)]) (and a (append a (list name))))]
    [_ #f]))

;; gives : H's ensures, branch, ret, the variable (H's parameter name, a string)
;;   -> ((PATH RECV) ...) or 'all; RECV #f, or for v an argument of a method
;;   the receiver: H's parameter (a string) as final(w), else 'other
(define (gives ens branch ret v)
  (define paths '())
  (define all? #f)
  (for* ([e ens] [c (conjuncts e branch ret)])
    (match (strip c)
      [`(op "==" ,l ,r)
       (define la (saccess l)) (define ra (saccess r))
       (when (and la ra (equal? (car la) v) (equal? (car ra) v) (eq? (cadr la) 'final) (eq? (cadr ra) 'old)
                  (equal? (cddr la) (cddr ra)))
         (if (null? (cddr la)) (set! all? #t) (set! paths (cons (list (cddr la) #f) paths))))]
      [`(op ,_ ...) (void)]
      [`(method ,r ,name ,_ ,args ...)
       (define a (saccess r))
       (when (and a (equal? (car a) v) (eq? (cadr a) 'final)) (set! paths (cons (list (append (cddr a) (list name)) #f) paths)))
       (define recv (if (and a (eq? (cadr a) 'final) (null? (cddr a))) (car a) 'other))
       (for ([x args])
         (define b (saccess x))
         (when (and b (equal? (car b) v) (eq? (cadr b) 'final)) (set! paths (cons (list (list name) recv) paths))))]
      [`(call (path ,f) ,args ...)
       (for ([x args])
         (define b (saccess x))
         (when (and b (equal? (car b) v) (eq? (cadr b) 'final)) (set! paths (cons (list (list (last (string-split f "::"))) #f) paths))))]
      [_ (void)]))
  (if all? 'all paths))

;; ---------------------------------------------------------------- def-use (docs/enumeration.md 15)
;; What an ensures clause writes and what a requires clause reads, by access path, for the
;; all-defs rule of goal-plan (R4): an output of P whose ensures some API's requires reads.
;; Unlike clause-reads (interference: only the predicate applications), every access counts:
;; a field compared (`self.ghost_id == owner.id`) is read at its path, a predicate applied at
;; x.p (`self.wf(*owner)`) may read anything under x.p.  Either way a write and a read match
;; when one path is a prefix of the other: an over-approximation, used only to choose a reader.

;; the source's ghost output name (`with -> NAME: Tracked<..>`), or #f
(define (source-ghost-out a)
  (define w (assq 'with-out (filter pair? (source-of a))))
  (and w (pair? (cdr w)) (match (cadr w) [`(p ,(? string? n) ,_ ...) n] [_ #f])))

;; clause-writes : source tree, result name, ghost output name -> ((KIND VAR PATH) ...),
;; KIND ret (the result; a leading `unwrap` dropped), gret (the ghost output) or final
;; (final(v), v a parameter); PATH the field and method names applied to it
(define (clause-writes tree ret gout)
  (define (acc e)
    (match e
      [`(paren ,x) (acc x)]
      [`(path ,(== ret)) (list 'ret ret '())]
      [`(path ,(? (lambda (s) (and gout (equal? s gout))))) (list 'gret gout '())]
      [`(view ,x) (acc x)]
      [`(deref ,x) (acc x)]
      [`(final (path ,v)) (list 'final v '())]
      [`(field ,x ,f) (let ([a (acc x)]) (and a (list (car a) (cadr a) (append (caddr a) (list f)))))]
      [`(method ,r ,name ,_ ,_ ...)
       (let ([a (acc r)])
         (and a (list (car a) (cadr a)
                      (if (and (eq? (car a) 'ret) (null? (caddr a)) (equal? name "unwrap")) '() (append (caddr a) (list name))))))]
      [_ #f]))
  (remove-duplicates
   (let walk ([e tree])
     (define a (acc e))
     (cond [a (list a)] [(pair? e) (append-map walk e)] [else '()]))))

;; requires-reads : requires tree (VIR's form) -> ((VAR PATH) ...), every maximal access
(define (requires-reads c)
  (define (acc e)
    (match e
      [(? symbol?) (cons e '())]
      [`(old ,x) (acc x)] [`(deref ,x) (acc x)] [`(final ,x) (acc x)]
      [`(field ,x ,f) (let ([a (acc x)]) (and a (cons (car a) (append (cdr a) (list (sym->name f))))))]
      [_ #f]))
  (remove-duplicates
   (let walk ([e c])
     (define a (and (pair? e) (acc e)))
     (cond [a (list (list (car a) (cdr a)))]
           [(pair? e) (append-map walk (match e [`(method ,r ,_ ,as ...) (cons r as)] [`(call ,_ ,as ...) as] [_ (cdr e)]))]
           [else '()]))))

(define (path-match? wp rp) (let ([n (min (length wp) (length rp))]) (equal? (take wp n) (take rp n))))

;; h-covers? : H, H's parameter name (symbol), branch, path -> boolean: after H
;; on the branch, H's ensures give or frame the path of the variable (a framed
;; prefix frames the path)
;; h-recv: the receiver H must name for an argument-read: H's parameter
;; shared with G's receiver (a string), #f for none
(define (h-covers? h hv branch path h-recv)
  (define (str x) (if (symbol? x) (symbol->string x) x))
  (define g (gives (source-ensures h) branch (or (source-ret-name h) "r") (str hv)))
  (or (eq? g 'all)
      (for/or ([pr g])
        (match-define (list p recv) pr)
        (and (or (not recv) (and h-recv (equal? recv (str h-recv))))
             (if recv (equal? p path) (and (<= (length p) (length path)) (equal? p (take path (length p)))))))))

;; interferes? : H G branch ((G-PARAM . H-PARAM) ...) -> the numbers of G's
;; clauses H may change something of (a shared variable G's clause reads at a
;; path H's ensures neither give nor frame on the branch), '() if none.
;; branch: 'ok, 'err (G on that branch of H's result), 'any (G either way).
(define (interferes? h g branch shared)
  (for/list ([c (api-requires g)] [i (in-naturals 1)]
             #:when (for/or ([rd (clause-reads c)])
                      (match-define (list v path recv) rd)
                      (define hv (assq v shared))
                      (and hv
                           (let ([hr (and recv (symbol? recv) (let ([x (assq recv shared)]) (and x (cdr x))))])
                             ;; an argument-read whose receiver H did not take ('none): only a frame of all of v covers it
                             (not (h-covers? h (cdr hv) branch path (and recv (or hr 'none))))))))
    i))
