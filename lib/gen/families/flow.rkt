#lang racket/base
;; flow_<F>_<G>_<I>: the output of F (its result, unwrapped from
;; Result/Option, or its ghost result) is argument I of G; G's requires are
;; asserted clause by clause before the call (结论19). Does F's ensures give
;; what G needs about F's output?
(require racket/list racket/match "../../model/api.rkt" "../../base/forms.rkt" "../../model/spec.rkt" "../../model/template.rkt" "../probe.rkt" "common.rkt")
(provide flow-client)

;; share?: G's tracked parameters are F's tracked parameters, or F's ghost
;; result, of the same type (up to references), each used once, when there
;; are such: a real caller passes the one `regions` to both calls, and the
;; owner F returns along with its result.  Fresh ones would be other objects,
;; and G's requires relating them to the flowing value would fail for that
;; reason alone.  Among several of the type: the one with G's parameter's
;; name, else F's ghost result, else none (a reader's owner is not to be
;; passed as a writer's).  When the ghost result is what flows, F's result is
;; shared the same way with G's exec parameters.  The rest are fresh.
;; Returns #f when a fresh tracked parameter is tied to the flowing value.
;; roles: the call knowledge's roles; a value is shared only with a parameter
;; whose role, when both are known, is its own (`reader-owner` not as a
;; `writer-owner`, the list's owner not as another list's)
;; assumed: api -> its assumptions ((tmpl PIECE ...) ...), from the call knowledge:
;; F's are the client's requires (F is called as in its probe, its parameters
;; are the client's); G's too, renamed to the arguments G is called with, when
;; every parameter of G they name is passed a client parameter (not the
;; flowing value, which does not exist at entry).
(define (flow-client table f out g p i share? [roles '()] #:assumed [assumed (lambda (a) '())])
  (match-define (list kind t) out)
  (define name (safe (format "flow_~a_~a_~a" (api-name f) (api-name g) i)))
  ;; f is called as in its probe: its parameters are the client's
  (define fprobe (probe-client f))
  (define fparams (form-ref fprobe 'params))
  (define fbody (form-ref fprobe 'body))
  (define fcall (match (car fbody) [`(let ,_ ,c) c] [`(do ,c) c]))
  ;; g's type parameters: bound by the flowing value, the rest renamed
  (define gvars (map car (api-generics g)))
  (define sigma (match-type (strip-ref (param-type p)) (strip-ref t) gvars '()))
  ;; lifetimes are kept: a table writes every lifetime as the one `'a`
  ;; (结论34), so F's `VmWriter<'a>` is G's
  (define fresh (for/list ([v (in-list gvars)] #:unless (assq v sigma))
                  (cons v (if (regexp-match? #rx"^'" (symbol->string v))
                              v
                              (string->symbol (format "~a_g" v))))))
  (define gsubst (append sigma fresh))
  (define gps (append (api-params g) (api-ghost-params g)))
  (define (gname q) (string->symbol (format "~a_g" (param-name q))))
  (define value (match kind
                  ['gret (cadr (memq '-> fcall))]       ; as the probe names it
                  [(or 'ok 'some) 'x] ['ret 'r]))
  ;; what can be shared: (NAME TYPE gret?) for F's tracked parameters and,
  ;; unless it is the flowing value, F's ghost result.  A ghost result
  ;; `Option<T>` after Ok/Some is the T inside, taken out by the provider
  ;; Option::tracked_unwrap (when the table has it) only if it is shared.
  (define fgr (and (api-ghost-ret f) (cadr (memq '-> fcall))))
  (define unwrap? (and fgr (memq kind '(ok some)) (api-ref table 'Option::tracked_unwrap)
                       (match (cadr (api-ghost-ret f)) [`(Option ,_) #t] [_ #f])))
  (define fgret (and fgr (not (eq? kind 'gret))
                     (if unwrap?
                         (list 'gro (cadr (cadr (api-ghost-ret f))) #t 'tracked)
                         (list fgr (cadr (api-ghost-ret f)) #t 'tracked))))
  ;; Conversely, when the ghost result flows, F's result goes with it (the
  ;; frame with its owner): (NAME TYPE #t exec), inside Ok/Some when F's
  ;; result is a Result/Option.
  (define-values (fres unwrap-ret)
    (match (and (eq? kind 'gret) (api-ret f))
      [#f (values #f #f)]
      [`(Result ,u ,_) (values (list 'x u #t 'exec) 'Ok)]
      [`(Option ,u) (values (list 'x u #t 'exec) 'Some)]
      [u (values (list 'r u #t 'exec) #f)]))
  ;; and the object F worked on (F's `&mut` exec parameter: the writer F filled),
  ;; with the flag of the produced values: shared only where G's requires tie it to
  ;; the flowing value (the owner F returned for it), design.md 3.5
  (define fobjs
    (for/list ([fp (in-list fparams)] #:when (and (eq? (cadr fp) 'exec) (match (caddr fp) [`(&mut ,_) #t] [_ #f])))
      (list (car fp) (caddr fp) #t 'exec)))
  (define sharable
    (append (if fgret (list fgret) '())
            (if fres (list fres) '())
            fobjs
            (for/list ([fp (in-list fparams)] #:when (eq? (cadr fp) 'tracked)) (list (car fp) (caddr fp) #f 'tracked))))
  ;; all the roles of a parameter (or ret, gret): it may have several (enum.rkt's param-roles)
  (define (role-of api x)
    (let ([rs (for/list ([r (in-list roles)] #:when (and (eq? (car r) (api-name api)) (eq? (cadr r) x))) (caddr r))])
      (and (pair? rs) rs)))
  ;; the role of a sharable value: F's parameter's, or of F's ghost result / result
  (define (value-role c)
    (cond [(memq (car c) '(gro x)) (role-of f (if (eq? (car c) 'x) 'ret 'gret))]
          [(eq? (car c) fgr) (role-of f 'gret)]
          [(eq? (car c) 'r) (role-of f 'ret)]
          [else (role-of f (car c))]))
  (define (pick q free)
    (define want (strip-ref (subst-type (param-type q) gsubst)))
    (define qrole (role-of g (param-name q)))
    (define cands (filter (lambda (c) (and (eq? (cadddr c) (param-mode q)) (equal? (strip-ref (cadr c)) want)
                                           (let ([vr (value-role c)]) (or (not qrole) (not vr) (and (ormap (lambda (r) (memq r vr)) qrole) #t)))))
                          free))
    ;; F's result or ghost result goes only where G's requires tie it to
    ;; the flowing argument (`writer.wf(owner_w)`), not to `owner_r`
    (define related?
      (for/or ([r (in-list (api-requires g))])
        (define vs (expr-vars r))
        (and (memq (param-name p) vs) (memq (param-name q) vs) #t)))
    (define ok (filter (lambda (c) (or (not (caddr c)) related?)) cands))
    (or (findf (lambda (c) (eq? (car c) (local (param-name q)))) ok)
        (findf caddr ok)
        (and (= (length ok) 1) (car ok))))
  (define shared                        ; ((j . NAME) ...)
    (if share?
        (let loop ([qs gps] [j 0] [free sharable] [acc '()])
          (cond
            [(null? qs) acc]
            [else
             (define q (car qs))
             (define c (and (not (= j i)) (memq (param-mode q) '(tracked exec)) (pick q free)))
             (if c
                 (loop (cdr qs) (add1 j) (remq c free) (cons (cons j (car c)) acc))
                 (loop (cdr qs) (add1 j) free acc))]))
        '()))
  ;; A parameter of G left fresh that G's requires tie to the flowing value
  ;; (`x.0.invariants(*owner_g, ..)` for a cursor with an owner no call produced;
  ;; `self_g.wf(gr)`, a new writer with the owner F returned): the clause cannot
  ;; hold, and the client would fail for that alone.  No such client (#f), as
  ;; consistent-fresh does in protocols.  An exec one too when what flows is F's
  ;; ghost result, an owner (2026-11-18, design.md 3.5); not when it is a value:
  ;; `split(offset)` with `offset <= self.size()` asks for an offset chosen for the
  ;; segment, as a caller does (five such flow clients verified).
  (define fresh-tied?
    (for/or ([q (in-list gps)] [j (in-naturals)]
             #:when (and (not (= j i)) (not (assv j shared))
                         (or (eq? (param-mode q) 'tracked) (and (eq? (param-mode q) 'exec) (eq? kind 'gret)))))
      (for/or ([r (in-list (api-requires g))])
        (define vs (expr-vars r))
        (and (memq (param-name p) vs) (memq (param-name q) vs) #t))))
  (define gparams
    (for/list ([q (in-list gps)] [j (in-naturals)] #:unless (or (= j i) (assv j shared)))
      (list (gname q) (match (param-mode q) ['spec 'ghost] [m m]) (subst-type (param-type q) gsubst))))
  (define gargs-all (for/list ([q (in-list gps)] [j (in-naturals)])
                      (cond [(= j i) value] [(assv j shared) => cdr] [else (gname q)])))
  (define-values (gargs gghost) (split-at gargs-all (length (api-params g))))
  (define gtypes (for/list ([v (in-list (free-generics g))]) (list v (cdr (assq v gsubst)))))
  (define gcall `(call ,(api-name g) ,gargs ,gghost ,@(if (api-ghost-ret g) '(-> gr_g) '())
                       ,@(if (null? gtypes) '() `((types ,@gtypes)))))
  (define unwrap (if (and unwrap? (memq 'gro (map cdr shared)))
                     `((let gro (call Option::tracked_unwrap (,fgr) ())))
                     '()))
  (define then `(,@unwrap
                 (assert-requires ,(api-name g) ,gargs ,gghost ,@(if (null? gtypes) (quote ()) `((types ,@gtypes))))
                 ,(if (api-ret g) `(let w ,gcall) `(do ,gcall))))
  (define body
    (match kind
      ['gret
       (if (and unwrap-ret (memq 'x (map cdr shared)))
           `((let r ,fcall) (if-let (,unwrap-ret x) r ,@then))
           `((let r ,fcall) ,@then))]
      ['ret `((let r ,fcall) ,@then)]
      ['ok `((let r ,fcall) (if-let (Ok x) r ,@then))]
      ['some `((let r ,fcall) (if-let (Some x) r ,@then))]))
  ;; G's assumptions, with its parameters' names (as `local` writes them:
  ;; self_) replaced by the client's arguments
  (define client-params (append (map car fparams) (map car gparams)))
  (define g-renaming
    (for/list ([q (in-list gps)] [a (in-list gargs-all)])
      (cons (symbol->string (local (param-name q))) a)))
  ;; (templates: renamed on their holes, all at once, model/template.rkt)
  (define g-assumed
    (for*/list ([cl (in-list (assumed g))]
                [named (in-value (filter (lambda (r) (memq (string->symbol (car r)) (template-vars cl))) g-renaming))]
                #:when (andmap (lambda (r) (memq (cdr r) client-params)) named))
      (template-map cl (lambda (x) (cond [(assoc (symbol->string x) named) => cdr] [else x])))))
  (define requires
    (remove-duplicates (append (assumed f) g-assumed)))
  (and (not fresh-tied?)
  `(client ,name
           (source ,(format "flow: the ~a of ~a as argument ~a of ~a" kind (api-name f) i (api-name g)))
           (type-params ,@(remove-duplicates (append (form-ref fprobe 'type-params) (map cdr fresh))))
           (params ,@fparams ,@gparams)
           (allow-open)
           (body ,@body)
           ,@(if (null? requires) '() `((requires ,@requires))))))
