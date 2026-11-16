#lang racket/base
;; Probing the API table against vostd (design.md 3.2): the probe client
;; of every entry (../gen/probe.rkt), run, and read as a fact per entry:
;;   (api NAME ok)
;;   (api NAME compile-error ERROR ...)        the declared signature does not match
;;   (api NAME requires-weaker ERROR ...)      a requires clause of the source is missing
;;   (api NAME ensures-not-given ERROR ...)    the declared ensures do not follow
;;   (api NAME vacuous CAUSE)                  the path is infeasible; CAUSE (see vacuity-causes):
;;                                             requires | after-call | unknown
;;   (api NAME ill-formed FACT)                the entry itself does not check (DSL level)
;; A table whose requires are stronger than the source's is not detected.
(require racket/list racket/match "../model/api.rkt" "../vostd/run.rkt" "../model/results.rkt"
         "../check/client.rkt" "../base/forms.rkt" "../gen/probe.rkt")
(provide probe-table probe-client none-variants)

(define (safe-name s)
  (string->symbol (regexp-replace* #rx"[^A-Za-z0-9_]" (format "~a" s) "_")))

;; The two causes of a vacuous probe.  The vacuity assertion comes after the
;; call, so it holds when the declared requires contradict each other, and
;; also when the callee's ensures, under them, give false (unsatisfiable
;; requires that only the callee can see through, or trusted code that is too
;; strong).  Each vacuous probe is run again with the same assumptions (the
;; requires lifted from its call, now written out) and no call:
;;   requires     still vacuous: the declared requires contradict each other
;;   after-call   no longer vacuous: the call brings in the contradiction
;;   unknown      the variant gave no verdict
;; vacuity-causes : target-file table-file table (probe ...) out-dir -> hash name -> cause
(define (vacuity-causes target-file table-file table probes out-dir)
  (define variants
    (for*/list ([p (in-list probes)]
                [plan (in-value (check-client table p))]
                #:unless (eq? (car plan) 'ill-formed))
      (cons (cadr p)
            `(client ,(safe-name (format "~a_no_call" (cadr p)))
                     (source ,(format "probe ~a without its call" (cadr p)))
                     (type-params ,@(form-ref p 'type-params))
                     (params ,@(form-ref p 'params))
                     (requires ,@(form-ref plan 'requires))
                     (allow-open)
                     (body)))))
  (cond
    [(null? variants) (hash)]
    [else
     (define results (run-clients target-file table-file (map cdr variants) out-dir))
     (for/hash ([v (in-list variants)])
       (values (car v)
               (match (result-of results (cadr (cdr v)))
                 [`(client ,_ verified (vacuous ,_ ...)) 'requires]
                 [`(client ,_ verified) 'after-call]
                 [_ 'unknown])))]))

;; None for a tracked Option parameter (the generator may pass it, enum.rkt):
;; the requires with None, lifted as a client's are, may be unsatisfiable in a
;; way only Verus sees (`raw_item_well_formed((paddr, level, prop,
;; Tracked(None)))` asks for `perm@ is Some` inside the spec function; enum's
;; none-forces? sees only `p is Some` written in the clause).  A client that
;; passes it assumes false from there on: every path after it is vacuous (27
;; such vm_space chains, 2026-11-12).  For each such parameter of an entry
;; whose probe is ok, the probe with None for it, without the call and with
;; the requires lifted from the call written out; vacuous gives
;;   (none-vacuous NAME PARAM)
;; none-vacuous : target-file table-file table (api ...) out-dir -> (fact ...)
(define (none-vacuous target-file table-file table apis out-dir)
  (define variants (none-variants table apis))
  (cond
    [(null? variants) '()]
    [else
     (define results (run-clients target-file table-file (map caddr variants) out-dir))
     (for/list ([v (in-list variants)]
                #:when (match (result-of results (cadr (caddr v))) [`(client ,_ verified (vacuous ,_ ...)) #t] [_ #f]))
       `(none-vacuous ,(car v) ,(cadr v)))]))

;; none-variants : table (api ...) -> ((API-NAME PARAM client) ...)
(define (none-variants table apis)
    (for*/list ([api (in-list apis)]
                [p (in-list (append (api-params api) (api-ghost-params api)))]
                #:when (and (eq? (param-mode p) 'tracked) (match (param-type p) [`(Option ,_) #t] [_ #f]))
                [pc (in-value (probe-client api))]
                [x (in-value (local (param-name p)))]
                [call-client (in-value (none-for pc x))]
                [plan (in-value (check-client table call-client))]
                #:unless (eq? (car plan) 'ill-formed))
      (list (api-name api) (param-name p)
            `(client ,(safe-name (format "~a_none_~a" (cadr pc) (param-name p)))
                     (source ,(format "probe ~a with None for ~a, without its call" (api-name api) (param-name p)))
                     (type-params ,@(form-ref pc 'type-params))
                     (params ,@(form-ref call-client 'params))
                     (requires ,@(form-ref plan 'requires))
                     (allow-open)
                     (body)))))

;; the probe client with (none) for its parameter x: x is no longer a parameter,
;; the call passes None, and nothing follows the call
(define (none-for pc x)
  (define (arg a) (if (eq? a x) '(none) a))
  (for/list ([f (in-list pc)])
    (match f
      [`(params ,ps ...) `(params ,@(filter (lambda (p) (not (eq? (car p) x))) ps))]
      [`(body ,stmts ...)
       `(body ,@(for/list ([s (in-list stmts)]
                           #:when (match s [`(,(or 'let 'do) ,_ ...) #t] [_ #f]))
                  (match s
                    [`(let ,r (call ,n ,as ,gs ,more ...)) `(let ,r (call ,n ,(map arg as) ,(map arg gs) ,@more))]
                    [`(do (call ,n ,as ,gs ,more ...)) `(do (call ,n ,(map arg as) ,(map arg gs) ,@more))]
                    [_ s])))]
      [_ f])))

(define (local x) (if (eq? x 'self) 'self_ x))

;; probe-table : target-file table-file out-dir -> (fact ...)
(define (probe-table target-file table-file out-dir)
  (define table (read-api-table table-file))
  (define apis (map (lambda (n) (api-ref table n)) (table-names table)))
  (define probes (map probe-client apis))
  (define results (run-clients target-file table-file probes out-dir))
  (define vacuous
    (for/list ([p (in-list probes)]
               #:when (match (result-of results (cadr p)) [`(client ,_ verified (vacuous ,_ ...)) #t] [_ #f]))
      p))
  (define causes (vacuity-causes target-file table-file table vacuous (build-path out-dir "no-call")))
  (define ok-apis
    (for/list ([api (in-list apis)] [p (in-list probes)]
               #:when (match (result-of results (cadr p)) [`(client ,_ verified) #t] [_ #f]))
      api))
  (append (probe-facts apis probes results causes)
          (none-vacuous target-file table-file table ok-apis (build-path out-dir "none"))))

(define (probe-facts apis probes results causes)
  (for/list ([api (in-list apis)] [p (in-list probes)])
    (define r (result-of results (cadr p)))
    (define n (api-name api))
    (match r
      [`(client ,_ ill-formed ,more ...) `(api ,n ill-formed ,@more)]
      [`(client ,_ compile-error ,errs ...) `(api ,n compile-error ,@errs)]
      [`(client ,_ verified (vacuous ,_ ...)) `(api ,n vacuous ,(hash-ref causes (cadr p) 'unknown))]
      [`(client ,_ verified) `(api ,n ok)]
      [`(client ,_ failed ,_ ...)
       (define-values (ens req)
         (partition (lambda (e) (regexp-match? #rx"declared ensures" (error-text e))) (result-errors r)))
       `(api ,n ,@(if (pair? req) `(requires-weaker ,@req) '()) ,@(if (pair? ens) `(ensures-not-given ,@ens) '()))]
      [`(client ,_ ,status ,more ...) `(api ,n ,status ,@more)]
      [_ `(api ,n no-result)])))
