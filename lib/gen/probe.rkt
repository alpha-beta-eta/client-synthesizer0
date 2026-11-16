#lang racket/base
;; The probe client of an API table entry (design.md, 结论31); probing
;; the table against vostd is ../analysis/probe.rkt.
;;
;; For each entry a probe client: parameters of exactly the declared types
;; and modes, so the requires lifted from the entry (结论8) are its
;; assumptions; one call (a spec function: a ghost binding); for a lemma, its
;; declared ensures asserted after the call.  Verus decides:
;;   (api NAME ok)
;;   (api NAME compile-error ERROR ...)        the declared signature does not match
;;   (api NAME requires-weaker ERROR ...)      a requires clause of the source is missing
;;   (api NAME ensures-not-given ERROR ...)    the declared ensures do not follow
;;   (api NAME vacuous CAUSE)                  the path is infeasible: the declared requires
;;                                             contradict each other, or the call brings in
;;                                             the contradiction (../analysis/probe.rkt)
;;   (api NAME ill-formed FACT)                the entry itself does not check (DSL level)
;; A table whose requires are stronger than the source's is not detected.
(require racket/list racket/match racket/string "../model/api.rkt" "../base/forms.rkt")
(provide probe-client)

(define (safe-name s)
  (string->symbol (regexp-replace* #rx"[^A-Za-z0-9_]" (format "~a" s) "_")))

(define (local x) (if (eq? x 'self) 'self_ x))

;; probe-client : api -> client
(define (probe-client api)
  (define name (safe-name (format "probe_~a" (api-name api))))
  (define ps (append (api-params api) (api-ghost-params api)))
  (define params
    (for/list ([p (in-list ps)])
      (list (local (param-name p))
            (match (param-mode p) ['spec 'ghost] [m m])
            (param-type p))))
  (define (arg p) (local (param-name p)))
  (define binding (for/list ([p (in-list ps)]) (cons (param-name p) (local (param-name p)))))
  (define types (for/list ([g (in-list (api-generics api))]
                           #:unless (for/or ([p (in-list ps)]) (mentions? (param-type p) (car g))))
                  (list (car g) (car g))))
  ;; the results are named r and gr, unless a parameter is
  (define (fresh x) (if (memq x (map arg ps)) (fresh (string->symbol (format "~a_" x))) x))
  (define r (fresh 'r))
  (define gr (fresh 'gr))
  (define body
    (match (api-mode api)
      ['spec
       (define args (map arg (api-params api)))
       ;; type parameters no parameter mentions (the method's own, `fill_panic_condition<T>`)
       (define free (let* ([syms (lambda (t) (let loop ([t t]) (if (pair? t) (append-map loop t) (list t))))]
                           ;; one the result mentions is given by the binding's type instead
                           [used (append (append-map (lambda (p) (syms (param-type p))) (api-params api))
                                         (if (api-ret api) (syms (api-ret api)) '()))])
                      (for/list ([g (in-list (api-generics api))] #:unless (memq (car g) used)) (car g))))
       `((ghost ,r ,(match (api-call api)
                      [`(method ,m) `(method ,(car args) ,(if (null? free) m (string->symbol (format "~a::<~a>" m (string-join (map symbol->string free) ", ")))) ,@(cdr args))]
                      ;; {T} in the path is the probe's own T (render.rkt does this for calls)
                      [`(function ,f) `(call ,(string->symbol (regexp-replace* #px"\\{([A-Za-z0-9_]+)\\}" f "\\1")) ,@args)])
                ;; the result's type, written when a type parameter only it mentions
                ;; would not be inferred
                ,@(let* ([syms (lambda (t) (let loop ([t t]) (if (pair? t) (append-map loop t) (list t))))]
                         [in-params (append-map (lambda (p) (syms (param-type p))) (api-params api))]
                         [gens (map car (api-generics api))])
                    (if (and (api-ret api)
                             (for/or ([g (in-list gens)]) (and (memq g (syms (api-ret api))) (not (memq g in-params)))))
                        (list (api-ret api))
                        '()))))]
      [_
       (define call `(call ,(api-name api) ,(map arg (api-params api)) ,(map arg (api-ghost-params api))
                           ,@(if (api-ghost-ret api) `(-> ,gr) '())
                           ,@(if (null? types) '() `((types ,@types)))))
       (append (list (if (api-ret api) `(let ,r ,call) `(do ,call)))
               (for/list ([e (in-list (api-ensures api))])
                 `(assert ,(subst-symbols e binding) "declared ensures")))]))
  `(client ,name
           (source ,(format "probe of the table entry ~a" (api-name api)))
           ;; with the declared bounds: a spec entry is no call, so they would not be inferred (结论6)
           (type-params ,@(for/list ([g (in-list (api-generics api))]) (if (null? (cdr g)) (car g) g)))
           (params ,@params)
           (allow-open)
           (body ,@body)))

(define (mentions? t x) (if (pair? t) (ormap (lambda (y) (mentions? y x)) t) (eq? t x)))

