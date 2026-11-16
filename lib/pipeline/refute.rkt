#lang racket/base
;; Refutation probes of a run's failures (docs/triage.md 3).
;;
;; A failed assertion P says only that the facts at that point do not give P.
;; Two different things look the same: the facts say nothing about P (a
;; missing ensures: a defect candidate), or they say not P (the client asks
;; for something that cannot hold there: a call after an Err that a real
;; caller would not make, a value of the wrong meaning; or the callee's spec
;; says the opposite of what it should).  The probe tells them apart
;; mechanically: the same client with the assertion negated (client.rkt's
;; (negate ID)).  Since P itself did not verify, the facts there are
;; consistent with not P; if not P verifies, P is false on every path that
;; reaches it.  Verus assumes a failed assertion after it, so where other
;; failures come before P on its path the refutation may rest on them: each
;; group is probed at a client where its clause fails first, when it has one
;; (groups.rkt: (at CLIENT ID)).
;;
;; One probe per group, all of a module's probes in one Verus run, into
;; RUN-DIR/refute/<m>/ as evaluate.rkt runs a module (resumed by its key:
;; the probes, the imports, the runner, the checkout's state); the probes
;; and the copy of the module's table beside it, <m>.clients.rktd and
;; <m>.table.rktd.  The facts, RUN-DIR/refute/<m>.rktd:
;;   (refute CLIENT ID STATUS (variant NAME))
;;   STATUS = refuted        the negation verified
;;          | open           the negation failed too: the facts do not decide P
;;          | no-assertion   the failure is not an assertion (a callee's precondition at a call)
;;          | not-concluded  the run did not conclude (crash, sanity, resource limit, compile error)
;; groups.rkt reads them: (refute STATUS) on the group, (refuted) among its labels.
(require racket/file racket/list racket/match racket/string racket/path
         "../model/results.rkt" "../model/api.rkt" "../base/forms.rkt"
         "groups.rkt" "evaluate.rkt")
(provide refute)

;; refute : run-dir [module-regex] -> (line ...)
(define (refute run-dir [only #rx""])
  (define manifest (file->value (build-path run-dir "manifest.rktd")))
  (define cfg (read-config (cadr (assq 'config (cdr manifest)))))
  (define vostd (cadr (assq 'vostd (cdr manifest))))
  (make-directory* (build-path run-dir "refute"))
  (for/list ([mod (in-list (group-failures run-dir #f only))])
    (define m (cadr mod))
    (define targets
      (remove-duplicates
       (for/list ([g (in-list (cddr mod))] #:when (and (pair? g) (eq? (car g) 'group)))
         ;; (at CLIENT ID [CULPRIT]): the probe is the client and the assertion
         (take (cdr (assq 'at (cddr g))) 2))))
    (define line
      (if (null? targets)
          (format "~a: no failures" m)
          (refute-module cfg vostd run-dir m targets)))
    (displayln line)
    line))

(define (refute-module cfg vostd run-dir m targets)
  (define clients
    (for/hash ([c (in-list (file->list (build-path run-dir "clients" (string-append m ".rktd"))))])
      (values (cadr c) c)))
  ;; (CLIENT ID VARIANT-NAME VARIANT-or-#f)
  (define probes
    (for/list ([t (in-list targets)] [i (in-naturals)])
      (match-define (list n id) t)
      (define vname (string->symbol (format "~a__refute~a" n i)))
      (define c (hash-ref clients n #f))
      (list n id vname (and c `(client ,vname ,@(cddr c) (negate ,id))))))
  (define variants (filter values (map cadddr probes)))
  ;; run as the evaluation runs a module (evaluate.rkt run-module: the
  ;; imports rustc suggests, halves after a crash, the key), on a copy of the
  ;; run's table taken afresh each time, so that the key sees the same imports
  ;; and the run's own table is not changed
  (define base (build-path run-dir "refute" m))
  (define clients-file (build-path run-dir "refute" (string-append m ".clients.rktd")))
  (define table-file (build-path run-dir "refute" (string-append m ".table.rktd")))
  (copy-file (build-path run-dir "tables" (string-append m ".rktd")) table-file #t)
  (write-forms clients-file variants)
  (define results
    (run-module (build-path (config-auto cfg) "targets" (string-append m ".rktd"))
                table-file (read-api-table table-file) clients-file variants base))
  (define sane? (equal? (assq 'sanity results) '(sanity ok)))
  (define facts
    (for/list ([p (in-list probes)])
      (match-define (list n id vname _) p)
      (define r (result-of results vname))
      (define at (filter (lambda (e) (equal? (error-id e) id)) (result-errors r)))
      (define status
        (cond
          [(and r (eq? (result-status r) 'ill-formed)
                (for/or ([x (in-list (cdddr r))]) (and (pair? x) (memq 'no-assertion-at (flatten x)) #t)))
           'no-assertion]
          [(or (not r) (not sane?) (not (memq (result-status r) '(verified failed)))) 'not-concluded]
          [(ormap (lambda (e) (regexp-match? #rx"rlimit|resource limit|timed out" (error-message e))) at) 'not-concluded]
          [(pair? at) 'open]
          [else 'refuted]))
      `(refute ,n ,id ,status (variant ,vname))))
  (write-forms (build-path run-dir "refute" (string-append m ".rktd")) facts)
  (format "~a: ~a probes, ~a" m (length facts)
          (string-join (for/list ([s (in-list '(refuted open no-assertion not-concluded))]
                                  #:when (memf (lambda (f) (eq? (cadddr f) s)) facts))
                         (format "~a ~a" (count (lambda (f) (eq? (cadddr f) s)) facts) s))
                       ", ")))
