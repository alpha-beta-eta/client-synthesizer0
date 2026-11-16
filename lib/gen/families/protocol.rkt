#lang racket/base
;; protocol_<NAME>_<sha>: the call sequences of real callers, from the call
;; knowledge (design.md 3.7).
(require racket/list racket/match "../../model/api.rkt" "../../base/forms.rkt" "../probe.rkt" "../enum.rkt" "../../check/prop.rkt" "../../model/knowledge.rkt" "common.rkt")
(provide generate-protocol-chains)

;; generate-protocol-chains : table names knowledge -> (client ...)
;; protocol_<NAME>_<sha>: for each protocol of the knowledge (a call sequence
;; real callers use) whose calls are all in the table, the chains whose main
;; path makes exactly those calls in that order (providers in between); the
;; else branches, if any, call the protocol's APIs.  Its parameters are those
;; of all the calls' probes.  A protocol stands for a usage, not a space to
;; cover: no else branches by default and at most CAP clients, the first in
;; enumeration order (with every argument choice, mm.io's protocols give
;; half a million clients and do not fit in memory).  The choices kept are
;; those that pass on what an earlier call produced (prefer-produced): with a
;; fresh parameter first, a later call's object was a parameter whose requires
;; cannot be lifted once a shared resource such as `regions` has been used, and
;; 60 of 74 protocol failures were that.  An object also goes with the owner
;; the same call returned (pair-by-origin), not with a fresh or another one;
;; and a produced value is not tied to a fresh parameter by one requires
;; clause (consistent-fresh: an owner no call in the sequence produced).  A
;; type parameter of several calls gets the bounds of all of them (`G` is
;; unbounded in `RwLock::new` but `G: SpinGuardian` on the guards).
;; design.md 3.5.
(define (generate-protocol-chains table names k #:else-depth [else-depth 0] #:max-choices [k-choices 2] #:max-clients [cap 8]
                                  #:repeat-last? [repeat? #t] #:identity [identity '()])
  (define apis (for/list ([n (in-list names)]) (api-ref table n)))
  (define steps (for/list ([a (in-list apis)] #:when (memq (api-mode a) '(exec proof))) a))
  (define providers (if (api-ref table 'Option::tracked_unwrap) '(Option::tracked_unwrap) '()))
  (define rels (relations steps identity))
  (append*
   (for/list ([pr (in-list (knowledge-protocols k))]
              #:when (andmap (lambda (n) (memq n (map api-name steps))) (cadr pr)))
     (match-define (list name calls) pr)
     (define f (api-ref table (car calls)))
     ;; The parameters of all the calls' probes: a real protocol involves
     ;; several objects (a reader and a writer, each from_kernel_space).  A
     ;; name taken by an earlier call gets the call's position as suffix.
     (define-values (type-params params var-roles)
       (for/fold ([tps '()] [ps '()] [vrs '()] #:result (values (reverse tps) (reverse ps) (reverse vrs)))
                 ([c (in-list calls)] [i (in-naturals)])
         (define pr (probe-client (api-ref table c)))
         (define rename
           (for/list ([p (in-list (form-ref pr 'params))])
             (cons (car p) (if (assq (car p) ps) (string->symbol (format "~a_~a" (car p) i)) (car p)))))
         (values (for/fold ([tps tps]) ([tp (in-list (form-ref pr 'type-params))])
                   (define (tp-name x) (if (pair? x) (car x) x))
                   (define (tp-bounds x) (if (pair? x) (cdr x) '()))
                   (define n (tp-name tp))
                   (cond
                     [(findf (lambda (x) (eq? n (tp-name x))) tps)
                      => (lambda (old)
                           (define bs (remove-duplicates (append (tp-bounds old) (tp-bounds tp))))
                           (for/list ([x (in-list tps)])
                             (if (eq? x old) (if (null? bs) n (cons n bs)) x)))]
                     [else (cons tp tps)]))
                 (for/fold ([ps ps]) ([p (in-list (form-ref pr 'params))])
                   (cons (cons (cdr (assq (car p) rename)) (cdr p)) ps))
                 (for/fold ([vrs vrs]) ([vr (in-list (knowledge-var-roles k (api-ref table c)))])
                   (define x (cdr (or (assq (car vr) rename) (cons #f (car vr)))))
                   (if (assq x vrs) vrs (cons (list x (cadr vr)) vrs))))))
     (define between `(* (alt ,@(for/list ([p (in-list providers)]) `(call ,p)) empty)))
     (define main (compile-property
                   `(property protocol (forall) (paths main)
                              (seq ,@(add-between (for/list ([c (in-list calls)]) `(call ,c)) between) ,between))))
     (define start (compile-property `(property start (forall) (seq (call ,(car calls)) (* any)))))
     (define spec
       `(enum ,(safe (format "protocol_~a" name))
              (type-params ,@type-params)
              (params ,@params)
              (apis ,@(remove-duplicates calls))
              (providers ,@providers)
              (depth ,(length calls))
              (else-depth ,else-depth)
              (properties start protocol)
              (explicit-requires)
              ,@(if repeat? '((repeat-last)) '())
              (relations ,@rels)
              (roles ,@(knowledge-roles k))
              (var-roles ,@var-roles)
              (max-choices ,k-choices)
              (prefer-produced)
              (pair-by-origin)
              (consistent-fresh)))
     (define assumed (knowledge-assumptions k f))
     (define cs (enumerate table spec (list start main)))
     (for/list ([c (in-list (take cs (min cap (length cs))))])
       (append c (if (null? assumed) '() `((requires ,@assumed))) '((allow-open)))))))
