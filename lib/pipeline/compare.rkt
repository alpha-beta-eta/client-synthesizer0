#lang racket/base
;; Comparing two evaluations (evaluate.rkt) client by client (evaluation.md 7.2):
;; client names are derived from their content, so the same client has the
;; same name in both.  For each module both evaluated: how many clients moved
;; from one status to another (among the clients both have), how many are only
;; in one, and the regressions (verified before, not now) by name.
(require racket/file racket/list racket/match "../model/results.rkt")
(provide compare-runs)

(define (results-file run m)
  (define f (build-path run "results" m "results.rktd"))
  (and (file-exists? f) f))

(define (statuses run m)
  (define f (results-file run m))
  (if f
      (for/hash ([r (in-list (file->list f))] #:when (eq? (car r) 'client))
        (values (cadr r) (result-status r)))
      #f))

(define (modules-of run)
  (define d (build-path run "results"))
  (for/list ([m (in-list (directory-list d))] #:when (directory-exists? (build-path d m)))
    (path->string m)))

;; compare-runs : run-dir run-dir -> ((module M (transitions ((A B) N) ...) (only-before N)
;;                                      (only-after N) (regressions NAME ...)) ...)
(define (compare-runs before after)
  (for*/list ([m (in-list (sort (remove-duplicates (append (modules-of before) (modules-of after))) string<?))]
              [a (in-value (statuses before m))] [b (in-value (statuses after m))]
              #:when (and a b))
    (define common (for/list ([k (in-hash-keys b)] #:when (hash-ref a k #f)) k))
    (define transitions
      (for/fold ([h (hash)]) ([k (in-list common)])
        (hash-update h (list (hash-ref a k) (hash-ref b k)) add1 0)))
    `(module ,m
       (transitions ,@(sort (for/list ([(k v) (in-hash transitions)]) (list k v))
                            string<? #:key (lambda (x) (format "~a" (car x)))))
       (only-before ,(count (lambda (k) (not (hash-ref b k #f))) (hash-keys a)))
       (only-after ,(count (lambda (k) (not (hash-ref a k #f))) (hash-keys b)))
       (regressions ,@(sort (for/list ([k (in-list common)]
                                       #:when (and (eq? (hash-ref a k) 'verified) (not (eq? (hash-ref b k) 'verified))))
                              k)
                            symbol<?)))))
