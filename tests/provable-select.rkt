#lang racket/base
;; Which groups `provable --unlabelled` tries (pipeline/provable.rkt).
(require rackunit "../lib/pipeline/provable.rkt")

(define (g . labels) `(group "k" (clients 1) (labels ,@labels)))
(check-true (unlabelled-group? (g)))
;; a stale verdict is to be judged again: as if unlabelled (groups.rkt's order)
(check-true (unlabelled-group? (g '(stale-verdict noise))))
(check-false (unlabelled-group? (g '(verdict noise))))
(check-false (unlabelled-group? (g '(issue N12))))
(check-false (unlabelled-group? (g '(limitation mm::f) '(stale-verdict noise))))
