#lang racket/base
;; "may panic here" clauses (model/spec.rkt panic-condition, check/client.rkt with-no-panic).
(require rackunit "../lib/model/spec.rkt")
(check-equal? (panic-condition '(implies (> a 1) (call vstd_extra::panic::may_panic))) '(> a 1))
(check-equal? (panic-condition '(implies c (implies (> a 1) (call may_panic)))) '(and c (> a 1)))
;; vostd eb1a9d044 writes it allowed_to_panic_if(P)
(check-equal? (panic-condition '(call vstd_extra::panic::allowed_to_panic_if (> a 1))) '(> a 1))
(check-equal? (panic-condition '(call allowed_to_panic_if (method x panic_condition))) '(method x panic_condition))
(check-equal? (panic-condition '(implies c (call allowed_to_panic_if (> a 1)))) '(and c (> a 1)))
(check-false (panic-condition '(call vstd_extra::panic::not_allowed_to_panic_if (> a 1))))
(check-false (panic-condition '(> a 1)))
