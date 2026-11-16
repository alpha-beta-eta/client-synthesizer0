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

;; the groups a provable directory tries: selection.rktd, else facts.rktd's
(require racket/file)
(define dir (make-temporary-file "cs-provable-~a" 'directory))
(let-values ([(m gs) (read-selection dir)]) (check-false m) (check-false gs))
(with-output-to-file (build-path dir "facts.rktd")
  (lambda ()
    (writeln '(provable "a" "k1" c1 "s2" f proved "t"))
    (writeln '(provable "a" "k1" c2 "s2" f proved "t"))
    (writeln '(provable "b" "k2" c3 "s1" #f no-culprit))))
(let-values ([(m gs) (read-selection dir)]) (check-false m) (check-equal? gs '(("a" "k1") ("b" "k2"))))
(write-to-file '(selection unlabelled ("a" "k1")) (build-path dir "selection.rktd"))
(let-values ([(m gs) (read-selection dir)]) (check-equal? m 'unlabelled) (check-equal? gs '(("a" "k1"))))
(delete-directory/files dir)
