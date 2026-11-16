#lang racket/base
;; An error outside every candidate is put down to the function whose body holds
;; it (pipeline/confirm.rkt): the innermost body, by file and line.
(require rackunit "../lib/pipeline/confirm.rkt")

(define fns
  '((mm::io::impl&%0::fill "ostd/src/mm/io.rs" 390 470)
    (mm::io::impl&%0::fill_closure "ostd/src/mm/io.rs" 440 455)
    (mm::io::impl&%0::write_val "ostd/src/mm/io.rs" 300 330)
    (mm::vm_space::impl&%0::cursor "ostd/src/mm/vm_space.rs" 240 265)))
(check-equal? (enclosing-function fns "ostd/src/mm/io.rs" 420) 'mm::io::impl&%0::fill)
;; inside a nested body: the innermost
(check-equal? (enclosing-function fns "ostd/src/mm/io.rs" 449) 'mm::io::impl&%0::fill_closure)
(check-equal? (enclosing-function fns "ostd/src/mm/io.rs" 316) 'mm::io::impl&%0::write_val)
;; the same line in another file, or outside every body: none
(check-false (enclosing-function fns "ostd/src/mm/vm_space.rs" 420))
(check-false (enclosing-function fns "ostd/src/mm/io.rs" 10))
