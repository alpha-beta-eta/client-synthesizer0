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

;; which clauses can move a function's proof: its callees', or its module's
(check-equal? (fn-module "mm::io::impl&%0::fill") "mm::io")
(check-equal? (fn-module "mm::frame::meta::get_slot") "mm::frame::meta")
(check-equal? (fn-module "specs::mm::io::impl&%3::split") "specs::mm::io")
(define (calls-of f) (if (equal? f "mm::vm_space::impl&%0::cursor") '("mm::page_table::impl&%10::cursor") '()))
;; same module, no call (fill and write_val in r1's slot 3)
(check-true (reaches? calls-of "mm::io::impl&%0::fill" "mm::io::impl&%0::write_val"))
;; a callee in another module
(check-true (reaches? calls-of "mm::vm_space::impl&%0::cursor" "mm::page_table::impl&%10::cursor"))
;; neither
(check-false (reaches? calls-of "mm::io::impl&%0::fill" "mm::vm_space::impl&%0::cursor"))
;; a submodule is another module
(check-false (reaches? calls-of "mm::page_table::impl&%9::f" "mm::page_table::cursor::impl&%4::query"))
