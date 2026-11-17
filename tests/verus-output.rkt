#lang racket/base
;; Reading Verus's output (vostd/run.rkt): expansions of failed assertions
;; (--expand-errors) and which errors are "may panic here" (model/results.rkt).
;; The input is real output, two clients of mm::vm_space.
(require rackunit racket/file racket/runtime-path "../lib/vostd/run.rkt" "../lib/model/results.rkt")

(define-runtime-path input "inputs/verus-expand.out")

(define-values (verified errors) (parse-verus (file->lines input)))
(check-equal? verified '(0 4))
(check-equal? (length errors) 4)
;; the expansion of the first error is printed after the second (the vacuity
;; assertion of the same client), so it is found in the second's block
(check-false (list-ref (list-ref errors 0) 6))
(check-equal? (list-ref (list-ref errors 1) 6)
              '("self_.clone_requires((mut_ref_current(perm)))"
                ("ostd/src/mm/frame/mod.rs:592" "ref_count != REF_COUNT_UNUSED")
                ("ostd/src/mm/frame/mod.rs:593" "may_panic()")))
;; an implication with an uninterpreted may_panic(): no source shown, no leaves
(check-equal? (cdr (list-ref (list-ref errors 3) 6)) '())

;; attributed facts of two clients a, b (as attribute makes them)
(define (fact c line text) (cons c `(error "s2/1" ,line "assertion failed" (text ,text))))
(define facts
  (list (fact 'a 22 "assert(self_.clone_requires((*perm))); // requires of mm::vm_space::impl&%5::clone")
        (fact 'a 23 "assert(false); // vacuity: must fail")
        (fact 'b 99 "assert(((*self_).0.find_next_panic_condition(len) ==> vstd_extra::panic::may_panic())); // requires of x")
        (fact 'b 100 "assert(false); // vacuity: must fail")))
(define attached (attach-expansions facts (map (lambda (e) (list-ref e 6)) errors)))
;; attached to the client's first error, not to the vacuity assertion it was printed after
(check-equal? (error-expanded (cdr (list-ref attached 0)))
              '(("ostd/src/mm/frame/mod.rs:592" "ref_count != REF_COUNT_UNUSED")
                ("ostd/src/mm/frame/mod.rs:593" "may_panic()")))
(check-equal? (error-expanded (cdr (list-ref attached 1))) '())
;; not panic only: ref_count != REF_COUNT_UNUSED failed as well
(check-false (panic-error? (cdr (list-ref attached 0))))
(check-true (panic-error? (cdr (list-ref attached 2))))
;; an expansion whose expression is not the error's is dropped
(check-equal? (error-expanded (cdr (car (attach-expansions (list (fact 'a 22 "assert(x.inv());") (fact 'a 23 "assert(false);"))
                                                           (map (lambda (e) (list-ref e 6)) (list (car errors) (cadr errors)))))))
              '())

;; panic-error?: only may_panic() failed inside, or a callee's requires line is such a clause
(check-true (panic-error? '(error "s2/1" 1 "assertion failed" (text "assert(f.clone_requires(*p));")
                                  (expanded ("ostd/src/mm/frame/mod.rs:593" "may_panic()")))))
(check-true (panic-error? '(error "s2.1" 1 "precondition not satisfied" (text "let v = r.read_val();")
                                  (callee "ostd/src/mm/io.rs:938" "old(self).cursor.vaddr % align_of::<T>() != 0 ==> may_panic(),"))))
(check-false (panic-error? '(error "s2.1" 1 "precondition not satisfied" (text "let v = r.query();")
                                   (callee "ostd/src/mm/vm_space.rs:501" "old(self).0.invariants(*old(owner)),"))))

;; a module mounted by #[path] is reported through the parent directory
(let-values ([(v es) (parse-verus '("error: assertion failed"
                                    "  --> ostd/src/../specs/mm/io/cs_clients.rs:18:12"
                                    "verification results:: 0 verified, 1 errors"))])
  (check-equal? (cadr (car es)) "ostd/specs/mm/io/cs_clients.rs")
  (check-equal? (caddr (car es)) 18))

;; a recommendation note after an error is not that error's: its `:::` is no callee
(let-values ([(v es) (parse-verus '("error: assertion failed"
                                    "  --> ostd/src/mm/io/cs_clients.rs:4698:12"
                                    ""
                                    "note: recommendation not met"
                                    "    --> ostd/src/mm/io/cs_clients.rs:5943:43"
                                    "    ::: tools/verus/source/vstd/layout.rs:55:9"
                                    "verification results:: 0 verified, 1 errors"))])
  (check-false (list-ref (car es) 3))
  (check-equal? (list-ref (car es) 4) '(("ostd/src/mm/io/cs_clients.rs" . 4698))))

;; a trigger note after an error is not that error's: its `-->` is another fix's quantifier
;; (r1 fixes round6: frame-8 blamed for an error in frame6-1's lemma)
(let-values ([(v es) (parse-verus '("error: assertion failed"
                                    "   --> ostd/src/../specs/mm/frame/linked_list/linked_list_owners.rs:595:25"
                                    "    |"
                                    "595 |                 implies l2.relate_region(regions) by {"
                                    ""
                                    "note: automatically chose triggers for this expression:"
                                    "   --> ostd/src/mm/frame/segment.rs:641:13"
                                    "note:   trigger 1 of 1:"
                                    "   --> ostd/src/mm/frame/segment.rs:641:43"
                                    "note: Verus printed one or more automatically chosen quantifier triggers"
                                    "error: could not compile `ostd` (lib) due to 1 previous error"))])
  (check-equal? (length es) 1)
  (check-equal? (list-ref (car es) 4) '(("ostd/specs/mm/frame/linked_list/linked_list_owners.rs" . 595))))
