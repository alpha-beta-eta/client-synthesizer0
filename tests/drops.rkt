#lang racket/base
;; Putting candidates into F's ensures and reading Verus's errors back to them
;; (analysis/drops.rkt, step 2 of design.md 3.9).
(require rackunit racket/string "../lib/analysis/drops.rkt" "../lib/vostd/run.rkt")

(define src
  '("    #[verus_spec(r =>"
    "        ensures"
    "            res.invariants(*final(entry_own), *regions),"
    "            *final(entry_own) == old(entry_own).from_pte_owner_spec(),"
    "    )]"))

;; after the clause ending at 4:70 (1-based, exclusive): before its comma, in id order
(define out (insert-candidates src '((4 70 7 "res.inv()") (4 70 3 "res.wf()"))))
(check-equal? out
              '("    #[verus_spec(r =>"
                "        ensures"
                "            res.invariants(*final(entry_own), *regions),"
                "            *final(entry_own) == old(entry_own).from_pte_owner_spec(),"
                "            /*DROP:3*/ res.wf(),"
                "            /*DROP:7*/ res.inv(),"
                "    )]"))
;; a clause without a trailing comma, and one further up: positions stay valid
(check-equal? (insert-candidates '("  ensures" "      a == b" "  {") '((2 13 0 "c")))
              '("  ensures" "      a == b," "      /*DROP:0*/ c" "  {"))
(check-equal? (length (insert-candidates src '((3 57 1 "x") (4 70 2 "y")))) 7)

;; blame: through parse-verus, the lines as the round left them
(define lines (list->vector out))
(define (line-of file l)
  (if (and (equal? file "ostd/src/a.rs") (<= 1 l (vector-length lines))) (vector-ref lines (sub1 l)) ""))
(define log
  '("error: postcondition not satisfied"
    "   --> ostd/src/a.rs:9:5"
    "    |"
    "   ::: ostd/src/a.rs:6:13"
    "    |"
    "6   |             /*DROP:7*/ res.inv(),"
    "    |             ------- failed this postcondition"
    ""
    "error: assertion failed"
    "   --> ostd/src/b.rs:1:5"
    ""
    "verification results:: 10 verified, 2 errors"))
(define-values (verified errors) (parse-verus log))
(check-equal? verified '(10 2))
(define-values (blamed unblamed) (blame errors line-of #t))
(check-equal? blamed '((unproved 7)))
(check-equal? (length unblamed) 1)
(check-true (string-prefix? (car (car unblamed)) "assertion failed"))

;; before verification (no results line): compile
(define-values (v2 e2)
  (parse-verus '("error[E0425]: cannot find value `res` in this scope"
                 "   --> ostd/src/a.rs:5:24")))
(define-values (b2 u2) (blame e2 line-of (and v2 #t)))
(check-equal? b2 '((compile 3)))
(check-equal? u2 '())

;; an rlimit error in a body names no candidate: the nearest ensures above it is blamed
(define body-lines (list->vector (append out '("    fn f() {" "        while x {" "        }" "    }"))))
(define (line-of2 file l) (if (<= 1 l (vector-length body-lines)) (vector-ref body-lines (sub1 l)) ""))
(define-values (v3 e3)
  (parse-verus '("error: while loop: resource limit (rlimit) exceeded; consider rerunning with `--profile` for more details"
                 "   --> ostd/src/a.rs:9:9"
                 "verification results:: 3 verified, 1 errors")))
(define-values (b3 u3) (blame e3 line-of2 (and v3 #t)))
(check-equal? b3 '((rlimit 3 7)))
(check-equal? u3 '())
