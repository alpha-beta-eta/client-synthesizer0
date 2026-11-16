#lang racket/base
;; The pure parts of hand-written fixes (pipeline/fixes.rkt): reading them,
;; planning the edits, mapping lines back, blaming errors, slots.
(require rackunit racket/file racket/list "../lib/pipeline/fixes.rkt")

(define dir (make-temporary-file "cs-fixes-~a" 'directory))
(write-to-file '(fix R1 (groups ("mm.io" "requires of f /1")) (why "w")
                     (replace "a.rs" "ensures x," "ensures x,\n    y,"))
               (build-path dir "f.rktd"))
(define fs (read-fixes (build-path dir "f.rktd")))
(check-equal? (length fs) 1)
(delete-directory/files dir)

(define (fix* id . edits) (car (read-fixes* `((fix ,id (groups) ,@(for/list ([e edits]) `(replace ,@e)))))))
(define (read-fixes* forms)
  (define d (make-temporary-file "cs-fixes-~a" 'directory))
  (with-output-to-file (build-path d "f.rktd") (lambda () (for ([x forms]) (writeln x))))
  (begin0 (read-fixes (build-path d "f.rktd")) (delete-directory/files d)))

(define text "fn a()\n  ensures x,\n{}\nfn b()\n  ensures y,\n{}\n")
(define (text-of f) (and (equal? f "a.rs") text))

;; two fixes in one file: the new text, and where each fix's lines are
(define-values (files bad)
  (plan-edits text-of (list (fix* 'R1 '("a.rs" "ensures x," "ensures x,\n    x2,"))
                            (fix* 'R2 '("a.rs" "ensures y," "ensures y, y2,")))))
(check-equal? bad '())
(define v (hash-ref files "a.rs"))
(check-equal? (car v) "fn a()\n  ensures x,\n    x2,\n{}\nfn b()\n  ensures y, y2,\n{}\n")
(check-equal? (cdr v) '((R1 2 2 2 3) (R2 5 5 6 6)))

;; lines back: inside a fix's new text, or the original line
(let-values ([(id o) (map-line (cdr v) 3)]) (check-equal? (list id o) '(R1 2)))
(let-values ([(id o) (map-line (cdr v) 4)]) (check-equal? (list id o) '(#f 3)))
(let-values ([(id o) (map-line (cdr v) 6)]) (check-equal? (list id o) '(R2 5)))
(let-values ([(id o) (map-line (cdr v) 7)]) (check-equal? (list id o) '(#f 6)))
(let-values ([(id o) (map-line (cdr v) 1)]) (check-equal? (list id o) '(#f 1)))

;; OLD not exactly once, a missing file, overlapping fixes: bad-edit, not applied
(define-values (f2 bad2)
  (plan-edits text-of (list (fix* 'R3 '("a.rs" "ensures" "requires"))
                            (fix* 'R4 '("b.rs" "x" "y"))
                            (fix* 'R5 '("a.rs" "ensures x," "ensures x, z,"))
                            (fix* 'R6 '("a.rs" "x,\n{}" "x,\n{ }")))))
(check-equal? (map car bad2) '(R3 R4 R6))
(check-equal? (car (hash-ref f2 "a.rs")) "fn a()\n  ensures x, z,\n{}\nfn b()\n  ensures y,\n{}\n")

;; errors: on a fix's new line -> that fix; elsewhere -> fixes whose functions reach it
(define spans (cdr v))
(define (spans-of f) (and (equal? f "a.rs") spans))
(define (fn-at f l) (cond [(<= 1 l 3) "m::a"] [(<= 4 l 6) "m::b"] [else #f]))
(define (reaches? g f) (equal? g f))
(define (edited id) (case id [(R1) '("m::a")] [(R2) '("m::b")] [else '()]))
(define (err msg file line) (list msg file line #f (list (cons file line)) '() #f))
(let-values ([(b u) (blame-fix-errors (list (err "postcondition not satisfied" "a.rs" 3)) spans-of fn-at reaches? edited '(R1 R2) #t)])
  (check-equal? b '((unproved R1))) (check-equal? u '()))
;; line 1 of the new text is fn a's body (original line 1): R1 edits fn a
(let-values ([(b u) (blame-fix-errors (list (err "assertion failed" "a.rs" 1)) spans-of fn-at reaches? edited '(R1 R2) #t)])
  (check-equal? b '((breaks-proof R1))) (check-equal? u '()))
;; an error no fix reaches
(let-values ([(b u) (blame-fix-errors (list (err "assertion failed" "c.rs" 9)) spans-of fn-at reaches? edited '(R1 R2) #t)])
  (check-equal? b '()) (check-equal? (length u) 1))

;; slots: related fixes apart; a fix with no known function alone
(check-equal? (fix-slots '(R1 R2 R3) edited (lambda (f g) #f)) '((R1 R2) (R3)))
(check-equal? (fix-slots '(R1 R2) edited (lambda (f g) #t)) '((R1) (R2)))

(check-equal? (norm-file "ostd/src/../specs/mm/io.rs") "ostd/specs/mm/io.rs")
(check-equal? (norm-file "./ostd/src/a.rs") "ostd/src/a.rs")

;; an edit above a body (its #[verus_spec], its ensures) belongs to the function that follows
(define vfns '(("m::a" "a.rs" 10 20) ("m::b" "a.rs" 30 40) ("m::c" "b.rs" 5 9)))
(check-equal? (function-at vfns "a.rs" 15) "m::a")
(check-equal? (function-at vfns "a.rs" 25) "m::b")
(check-equal? (function-at vfns "a.rs" 3) "m::a")
(check-false (function-at vfns "a.rs" 45))
(check-equal? (function-at vfns "b.rs" 1) "m::c")

;; OLD and NEW take the edited file's line ending (a fix written on a CRLF checkout, an LF copy)
(let-values ([(f bad) (plan-edits text-of (list (fix* 'R7 '("a.rs" "  ensures x,\r\n{}" "  ensures x, w,\r\n{}"))))])
  (check-equal? bad '())
  (check-equal? (car (hash-ref f "a.rs")) "fn a()\n  ensures x, w,\n{}\nfn b()\n  ensures y,\n{}\n"))
(define crlf "fn a()\r\n  ensures x,\r\n{}\r\n")
(let-values ([(f bad) (plan-edits (lambda (p) crlf) (list (fix* 'R8 '("c.rs" "  ensures x,\n{}" "  ensures x, w,\n{}"))))])
  (check-equal? bad '())
  (check-equal? (car (hash-ref f "c.rs")) "fn a()\r\n  ensures x, w,\r\n{}\r\n"))

;; no-fix forms are kept for the record, not run
(let ([d (make-temporary-file "cs-fixes-~a" 'directory)])
  (with-output-to-file (build-path d "f.rktd")
    (lambda () (writeln '(fix R9 (groups) (replace "a.rs" "x" "y"))) (writeln '(no-fix ("mm.io" "k") "trusted"))))
  (check-equal? (map (lambda (f) (length (read-fixes (build-path d "f.rktd")))) '(1)) '(1))
  (check-equal? (read-no-fixes (build-path d "f.rktd")) '((("mm.io" "k") "trusted")))
  (delete-directory/files d))

;; ostd's own result, not a dependency's; none when ostd reported nothing
(check-equal? (ostd-results '(">> cargo-verus verify -p \"bitflags\"" "verification results:: 44 verified, 0 errors"
                              ">> \"cargo-verus\" \"verify\" \"-p\" \"ostd\"" "verification results:: 1520 verified, 0 errors"))
              '(1520 0))
(check-false (ostd-results '("verification results:: 44 verified, 0 errors" ">> \"cargo-verus\" \"verify\" \"-p\" \"ostd\"" "Finished")))
;; the dependencies reported inside ostd's command: ostd's is the last
(check-equal? (ostd-results '(">> \"cargo-verus\" \"verify\" \"-p\" \"ostd\"" "verification results:: 44 verified, 0 errors"
                              "verification results:: 1520 verified, 0 errors"))
              '(1520 0))
