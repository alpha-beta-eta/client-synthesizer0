#lang racket/base
;; Triage (docs/triage.md): attribution of a failure to a call, verdicts kept
;; by fingerprints, a clause in the culprit's terms.  No Verus, no vostd.
(require rackunit racket/file "../lib/base/forms.rkt" "../lib/model/api.rkt"
         "../lib/analysis/attribute.rkt" "../lib/model/verdicts.rkt"
         (only-in "../lib/pipeline/provable.rkt" clause-in-callee)
         (only-in "../lib/pipeline/confirm.rkt" slots group-status norm-path))

(define dir (make-temporary-file "triage~a" 'directory))
(define tfile (build-path dir "t.rktd"))
;; make : (&mut T) T -> Option<T>; look : &T; and their sources
(write-forms tfile
  `((fn m::make (mode exec) (function "make")
        (params (o exec (&mut T)) (v exec T)) (ret (Option T))
        (source (params (p "o" "&mut T" (ref "_" mut)) (p "v" "T" #f))
                (with-in) (with-out) (ret "res" "Option<T>") (attrs)
                (ensures (c "src/m.rs:10:13: 10:30" "res is Some" (lit "x")))))
    (fn m::look (mode exec) (function "look") (params (o exec (& T))) (ret bool)
        (source (params (p "o" "&T" (ref "_" shared))) (with-in) (with-out) (ret "b" "bool") (attrs "external_body")
                (ensures (c "src/m.rs:20:13: 20:20" "b" (lit "b")))))))
(define t (read-api-table tfile))

(define plan
  `(client c (source "") (generics) (params) (requires)
           (body (ghost "s1" old_a (deref a))
                 (call "s2" r m::make (args (mutref a) (move v)) (gargs) (gret #f) (subst))
                 (call "s3" #f m::look (args (ref a)) (gargs) (gret #f) (subst))
                 (if-let "s4" Some x r
                         (then (assert-requires "s4.1" m::look ((method x inv) (method a inv) (method w inv))))
                         (else)))))
;; the payload of make's result; a, which make changed by &mut (look only reads it);
;; w, a parameter nothing touched
(check-equal? (culprit t plan "s4.1/1") '(m::make "s2" x))
(check-equal? (culprit t plan "s4.1/2") '(m::make "s2" a))
(check-equal? (culprit t plan "s4.1/3") 'entry)
(check-false (culprit t plan "s3"))      ; a call, not an assertion
(check-equal? (expr-vars '(method (field x f) m (const K) (call g y))) '(x y))

;; in make's terms: the payload under the guard, a passed `&mut a` as *final(o)
(define-values (f1 t1 s1) (clause-in-callee t plan "s4.1/1"))
(check-equal? (list f1 s1 t1) '(m::make expressed "res is Some ==> (res->Some_0.inv())"))
(define-values (f2 t2 s2) (clause-in-callee t plan "s4.1/2"))
(check-equal? t2 "res is Some ==> ((*final(o)).inv())")
(define-values (f3 t3 s3) (clause-in-callee t plan "s4.1/3"))
(check-equal? s3 'no-culprit)
;; a snapshot of *a before the call, a passed on as the &mut reference it is: *old(o)
(define plan2
  `(client c (source "") (generics) (params) (requires)
           (body (ghost "s1" old_a (deref a))
                 (call "s2" #f m::make (args (same a) (move v)) (gargs) (gret #f) (subst))
                 (assert "s3" (== (field old_a f) (field (deref a) f)) ""))))
(define-values (f4 t4 s4) (clause-in-callee t plan2 "s3"))
(check-equal? t4 "((*old(o)).f == (*final(o)).f)")

;; verdicts: current while the fingerprints are the same
(define vfile (build-path dir "v.rktd"))
(write-forms vfile `((verdict (group "requires of m::look /1") (by m::make) (judgement noise) (reason "r")
                              (specs (m::look "aa") (m::make "bb")) (at "c0"))))
(define vs (read-verdicts vfile))
(check-equal? (verdict-judgement (verdict-for vs "m" "requires of m::look /1" 'm::make)) 'noise)
(check-false (verdict-for vs "m" "requires of m::look /1" 'm::other))
(check-equal? (verdict-status (car vs) (hash 'm::look "aa" 'm::make "bb")) 'current)
(check-equal? (verdict-status (car vs) (hash 'm::look "aa" 'm::make "cc")) 'stale)
(check-equal? (verdict-status (car vs) (hash 'm::look "aa")) 'stale)
(check-equal? (key-apis "requires of m::look /1") '(m::look))
(check-equal? (key-apis "after an error of m::make") '(m::make))

;; confirmation: slots of clauses whose functions neither are the same nor call each other
(define (calls-of f) (case f [("a") '("b")] [else '()]))   ; a calls b
(check-equal? (slots '((0 . "a") (1 . "a") (2 . "b") (3 . "c") (4 . "b")) calls-of)
              '((0 3) (1) (2) (4)))
(check-equal? (slots '((0 . "b") (1 . "c") (2 . "c")) calls-of) '((0 1) (2)))
(check-equal? (norm-path "ostd::mm::x::impl&%0::_VERUS_VERIFIED_f") "mm::x::impl&%0::f")
(check-equal? (map (lambda (b a) (group-status b a)) '(3 3 3 0) '(0 1 3 0)) '(fixed reduced unchanged no-clients))

(delete-directory/files dir)
