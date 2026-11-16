#lang racket/base
;; Tests of deriv.rkt on letters a, b, c: regular, context-free (including
;; left recursion), intersection and complement.
(require rackunit "../lib/base/deriv.rkt")

(define (letter? r) (and (memq r '(a b c any)) #t))
(define (match? p k) (or (eq? p 'any) (eq? p k)))

;; in? : G (letter ...) -> (list nullable? maybe-nonempty?)
(define (in? g w)
  (define n (for/fold ([n (compile-grammar g letter?)]) ([x (in-list w)]) (derive n x match?)))
  (list (nullable? n) (maybe-nonempty? n)))

(define dyck '(grammar S (S (alt eps (seq a S b S)))))
(test-equal? "dyck: empty" (in? dyck '()) '(#t #t))
(test-equal? "dyck: a a b b" (in? dyck '(a a b b)) '(#t #t))
(test-equal? "dyck: a b a b" (in? dyck '(a b a b)) '(#t #t))
(test-equal? "dyck: a a b (prefix)" (in? dyck '(a a b)) '(#f #t))
(test-equal? "dyck: a b b (dead)" (in? dyck '(a b b)) '(#f #f))

(define left '(grammar L (L (alt (seq L a) b))))
(test-equal? "left recursion: b a a" (in? left '(b a a)) '(#t #t))
(test-equal? "left recursion: a (dead)" (in? left '(a)) '(#f #f))
(test-equal? "left recursion: empty" (in? left '()) '(#f #t))

;; a^n b^n c^n as the intersection of two context-free languages
(define abc '(and (grammar X (X (seq P (* c))) (P (alt eps (seq a P b))))
                  (grammar Y (Y (seq (* a) Q)) (Q (alt eps (seq b Q c))))))
(test-equal? "abc: a a b b c c" (in? abc '(a a b b c c)) '(#t #t))
(test-equal? "abc: a b c c (dead)" (in? abc '(a b c c)) '(#f #f))

(define never-ab '(not (contains a b)))
(test-equal? "not contains: a c b" (in? never-ab '(a c b)) '(#f #t))
(test-equal? "not contains: b a" (in? never-ab '(b a)) '(#t #t))

(test-equal? "not of a nested grammar" (in? `(not ,dyck) '(a)) '(#t #t))
(test-exn "not over an outer nonterminal is rejected" #rx"nonterminal under not"
          (lambda () (compile-grammar '(grammar S (S (alt eps (not S)))) letter?)))
