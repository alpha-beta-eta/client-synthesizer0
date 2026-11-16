#lang racket/base
;; Names across an update, by the source's keys (pipeline/rename.rkt).
(require rackunit racket/file racket/string "../lib/pipeline/rename.rkt")

(define dir (make-temporary-file "rename~a" 'directory))
(define (dir* n) (let ([d (build-path dir n)]) (make-directory* d) d))
(define (entry name key) `(fn ,name (method m) (source (key ,key) (span "f.rs:1:1: 2:2"))))
(define (table d forms) (with-output-to-file (build-path d "m.rktd") (lambda () (for ([f forms]) (writeln f)))))

(define old (dir* "old")) (define new (dir* "new"))
(table old (list (entry 'm::impl&%1::f "m::<A as T>::f") (entry 'm::impl&%2::g "m::B::g") (entry 'm::h "m::h")))
;; impls renumbered (and swapped), h gone
(table new (list (entry 'm::impl&%2::f "m::<A as T>::f") (entry 'm::impl&%1::g "m::B::g")))
(define-values (rs lost) (renames old new))
(check-equal? rs '((m::impl&%1::f . m::impl&%2::f) (m::impl&%2::g . m::impl&%1::g)))
(check-equal? lost '(m::h))

(define k (build-path dir "k.rktd"))
(with-output-to-file k
  (lambda () (void (write-string ";; a comment that stays\n(claim m::impl&%1::f \"ret\" (why \"m::impl&%1::f in a string stays\"))\n(role m::impl&%2::g self owner)\n"))))
(check-equal? (rename-file! k rs) 2)
(define text (file->string k))
(check-true (string-contains? text ";; a comment that stays"))
(check-true (string-contains? text "(claim m::impl&%2::f "))       ; swapped in one pass, not twice
(check-true (string-contains? text "(role m::impl&%1::g self"))
(check-true (string-contains? text "\"m::impl&%1::f in a string stays\""))
(check-equal? (rename-file! k '()) 0)

(delete-directory/files dir)
