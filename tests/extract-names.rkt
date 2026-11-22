#lang racket/base
;; Names VIR writes that Rust cannot (vostd/extract.rkt, design.md 4.2).
(require rackunit "../lib/vostd/extract.rkt")

;; Verus-generated items are not APIs; an impl's method, a plain function and
;; an inherited default method (already renamed `impl&%N::m`) are
(check-true (generated-item-path? "ostd::mm::page_prop::vdis%1%clone_clause_autoderived%"))
(check-false (generated-item-path? "ostd::mm::page_prop::impl&%26::union"))
(check-false (generated-item-path? "ostd::mm::page_size"))

;; an impl's associated constant goes through the self type, as a call does
(define c `(> ConstVar (Fun :path ostd::mm::page_prop::impl&%26::AVAIL1_SPEC)))
(define (method? _) #f)
(define (ptypes . _) #f)
(check-equal? (parameterize ([current-impl-path
                              (lambda (p typs)
                                (and (equal? (format "~a" p) "ostd::mm::page_prop::impl&%26::AVAIL1_SPEC")
                                     (null? typs)
                                     "PageFlags::AVAIL1_SPEC"))])
                (expr c method? ptypes))
              '(const PageFlags::AVAIL1_SPEC))
;; not written as `crate::..::impl&%26::AVAIL1_SPEC` when the self type is unknown
(check-exn no? (lambda () (expr c method? ptypes)))
;; a module's constant stays as it was
(check-equal? (expr `(> ConstVar (Fun :path ostd::mm::PAGE_SIZE)) method? ptypes) '(const crate::mm::PAGE_SIZE))

;; a constant VIR calls as a function of no arguments (a trait's associated
;; constant, `PagingConstsTrait::NR_LEVELS`) is written without `()` (E0618)
(define k `(> Call :target (CallTarget Fun (CallTargetKind Static) (Fun :path ostd::mm::MAX_NR_LEVELS) ()) :args ()))
(check-equal? (parameterize ([current-const-fn? (lambda (p) (equal? (format "~a" p) "ostd::mm::MAX_NR_LEVELS"))])
                (expr k method? ptypes))
              '(const crate::mm::MAX_NR_LEVELS))
(check-equal? (expr k method? ptypes) '(call crate::mm::MAX_NR_LEVELS))
