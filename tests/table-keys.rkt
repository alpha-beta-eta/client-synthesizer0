#lang racket/base
;; An API of the user's extracted tables (data/auto/apis) by its source key,
;; which stays across vostd versions: the `impl&%N` in a name is renumbered
;; when impls are added before it (2026-11-22: 8e4b202d6 -> eb1a9d044 broke
;; tests that named `mm::frame::impl&%5::from_unused`).
(require racket/file racket/match)
(provide api-by-key)

;; api-by-key : table-file key-string -> symbol or #f
(define (api-by-key file key)
  (for/first ([x (in-list (file->list file))]
              #:when (and (pair? x) (memq (car x) '(fn api)) (equal? (key-of x) key)))
    (cadr x)))

(define (key-of x)
  (match x
    [(list 'key (? string? k)) k]
    [(? pair?) (or (key-of (car x)) (key-of (cdr x)))]
    [_ #f]))
