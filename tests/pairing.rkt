#lang racket/base
;; goal_err and flow pair by role and origin (design.md 3.5), on the real mm.io table and knowledge.
(require rackunit racket/runtime-path racket/list racket/string
         "../lib/model/api.rkt" "../lib/model/knowledge.rkt" "../lib/gen/families/goal.rkt"
         "../lib/gen/families/common.rkt" "table-keys.rkt")
(define-runtime-path io-table "../data/auto/apis/mm.io.rktd")
(define-runtime-path io-knowledge "../data/auto/knowledge/mm.io.rktd")
(when (and (file-exists? io-table) (file-exists? io-knowledge))
  (define t (read-api-table io-table))
  (define k (read-knowledge io-knowledge))
  (define-values (read-once write fill) (apply values (map (lambda (k) (api-by-key io-table k))
                                                         '("mm::io::VmReader<'a, Infallible>::read_once" "mm::io::VmWriter<'a, Infallible>::write"
                                                           "mm::io::VmWriter<'a, Infallible>::fill"))))
  (define names (filter values (list read-once write fill (api-by-key io-table "mm::io::VmReader<'a, Infallible>::from_kernel_space"))))
  (define cs (generate-goals t names #:knowledge k))
  (define (client named) (findf (lambda (c) (eq? (cadr c) named)) cs))
  ;; read_once failed, then write: the reader's owner goes to write's owner_r (reader-owner), not owner_w
  (define ge (client (safe (format "goal_err_~a_~a" read-once write))))
  (when ge
    (define call (let loop ([x ge]) (cond [(and (pair? x) (eq? (car x) 'call) (eq? (cadr x) write)) x]
                                          [(pair? x) (ormap loop x)] [else #f])))
    (check-not-false call)
    ;; (call write (self reader) (owner_w owner_r) ..): H's `owner` is the reader's, so it is owner_r
    (check-equal? (list-ref (cadddr call) 1) 'owner (format "~s" call))
    (check-not-equal? (list-ref (cadddr call) 0) 'owner (format "~s" call)))
  ;; flow: no client where a new writer gets the owner F returned (`self_g.wf(gr)`)
  (for ([c (in-list cs)] #:when (regexp-match? #rx"^flow_" (symbol->string (cadr c))))
    (define params (map car (cdr (assq 'params (cddr c)))))
    (define call (let loop ([x (cdr (assq 'body (cddr c)))])
                   (cond [(and (pair? x) (eq? (car x) 'call) (memq (cadr x) names) (not (eq? (cadr x) (car names)))) x]
                         [(pair? x) (ormap loop x)] [else #f])))
    (when (and call (eq? (cadr call) fill))
      ;; fill's receiver is a new parameter only when its owner is new too
      (define recv (car (caddr call)))
      (define owner (car (cadddr call)))
      (check-false (and (regexp-match? #rx"_g$" (symbol->string recv)) (not (regexp-match? #rx"_g$" (symbol->string owner))))
                   (format "~a: ~s" (cadr c) call)))))

;; flow with a value flowing: a fresh offset tied to the segment is kept (split's `offset <= self.size()`)
(define-runtime-path seg-table "../data/auto/apis/mm.frame.segment.rktd")
(define-runtime-path seg-knowledge "../data/auto/knowledge/mm.frame.segment.rktd")
(when (and (file-exists? seg-table) (file-exists? seg-knowledge))
  (define t (read-api-table seg-table))
  (define k (read-knowledge seg-knowledge))
  (define-values (slice split) (values (api-by-key seg-table "mm::frame::segment::Segment<M>::slice")
                                      (api-by-key seg-table "mm::frame::segment::Segment<M>::split")))
  (define names (filter values (list slice split)))
  (define cs (generate-goals t names #:knowledge k))
  (check-not-false (findf (lambda (c) (eq? (cadr c) (safe (format "flow_~a_~a_0" slice split)))) cs)))
