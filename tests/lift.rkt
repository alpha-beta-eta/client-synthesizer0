#lang racket/base
;; Which callee clauses become the client's requires (lift-clauses, design.md 3.4).
(require rackunit "../lib/check/client.rkt")

(define params '((p tracked Obj) (regions tracked (&mut Regions)) (q exec Obj) (o tracked Owner)))
(define s0 (initial-state #f '() params))
(define (touch s x #:moved? [moved? #f])
  (define v (hash-ref (st-env s) x))
  (struct-copy st s [env (hash-set (st-env s) x (struct-copy var v [touched? #t] [state (if moved? 'moved (var-state v))]))]))
(define (with-local s x)
  (struct-copy st s [env (hash-set (st-env s) x (var 'tracked 'Obj 'live #f #f '()))]))

;; all untouched: lifted (as before)
(check-true (liftable? s0 '(method p wf (deref regions))))
;; regions touched by `&mut`, p not yet used: lifted, at the entry (the second exception)
(define s1 (touch s0 'regions))
(check-true (liftable? s1 '(method p wf (deref regions))))
;; both touched: not, unless it is one parameter's invariant (the first exception)
(define s2 (touch s1 'p))
(check-false (liftable? s2 '(method p wf (deref regions))))
(check-true (liftable? s2 '(method p inv)))
;; a moved parameter: not (a real caller no longer holds it)
(define s3 (touch s0 'o #:moved? #t))
(check-false (liftable? s3 '(method p inv_with (deref o))))
;; a local (an earlier call's result) is not in scope at the entry: not
(define s4 (with-local s1 'x1))
(check-false (liftable? s4 '(method x1 wf (deref regions))))
(check-false (liftable? s4 '(and (method p wf (deref regions)) (method x1 inv))))
;; lift-clauses adds exactly the liftable ones
(check-equal? (st-requires (lift-clauses s4 '((method p wf (deref regions)) (method x1 wf (deref regions)))))
              '((method p wf (deref regions))))

;; a parameter an earlier call took (even copied) is no longer fresh: the clause is not lifted
(define s5 (struct-copy st s1 [used '(p)]))
(check-false (liftable? s5 '(method p wf (deref regions))))
;; a clause between a fresh parameter and an untouched one an earlier call used: not lifted either
(define s6 (struct-copy st s1 [used '(q)]))
(check-false (liftable? s6 '(method p related q (deref regions))))

;; end to end, on the real table: `paddr` given to from_unused is not fresh at inc_frame_ref_count,
;; so its ref_count clause is not assumed at the entry (that made the Ok branch vacuous)
(require racket/runtime-path racket/list "../lib/model/api.rkt")
(define-runtime-path frame-table "../data/auto/apis/mm.frame.rktd")
(when (file-exists? frame-table)
  (define t (read-api-table frame-table))
  (define c '(client c (type-params (M AnyFrameMeta (Repr MetaSlotStorage) OwnerOf))
                     (params (paddr exec usize) (metadata exec M) (regions tracked (&mut MetaRegionOwners))
                             (repr_perm tracked (&mut (assoc M ReprPerm "vstd_extra::cast_ptr::Repr<MetaSlotStorage>"))))
                     (body (let r (call mm::frame::impl&%5::from_unused (paddr metadata) (regions repr_perm)))
                           (if-let (Ok x) r (then)
                                   (else (assert-requires mm::frame::inc_frame_ref_count (paddr) (regions))
                                         (let w_g (call mm::frame::inc_frame_ref_count (paddr) (regions))))))))
  (define e (check-client t c))
  (check-equal? (car e) 'client (format "~s" e))
  (define req (format "~s" (cdr (or (assq 'requires (cddr e)) '(requires)))))
  (check-false (regexp-match? #rx"ref_count" req) req))

;; one owner describes one object: the same relation of the owner to another object is not lifted
(define s7 (struct-copy st s1 [requires '((method (field q 0) invariants (deref o) (deref regions)))]))
(check-false (liftable? s7 '(method (field (field p pt_cursor) 0) invariants (deref o) (deref regions))))
;; a different relation, or the same object, is
(check-true (liftable? s7 '(method p wf (deref regions))))
