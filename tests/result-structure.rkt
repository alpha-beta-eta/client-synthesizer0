#lang racket/base
;; The structure of results (design.md 3.1): a tuple taken apart (untuple), and
;; the Err payload bound in the else branch; checked by client.rkt, written by
;; render.rkt.  On the extracted tables of vostd 8e4b202d6 (data/ is the user's:
;; skipped when the tables are not there).
(require rackunit racket/file racket/string racket/match racket/runtime-path
         "../lib/model/api.rkt" "../lib/check/client.rkt" "../lib/gen/render.rkt")

(define-runtime-path apis "../data/auto/apis")
(define nn (build-path apis "sync.rcu.non_null.rktd"))
(define uq (build-path apis "mm.frame.unique.rktd"))

(define (render table c)
  (define e (check-client table c))
  (check-equal? (car e) 'client (format "~s" e))
  (define-values (text _) (render-module table (list e)))
  text)

(when (file-exists? nn)
  (define t (read-api-table nn))
  (define into-raw '|sync::rcu::non_null::impl&%2::into_raw|)
  (define from-raw '|sync::rcu::non_null::impl&%2::from_raw|)
  ;; the modes from the source's return type: (NonNull<..>, Tracked<..>)
  (check-equal? (api-ret-modes (api-ref t into-raw)) '(exec tracked))
  ;; into_raw's pointer and permission go to from_raw separately
  (define c
    `(client c (type-params (T static)) (params (b exec (Box T))) (allow-open)
             (body (let v0 (call ,into-raw (b) ()))
                   (untuple ((p exec) (perm tracked)) v0)
                   (let v1 (call ,from-raw (p) (perm))))))
  (define text (render t c))
  (check-true (string-contains? text "let (mut p, Tracked(perm)) = v0;") text)
  ;; the tuple is moved: using it again is not well-formed
  (define again
    `(client c (type-params (T static)) (params (b exec (Box T))) (allow-open)
             (body (let v0 (call ,into-raw (b) ()))
                   (untuple ((p exec) (perm tracked)) v0)
                   (untuple ((q exec) (perm2 tracked)) v0))))
  (check-equal? (car (check-client t again)) 'ill-formed)
  ;; wrong arity
  (define arity
    `(client c (type-params (T static)) (params (b exec (Box T))) (allow-open)
             (body (let v0 (call ,into-raw (b) ())) (untuple ((p exec)) v0))))
  (check-equal? (car (check-client t arity)) 'ill-formed))

(when (file-exists? uq)
  (define t (read-api-table uq))
  (define try-from '|mm::frame::unique::impl&%9::try_from|)
  ;; Err(frame) gives the frame back: the else branch has it
  (define c
    `(client c (type-params (M AnyFrameMeta (Repr MetaSlotStorage) OwnerOf)) (params (f exec (Frame M))) (allow-open)
             (body (let v0 (call ,try-from (f) ()))
                   (if-let (Ok x0) v0 (then) (else (Err e0) (let v1 (call ,try-from (e0) ())))))))
  (define e (check-client t c))
  (check-equal? (car e) 'client (format "~s" e))
  (check-true (and (memf (lambda (s) (match s [`(if-let ,_ Ok ,_ ,_ ,_ ,_ (err e0)) #t] [_ #f])) (cdr (assq 'body (cddr e)))) #t))
  (define-values (text _) (render-module t (list e)))
  (check-true (string-contains? text "match v0 {") text)
  (check-true (string-contains? text "Err(mut e0) => {") text)
  ;; the payload is not in the then branch
  (define wrong
    `(client c (type-params (M AnyFrameMeta (Repr MetaSlotStorage) OwnerOf)) (params (f exec (Frame M))) (allow-open)
             (body (let v0 (call ,try-from (f) ()))
                   (if-let (Ok x0) v0 (then (let v1 (call ,try-from (e0) ()))) (else (Err e0))))))
  (check-equal? (car (check-client t wrong)) 'ill-formed))
