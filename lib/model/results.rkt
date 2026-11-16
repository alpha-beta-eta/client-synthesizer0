#lang racket/base
;; Reading plans (elaborated clients, client.rkt) and results (run.rkt).
;;
;;   result = (client NAME STATUS ITEM ...)
;;     STATUS = verified | failed | not-verified | compile-error | ill-formed
;;     ITEM   = (error ID LINE MESSAGE (text LINE-TEXT) [(callee FILE:LINE SOURCE-LINE)]
;;                     [(expanded (FILE:LINE FAILED-TEXT) ...)]  the conjuncts that failed
;;                     (help HEADING CODE ...) ...)       rustc's suggestions
;;            | (vacuous TAIL-ID ...)
(require racket/list racket/match racket/string)
(provide result-of result-status result-errors result-vacuous
         error-id error-message error-text error-callee error-expanded panic-error? panic-leaf?
         plan-of plan-body plan-stmt stmt-label)

;; result-of : (result ...) NAME -> result or #f
(define (result-of results name)
  (findf (lambda (r) (and (pair? r) (eq? (car r) 'client) (eq? (cadr r) name))) results))

(define (result-status r) (caddr r))

;; result-errors : result-or-#f -> (error ...)
(define (result-errors r)
  (if r (filter (lambda (e) (and (pair? e) (eq? (car e) 'error))) (cdddr r)) '()))

;; result-vacuous : result-or-#f -> (TAIL-ID ...)
(define (result-vacuous r)
  (define v (and r (assq 'vacuous (filter pair? (cdddr r)))))
  (if v (cdr v) '()))

(define (error-id e) (cadr e))
(define (error-message e) (cadddr e))
(define (error-text e) (let ([t (assq 'text (cddddr e))]) (if t (cadr t) "")))
;; error-callee : error -> (FILE:LINE SOURCE-LINE) or #f
(define (error-callee e) (let ([c (assq 'callee (cddddr e))]) (and c (cdr c))))

;; panic-error? : error -> boolean
;; An error at a "may panic here" clause `P ==> may_panic()`: the client's own
;; assertion of a requires (`assert((P ==> may_panic())); // requires of ..`),
;; or a callee's precondition whose source line is such a clause (Verus reports
;; a requires the client did not assert as "precondition not satisfied" with
;; the callee's line).  Not judged (evaluation.md 7.1).
;; Also an error whose expansion (error-expanded) fails only at `may_panic()`:
;; the saturation clause inside an opaque requires such as `clone_requires`.
(define (panic-error? e)
  (or (regexp-match? #rx"may_panic[(][)][)]+; //" (error-text e))
      (let ([c (error-callee e)])
        (and c (pair? (cdr c)) (regexp-match? #rx"==> *(vstd_extra::panic::)?may_panic[(][)],?$" (cadr c))))
      (let ([leaves (error-expanded e)])
        (and (pair? leaves) (andmap panic-leaf? leaves)))))

;; error-expanded : error -> (("file:line" "failed text") ...), the conjuncts
;; that failed inside the asserted expression (run.rkt, --expand-errors), or '()
(define (error-expanded e) (let ([x (assq 'expanded (filter pair? (cddddr e)))]) (if x (cdr x) '())))

(define (panic-leaf? l) (regexp-match? #px"^(vstd_extra::panic::)?may_panic\\(\\)$" (cadr l)))

;; ================================================================ plans

(define (plan-of plan name) (findf (lambda (p) (eq? (cadr p) name)) plan))

;; plan-body : elaborated client -> (ESTMT ...), or '() for an ill-formed one
(define (plan-body p) (if (and p (eq? (car p) 'client)) (cdr (assq 'body (cddr p))) '()))

;; plan-stmt : (ESTMT ...) ID -> ESTMT or #f
;; The statement an id names; a clause id ("s3/2", "s3/inv1") names its statement.
(define (plan-stmt body id)
  (define sid (car (string-split id "/")))
  (let loop ([body body])
    (for/or ([s (in-list body)])
      (match s
        [`(,_ ,(== sid) ,_ ...) s]
        [`(if-let ,_ ,_ ,_ ,_ (then ,tb ...) (else ,eb ...) ,_ ...) (loop (append tb eb))]
        [`(if ,_ ,_ (then ,tb ...) (else ,eb ...)) (loop (append tb eb))]
        [`(if-not ,_ ,_ ,inner ...) (loop inner)]
        [`(repeat ,_ ,_ ,_ ,inner ...) (loop inner)]
        [_ #f]))))

;; stmt-label : (ESTMT ...) ID -> what failed at the id, for summaries:
;; the API called, "requires of API", "loop invariant", or the statement kind.
(define (stmt-label body id)
  (match (and id (plan-stmt body id))
    [#f #f]
    [`(call ,_ ,_ ,api ,_ ...) api]
    [`(assert-requires ,_ ,api ,_) (format "requires of ~a" api)]
    [`(repeat ,_ ,_ ...) #:when (regexp-match? #rx"/inv" id) "loop invariant"]
    [`(,kind ,_ ...) kind]))
