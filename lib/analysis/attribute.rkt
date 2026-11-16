#lang racket/base
;; Attribution of a failed assertion to a call (docs/triage.md 5).
;;
;; A failed clause asks for a fact about some variables.  The call that
;; should have given it is the last call on the path that produced one of
;; them (its result, its ghost result, or a value taken out of those: an
;; if-let's payload, a tuple's part) or changed one (passed by `&mut`).  When
;; no call touched them since the client's entry, the fact is asked of the
;; client's own parameters (`entry`): a clause that was not lifted into the
;; client's requires (a tied fresh parameter, goal.rkt), not a callee's.
;;
;; This follows the statements in the order of the elaborated client
;; (check-client), taking every statement before the failure (id-before?):
;; the statements of an earlier branch count as if that branch ran, an
;; over-approximation that only matters for clients with branches before the
;; failure.
;;
;; culprit : table plan-form ID -> (list API CALL-ID VAR) | 'entry | #f
;;   #f when ID is not an assertion of the client (a callee's precondition at a call)
;; asserted-expr : (ESTMT ...) ID -> E or #f   the expression asserted at ID
;; expr-vars : E -> (symbol ...)               the variables an expression reads
(require racket/list racket/match racket/string "../model/api.rkt" "../model/results.rkt")
(provide culprit asserted-expr expr-vars id-before? call-writes)

;; Statement ids (render.rkt): "s2.4.e1/1" is clause 1 of the first statement
;; of the else branch of statement 4 of the then branch of statement 2.
;; parse-id : string -> (values ((KIND . N) ...) CLAUSE) or (values #f #f)
(define (parse-id id)
  (match (and (string? id) (regexp-match #px"^s([0-9e.]+)(?:/([0-9]+))?$" id))
    [(list _ path clause)
     (define comps
       (for/list ([c (in-list (string-split path "."))])
         (match (regexp-match #px"^(e?)([0-9]+)$" c)
           [(list _ e n) (cons (if (equal? e "e") 'else 'then) (string->number n))]
           [_ #f])))
     (if (andmap values comps) (values comps (if clause (string->number clause) 0)) (values #f #f))]
    [_ (values #f #f)]))

;; id-before? : id id -> whether the first comes before the second on the
;; second's path (an earlier statement of an enclosing block, or an earlier
;; clause of the same statement).
(define (id-before? a b)
  (define-values (ca ka) (parse-id a))
  (define-values (cb kb) (parse-id b))
  (and ca cb
       (let loop ([ca ca] [cb cb])
         (cond
           [(and (null? ca) (null? cb)) (< ka kb)]
           [(null? ca) #t]                     ; a encloses b
           [(null? cb) #f]                     ; a is inside b's branches
           [(equal? (car ca) (car cb)) (loop (cdr ca) (cdr cb))]
           [else (and (eq? (caar ca) (caar cb)) (< (cdar ca) (cdar cb)))]))))

(define (asserted-expr body id)
  (define n (match (regexp-match #px"/([0-9]+)$" id) [(list _ k) (string->number k)] [_ #f]))
  (match (plan-stmt body id)
    [`(assert-requires ,_ ,_ ,clauses) #:when (and n (<= 1 n (length clauses))) (list-ref clauses (sub1 n))]
    [`(assert ,(== id) ,e ,_ ...) e]
    [_ #f]))

;; The variables an expression reads: not the names of methods, fields,
;; functions, constructors and constants.
(define (expr-vars e)
  (remove-duplicates
   (let loop ([e e])
     (match e
       [(? symbol? x) (if (memq x '(true false)) '() (list x))]
       [`(const ,_) '()]
       [`(src ,_) '()]
       [`(tmpl ,ps ...) (append-map loop (filter (lambda (p) (not (string? p))) ps))]
       [`(method ,a ,_ ,args ...) (append-map loop (cons a args))]
       [`(,(or 'field 'arrow) ,a ,_) (loop a)]
       [`(is ,a ,_) (loop a)]
       [`(as ,a ,_) (loop a)]
       [`(call ,_ ,args ...) (append-map loop args)]
       [`(record ,_ ,fs ...) (append-map (lambda (f) (loop (cadr f))) fs)]
       [`(,(or 'forall 'exists) ,bs ,body)
        (remq* (map car bs) (loop body))]
       [`(,(? symbol?) ,args ...) (append-map loop args)]
       [_ '()]))))

;; call-writes : table ESTMT -> (symbol ...), the variables a call changes or binds
(define (call-writes table s)
  (match s
    [`(call ,_ ,bind ,api-name (args ,as ...) (gargs ,gs ...) ,rest ...)
     (define api (api-ref table api-name))
     (define (mut? p) (and p (match (param-type p) [`(&mut ,_) #t] [_ #f])))
     (define (changed xs ps)
       (for/list ([a (in-list xs)] [i (in-naturals)]
                  #:when (match a
                           [`(mutref ,(? symbol?)) #t]
                           [`(,(or 'same 'reref) ,(? symbol?)) (mut? (and api (< i (length ps)) (list-ref ps i)))]
                           [_ #f]))
         (cadr a)))
     (append (changed as (if api (api-params api) '()))
             (changed gs (if api (api-ghost-params api) '()))
             (if (symbol? bind) (list bind) '())
             (match (assq 'gret rest) [`(gret ,(? symbol? g)) (list g)] [_ '()]))]
    [_ '()]))

(define (culprit table form id)
  (define body (plan-body form))
  (define e (asserted-expr body id))
  (and e
       (let ()
         ;; var -> (CALL-ID . API), the last call that wrote it before id
         (define writer (make-hasheq))
         (define (from! x ys) ; x takes the latest writer of ys
           (define ws (filter values (for/list ([y (in-list ys)]) (hash-ref writer y #f))))
           (if (null? ws) (hash-remove! writer x) (hash-set! writer x (latest ws))))
         (let walk ([ss body])
           (for ([s (in-list ss)])
             (define sid (and (pair? s) (pair? (cdr s)) (cadr s)))
             (when (and (string? sid) (id-before? sid id))
               (match s
                 ;; a vstd provider (`Option::tracked_unwrap`) only passes on what it is
                 ;; given: what it returns is from its arguments' writers
                 [`(call ,cid ,bind ,(? provider?) (args ,as ...) (gargs ,gs ...) ,rest ...)
                  (define ins (for/list ([a (in-list (append as gs))] #:when (and (pair? a) (pair? (cdr a)) (symbol? (cadr a)))) (cadr a)))
                  (when (symbol? bind) (from! bind ins))
                  (match (assq 'gret rest) [`(gret ,(? symbol? g)) (from! g ins)] [_ (void)])]
                 [`(call ,cid ,_ ,api ,_ ...)
                  (for ([x (in-list (call-writes table s))]) (hash-set! writer x (cons cid api)))]
                 [`(ghost ,_ ,x ,e ,_ ...) (from! x (expr-vars e))]
                 [`(untuple ,_ ((,xs ,_ ,_) ...) ,y) (for ([x (in-list xs)]) (from! x (list y)))]
                 [`(if-let ,_ ,_ ,x ,y (then ,tb ...) (else ,eb ...) ,more ...)
                  (from! x (list y))
                  (match (assq 'err more) [`(err ,(? symbol? er)) (from! er (list y))] [_ (void)])
                  (walk tb) (walk eb)]
                 [`(if ,_ ,_ (then ,tb ...) (else ,eb ...)) (walk tb) (walk eb)]
                 [`(if-not ,_ ,_ ,inner ...) (walk inner)]
                 [`(repeat ,_ ,_ ,_ ,inner ...) (walk inner)]
                 [_ (void)]))))
         (define touched
           (for*/list ([v (in-list (expr-vars e))] [w (in-value (hash-ref writer v #f))] #:when w)
             (cons v w)))
         (if (null? touched)
             'entry
             (let ([last (latest-of touched)])
               (list (cddr last) (cadr last) (car last)))))))

;; the APIs of vstd's providers (lib/providers/vstd.rktd)
(define provider-names
  (let ([names #f])
    (lambda ()
      (unless names
        (set! names (for/hasheq ([n (in-list (table-names (read-api-table vstd-providers)))]) (values n #t))))
      names)))
(define (provider? api) (hash-ref (provider-names) api #f))

;; the latest of writers (CALL-ID . API)
(define (latest ws)
  (for/fold ([a (car ws)]) ([b (in-list (cdr ws))]) (if (id-before? (car a) (car b)) b a)))
;; the latest of (VAR CALL-ID . API)
(define (latest-of ts)
  (for/fold ([a (car ts)]) ([b (in-list (cdr ts))]) (if (id-before? (cadr a) (cadr b)) b a)))
