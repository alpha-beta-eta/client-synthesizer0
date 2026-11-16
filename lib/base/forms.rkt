#lang racket/base
;; Small helpers on the S-expression forms every module reads and writes:
;; tables, clients, enumeration specs, plans and results.
(require racket/list racket/string racket/pretty)
(provide form-ref form-flag? subst-symbols type-matches? stmt-id path-of write-forms)

;; form-ref : form symbol [default] -> the rest of the first field (KEY ...)
;; A form is (HEAD NAME FIELD ...), e.g. (client NAME (params ..) (body ..)).
(define (form-ref form key [default '()])
  (or (for/first ([f (in-list (cddr form))] #:when (and (pair? f) (eq? (car f) key))) (cdr f))
      default))

;; form-flag? : form symbol -> whether the field (KEY) is present
(define (form-flag? form key)
  (and (for/or ([f (in-list (cddr form))]) (and (pair? f) (eq? (car f) key))) #t))

;; subst-symbols : any ((symbol . any) ...) -> any, every symbol in binding replaced
(define (subst-symbols e binding)
  (cond [(and (symbol? e) (assq e binding)) => cdr]
        [(pair? e) (map (lambda (x) (subst-symbols x binding)) e)]
        [else e]))

;; type-matches? : TYPE-PATTERN TYPE -> boolean; `_` matches any type
(define (type-matches? pat typ)
  (cond [(eq? pat '_) #t]
        [(symbol? pat) (eq? pat typ)]
        [(and (pair? pat) (pair? typ) (= (length pat) (length typ))) (andmap type-matches? pat typ)]
        [else #f]))

;; Statement ids (design.md 结论4): "s3.2" is statement 2 of the body of
;; statement 3, "s3.e1" statement 1 of its else branch.
;; stmt-id : (segment ...) segment -> id, path being the reversed segments of the parent
(define (stmt-id path seg)
  (apply string-append "s" (add-between (reverse (cons seg path)) ".")))

;; path-of : id -> the reversed segments of the id
(define (path-of id)
  (reverse (string-split (substring id 1) ".")))

(define (write-forms file forms)
  (call-with-output-file file #:exists 'truncate
    (lambda (o) (for ([f (in-list forms)]) (pretty-write f o)))))
