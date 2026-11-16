#lang racket/base
;; The whole-module scan (design.md 3.2, evaluation.md 4): extract the tables
;; from VIR, then repair and probe each one.
;;
;; AUTO-DIR gets apis/, targets/ and left-out.rktd (extract.rkt), fixes/<m>.rktd
;; (the overlay of mechanical repairs, when there are any; repair.rkt) and
;; probe/<m>.rktd (the facts of the last round).  RUN-DIR/<m>/ keeps the runs.
;; There are no hand overlays: a table is what extraction and the mechanical
;; repairs give (design.md 原则10); what a person decides about the APIs is
;; call knowledge (must-close, roles, ...).
;; TABLE-REGEX limits repair and probe to the tables whose names match (e.g.
;; `^mm[.]kspace`); everything is extracted all the same.  Modules run one
;; after another: they share the vostd checkout.
(require racket/file racket/list racket/pretty racket/path racket/string
         "../vostd/extract.rkt" "../analysis/repair.rkt" "../base/forms.rkt")
(provide scan)

;; scan : vir module-regex vostd item-index auto-dir run-dir table-regex
;;   -> the extraction summary; writes AUTO-DIR as above
(define (scan vir rx vostd ii auto run-dir [only #rx""])
  (define summary (extract-tables vir rx vostd ii auto))
  (make-directory* (build-path auto "fixes"))
  (make-directory* (build-path auto "probe"))
  (for ([t (in-list (sort (map path->string (directory-list (build-path auto "apis"))) string<?))]
        #:when (regexp-match? only t))
    (define m (path->string (path-replace-extension t #"")))
    (define dir (build-path run-dir m))
    (printf "~a\n" m)
    (flush-output)
    (define facts (repair-table (build-path auto "targets" t) (build-path auto "apis" t) dir))
    (define fix (build-path dir "table.rktd"))
    (define fixes (build-path auto "fixes" t))
    (if (file-exists? fix) (copy-overlay fix fixes) (when (file-exists? fixes) (delete-file fixes)))
    (write-forms (build-path auto "probe" t) facts))
  summary)

;; copy-overlay : the repair's overlay (in the run directory, its base an
;; absolute path) -> AUTO-DIR/fixes/<m>.rktd, its base relative to it
;; (`../apis/<m>.rktd`): the data stay valid where the
;; repository is moved or copied.
(define (copy-overlay from to)
  (define dir (path-only (path->complete-path to)))
  (define (rel p) (path->string (find-relative-path (simplify-path dir) (simplify-path (path->complete-path p)))))
  (define text (file->string from))
  (define base (for/first ([f (in-list (file->list from))] #:when (and (pair? f) (eq? (car f) 'base))) (cadr f)))
  (define r (and base (string-replace (rel base) "\\" "/")))
  (call-with-output-file to #:exists 'truncate
    (lambda (o)
      (write-string (if r
                        (string-replace (string-replace text (format "~s" base) (format "~s" r))
                                        (format "Repairs of ~a " base) (format "Repairs of ~a " r))
                        text)
                    o))))
