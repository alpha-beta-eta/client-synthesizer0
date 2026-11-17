#lang racket/base
;; How one module's clients are run (design.md 3.8): the run itself
;; (vostd/run.rkt), halves after a crash, and the rounds of imports rustc
;; suggests (or reports private).  What this file decides changes a module's
;; results, so its hash is part of the key a run resumes by (evaluate.rkt's
;; runner-version), with render.rkt's, run.rkt's and repair.rkt's.
(require racket/file racket/list racket/match racket/string
         "../model/api.rkt" "../model/results.rkt" "../base/forms.rkt" "../vostd/run.rkt"
         (only-in "../analysis/repair.rkt" import-suggestion choose-uses))
(provide run-with-imports run-split private-uses without-uses)

(define min-split 16)

(define (run-split target table cs dir)
  (run-clients target table cs dir)
  (define results (file->list (build-path dir "results.rktd")))
  (cond
    [(and (equal? (assq 'verification results) '(verification crashed)) (> (length cs) min-split))
     (define-values (a b) (split-at cs (quotient (length cs) 2)))
     (define ra (run-split target table a (build-path dir "1")))
     (define rb (run-split target table b (build-path dir "2")))
     (define (facts rs) (filter (lambda (r) (not (eq? (car r) 'client))) rs))
     (define crashed? (member '(verification crashed) (append (facts ra) (facts rb))))
     (define merged
       (append (if crashed? '((verification crashed)) '())
               (filter (lambda (f) (not (eq? (car f) 'verification))) (facts ra))
               (filter (lambda (r) (eq? (car r) 'client)) (append ra rb))))
     (write-forms (build-path dir "results.rktd") merged)
     merged]
    [else results]))

;; import-uses : results existing-use-lines -> new use lines
;; The imports rustc suggests for the compile errors of the clients.
(define (import-uses results existing)
  (choose-uses
   existing
   (for*/list ([r (in-list results)] #:when (and (eq? (car r) 'client) (eq? (result-status r) 'compile-error))
               [e (in-list (result-errors r))]
               [h (in-list (cddddr e))] #:when (and (pair? h) (eq? (car h) 'help))
               [u (in-value (match (cdr h) [(list heading code ...) (import-suggestion heading code)] [_ #f]))]
               #:when u)
     u)))

(define (count-verified results)
  (count (lambda (r) (and (eq? (car r) 'client) (eq? (result-status r) 'verified))) results))

;; run-with-imports : target table-file cs dir -> results
;; The imports rustc suggests are added and the module run again, in rounds
;; (at most import-rounds): rustc reports its errors in stages, names first
;; (`SpinGuardian` not found) and methods only once those resolve (`deref`
;; of a trait not in scope), so the suggestions of the next stage appear
;; only after a round.  A round is kept only if no client that verified
;; stops verifying; the rounds' directories are DIR/imports, imports-2, ..
;; A use line of the table's own (uses ..) forms that rustc reports private
;; (E0603) is taken out in the same round: it names a module through a private
;; child (`use crate::mm::page_table::cursor::*;`, write-module-table's import
;; of another module, from the client module beside page_table), which no
;; caller outside the parent can write either; the parent's re-exports, or the
;; suggestions of the next round, supply the names (design.md 3.8).
(define import-rounds 3)
(define (run-with-imports target table-file cs dir)
  (define results0 (run-split target table-file cs dir))
  (define (report results added dropped)
    (append (if (null? added) '() `((imports ,@added)))
            (if (null? dropped) '() `((dropped-imports ,@dropped)))
            results))
  (let loop ([results results0] [rdir dir] [added '()] [dropped '()] [round 1])
    (define forms (file->list table-file))
    (define extra (if (<= round import-rounds)
                      (import-uses results (api-table-uses (read-api-table table-file)))
                      '()))
    (define private (if (<= round import-rounds) (private-uses results rdir forms) '()))
    (cond
      [(and (null? extra) (null? private))
       (define rs (report results added dropped))
       (unless (and (null? added) (null? dropped))
         (write-forms (build-path dir "results.rktd") rs))
       rs]
      [else
       (write-forms table-file (append (without-uses forms private)
                                       (if (null? extra) '() `((uses ,@extra)))))
       (define ndir (build-path dir (if (= round 1) "imports" (format "imports-~a" round))))
       (define next (run-split target table-file cs ndir))
       (cond
         [(>= (count-verified next) (count-verified results))
          (loop next ndir (append added extra) (append dropped private) (add1 round))]
         [else
          (write-forms table-file forms)
          (loop results rdir added dropped (add1 import-rounds))])])))

;; private-uses : results run-dir table-forms -> (use-line ...)
;; The use lines of the table file's own (uses ..) forms (not its bases') at
;; which the run's unattributed errors are E0603: the line of the rendered
;; clients.rs the error points at is that use line.
(define (private-uses results rdir forms)
  (define own (append* (for/list ([f (in-list forms)] #:when (and (pair? f) (eq? (car f) 'uses))) (cdr f))))
  (define rendered (build-path rdir "clients.rs"))
  (define lines (if (file-exists? rendered) (list->vector (file->lines rendered)) (vector)))
  (remove-duplicates
   (for*/list ([r (in-list results)]
               #:when (and (pair? r) (eq? (car r) 'unattributed) (= (length r) 3)
                           (regexp-match? #rx"^\\[E0603\\]" (cadr r)))
               [n (in-value (match (regexp-match #rx":([0-9]+)$" (caddr r))
                              [(list _ k) (string->number k)] [_ #f]))]
               #:when (and n (<= 1 n (vector-length lines)))
               [text (in-value (string-trim (vector-ref lines (sub1 n))))]
               #:when (member text own))
     text)))

;; without-uses : table-forms (use-line ...) -> table-forms, the lines taken
;; out of the (uses ..) forms (a form left empty goes)
(define (without-uses forms lines)
  (if (null? lines)
      forms
      (for*/list ([f (in-list forms)]
                  [g (in-value (if (and (pair? f) (eq? (car f) 'uses))
                                   (cons 'uses (filter (lambda (u) (not (member u lines))) (cdr f)))
                                   f))]
                  #:unless (equal? g '(uses)))
        g)))
