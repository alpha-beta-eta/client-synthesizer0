#lang racket/base
;; Known issues, run again (design.md 3.11, evaluation.md 3.1 step 9).
;;
;; regress: the witnesses of the issues (lib/model/issues.rkt), grouped by
;; the module they run in, run as an evaluation runs a module's clients
;; (evaluate.rkt: the table from the configuration's auto/ with the other
;; modules' whose APIs they call, the same key for resuming).  The checkout
;; is the environment's: run once on the original and once, with CS_ENV, on
;; the patched one.  The run directory, as an evaluation's:
;;   manifest.rktd        configuration, issues, vostd, commit, Verus, changed files
;;   tables/<m>.rktd, clients/<m>.rktd, results/<m>/
;;   modules.rktd         one line per module
;;   issues.rktd          the report of this run (regress-report)
;;
;; regress-report: each issue's status in a run, or on the original and on
;; the patched run, and the witnesses that do not do what is expected.
;;
;; witness-forms: clients of a run, printed as witnesses, the expectation
;; their first judged error.
(require racket/file racket/list racket/match racket/path racket/pretty racket/string racket/port racket/system
         "../model/api.rkt" "../model/issues.rkt" "../model/results.rkt" "../base/forms.rkt"
         "../base/env.rkt" "../vostd/git.rkt"
         (only-in "evaluate.rkt" read-config config-auto config-providers table-of module-of
                  write-module-table must-close-of run-module verus-version))
(provide regress regress-report witness-forms)

;; The other modules (with a table in AUTO) whose APIs a client names.
(define (modules-called c auto m)
  (define found '())
  (let walk ([x c])
    (cond [(pair? x) (walk (car x)) (walk (cdr x))]
          [(symbol? x)
           (define o (module-of x))
           (when (and o (not (equal? o m)) (not (member o found)) (table-of auto o))
             (set! found (cons o found)))]
          [else (void)]))
  (sort found string<?))

;; clients-by-module : (issue ...) -> ((m client ...) ...), each client once
(define (clients-by-module issues)
  (define h (make-hash))
  (for* ([i (in-list issues)] [w (in-list (issue-witnesses i))])
    (define m (witness-module w))
    (define c (witness-client w))
    (define cur (hash-ref h m '()))
    (define same (findf (lambda (x) (eq? (cadr x) (cadr c))) cur))
    (cond [(not same) (hash-set! h m (append cur (list c)))]
          [(equal? same c) (void)]
          [else (error 'regress "~a: another witness in ~a is also named ~a, and differs" (issue-id i) m (cadr c))]))
  (for/list ([m (in-list (sort (hash-keys h) string<?))]) (cons m (hash-ref h m))))

;; regress : config-file issues-dir run-dir -> (fact ...)
(define (regress config-file issues-dir run-dir)
  (define cfg (read-config config-file))
  (define auto (config-auto cfg))
  (define issues (read-issues issues-dir))
  (define groups (clients-by-module issues))
  (for ([d (in-list '("tables" "clients" "results"))]) (make-directory* (build-path run-dir d)))
  (define-values (runnable missing) (partition (lambda (g) (table-of auto (car g))) groups))
  (define vostd
    (and (pair? runnable)
         (cadr (assq 'vostd (read-target (build-path auto "targets" (string-append (car (car runnable)) ".rktd")))))))
  (write-forms (build-path run-dir "manifest.rktd")
               `((manifest
                  (config ,(path->string (path->complete-path config-file)))
                  (issues ,(path->string (path->complete-path issues-dir)))
                  ,@(if vostd
                        `((vostd ,vostd) (commit ,(git-head vostd)) (verus ,(verus-version vostd))
                          (changed ,@(changed-files vostd)))
                        '())
                  (modules ,@(map car runnable)))))
  (define lines
    (append
     (for/list ([g (in-list missing)]) `(module ,(car g) (no-table ,(path->string auto))))
     (for/list ([g (in-list runnable)])
       (define m (car g))
       (define cs (cdr g))
       (define others (remove-duplicates (append* (for/list ([c (in-list cs)]) (modules-called c auto m)))))
       (define table-file (build-path run-dir "tables" (string-append m ".rktd")))
       (define table (write-module-table auto (config-providers cfg) m others table-file (must-close-of cfg (cons m others))))
       (define clients-file (build-path run-dir "clients" (string-append m ".rktd")))
       (write-forms clients-file cs)
       (define results (run-module (build-path auto "targets" (string-append m ".rktd"))
                                   table-file table clients-file cs (build-path run-dir "results" m)))
       (define line `(module ,m (witnesses ,(length cs)) ,(or (assq 'sanity results) '(sanity none))))
       (pretty-write line)
       (flush-output)
       line)))
  (write-forms (build-path run-dir "modules.rktd") lines)
  (define report (regress-report issues-dir run-dir))
  (write-forms (build-path run-dir "issues.rktd") report)
  report)

;; The files the checkout changes (a patch applied), without Cargo.lock.
(define (changed-files vostd)
  (define out (with-output-to-string
                (lambda () (system* (git-program) "-C" (if (path? vostd) (path->string vostd) vostd) "diff" "--name-only"))))
  (for/list ([l (in-list (string-split out "\n"))] #:unless (regexp-match? #rx"Cargo[.]lock$" l)) l))

;; ================================================================ report

(define (run-results run m)
  (define f (build-path run "results" m "results.rktd"))
  (if (file-exists? f) (file->list f) '()))

(define (statuses run i)
  (for/list ([w (in-list (issue-witnesses i))])
    (witness-status w (run-results run (witness-module w)))))

(define status-order '(shows passes vacuous other broken not-run not-concluded))
(define (counts ss)
  (for/list ([k (in-list status-order)] #:when (memq k ss)) (list k (count (lambda (s) (eq? s k)) ss))))

(define (first-error-text run w)
  (define r (result-of (run-results run (witness-module w)) (cadr (witness-client w))))
  (define e (and r (first-judged-error r)))
  (if e (list (error-text e)) '()))

(define (tally key xs)
  (define ks (remove-duplicates xs))
  `(,key ,@(for/list ([k (in-list ks)]) (list k (count (lambda (x) (eq? x k)) xs)))))

;; regress-report : issues-dir run [patched-run] -> (fact ...)
(define (regress-report issues-dir run [patched #f])
  (define issues (read-issues issues-dir))
  (define lines
    (for/list ([i (in-list issues)])
      (define o (statuses run i))
      (define p (and patched (statuses patched i)))
      (define head
        (if patched
            `(issue ,(issue-id i) (original ,(original-status o) ,@(counts o))
                    (patched ,(patched-status p) ,@(counts p)))
            `(issue ,(issue-id i) ,(original-status o) ,@(counts o))))
      (define details
        (for/list ([w (in-list (issue-witnesses i))] [so (in-list o)] [sp (in-list (or p (map (lambda (_) 'passes) o)))]
                   #:unless (and (eq? so 'shows) (memq sp '(passes other))))
          `(witness ,(issue-id i) ,(cadr (witness-client w))
                    (original ,so ,@(if (eq? so 'shows) '() (first-error-text run w)))
                    ,@(if patched `((patched ,sp ,@(if (eq? sp 'passes) '() (first-error-text patched w)))) '()))))
      (list (list* head (append (if (issue-no-witness i) `((no-witness ,(issue-id i) ,(issue-no-witness i))) '()) details))
            (original-status o) (and p (patched-status p)))))
  (append (list (tally 'original (map cadr lines)))
          (if patched (list (tally 'patched (map caddr lines))) '())
          (append* (map car lines))))

;; ================================================================ taking witnesses

;; default-expectation : error -> (requires API N), (claim), or (EXPECTED): the
;; failed clause by its identity (issues.rkt); (EXPECTED) is not readable as an
;; expectation, so a witness without one is written by hand before use
(define (default-expectation e)
  (define t (error-text e))
  (define id (error-id e))
  (define api (and (string? t) (regexp-match #px"// requires of (\\S+)\\s*$" t)))
  (define n (and (string? id) (regexp-match #px"/([0-9]+)$" id)))
  (cond
    [(and api n) (list 'requires (string->symbol (cadr api)) (string->number (cadr n)))]
    [(and (string? t) (regexp-match? #px"// claim\\s*$" t)) '(claim)]
    [else '(EXPECTED)]))

;; witness-forms : run (NAME ...) -> (form ...), with a comment line before each
(define (witness-forms run names)
  (define cdir (build-path run "clients"))
  (define files (for/list ([f (in-list (directory-list cdir))] #:when (regexp-match? #rx"[.]rktd$" (path->string f))) f))
  (for/list ([n (in-list names)])
    (define found
      (for*/first ([f (in-list files)] [c (in-list (file->list (build-path cdir f)))] #:when (eq? (cadr c) n))
        (cons (path->string (path-replace-extension f #"")) c)))
    (unless found (error 'witness "~a: no client ~a" run n))
    (define m (car found))
    (define r (result-of (run-results run m) n))
    (define e (and r (first-judged-error r)))
    (list (format ";; ~a in ~a: ~a~a" n m (if r (result-status r) 'not-run)
                  (if e (format ", ~a at ~s" (error-message e) (error-text e)) ""))
          `(witness (module ,m) (fails ,(if e (default-expectation e) (quote (EXPECTED)))) ,(cdr found)))))
