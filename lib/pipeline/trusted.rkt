#lang racket/base
;; Trusted code (design.md 3.12, evaluation.md 9): what Verus trusts without
;; checking, listed mechanically (lib/vostd/trusted.rkt), the judgements of it
;; as data (lib/model/audit.rkt) checked against the checkout, and the
;; demonstrations that some of it is too strong, run as verified code.
;;
;; list-trusted: every site at a commit of the checkout (default HEAD).
;;
;; audit-check: the verdicts (data/audit/verdicts/*.rktd) against the sites
;; at the checkout's HEAD, with the demos' statuses of a demo run if given;
;; accept-audit!: after the changed sites were judged again, their
;; fingerprints are written and the files are at HEAD.
;;
;; run-demos: each demo file (data/audit/demos/*.rs) says on its first line
;; where it goes:
;;   // Module path: ostd/src/mm/frame/audit_demo.rs (crate::mm::frame::audit_demo),
;;   //   `mod audit_demo;` in ostd/src/mm/frame/mod.rs
;; It is installed there, its module verified, and the checkout restored.  A
;; run directory as an evaluation's (pipeline/evaluate.rkt), so that `compare`
;; and resuming work the same way:
;;   manifest.rktd             vostd, commit, Verus version, the demo files
;;   results/<demo>/results.rktd   (client FN STATUS (error MESSAGE LINE) ...) ... (sanity ..)
;;   results/<demo>/verus.out, key.sha   the run, and the hash of the demo and the checkout's state
;;   demos.rktd                one line per demo
;; A demo function verifies when no error falls in it; `demo_sanity` (an
;; `assert(false)`) must fail, and must be the only one that does, or the
;; module was not really verified and nothing is to be concluded: then
;; (sanity bad) and every function's status is not-concluded.
(require racket/file racket/list racket/match racket/string racket/path racket/pretty file/sha1
         "../vostd/run.rkt" "../vostd/git.rkt" "../vostd/trusted.rkt" "../model/audit.rkt"
         (only-in "evaluate.rkt" vostd-state verus-version restore-lock))
(provide list-trusted audit-check accept-audit! run-demos demo-statuses)

;; ================================================================ listing

(define (list-trusted vostd [commit #f])
  (trusted-sites vostd (or commit (git-head vostd))))

(define (audit-files dir)
  (for/list ([f (in-list (sort (map path->string (directory-list dir)) string<?))]
             #:when (regexp-match? #rx"[.]rktd$" f))
    (build-path dir f)))

;; audit-check : vostd verdict-dir [demo-run-dir] -> (fact ...)
(define (audit-check vostd dir [demo-run #f])
  (define audits (map read-audit (audit-files dir)))
  (define head (git-head vostd))
  (cons `(checkout ,head)
        (check-audit audits (trusted-sites vostd head) (and demo-run (demo-statuses demo-run)))))

;; accept-audit! : vostd verdict-dir [regexp] -> (fact ...)
(define (accept-audit! vostd dir [only #rx""])
  (define head (git-head vostd))
  (define sites (trusted-sites vostd head))
  (for/list ([f (in-list (audit-files dir))])
    (define-values (a ids) (accept-audit (read-audit f) sites head only))
    (write-audit a)
    `(accepted ,(audit-area a) (at ,head) ,@ids)))

;; ================================================================ demos

(define (demo-placement file)
  (match (regexp-match #px"^// Module path: (\\S+) \\(crate::(\\S+)\\), `([^`]+)` in (\\S+)" (car (file->lines file)))
    [(list _ dest module line mod-file) (values dest module line mod-file)]
    [_ (error 'run-demos "~a: no placement on the first line" file)]))

(define (file-name p) (path->string (file-name-from-path p)))
(define (stem p) (path->string (path-replace-extension (file-name-from-path p) #"")))

;; run-demos : vostd target-dir (demo-file ...) run-dir -> (fact ...)
(define (run-demos vostd target-dir files run-dir)
  (make-directory* (build-path run-dir "results"))
  (write-forms (build-path run-dir "manifest.rktd")
               `((manifest (vostd ,vostd) (commit ,(git-head vostd)) (verus ,(verus-version vostd))
                           (demos ,@(map file-name files)))))
  (define lines
    (for/list ([file (in-list files)])
      (define line (run-demo vostd target-dir file run-dir))
      (pretty-write line)
      (flush-output)
      line))
  (write-forms (build-path run-dir "demos.rktd") lines)
  lines)

(define (run-demo vostd target-dir file run-dir)
  (define-values (dest module line mod-file) (demo-placement file))
  (define text (file->string file))
  (define dir (build-path run-dir "results" (stem file)))
  (define sha (sha1 (open-input-string (string-append text (vostd-state vostd)))))
  (define sha-file (build-path dir "key.sha"))
  (define results
    (cond
      [(and (file-exists? sha-file) (equal? (file->string sha-file) sha) (file-exists? (build-path dir "results.rktd")))
       (file->list (build-path dir "results.rktd"))]
      [else
       (when (directory-exists? dir) (delete-directory/files dir))
       (make-directory* dir)
       (define target `((vostd ,vostd) (package "ostd") (module ,module) (file ,dest)
                        (mod-file ,mod-file) (mod-anchor end) (mod-line ,line) (target-dir ,target-dir)))
       (define out (build-path dir "verus.out"))
       (with-client-module target
         (lambda ()
           (call-with-output-file (build-path vostd dest) #:exists 'truncate (lambda (o) (write-string text o)))
           (run-verus target out)))
       (restore-lock vostd)
       (define-values (verified errors) (parse-verus (file->lines out)))
       (define rs (demo-results text dest verified errors))
       (write-forms (build-path dir "results.rktd") rs)
       (call-with-output-file sha-file #:exists 'truncate (lambda (o) (write-string sha o)))
       rs]))
  (summarize (file-name file) results))

;; the results of one demo module's run
(define (demo-results text dest verified errors)
  ;; the demo function each line is in
  (define fns
    (for/fold ([cur #f] [acc '()] #:result (list->vector (reverse acc))) ([l (in-list (string-split text "\n" #:trim? #f))])
      (define n (match (regexp-match #px"\\bfn\\s+(demo_[A-Za-z0-9_]*)" l) [(list _ n) n] [_ cur]))
      (values n (cons n acc))))
  (define (fn-at ln) (and ln (<= 1 ln (vector-length fns)) (vector-ref fns (sub1 ln))))
  (define here (regexp (string-append (regexp-quote (file-name dest)) "$")))
  (define in-demo (for/list ([e (in-list errors)] #:when (and (cadr e) (regexp-match? here (cadr e))))
                    (cons (fn-at (caddr e)) e)))
  (define all (remove-duplicates (filter values (vector->list fns))))
  (define failed (remove-duplicates (filter values (map car in-demo))))
  (define sane? (and verified (equal? failed '("demo_sanity")) (= (length errors) (length in-demo))))
  (append
   (for/list ([f (in-list all)])
     (define es (filter (lambda (x) (equal? (car x) f)) in-demo))
     `(client ,(string->symbol f)
              ,(cond [(not sane?) 'not-concluded] [(null? es) 'verified] [else 'failed])
              ,@(for/list ([x (in-list es)]) `(error ,(cadr x) ,(cadddr x)))))
   (list `(sanity ,(if sane? 'ok 'bad))
         `(verus ,@(or verified '(not-verified)))
         `(errors-outside ,(- (length errors) (length in-demo))))))

(define (summarize name results)
  (define clients (filter (lambda (r) (eq? (car r) 'client)) results))
  `(demo ,name ,(assq 'sanity results)
         (verified ,@(for/list ([c clients] #:when (eq? (caddr c) 'verified)) (cadr c)))
         (failed ,@(for/list ([c clients] #:when (eq? (caddr c) 'failed)) (cadr c)))
         ,(assq 'verus results)))

;; demo-statuses : run-dir -> hash "FILE.rs" -> hash "FN" -> STATUS
(define (demo-statuses run-dir)
  (define d (build-path run-dir "results"))
  (for/hash ([m (in-list (if (directory-exists? d) (directory-list d) '()))]
             #:when (file-exists? (build-path d m "results.rktd")))
    (values (string-append (path->string m) ".rs")
            (for/hash ([r (in-list (file->list (build-path d m "results.rktd")))] #:when (eq? (car r) 'client))
              (values (symbol->string (cadr r)) (caddr r))))))

(define (write-forms file forms)
  (call-with-output-file file #:exists 'truncate (lambda (o) (for ([f (in-list forms)]) (pretty-write f o)))))
