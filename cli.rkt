#lang racket/base
;; client-synthesizer0: the command line (README.md; docs/design.md).
;;
;; The vostd checkout, Cargo's target directory and item-index are the
;; environment's (env.rktd under env.local.rktd or the file CS_ENV names;
;; lib/base/env.rkt).
;;   racket cli.rkt env                         is the environment ready
;;
;; Tables (design.md 3.2):
;;   racket cli.rkt scan     VIR MODULE-REGEX AUTO-DIR RUN-DIR [TABLE-REGEX]
;;                           extract the tables (and the targets: each module's
;;                           clients go beside it, design.md 3.8), repair and probe them
;;   racket cli.rkt vir-cache VIR OUT.fasl      read crate.vir once, keep it as fasl
;;   racket cli.rkt digest   VIR TABLE-DIR COMMIT OUT
;;                           fingerprints of the specifications of the table entries
;;   racket cli.rkt rename-by-key OLD-APIS NEW-APIS FILE-OR-DIR ...
;;                           after an update of vostd: names whose VIR name changed but
;;                           whose source key did not, rewritten in the files
;;
;; Call knowledge (design.md 3.7):
;;   racket cli.rkt knowledge AUTO-DIR KNOWLEDGE-DIR [MODULE-REGEX] [--providers FILE] [--fix] [--accept]
;;                           check the knowledge against the tables and its drift
;;                           against the checkout; --fix moves anchors, --accept records
;;                           the review (after reading the files again)
;;
;; Clients (design.md 3.6, 3.8):
;;   racket cli.rkt evaluate CONFIG RUN-DIR     generate and run the clients of every module; resumes
;;   racket cli.rkt compare  RUN-DIR RUN-DIR    status transitions client by client
;;   racket cli.rkt coverage RUN-DIR [MODULE-REGEX]
;;                           which ensures clauses some verified client's proof uses
;;                           (one logged run, the solver's unsat cores; design.md 3.10)
;;
;; Facts about failures (design.md 3.9, docs/triage.md):
;;   racket cli.rkt groups   RUN-DIR [KNOWLEDGE-DIR [ISSUES-DIR]] [MODULE-REGEX] [--verdicts DIR [--digests FILE]]
;;                           failures grouped by clause, labelled, with culprits and verdicts
;;   racket cli.rkt refute   RUN-DIR [MODULE-REGEX]      each group's assertion negated
;;   racket cli.rkt provable RUN-DIR COPY [MODULE-REGEX] [--dry] [--unlabelled KNOWLEDGE ISSUES VERDICTS]
;;                           each group's clause added to its culprit's ensures in COPY
;;   racket cli.rkt confirm  RUN-DIR COPY VIR [MODULE-REGEX] [--dry]
;;                           provable's survivors confirmed one by one, the failed clients rerun
;;   racket cli.rkt fixes    RUN-DIR COPY VIR FIXES-FILE
;;                           hand-written fixes (exact replacements) verified together and alone,
;;                           the target groups' modules rerun (design.md 3.9)
;;   racket cli.rkt drops   VIR MODULE-REGEX AUTO-DIR COPY OUT-DIR [--base PATCH]
;;                           facts functions prove and do not export
;;   racket cli.rkt verdict  RUN-DIR MODULE KEY JUDGEMENT REASON FILE [--issue ID] [--any-culprit]
;;                           append a verdict on a group to FILE
;;
;; Known issues (design.md 3.11):
;;   racket cli.rkt regress  CONFIG ISSUES RUN-DIR      run the witnesses; resumes
;;   racket cli.rkt regress-report ISSUES RUN-DIR [PATCHED-RUN-DIR]
;;   racket cli.rkt witness  RUN-DIR CLIENT ...         clients of a run printed as witnesses
;;
;; Trusted code (design.md 3.12):
;;   racket cli.rkt trusted  [COMMIT]                   the trusted sites at COMMIT
;;   racket cli.rkt audit    VERDICT-DIR [DEMO-RUN-DIR] [--accept [ID-REGEX]]
;;   racket cli.rkt demos    RUN-DIR DEMO.rs ...
;;
;; One table, one set of clients (for looking at a single case):
;;   racket cli.rkt check   TABLE CLIENTS              well-formedness only
;;   racket cli.rkt render  TABLE CLIENTS OUT.rs       the module run would verify
;;   racket cli.rkt run     TARGET TABLE CLIENTS OUT-DIR
;;   racket cli.rkt summary OUT-DIR                    group the results of a run
;;   racket cli.rkt probe   TARGET TABLE OUT-DIR       check every table entry against vostd
;;   racket cli.rkt extract VIR MODULE-REGEX OUT-DIR   tables and targets from VIR
;;   racket cli.rkt repair  TARGET TABLE OUT-DIR       probe, and apply rustc's suggestions
(require racket/list racket/match racket/file racket/pretty racket/string
         "lib/model/api.rkt" "lib/check/client.rkt" "lib/gen/render.rkt" "lib/vostd/run.rkt"
         "lib/analysis/probe.rkt" "lib/model/results.rkt" "lib/vostd/extract.rkt" "lib/analysis/repair.rkt"
         "lib/base/forms.rkt"
         "lib/pipeline/scan.rkt" "lib/pipeline/check-knowledge.rkt" "lib/pipeline/evaluate.rkt"
         "lib/pipeline/groups.rkt" "lib/pipeline/refute.rkt" "lib/pipeline/provable.rkt" "lib/pipeline/confirm.rkt"
         "lib/pipeline/compare.rkt" "lib/pipeline/drops.rkt" "lib/pipeline/rename.rkt" "lib/pipeline/trusted.rkt"
         "lib/pipeline/regress.rkt" "lib/pipeline/coverage.rkt" (only-in "lib/pipeline/fixes.rkt" fixes fixes-base)
         "lib/vostd/spec-digest.rkt" "lib/base/env.rkt" "lib/pipeline/environment.rkt"
         (only-in "lib/vostd/vir.rkt" cache-vir))

(define (read-clients file) (file->list file))

(define (check table-file clients-file)
  (define table (read-api-table table-file))
  (for ([c (in-list (read-clients clients-file))])
    (define e (check-client table c))
    (if (eq? (car e) 'ill-formed)
        (pretty-write `(client ,(cadr e) ill-formed ,@(cdddr e)))
        (pretty-write `(client ,(cadr e) well-formed)))))

(define (render table-file clients-file out)
  (define table (read-api-table table-file))
  (define es (filter (lambda (e) (eq? (car e) 'client))
                     (map (lambda (c) (check-client table c)) (read-clients clients-file))))
  (define-values (text _lmap) (render-module table es))
  (call-with-output-file out #:exists 'truncate (lambda (o) (write-string text o)))
  (void))

;; summary: counts by status; failures grouped by the API of the failing
;; statement, the message and the callee location.
(define (summary dir)
  (define results (file->list (build-path dir "results.rktd")))
  (define plan (file->list (build-path dir "plan.rktd")))
  (for ([r (in-list results)] #:unless (eq? (car r) 'client)) (pretty-write r))
  (define clients (filter (lambda (r) (eq? (car r) 'client)) results))
  (printf "\n")
  (for ([g (in-list (group-by caddr clients))])
    (printf "~a: ~a\n" (caddr (car g)) (length g)))
  (define failures
    (for*/list ([r (in-list clients)] #:when (memq (result-status r) '(failed compile-error not-verified))
                [e (in-list (result-errors r))])
      (define callee (error-callee e))
      (list (stmt-label (plan-body (plan-of plan (cadr r))) (error-id e))
            (error-message e)
            (if callee (format "~a  ~a" (car callee) (cadr callee)) "")
            (cadr r))))
  (unless (null? failures) (printf "\nfailures (api, message, callee): clients\n"))
  (for ([g (in-list (group-by (lambda (f) (take f 3)) failures))])
    (printf "  ~a | ~a | ~a: ~a\n" (car (car g)) (cadr (car g)) (caddr (car g))
            (map cadddr g)))
  (for ([r (in-list clients)] #:when (eq? (result-status r) 'ill-formed))
    (printf "  ill-formed ~a: ~s\n" (cadr r) (cdddr r)))
  (for ([r (in-list clients)] #:when (pair? (result-vacuous r)))
    (printf "  VACUOUS ~a: ~a\n" (cadr r) (result-vacuous r))))


(module+ main
  (match (current-command-line-arguments)
    [(vector "check" t c) (check t c)]
    [(vector "render" t c o) (render t c o)]
    [(vector "run" target t c dir)
     (run-clients target t (read-clients c) dir)
     (summary dir)]
    [(vector "summary" dir) (summary dir)]
    [(vector "probe" target t dir)
     (for-each pretty-write (probe-table target t dir))]
    [(vector "extract" vir rx dir)
     (pretty-write (extract-tables vir (regexp rx) (env-ref 'vostd) (env-program 'item-index) dir))]
    [(vector "repair" target t dir)
     (for-each pretty-write (repair-table target t dir))]
    [(vector "scan" vir rx auto run-dir more ...)
     (pretty-write (scan vir (regexp rx) (env-ref 'vostd) (env-program 'item-index) auto run-dir
                         (if (pair? more) (regexp (car more)) #rx"")))]
    [(vector "knowledge" auto kdir more0 ...)
     ;; --providers FILE (default: the vstd providers that come with the tool)
     (define-values (providers more)
       (let loop ([xs more0] [p vstd-providers] [acc '()])
         (match xs
           [(list "--providers" f rest ...) (loop rest f acc)]
           [(list x rest ...) (loop rest p (cons x acc))]
           ['() (values p (reverse acc))])))
     (define flags (filter (lambda (x) (regexp-match? #rx"^--" x)) more))
     (define rx (let ([r (filter (lambda (x) (not (regexp-match? #rx"^--" x))) more)]) (if (pair? r) (regexp (car r)) #rx"")))
     (when (pair? flags)
       (for-each pretty-write (update-knowledge! auto kdir rx #:fix? (and (member "--fix" flags) #t)
                                                 #:accept? (and (member "--accept" flags) #t))))
     (for-each pretty-write (check-knowledge auto kdir providers rx))]
    [(vector "digest" vir tdir commit out)
     (define ds (spec-digests vir tdir (env-ref 'vostd) commit))
     (make-parent-directory* out)
     (write-forms out ds)
     (printf "~a digests
" (length (cdr ds)))]
    [(vector "env") (for-each pretty-write (check-env))]
    [(vector "vir-cache" vir out) (printf "~a items
" (cache-vir vir out))]
    [(vector "evaluate" cfg dir) (void (evaluate cfg dir))]
    [(vector "drops" vir rx auto copy dir) (void (drops vir rx auto copy dir))]
    [(vector "drops" vir rx auto copy dir "--base" patch) (void (drops vir rx auto copy dir #:base patch))]
    [(vector "rename-by-key" old new targets ..1)
     (define-values (rs lost) (renames old new))
     (pretty-write `(renamed ,(length rs) ,@rs))
     (pretty-write `(no-new-entry ,(length lost) ,@lost))
     (for* ([t (in-list targets)]
            [f (in-list (if (directory-exists? t)
                            (for/list ([p (in-directory t)] #:when (regexp-match? #rx"[.]rktd$" (path->string p))) p)
                            (list t)))])
       (define n (rename-file! f rs))
       (when (> n 0) (printf "~a: ~a names\n" f n)))]
    [(vector "verdict" dir m key j reason file more ...)
     (pretty-write (record-verdict dir m key (string->symbol j) reason file
                                   #:issue (match (member "--issue" more) [(list* _ i _) (string->symbol i)] [_ #f])
                                   #:by? (not (member "--any-culprit" more))))]
    [(vector "groups" dir more0 ...)
     ;; options anywhere after RUN-DIR: --verdicts DIR, --digests FILE, --members (every group's clients)
     (define (opt name) (match (member name more0) [(list* _ v _) v] [_ #f]))
     (define members? (and (member "--members" more0) #t))
     (define more (let loop ([xs (remove "--members" more0)])
                    (match xs
                      [(list* (or "--verdicts" "--digests") _ rest) (loop rest)]
                      [(cons x rest) (cons x (loop rest))]
                      ['() '()])))
     (define kdir (and (pair? more) (directory-exists? (car more)) (car more)))
     (define more2 (if kdir (cdr more) more))
     (define idir (and kdir (pair? more2) (directory-exists? (car more2)) (car more2)))
     (define rx (let ([r (if idir (cdr more2) more2)]) (if (pair? r) (regexp (car r)) #rx"")))
     (for-each pretty-write (group-failures dir kdir rx idir #:verdicts (opt "--verdicts") #:digests (opt "--digests") #:members? members?))]
    [(vector "provable" dir copy more0 ...)
     ;; --unlabelled KNOWLEDGE-DIR ISSUES-DIR VERDICTS-DIR
     (define ul (let ([t (member "--unlabelled" more0)])
                  (and t (if (>= (length t) 4) (take (cdr t) 3)
                             (error 'provable "--unlabelled KNOWLEDGE-DIR ISSUES-DIR VERDICTS-DIR")))))
     (define more (let ([m (remove "--dry" more0)])
                    (if ul (let-values ([(a b) (splitf-at m (lambda (x) (not (equal? x "--unlabelled"))))]) (append a (drop b 4))) m)))
     (void (provable dir copy (if (pair? more) (pregexp (car more)) #rx"") #:dry? (and (member "--dry" more0) #t)
                     #:unlabelled ul))]
    ;; fixes-base FACTS FIXES-FILE [PREVIOUS-BASE]: the next run's base, the fixes that held (design.md 3.9)
    [(vector "fixes-base" facts file more ...)
     (for-each writeln (fixes-base facts file (and (pair? more) (car more))))]
    [(vector "fixes" dir copy vir file more ...)
     ;; --base FILE: confirmed fixes, frozen; --base-run DIR: the run with exactly the base (design.md 3.9)
     (define (opt name) (match (member name more) [(list* _ v _) v] [_ #f]))
     ;; --copies DIR,DIR: more copies of vostd, to verify slots in parallel
     (void (fixes dir copy vir file #:base (opt "--base") #:base-run (opt "--base-run")
                  #:copies (let ([c (opt "--copies")]) (if c (string-split c ",") '()))))]
    [(vector "confirm" dir copy vir more0 ...)
     (define more (remove "--dry" more0))
     (void (confirm dir copy vir (if (pair? more) (pregexp (car more)) #rx"") #:dry? (and (member "--dry" more0) #t)))]
    [(vector "refute" dir more ...) (void (refute dir (if (pair? more) (regexp (car more)) #rx"")))]
    [(vector "compare" a b) (for-each pretty-write (compare-runs a b))]
    [(vector "coverage" dir more ...) (for-each pretty-write (coverage dir (if (pair? more) (regexp (car more)) #rx"")))]
    [(vector "regress" cfg issues dir) (void (regress cfg issues dir))]
    [(vector "regress-report" issues run more ...)
     (for-each pretty-write (regress-report issues run (and (pair? more) (car more))))]
    [(vector "witness" run names ...)
     (for ([w (in-list (witness-forms run (map string->symbol names)))])
       (displayln (car w))
       (pretty-write (cadr w)))]
    [(vector "trusted") (for-each pretty-write (list-trusted (env-ref 'vostd)))]
    [(vector "trusted" commit) (for-each pretty-write (list-trusted (env-ref 'vostd) commit))]
    [(vector "audit" dir more ...)
     (define vostd (env-ref 'vostd))
     (define acc (member "--accept" more))
     (define run (let ([r (takef more (lambda (x) (not (equal? x "--accept"))))]) (and (pair? r) (car r))))
     (when acc
       (for-each pretty-write (accept-audit! vostd dir (if (pair? (cdr acc)) (regexp (cadr acc)) #rx""))))
     (for-each pretty-write (audit-check vostd dir run))]
    [(vector "demos" dir files ...)
     (void (run-demos (env-ref 'vostd) (env-ref 'target-dir) files dir))]
    [_ (eprintf "usage: see the comment at the top of cli.rkt\n") (exit 2)]))
