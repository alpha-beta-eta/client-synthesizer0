#lang racket/base
;; Evaluating the specs of whole modules (design.md 3.6-3.9, evaluation.md 6).
;;
;; An evaluation is described by a configuration (an S-expression file):
;;   (evaluation
;;     (auto DIR)                 the whole-module scan: apis/, fixes/, probe/, targets/
;;     [(providers FILE)]         the vstd providers' table (default: lib/providers/vstd.rktd)
;;     [(knowledge DIR)]          call knowledge, DIR/<m>.rktd
;;     [(identity FILE)]          round-trip declarations
;;     [(modules REGEX)]          the modules to evaluate (default: all)
;;     [(families NAME ...)]      from the registry (gen/families.rkt; default: all)
;;     [(elided-lifetimes)])      a free lifetime may be '_ (design.md 3.5)
;; Paths in it are relative to the configuration file.
;;
;; The run directory:
;;   manifest.rktd        the configuration, the vostd commit and Verus version
;;   tables/<m>.rktd      the module's table with the providers (and the tables
;;                        of other modules its protocols call)
;;   clients/<m>.rktd     the clients generated
;;   results/<m>/         the run of them (vostd/run.rkt), with key.sha
;;   modules.rktd         one line per module (rewritten after each module)
;; A module whose results/<m>/key.sha is the hash of the clients generated now,
;; of the imports of its table, of the clients as elaborated against the table
;; (client.rkt: the clauses asserted and lifted), of the code that renders and runs them
;; (render.rkt, run.rkt) and of the checkout's state (its commit and `git
;; diff`, without Cargo.lock) is not run again: an interrupted evaluation
;; resumes where it stopped, and results of another state of vostd (a patch
;; applied or not), of other imports (a repair changed) or of another version
;; of the runner are not reused.
;;
;; A client runs inside module m (targets/<m>.rktd) but may name another
;; module's types (a protocol's calls, a type an API's signature mentions
;; that m does not import).  What is in scope there is known only to rustc:
;; after a run, the import suggestions of its compile errors (one candidate,
;; as in repair.rkt) join the table's uses and the module runs again, in
;; results/<m>/imports/; that run is kept unless fewer clients verify.
;;
;; Verus may crash on a large module (a panic in the solver, out of memory);
;; then the clients run again in two halves, results/<m>/1 and /2,
;; recursively down to MIN-SPLIT clients, and the results are merged.
(require racket/file racket/list racket/match racket/path racket/pretty racket/string racket/system
         racket/port racket/runtime-path file/sha1
         "../model/api.rkt" "../model/results.rkt" "../model/knowledge.rkt" "../base/forms.rkt"
         "../gen/families.rkt" "../vostd/run.rkt" "../vostd/git.rkt" "../base/env.rkt"
         (only-in "../analysis/repair.rkt" import-suggestion choose-uses)
         (only-in "../check/client.rkt" check-client)
         (only-in "../gen/enum.rkt" current-none-vacuous))
(provide evaluate read-config summary-line probe-ok probe-none-vacuous generate-module vostd-state verus-version restore-lock runner-version
         config-auto config-providers table-of module-of write-module-table must-close-of run-module)

(define min-split 16)

;; ================================================================ configuration

(struct config (file auto providers knowledge identity modules families elided-lifetimes?)
  #:transparent)

(define config-keys '(auto providers knowledge identity modules families elided-lifetimes))

;; An unknown key is an error, not ignored: a configuration of the earlier tool
;; (`chain`, `module` overrides) would otherwise run with other options than it says.
(define (read-config file)
  (define forms (file->list file))
  (define ev (or (assq 'evaluation forms) (error 'evaluate "~a: no (evaluation ..)" file)))
  (for ([f (in-list (cdr ev))])
    (unless (and (pair? f) (memq (car f) config-keys))
      (error 'evaluate "~a: unknown form ~s (the keys: ~a)" file f config-keys)))
  (define dir (let-values ([(d _n _x) (split-path (path->complete-path file))]) d))
  (define (path p) (simplify-path (if (absolute-path? p) p (build-path dir p))))
  (define (one key [default #f]) (match (assq key (cdr ev)) [`(,_ ,v) v] [_ default]))
  (define fams (cond [(assq 'families (cdr ev)) => cdr] [else family-names]))
  (for-each family-ref fams)
  (config file
          (path (or (one 'auto) (error 'evaluate "no (auto DIR)")))
          (let ([p (one 'providers)]) (if p (path p) (simplify-path vstd-providers)))
          (let ([k (one 'knowledge)]) (and k (path k)))
          (let ([i (one 'identity)]) (and i (path i)))
          (regexp (one 'modules ".*"))
          fams
          (and (assq 'elided-lifetimes (cdr ev)) #t)))

;; ================================================================ the scan's data

(define (table-of auto m)
  (for/first ([d (in-list '("fixes" "apis"))]
              #:when (file-exists? (build-path auto d (string-append m ".rktd"))))
    (build-path auto d (string-append m ".rktd"))))

(define (probe-ok facts-file)
  (for/list ([f (in-list (file->list facts-file))]
             #:when (and (eq? (car f) 'api) (eq? (caddr f) 'ok)))
    (cadr f)))

;; probe-none-vacuous : (facts-file ...) -> hash API-name -> (PARAM ...), the
;; tracked Option parameters None may not be given for (analysis/probe.rkt)
(define (probe-none-vacuous files)
  (for*/fold ([h (hash)]) ([file (in-list files)] #:when (file-exists? file)
                           [f (in-list (file->list file))]
                           #:when (and (pair? f) (eq? (car f) 'none-vacuous)))
    (hash-update h (cadr f) (lambda (l) (cons (caddr f) l)) '())))

;; The module of an API name: mm::frame::segment::impl&%3::slice is mm.frame.segment.
(define (module-of a)
  (match (regexp-match #rx"^(.*?)::(impl&%[0-9]+::)?[^:]+$" (symbol->string a))
    [(list _ path _) (regexp-replace* #rx"::" path ".")]
    [_ #f]))

;; ================================================================ versions



;; The Verus `cargo dv` runs: the project's (env.rktd's verus-bin), or the one
;; `cargo dv bootstrap` installed on PATH (~/.cargo/bin), or, with older Verus,
;; the build in the checkout's tools/verus.
;; "0.2026.11.05.84ae63e": the date and the commit of asterinas/verus.
(define (verus-version vostd)
  (define exe
    (or (for/first ([n (in-list '("verus.exe" "verus"))]
                    #:when (file-exists? (build-path vostd "tools" "verus" "source" "target-verus" "release" n)))
          (build-path vostd "tools" "verus" "source" "target-verus" "release" n))
        (let ([bin (env-ref 'verus-bin #f)])
          (and bin (for/first ([n (in-list '("verus.exe" "verus"))] #:when (file-exists? (build-path bin n)))
                     (build-path bin n))))
        (find-executable-path "verus.exe")
        (find-executable-path "verus")))
  (if exe
      (let ([s (string-trim (with-output-to-string
                              (lambda () (parameterize ([current-error-port (open-output-nowhere)])
                                           (system* exe "--version")))))])
        ;; no version in the output (Verus did not start: a toolchain missing
        ;; from PATH): what it printed, or "unknown"
        (cond [(regexp-match #rx"[0-9]+(?:[.][0-9a-f]+)+" s) => car]
              [(equal? s "") "unknown"]
              [else s]))
      "unknown"))

(define (path->string* p) (if (path? p) (path->string p) p))

;; The state of a checkout: its commit and the hash of its changes (not Cargo.lock).
(define (vostd-state vostd)
  (define diff (with-output-to-string
                 (lambda () (system* (git-program) "-C" (path->string* vostd)
                                     "diff" "HEAD" "--" "." ":(exclude)Cargo.lock"))))
  (string-append (git-head vostd) " " (sha1 (open-input-string diff))))

(define (restore-lock vostd)
  (void (system* (git-program) "-C" (path->string* vostd) "checkout" "--" "Cargo.lock")))

;; ================================================================ generation

;; The clients of module m: every configured family's.  No family needs a
;; budget by depth any more (the goal family asks one question per client).
(define (generate cfg m table names protocol-names k)
  (define id (if (config-identity cfg) (file->list (config-identity cfg)) '()))
  (define ctx (context table names k id protocol-names (config-elided-lifetimes? cfg)))
  (append*
   (for/list ([name (in-list (config-families cfg))])
     (define fam (family-ref name))
     (if (and (family-needs-knowledge? fam) (null? k)) '() ((family-generate fam) ctx)))))

;; ================================================================ running

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
(define import-rounds 3)
(define (run-with-imports target table-file cs dir)
  (define results0 (run-split target table-file cs dir))
  (let loop ([results results0] [all '()] [round 1])
    (define extra (and (<= round import-rounds)
                       (import-uses results (api-table-uses (read-api-table table-file)))))
    (cond
      [(or (not extra) (null? extra))
       (unless (null? all)
         (write-forms (build-path dir "results.rktd") (append `((imports ,@all)) results)))
       (if (null? all) results (append `((imports ,@all)) results))]
      [else
       (define forms (file->list table-file))
       (write-forms table-file (append forms `((uses ,@extra))))
       (define next (run-split target table-file cs
                               (build-path dir (if (= round 1) "imports" (format "imports-~a" round)))))
       (cond
         [(>= (count-verified next) (count-verified results))
          (loop next (append all extra) (add1 round))]
         [else
          (write-forms table-file forms)
          (loop results all (add1 import-rounds))])])))

;; A failed client all of whose errors are at clauses `P ==> may_panic()`
;; (asserted by the client, or a callee's precondition: results.rkt).
(define (panic-only? r)
  (define errs (result-errors r))
  (and (eq? (result-status r) 'failed) (pair? errs) (andmap panic-error? errs)))

;; The family of a client, by its name's prefix (the goal family's R1 clients
;; are named flow_ after the realizer they share with the earlier flow family).
(define family-prefixes '(("goal_" . goal) ("flow_" . goal) ("claim_" . claim) ("protocol_" . protocol)))
(define (client-family name)
  (for/first ([p (in-list family-prefixes)] #:when (string-prefix? (symbol->string name) (car p))) (cdr p)))

;; summary-line : module clients results -> (module M ...)
(define (summary-line m n results)
  (define clients (filter (lambda (r) (eq? (car r) 'client)) results))
  `(module ,m (clients ,n)
     ,(or (assq 'sanity results) '(sanity none))
     ,@(if (member '(verification crashed) results) '((verus-crashed)) '())
     ,@(for/list ([g (in-list (group-by result-status clients))])
         (list (result-status (car g)) (length g)))
     ;; failed only at "may panic here" clauses (`P ==> may_panic()`)
     (failed-panic-only ,(count panic-only? clients))
     (families ,@(for*/list ([f (in-list (remove-duplicates (map cdr family-prefixes)))]
                             [rs (in-value (filter (lambda (r) (eq? (client-family (cadr r)) f)) clients))]
                             #:when (pair? rs))
                   (list f (count (lambda (r) (eq? (result-status r) 'verified)) rs) (length rs))))
     (vacuous ,@(for/list ([r (in-list clients)] #:when (pair? (result-vacuous r))) (cadr r)))))

;; ================================================================ evaluate

(define-runtime-path render-source "../gen/render.rkt")
(define-runtime-path run-source "../vostd/run.rkt")
(define (runner-version)
  (string-append (call-with-input-file render-source sha1) (call-with-input-file run-source sha1)))

;; evaluate : config-file run-dir -> (line ...)
(define (evaluate config-file run-dir)
  (define cfg (read-config config-file))
  (define auto (config-auto cfg))
  (define modules
    (for/list ([f (in-list (sort (map path->string (directory-list (build-path auto "probe"))) string<?))]
               #:when (regexp-match? (config-modules cfg) f))
      (path->string (path-replace-extension f #""))))
  (when (null? modules)
    (error 'evaluate "no module in ~a matches ~a (it is matched against the file names, \"mm.frame.rktd\")"
           (build-path auto "probe") (object-name (config-modules cfg))))
  (for ([d (in-list '("tables" "clients" "results"))]) (make-directory* (build-path run-dir d)))
  (define vostd (cadr (assq 'vostd (read-target (build-path auto "targets" (string-append (car modules) ".rktd"))))))
  (write-forms (build-path run-dir "manifest.rktd")
               `((manifest
                  (config ,(path->string (path->complete-path config-file)))
                  (vostd ,vostd) (commit ,(git-head vostd)) (verus ,(verus-version vostd))
                  (modules ,@modules))
                 ,@(file->list config-file)))
  (define lines
    (for/fold ([lines '()] #:result (reverse lines)) ([m (in-list modules)])
      (define line (evaluate-module cfg m run-dir))
      (pretty-write line)
      (flush-output)
      (define all (reverse (cons line lines)))
      (write-forms (build-path run-dir "modules.rktd") all)
      (cons line lines)))
  lines)

(define (evaluate-module cfg m run-dir)
  (define-values (cs table table-file) (generate-module cfg m run-dir))
  (define clients-file (build-path run-dir "clients" (string-append m ".rktd")))
  (write-forms clients-file cs)
  (define target (build-path (config-auto cfg) "targets" (string-append m ".rktd")))
  (cond
    [(null? cs) `(module ,m (clients 0))]
    [else
     (summary-line m (length cs)
                   (run-module target table-file table clients-file cs (build-path run-dir "results" m)))]))

;; generate-module : cfg m run-dir -> (values clients table table-file)
;; The module's table (written to RUN-DIR/tables/) and its clients, without
;; running them: what a change of the tables or the generator does, offline.
(define (generate-module cfg m run-dir)
  (define auto (config-auto cfg))
  (define k (let ([d (config-knowledge cfg)]) (read-knowledge (and d (build-path d (string-append m ".rktd"))))))
  ;; the other modules whose APIs the protocols call: their tables too
  (define others
    (remove-duplicates
     (for*/list ([pr (in-list (knowledge-protocols k))] [a (in-list (cadr pr))]
                 [o (in-value (module-of a))]
                 #:when (and o (not (equal? o m)) (file-exists? (build-path auto "probe" (string-append o ".rktd")))))
       o)))
  (define table-file (build-path run-dir "tables" (string-append m ".rktd")))
  (define table (write-module-table auto (config-providers cfg) m others table-file (must-close-of cfg (cons m others))))
  (define names (probe-ok (build-path auto "probe" (string-append m ".rktd"))))
  (define protocol-names
    (append names
            (for*/list ([o (in-list others)] [n (in-list (probe-ok (build-path auto "probe" (string-append o ".rktd"))))]
                        #:when (for/or ([pr (in-list (knowledge-protocols k))]) (memq n (cadr pr))))
              n)))
  (define cs
    (parameterize ([current-none-vacuous
                    (probe-none-vacuous (for/list ([o (in-list (cons m others))])
                                          (build-path auto "probe" (string-append o ".rktd"))))])
      (generate cfg m table names protocol-names k)))
  (values cs table table-file))

;; must-close-of : cfg (module ...) -> (TYPE ...), the knowledge's must-close
;; entries of the modules
(define (must-close-of cfg ms)
  (define d (config-knowledge cfg))
  (remove-duplicates
   (append* (for/list ([o (in-list ms)])
              (knowledge-must-close (read-knowledge (and d (build-path d (string-append o ".rktd")))))))))

;; write-module-table : auto providers-file m (other-module ...) table-file (TYPE ...) -> table
;; The table a module's clients run with: the module's (fixes/ or
;; apis/), the other modules' whose APIs they call, the providers, and the
;; must-close types the knowledge names.  The client module is beside module m
;; (targets/<m>.rktd) and sees m's items through the table's uses; another
;; module's items are imported from that module.
(define (write-module-table auto providers m others table-file must-close)
  (write-forms table-file `((base ,(path->string (table-of auto m)))
                            ,@(for/list ([o (in-list others)]) `(base ,(path->string (table-of auto o)) entries))
                            (base ,(path->string providers))
                            ,@(if (null? must-close) '() `((must-close ,@must-close)))
                            ,@(if (null? others) '()
                                  `((uses ,@(for/list ([o (in-list others)])
                                              (format "use crate::~a::*;" (regexp-replace* #rx"[.]" o "::"))))))))
  (read-api-table table-file))

;; run-module : target table-file table clients-file (client ...) dir -> results
;; Runs the clients into DIR unless DIR/key.sha is the key of this run (the
;; clients, the table's imports, the runner, the checkout's state), and the
;; clients as elaborated against the table (what is rendered: the requires
;; asserted and lifted).  Without the elaboration a change of a table entry's
;; requires, or of client.rkt, reused results of the old clauses (2026-11-11:
;; the `&` added in segment's two clients did not rerun the module).
(define (run-module target table-file table clients-file cs dir)
  (define vostd (cadr (assq 'vostd (read-target target))))
  (define elaborated (format "~s" (for/list ([c (in-list cs)]) (check-client table c))))
  (define sha (sha1 (open-input-string (string-append (call-with-input-file clients-file sha1)
                                                      (format "~s" (api-table-uses table))
                                                      (sha1 (open-input-string elaborated))
                                                      (runner-version)
                                                      (vostd-state vostd)))))
  (define sha-file (build-path dir "key.sha"))
  (cond
    [(and (file-exists? sha-file) (equal? (file->string sha-file) sha)
          (file-exists? (build-path dir "results.rktd")))
     (file->list (build-path dir "results.rktd"))]
    [else
     (when (directory-exists? dir) (delete-directory/files dir))
     (define results (run-with-imports target table-file cs dir))
     ;; verification may rewrite the checkout's Cargo.lock: it is not left changed
     (restore-lock vostd)
     (call-with-output-file sha-file #:exists 'truncate (lambda (o) (write-string sha o)))
     results]))
