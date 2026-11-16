#lang racket/base
;; Running Verus on rendered clients and attributing its errors (design.md, 结论10-11).
;;
;; A target file says where in a vostd checkout the client module goes:
;;   (package NAME) (module "a::b::clients") (file "path/to/clients.rs")
;;   (mod-file "path/to/mod.rs") (mod-anchor "LINE") (mod-line "mod clients;")
;; The checkout and Cargo's target directory are the environment's
;; (base/env.rkt), unless the target names its own (vostd DIR) (target-dir DIR).
;; Paths in file and mod-file are relative to the checkout.
(require racket/future racket/list racket/match racket/string racket/file racket/system racket/pretty racket/port
         "../model/api.rkt" "../check/client.rkt" "../gen/render.rkt" "../base/forms.rkt" "../base/env.rkt" "git.rkt")
(provide run-clients run-verus parse-verus with-client-module attach-expansions verus-extra-args)

(define (target-ref target key)
  (cond [(assq key target) => cadr]
        [else (error 'run "target: missing ~a" key)]))

;; run-clients : target-file table-file (client ...) out-dir -> results
;; Writes into out-dir: plan.rktd (elaborated clients), clients.rs and
;; linemap.rktd (the last rendering), verus-N.out, results.rktd.
(define (run-clients target-file table-file clients out-dir)
  (define target (read-target target-file))
  (check-table-commit table-file (target-ref target 'vostd))
  (define table (read-api-table table-file))
  (make-directory* out-dir)
  (define elaborated (for/list ([c (in-list clients)]) (check-client table c)))
  (write-forms (build-path out-dir "plan.rktd") elaborated)
  (define-values (ill ok) (partition (lambda (e) (eq? (car e) 'ill-formed)) elaborated))
  (with-client-module target (lambda () (run-loop target table-file table ill ok out-dir))))

;; A compile error stops Verus before verification, for every client in the
;; module.  Clients with compile errors are dropped and the rest rerun.
(define (run-loop target table-file table ill ok out-dir)
  (let loop ([ok ok] [dropped '()] [attempt 1] [seconds '()])
    (define t0 (current-inexact-milliseconds))
    (define-values (verified errors) (verify-once target table ok out-dir attempt))
    ;; wall-clock seconds of each attempt, so that slow runs (and the machine's
    ;; sleeping) show in the results
    (define secs (append seconds (list (inexact->exact (round (/ (- (current-inexact-milliseconds) t0) 1000))))))
    (define-values (lmap) (file->value (build-path out-dir "linemap.rktd")))
    (define attributed
      (attribute errors lmap (target-ref target 'file)
                 (file->lines (build-path out-dir "clients.rs")) (target-ref target 'vostd)))
    ;; A panic inside Verus (e.g. the solver's statistics missing) or running
    ;; out of memory is not a compile error: no client is to blame, so none
    ;; is dropped.
    (define crashed?
      (and (not verified)
           (for/or ([l (in-list (file->lines (build-path out-dir (format "verus-~a.out" attempt))))])
             (regexp-match? #rx"^thread .* panicked at rust_verify|^memory allocation of [0-9]+ bytes failed" l))))
    ;; Only an error that is not a verification failure stops Verus: a run
    ;; that ended without results because of one client's trigger error
    ;; (which comes after other clients' assertion failures) must drop that
    ;; client, not every client with a failure.  Every client has one (its
    ;; vacuity assertion), so all of mm.frame.segment's 786 were dropped
    ;; (2026-11-11).
    (define compile-failed
      (remove-duplicates (for/list ([a (in-list attributed)]
                                    #:when (and (not verified) (car a) (not (verification-failure? (list-ref a 4)))))
                           (car a))))
    (cond
      [(and (not verified) (not crashed?) (pair? compile-failed) (< attempt 4))
       (loop (filter (lambda (c) (not (memq (cadr c) compile-failed))) ok)
             (append dropped
                     (for/list ([n (in-list compile-failed)])
                       `(client ,n compile-error
                                ,@(for/list ([a (in-list attributed)] #:when (eq? (car a) n)) (cdr a)))))
             (add1 attempt) secs)]
      [else
       (define sanity (sanity-fact attributed verified))
       (define results
         (append
          `((run (vostd ,(target-ref target 'vostd)) (commit ,(git-head (target-ref target 'vostd)))
                 (module ,(target-ref target 'module)) (table ,(path->string* table-file))
                 (attempts ,attempt) (seconds ,@secs))
            ,(cond [verified `(verification ,@verified)] [crashed? '(verification crashed)] [else '(verification none)])
            ,sanity)
          (for/list ([e (in-list ill)])
            (match-define `(ill-formed ,n ,_ (at ,id) ,fact) e)
            `(client ,n ill-formed (at ,id) ,fact))
          dropped
          (for/list ([c (in-list ok)])
            (define n (cadr c))
            (define all (for/list ([a (in-list attributed)] #:when (eq? (car a) n)) (cdr a)))
            ;; The vacuity assertions must fail; a path whose assertion did not
            ;; fail has contradictory assumptions (结论29).
            (define-values (vac errs) (partition (lambda (e) (vacuity-id? (cadr e))) all))
            (define vacuous
              (for/list ([m (in-list lmap)]
                         #:when (and (eq? (car m) 'item) (eq? (caddr m) n) (vacuity-id? (cadddr m))
                                     (not (findf (lambda (e) (equal? (cadr e) (cadddr m))) vac))))
                (cadddr m)))
            ;; Not inferred when Verus may have given up on the function: an error
            ;; not on a statement (e.g. at the signature), or a resource limit.
            (define aborted? (for/or ([e (in-list errs)])
                               (or (not (cadr e)) (regexp-match? #rx"rlimit|resource limit|timed out|timeout" (cadddr e)))))
            (define vac-fact (cond [(not (and verified (pair? vacuous))) '()]
                                   [aborted? '((vacuity-unknown))]
                                   [else `((vacuous ,@vacuous))]))
            ;; without (sanity ok) the run is not to be trusted (结论11): a
            ;; client without errors is not taken as verified
            (cond [(not verified) `(client ,n not-verified ,@errs)]
                  [(not (equal? sanity '(sanity ok))) `(client ,n not-verified (sanity-not-ok) ,@errs)]
                  [(null? errs) `(client ,n verified ,@vac-fact)]
                  [else `(client ,n failed ,@errs ,@vac-fact)]))
          (for/list ([a (in-list attributed)] #:when (not (car a))) `(unattributed ,@(cdr a)))))
       (write-forms (build-path out-dir "results.rktd") results)
       results])))

(define (path->string* p) (if (path? p) (path->string p) p))

;; The messages of Verus's failed proof obligations (not errors that stop it).
(define (verification-failure? msg)
  (regexp-match? #px"^(assertion failed|precondition not satisfied|postcondition not satisfied|possible arithmetic underflow/overflow|invariant not satisfied|.*loop invariant|decreases not satisfied|cannot prove termination|function body check: resource limit|.*timed out)" msg))

;; The sanity client must fail with exactly its one assertion (结论11).
(define (sanity-fact attributed verified)
  (define n (count (lambda (a) (eq? (car a) sanity-name)) attributed))
  (cond [(not verified) '(sanity not-verified)]
        [(= n 1) '(sanity ok)]
        [else `(sanity unexpected ,n)]))

;; verify-once : ... -> (values (VERIFIED ERRORS)-or-#f (error ...))
;; Rendered for the target's module: use_type_invariant only where the clients
;; can see the type's invariant (render.rkt client-module).
(define (verify-once target table clients out-dir attempt)
  (define-values (text lmap) (parameterize ([client-module (target-ref target 'module)]) (render-module table clients)))
  (define vostd (target-ref target 'vostd))
  (define module-file (build-path vostd (target-ref target 'file)))
  (make-parent-directory* module-file)
  (call-with-output-file module-file #:exists 'truncate
    (lambda (o) (write-string text o)))
  (call-with-output-file (build-path out-dir "clients.rs") #:exists 'truncate
    (lambda (o) (write-string text o)))
  (write-forms (build-path out-dir "linemap.rktd") (list lmap))
  (define out (build-path out-dir (format "verus-~a.out" attempt)))
  (run-verus target out)
  (parse-verus (file->lines out)))

;; Each client has a z3 of its own (render.rkt, spinoff_prover), and Verus runs
;; one per core: on a machine with many cores and little memory that runs out
;; of memory (32 cores, 7.7 GB: 31 z3 used 6 GB).  Without (verus-threads N),
;; where the total memory is known (/proc/meminfo), about 2 GB for rust_verify
;; and 350 MB per z3; elsewhere Verus's default.
(define (default-threads)
  (define kb (and (file-exists? "/proc/meminfo")
                  (for/or ([l (in-list (file->lines "/proc/meminfo"))])
                    (match (regexp-match #px"^MemTotal:\\s+([0-9]+) kB" l)
                      [(list _ n) (string->number n)] [_ #f]))))
  (and kb (max 2 (min (processor-count) (quotient (- (quotient kb 1024) 2048) 350)))))

(define (run-verus target out)
  (define cargo (or (find-executable-path "cargo.exe") (find-executable-path "cargo")
                    (error 'run "cargo not found")))
  (define env (verus-environment (current-environment-variables)))
  (environment-variables-set! env #"CARGO_TARGET_DIR"
                              (string->bytes/utf-8 (target-ref target 'target-dir)))
  (call-with-output-file out #:exists 'truncate
    (lambda (o)
      (parameterize ([current-directory (target-ref target 'vostd)]
                     [current-environment-variables env]
                     [current-output-port o]
                     [current-error-port o])
        (define threads (or (env-ref 'verus-threads #f) (default-threads)))
        (unless (or (not threads) (exact-positive-integer? threads))
          (error 'run "(verus-threads ~s): a positive integer" threads))
        (apply system* cargo "dv" "focus" "--package" (target-ref target 'package) "-e" "200"
               ;; --expand-errors: which conjuncts of an opaque requires failed (expansion)
               "--" "--verify-only-module" (target-ref target 'module) "--expand-errors"
               (append
                (if threads (list "--num-threads" (number->string threads)) '())
                (verus-extra-args)))))))

;; Extra Verus arguments for one run: `--log smt --log-dir D` for coverage
;; (pipeline/coverage.rkt).  A parameter, not the environment, so that an
;; evaluation never runs with arguments its key does not record.
(define verus-extra-args (make-parameter '()))

;; parse-verus : (line ...) -> (values (VERIFIED ERRORS)-or-#f (error ...))
;;   error = (MESSAGE FILE LINE CALLEE LOCS)
;;   FILE, LINE: the first `-->` location; CALLEE: "file:line" of the first `:::` note, or #f;
;;   LOCS: every `-->` and `:::` location of the block, ((FILE . LINE) ...), in order
(define (parse-verus lines)
  (define verified
    (for/or ([l (in-list lines)])
      (match (regexp-match #px"verification results:: ([0-9]+) verified, ([0-9]+) errors" l)
        [(list _ v e) (list (string->number v) (string->number e))]
        [_ #f])))
  (define errors
    (let loop ([ls lines] [acc '()])
      (match ls
        ['() (reverse acc)]
        [(cons l rest)
         (match (regexp-match #px"^error(\\[E[0-9]+\\])?: (.*)$" l)
           [(list _ code msg)
            #:when (not (regexp-match? #px"^(could not compile|process didn't exit|aborting due)" msg))
            (define-values (whole after) (splitf-at rest (lambda (x) (not (regexp-match? #px"^(error|warning)" x)))))
            ;; Verus's own notes are separate diagnostics, not this error's: an
            ;; expansion (--expand-errors) belongs to an earlier error (attribute);
            ;; a recommendation not met (with its `:::` location, which would be
            ;; taken as this error's callee) and the progress note belong to none
            (define-values (block _rest)
              (splitf-at whole (lambda (x) (not (regexp-match? #px"^note: (diagnostics via expansion|recommendation not met|verifying module)" x)))))
            (define note (memf (lambda (x) (regexp-match? #px"^note: diagnostics via expansion" x)) whole))
            (define loc (for/or ([b (in-list block)]) (regexp-match #px"^\\s*--> (.*):([0-9]+):[0-9]+$" b)))
            (define callee (for/or ([b (in-list block)]) (regexp-match #px"^\\s*::: (.*):([0-9]+):[0-9]+$" b)))
            (define locs (for*/list ([b (in-list block)]
                                     [m (in-value (regexp-match #px"^\\s*(?:-->|:::) (.*):([0-9]+):[0-9]+$" b))]
                                     #:when m)
                           (cons (normalize (cadr m)) (string->number (caddr m)))))
            (loop after
                  (cons (list (if code (string-append code " " msg) msg)
                              (and loc (normalize (cadr loc)))
                              (and loc (string->number (caddr loc)))
                              (and callee (format "~a:~a" (normalize (cadr callee)) (caddr callee)))
                              locs
                              (helps block)
                              (and (pair? note) (expansion (cdr note))))
                        acc))]
           [_ (loop rest acc)])])))
  (values verified errors))

;; expansion : lines after "note: diagnostics via expansion" -> (EXPR LEAF ...)
;;   EXPR: the first line of the expanded expression (Verus prints `*r` as
;;   `mut_ref_current(r)`); LEAF = ("file:line" "underlined text"), the parts of
;;   the source that failed, from the excerpts that end the note.  Verus expands
;;   the first failing assertion of a function, through open spec functions,
;;   down to the conjuncts that fail; leaves only where it shows the source.
(define (expansion lines)
  (define body (takef lines (lambda (l) (not (regexp-match? #px"^note:" l)))))
  (define expr (for/first ([l (in-list body)] #:when (regexp-match? #px"\\S" l)) (string-trim l)))
  (define leaves
    (let loop ([ls body] [file #f] [acc '()])
      (match ls
        [(list* l rest)
         #:when (regexp-match #px"^\\s*--> (.*):([0-9]+):[0-9]+$" l)
         (loop rest (normalize (cadr (regexp-match #px"^\\s*--> (.*):([0-9]+):[0-9]+$" l))) acc)]
        [(list* code marks rest)
         #:when (and file (regexp-match #px"^\\s*[0-9]+ \\| " code) (regexp-match #px"^\\s*\\| .*\\^" marks))
         (define n (cadr (regexp-match #px"^\\s*([0-9]+) \\| " code)))
         (define c (cadr (regexp-match #px"^\\s*[0-9]+ \\| (.*)$" code)))
         (define m (cadr (regexp-match #px"^\\s*\\| (.*)$" marks)))
         (define spans
           (for/list ([p (in-list (regexp-match-positions* #px"\\^+" m))]
                      #:when (<= (cdr p) (string-length c)))
             (list (format "~a:~a" file n) (substring c (car p) (cdr p)))))
         (loop rest file (append (reverse spans) acc))]
        [(cons _ rest) (loop rest file acc)]
        ['() (reverse acc)])))
  (and expr (cons expr leaves)))

;; Verus writes the files of a module mounted by `#[path]` through the parent
;; directory (`ostd/src/../specs/mm/io.rs`): `dir/..` is taken out, or nothing
;; there would be in the client module (specs::*).
(define (normalize p)
  (let loop ([p (string-replace p "\\" "/")])
    (define q (regexp-replace #rx"(^|/)[^/.][^/]*/[.][.]/" p "\\1"))
    (if (equal? q p) p (loop q))))

;; helps : block lines -> ((help HEADING CODE ...) ...)
;; rustc's `help:` suggestions; CODE is a line it would add (`+ use a::B;`) or
;; the text it would insert into a line (shown under it as `+++`).
(define (helps block)
  (let loop ([ls block] [acc '()])
    (match ls
      ['() (reverse acc)]
      [(cons l rest)
       (match (regexp-match #px"^help: (.*)$" l)
         [(list _ heading)
          (define-values (body after) (splitf-at rest (lambda (x) (not (regexp-match? #px"^(help|note):" x)))))
          (loop after (cons `(help ,heading ,@(suggested-code body)) acc))]
         [_ (loop rest acc)])])))

(define (suggested-code body)
  (let loop ([ls body] [acc '()])
    (match ls
      ['() (reverse acc)]
      [(cons l rest)
       (cond
         [(regexp-match #px"^\\s*[0-9]+\\s*\\+\\s?(.*?)\\s*$" l)
          => (lambda (m) (loop rest (cons (cadr m) acc)))]
         [(and (pair? rest)
               (regexp-match #px"^\\s*[0-9]+\\s*\\| (.*)$" l)
               (regexp-match #px"^\\s*\\| (\\s*)(\\++)\\s*$" (car rest)))
          (define code (cadr (regexp-match #px"^\\s*[0-9]+\\s*\\| (.*)$" l)))
          (define m (regexp-match #px"^\\s*\\| (\\s*)(\\++)\\s*$" (car rest)))
          (define start (string-length (cadr m)))
          (define end (+ start (string-length (caddr m))))
          (loop (cdr rest) (if (<= end (string-length code)) (cons (substring code start end) acc) acc))]
         [else (loop rest acc)])])))

;; attribute : (error ...) linemap file rendered-lines vostd -> ((CLIENT-or-#f . FACT) ...)
;;   FACT = (error ID LINE "message" (text "rendered line") [(callee "file:line" "source line")] (help ..) ...)
;; The texts make a result readable without the sources (结论30).
;; The error is placed at its `-->` location; when that is not in a client
;; (e.g. a trait method not in scope is reported at its declaration in core),
;; at the first other location of the block that is.
(define (attribute errors lmap file rendered vostd)
  (define sources (make-hash))
  (define (source-line f n)
    (define ls (hash-ref! sources f (lambda () (with-handlers ([exn:fail? (lambda (_) '())])
                                                 (file->lines (build-path vostd f))))))
    (if (<= 1 n (length ls)) (string-trim (list-ref ls (sub1 n))) ""))
  (define (in-module? f) (and f (string-suffix? (normalize file) f)))
  (define (item-at line) (for/first ([m (in-list lmap)] #:when (and (eq? (car m) 'item) (= (cadr m) line))) m))
  (define (range-at line) (for/first ([m (in-list lmap)]
                                      #:when (and (eq? (car m) 'client) (<= (caddr m) line (cadddr m))))
                            m))
  (define facts
    (for/list ([e (in-list errors)])
      (match-define (list msg efile eline callee locs hs _) e)
    (define line
      (for/first ([l (in-list (cons (cons efile eline) locs))]
                  #:when (and (in-module? (car l)) (cdr l) (or (item-at (cdr l)) (range-at (cdr l)))))
        (cdr l)))
    (define item (and line (item-at line)))
    (define range (and line (range-at line)))
    (define text (if (and line (<= 1 line (length rendered))) (string-trim (list-ref rendered (sub1 line))) ""))
    (define callee-fact
      (match (and callee (regexp-match #px"^(.*):([0-9]+)$" callee))
        [(list _ f n) #:when (not (in-module? f)) `((callee ,callee ,(source-line f (string->number n))))]
        [_ '()]))
    (define fact `(error ,(and item (cadddr item)) ,line ,msg (text ,text) ,@callee-fact ,@hs))
    (cond [item (cons (caddr item) fact)]
          [range (cons (cadr range) fact)]
          [else (cons #f `(,msg ,(and efile (format "~a:~a" efile eline))))])))
  (attach-expansions facts (map (lambda (e) (list-ref e 6)) errors)))

;; attach-expansions : ((CLIENT . FACT) ...) (expansion-or-#f ...) -> ((CLIENT . FACT) ...)
;; Verus prints a function's errors, then the expansion of its first one: an
;; expansion found after error k is for the first of the errors of the same
;; client just before it (since the last expansion).  It is attached as
;; (expanded LEAF ...) only when its expression is that error's (the asserted
;; text, or the callee's requires line), and only when it shows leaves.
(define (attach-expansions facts xs)
  (define fv (list->vector facts))
  (define xv (list->vector xs))
  (define (norm s) (regexp-replace* #px"mut_ref_current|vstd_extra::panic::|[\\s*()]" s ""))
  (define (fact-texts f)
    (filter string?
            (list (let ([t (assq 'text (filter pair? (cdr f)))]) (and t (cadr t)))
                  (let ([c (assq 'callee (filter pair? (cdr f)))]) (and c (caddr c))))))
  (for ([k (in-range (vector-length fv))])
    (define x (vector-ref xv k))
    (define c (car (vector-ref fv k)))
    (when (and x c (pair? (cdr x)))
      (define j (let back ([j k])
                  (if (and (> j 0) (eq? (car (vector-ref fv (sub1 j))) c) (not (vector-ref xv (sub1 j))))
                      (back (sub1 j))
                      j)))
      (define f (vector-ref fv j))
      (when (and (eq? (cadr f) 'error)
                 (for/or ([t (in-list (fact-texts f))]) (string-contains? (norm t) (norm (car x)))))
        (define-values (head tail) (split-at (cdr f) (min (length (cdr f)) (if (assq 'callee (filter pair? (cdr f))) 6 5))))
        (vector-set! fv j (cons c (append head `((expanded ,@(cdr x))) tail))))))
  (vector->list fv))

;; with-client-module : target thunk -> its result
;; The module declaration is added after the anchor line (or at the end of the
;; file, for the anchor `end`) for the duration of the run; afterwards the
;; declaring file is restored and the client module removed, so that one
;; run's clients cannot break the build of the next (a declaration left by an
;; older version of this tool is removed too).
(define (with-client-module target thunk)
  (clean-leftovers (target-ref target 'vostd) (target-ref target 'mod-line) (target-ref target 'file))
  (define file (build-path (target-ref target 'vostd) (target-ref target 'mod-file)))
  (define module-file (build-path (target-ref target 'vostd) (target-ref target 'file)))
  (define line (target-ref target 'mod-line))
  (define anchor (target-ref target 'mod-anchor))
  (define original (file->bytes file))
  ;; verification may rewrite the checkout's Cargo.lock: it is put back as it was
  (define lock (build-path (target-ref target 'vostd) "Cargo.lock"))
  (define original-lock (and (file-exists? lock) (file->bytes lock)))
  (define lines (filter (lambda (l) (not (equal? l line))) (file->lines file)))
  (define stale? (not (= (length lines) (length (file->lines file)))))
  (define new
    (if (eq? anchor 'end)
        (append lines (list line))
        (begin
          (unless (member anchor lines) (error 'run "~a: anchor ~s not found" file anchor))
          (append* (for/list ([l (in-list lines)]) (if (equal? l anchor) (list l line) (list l)))))))
  (dynamic-wind
   (lambda () (display-lines-to-file new file #:exists 'truncate))
   thunk
   (lambda ()
     (if stale?
         (display-lines-to-file lines file #:exists 'truncate)
         (call-with-output-file file #:exists 'truncate (lambda (o) (write-bytes original o))))
     (when (and original-lock (not (equal? (file->bytes lock) original-lock)))
       (call-with-output-file lock #:exists 'truncate (lambda (o) (write-bytes original-lock o))))
     (when (file-exists? module-file) (delete-file module-file)))))

;; clean-leftovers : vostd mod-line module-file -> void
;; What an interrupted run (killed before its cleanup) leaves in the checkout,
;; in any module: client modules (untracked files with the client module's
;; name) and files whose only change is the module declaration.  Without this
;; another module's client module is compiled into the crate on the next run.
;; Nothing else is touched (the user's changes stay).
(define (clean-leftovers vostd line module-file)
  (define name (let-values ([(_d n _x) (split-path module-file)]) (path->string n)))
  (define (git-lines . args)
    (string-split (with-output-to-string
                    (lambda () (parameterize ([current-error-port (open-output-nowhere)])
                                 (apply system* (git-program) "-C" (path->string* vostd) args))))
                  "\n"))
  (for ([f (in-list (git-lines "ls-files" "--others" "--exclude-standard"))]
        #:when (and (not (equal? f "")) (regexp-match? (pregexp (string-append "(^|/)" (regexp-quote name) "$")) f)))
    (eprintf "run: removing a client module left by an interrupted run: ~a\n" f)
    (delete-file (build-path vostd f)))
  (for ([f (in-list (git-lines "diff" "--name-only"))] #:when (regexp-match? #rx"[.]rs$" f))
    (define changed (filter (lambda (l) (regexp-match? #px"^[+-](?![+-])" l)) (git-lines "diff" "-U0" "--" f)))
    (when (equal? changed (list (string-append "+" line)))
      (eprintf "run: restoring ~a (a module declaration left by an interrupted run)\n" f)
      (git-lines "checkout" "--" f))))

;; The table must be for the checkout's commit (design.md 3.2): a table that
;; lags gives clients of the old signatures, and its requires stronger than
;; the source are not caught by the probe.  CS_ANY_COMMIT=1 runs anyway (an
;; experiment on purpose against another commit, not a result).
(define (check-table-commit table-file vostd)
  (define head (git-head vostd))
  (define cs (table-commits table-file))
  (unless (or (getenv "CS_ANY_COMMIT") (and (pair? cs) (andmap (lambda (c) (same-commit? c head)) cs)))
    (error 'run "table ~a is for ~a, the checkout ~a is at ~a: update the table (evaluation.md 3.1), or set CS_ANY_COMMIT=1"
           table-file (if (null? cs) "no recorded commit (add (at \"COMMIT\"))" (string-join cs ", ")) vostd head)))

