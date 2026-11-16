#lang racket/base
;; What wrappers drop (design.md 3.9): the three steps, in OUT.
;;
;;   cand.rktd          step 1, the candidates (lib/analysis/drops.rkt); a
;;                      candidate's id is its position in this file
;;   rounds.rktd        step 2, one form per round of verifying ostd in COPY:
;;                      (round N (inserted K) (verified V E) (KIND ID ...) ...),
;;                      KIND compile | unproved | rlimit | other; (done N) when a round
;;                      blamed nothing and ostd verified with 0 errors
;;   verus-rN.out       that round's Verus output
;;   survivors.patch    the survivors in F's ensures, as `git diff` of COPY
;;   knowledge/<m>.rktd step 3, the survivors whose F is in a table, as claims
;;   claims.rktd        the evaluation of them (families claim), run in run/
;;                      on the environment's checkout
;;   drops.rktd         per candidate: (drop ID STATUS F G TEXT), STATUS
;;                      compile | unproved | rlimit | other (step 2 dropped it),
;;                      private (F proves it, F is in no table), exported (the
;;                      claim verified: F's ensures implies it), dropped (the
;;                      claim failed: proved and not exported), claim-error
;;                      (the claim client did not compile)
;;
;; COPY is a copy of the checkout at the same commit (never the environment's
;; checkout: its ostd/ is rewritten each round, then restored); Cargo's target
;; directory is the environment's (drops-target-dir DIR), by default
;; target-dir with "-drops".  Each step is skipped when its file is there, so
;; an interrupted analysis resumes; a round restores COPY first.
;;
;; With a base patch (#:base PATCH, `--base`), the analysis is of the patched
;; vostd: the next layer up, once a fix gives a function new ensures, may drop
;; them in turn.  The environment's checkout must have PATCH applied (step 1
;; reads its source, step 3 runs there; a CS_ENV overlay naming a patched
;; copy); COPY stays clean and gets PATCH after each restore, so
;; survivors.patch includes it.  VIR is still the commit's: the base may
;; change specifications, not bodies (the calls step 1 follows).
(require racket/file racket/list racket/match racket/port racket/string racket/system racket/path
         "../analysis/drops.rkt" "../vostd/vir.rkt" "../vostd/run.rkt" "../vostd/git.rkt"
         "../base/env.rkt" "../model/api.rkt" "evaluate.rkt")
(provide drops verify-rounds clean? restore)

(define (drops vir module-rx auto copy out #:base [base0 #f])
  (define vostd (env-ref 'vostd))
  (define (canon p) (simplify-path (path->complete-path p)))
  (define base (and base0 (path->string (canon base0))))
  (when (equal? (canon copy) (canon vostd))
    (error 'drops "~a is the environment's checkout; give a copy of it" copy))
  (unless (equal? (git-head copy) (git-head vostd))
    (error 'drops "~a is at ~a, the environment's checkout at ~a" copy (git-head copy) (git-head vostd)))
  (when base
    (unless (file-exists? base) (error 'drops "no base patch ~a" base))
    (unless (parameterize ([current-directory vostd] [current-error-port (open-output-nowhere)])
              (system* (git-program) "apply" "--check" "-R" base))
      (error 'drops "the environment's checkout ~a does not have ~a applied" vostd base)))
  ;; COPY as the analysis starts from: the commit, with the base patch
  (define (reset)
    (restore copy)
    (when base
      (parameterize ([current-directory copy])
        (unless (system* (git-program) "apply" base) (error 'drops "~a: cannot apply ~a" copy base)))))
  (make-directory* out)
  (define (o f) (build-path out f))
  (define rounds-file (o "rounds.rktd"))
  (unless (or (file-exists? rounds-file) (clean? copy))
    (error 'drops "~a has changes in ostd/: give a clean copy" copy))

  ;; step 1
  (unless (file-exists? (o "cand.rktd"))
    (define cs (drop-candidates (load-vir vir) (load-records (env-program 'item-index) vostd) (pregexp module-rx)))
    (with-output-to-file (o "cand.rktd") (lambda () (for ([c (in-list cs)]) (writeln c)))))
  (define cands (file->list (o "cand.rktd")))
  (printf "step 1: ~a candidates in ~a functions\n" (length cands) (length (remove-duplicates (map cadr cands))))

  ;; step 2
  (define rounds (verify-rounds copy cands out reset))
  (define excluded (excluded-ids rounds))
  (define step2 (for*/hash ([r (in-list rounds)] #:when (eq? (car r) 'round)
                            [b (in-list (cddddr r))] [i (in-list (cdr b))])
                  (values i (car b))))

  ;; step 3
  (define by-vir (table-fns (build-path auto "apis")))
  (define kdir (o "knowledge"))
  (define claim-of (make-hash)) ; id -> (m . i)
  (define per-module (make-hash))
  (for ([c (in-list cands)] [id (in-naturals)] #:unless (memv id excluded))
    (match-define `(cand ,f-path ,_ ,_ ,_ ,g-path ,g-span ,_ ,claim) c)
    (match (hash-ref by-vir f-path #f)
      [#f (void)]
      [(cons m f)
       (define l (hash-ref per-module m '()))
       (hash-set! claim-of id (cons m (length l)))
       (hash-set! per-module m (append l (list `(claim ,(api-name f) ,(claim-text claim f)
                                                     (from (comment ,g-span ,(format "drops ~a: ~a" id g-path)))
                                                     (why ,(format "drops candidate ~a: ~a ensures it, and F proves it once it is added" id g-path))))))]))
  (make-directory* kdir)
  (for ([(m cs) (in-hash per-module)])
    (with-output-to-file (build-path kdir (string-append m ".rktd")) #:exists 'truncate
      (lambda () (writeln `(module ,m)) (for ([c (in-list cs)]) (writeln c)))))
  (define modules (sort (hash-keys per-module) string<?))
  (with-output-to-file (o "claims.rktd") #:exists 'truncate
    (lambda ()
      (displayln ";; drops step 3: the survivors of step 2 as claims (lib/pipeline/drops.rkt)")
      (pretty-write* `(evaluation
                       (auto ,(path->string (canon auto)))
                       (knowledge "knowledge")
                       (modules ,(format "^(~a)[.]rktd$" (string-join (map (lambda (m) (regexp-replace* #rx"[.]" m "[.]")) modules) "|")))
                       (families claim)))))
  (unless (null? modules) (void (evaluate (o "claims.rktd") (o "run"))))

  ;; the report
  (define statuses
    (for/hash ([m (in-list modules)])
      (define f (build-path out "run" "results" m "results.rktd"))
      (values m (for/hash ([c (in-list (if (file-exists? f) (file->list f) '()))]
                           #:when (and (pair? c) (eq? (car c) 'client)))
                  (values (cadr c) (caddr c))))))
  (define report
    (for/list ([c (in-list cands)] [id (in-naturals)])
      (match-define `(cand ,f-path ,_ ,_ ,_ ,g-path ,_ ,text ,_) c)
      (define st
        (cond [(hash-ref step2 id #f)]
              [(hash-ref claim-of id #f)
               => (lambda (mi)
                    (define f (cdr (hash-ref by-vir f-path)))
                    (define name (string->symbol (format "claim_~a_~a" (regexp-replace* #rx"[^A-Za-z0-9_]" (symbol->string (api-name f)) "_") (cdr mi))))
                    (match (hash-ref (hash-ref statuses (car mi) (hash)) name #f)
                      ['verified 'exported]
                      ['failed 'dropped]
                      ['compile-error 'claim-error]
                      [s (or s 'not-run)]))]
              [else 'private]))
      `(drop ,id ,st ,f-path ,g-path ,text)))
  (with-output-to-file (o "drops.rktd") #:exists 'truncate (lambda () (for ([r (in-list report)]) (writeln r))))
  (define tally (for/fold ([h (hash)]) ([r (in-list report)]) (hash-update h (caddr r) add1 0)))
  (printf "~a\n" (string-join (for/list ([k (in-list '(compile unproved rlimit other private exported dropped claim-error not-run))]
                                         #:when (hash-ref tally k #f))
                                (format "~a ~a" k (hash-ref tally k)))
                              ", "))
  report)

;; verify-rounds : copy (cand ...) out-dir reset -> rounds
;; Step 2 (also triage's `provable`, provable.rkt): the candidates into their
;; functions' ensures in COPY (reset first puts COPY as the analysis starts
;; from), ostd verified, the candidates its errors blame taken out, again
;; until a round blames none.  OUT/rounds.rktd, OUT/verus-rN.out,
;; OUT/survivors.patch; resumes from rounds.rktd; COPY restored at the end.
(define (verify-rounds copy cands out reset)
  (define (o f) (build-path out f))
  (define rounds-file (o "rounds.rktd"))
  (define target (or (env-ref 'drops-target-dir #f) (string-append (env-ref 'target-dir) "-drops")))
  (let loop ()
    (define rounds (if (file-exists? rounds-file) (file->list rounds-file) '()))
    (unless (assq 'done rounds)
      (define n (add1 (length rounds)))
      (define excluded (excluded-ids rounds))
      (reset)
      (define k (insert-all copy cands excluded))
      (define log (o (format "verus-r~a.out" n)))
      (verify-ostd copy target log)
      ;; ostd's part of the output: dv verifies the dependencies first
      (define lines (let ([ls (file->lines log)])
                      (define i (for/last ([l (in-list ls)] [k (in-naturals)] #:when (regexp-match? #px"\"-p\" \"ostd\"" l)) k))
                      (if i (drop ls i) ls)))
      (define-values (verified errors) (parse-verus lines))
      (define-values (blamed unblamed) (blame errors (line-reader copy) (and verified #t)))
      (cond
        [(pair? unblamed)
         (restore copy)
         (error 'drops "round ~a: ~a errors name no candidate (~a); the first: ~s" n (length unblamed) log (car unblamed))]
        [(and (null? blamed) (not (and verified (zero? (cadr verified)))))
         (restore copy)
         (error 'drops "round ~a: no candidate blamed, but ostd does not verify (~a)" n log)]
        [else
         (with-output-to-file rounds-file #:exists 'append
           (lambda ()
             (writeln `(round ,n (inserted ,k) (verified ,@(or verified '(#f #f))) ,@blamed))
             (when (null? blamed) (writeln `(done ,n)))))
         (printf "round ~a: ~a inserted, ~a\n" n k
                 (if (null? blamed) (format "ostd ~a verified, 0 errors" (car verified))
                     (string-join (for/list ([b (in-list blamed)]) (format "~a ~a" (car b) (length (cdr b)))) ", ")))
         (when (null? blamed)
           (call-with-output-file (o "survivors.patch") #:exists 'truncate
             (lambda (p) (parameterize ([current-directory copy] [current-output-port p])
                           (system* (git-program) "diff" "--" "ostd")))))
         (loop)])))
  (restore copy)
  (file->list rounds-file))

(define (excluded-ids rounds)
  (for*/list ([r (in-list rounds)] #:when (eq? (car r) 'round) [b (in-list (cddddr r))] [i (in-list (cdr b))]) i))

(define (clean? copy)
  (parameterize ([current-directory copy] [current-output-port (open-output-nowhere)])
    (system* (git-program) "diff" "--quiet" "--" "ostd")))
(define (restore copy)
  (parameterize ([current-directory copy])
    ;; Cargo.lock: cargo dv rewrites it
    (unless (system* (git-program) "checkout" "-q" "--" "ostd" "Cargo.lock") (error 'drops "~a: git checkout failed" copy))))

;; span "f.rs:126:13: 126:70" -> (values file 126 70), the end of the clause
(define (span-end s)
  (match (regexp-match #px"^(.*):[0-9]+:[0-9]+: ([0-9]+):([0-9]+)$" s)
    [(list _ f l c) (values f (string->number l) (string->number c))]))

;; insert-all : copy cands excluded -> how many were inserted
(define (insert-all copy cands excluded)
  (define by-file (make-hash))
  (for ([c (in-list cands)] [id (in-naturals)] #:unless (memv id excluded))
    (match-define `(cand ,_ ,_ ,file ,after ,_ ,_ ,text ,_) c)
    (define-values (_f l col) (span-end after))
    (hash-update! by-file file (lambda (xs) (cons (list l col id text) xs)) '()))
  (for ([(file ins) (in-hash by-file)])
    (define path (build-path copy file))
    (define lines (insert-candidates (file->lines path #:line-mode 'linefeed) ins))
    (call-with-output-file path #:exists 'truncate
      (lambda (p) (for ([s (in-list lines)]) (write-string s p) (newline p)))))
  (for/sum ([ins (in-hash-values by-file)]) (length ins)))

(define (line-reader copy)
  (define cache (make-hash))
  (lambda (file l)
    (define v (hash-ref! cache file
                         (lambda () (define p (build-path copy file))
                           (if (file-exists? p) (list->vector (file->lines p)) (vector)))))
    (if (<= 1 l (vector-length v)) (vector-ref v (sub1 l)) "")))

;; cargo dv verify --package ostd in copy, with the project's Verus
(define (verify-ostd copy target log)
  (define cargo (or (find-executable-path "cargo.exe") (find-executable-path "cargo") (error 'drops "cargo not found")))
  (define e (verus-environment (current-environment-variables)))
  (environment-variables-set! e #"CARGO_TARGET_DIR" (string->bytes/utf-8 target))
  (call-with-output-file log #:exists 'truncate
    (lambda (p)
      (parameterize ([current-directory copy] [current-environment-variables e]
                     [current-output-port p] [current-error-port p])
        (system* cargo "dv" "verify" "--package" "ostd")))))

;; vir-path -> (module . fn), from the tables in dir
(define (table-fns dir)
  (for*/hash ([f (in-directory dir)] #:when (regexp-match? #px"\\.rktd$" (path->string f))
              [m (in-value (regexp-replace #px"\\.rktd$" (path->string (file-name-from-path f)) ""))]
              [form (in-list (file->list f))]
              #:when (and (pair? form) (eq? (car form) 'fn) (fn-field form 'vir-path)))
    (values (car (fn-field form 'vir-path)) (cons m form))))
(define (fn-field form k) (for/first ([x (in-list (cddr form))] #:when (and (pair? x) (eq? (car x) k))) (cdr x)))

;; claim-text : candidate's claim text, F's entry -> the claim
;; The claim client binds the ghost result's value (claim.rkt): F's ghost result
;; `p@` (a Tracked's view) or `p` is gret.  A ghost Option next to a Result: F
;; says its facts under `ret is Ok` and nothing ties Some to Ok, so the claim
;; takes both guards (still implied by what step 2 proved).
(define (claim-text claim f)
  (define src (fn-field f 'source))
  (define w (and (pair? src) (for/first ([x (in-list src)] #:when (and (pair? x) (eq? (car x) 'with-out))) (cdr x))))
  (define gname (and (pair? w) (cadr (car w))))
  (define t
    (if gname
        (let ([q (regexp-quote gname)])
          (regexp-replace* (pregexp (format "\\b~a\\b" q))
                           (regexp-replace* (pregexp (format "\\b~a@" q)) claim "gret")
                           "gret"))
        claim))
  (if (and (regexp-match? #px"^gret\\s+is\\s+Some\\b" t)
           (match (api-ret f) [`(Result ,_ ...) #t] [_ #f]))
      (format "ret is Ok ==> (~a)" t)
      t))

(define (pretty-write* x) ((dynamic-require 'racket/pretty 'pretty-write) x))
