#lang racket/base
;; Coverage of the ensures clauses by a run's clients (design.md 3.10;
;; docs/enumeration.md 18, 19; docs/survey/J-coverage-vacuity.md).
;;
;; The question: which clause of which callee's ensures does some client's
;; proof need?  A clause no client needs is not checked by the evaluation: it
;; may be wrong or missing without any client noticing.  (It may also be
;; derivable from the others; that is not asked here.)
;;
;; One Verus run per module with `--log smt`: one SMT file per client (each
;; has `#[verifier::spinoff_prover]`).  Verus states a callee F's ensures as
;; one axiom `(= (ens%F ..) (and c_1 .. c_n))`, a conjunct per clause, after
;; the conjuncts it adds itself (the result type's invariant, an inherited
;; trait ensures), and drops clauses that are literally `true`.  Each conjunct
;; c_j of an API of the run's table gets a guard `(=> g c_j)`; in the client's
;; query every `(check-sat)` becomes `(check-sat-assuming (g ..))`.  Verus
;; checks a function's body, then, a label having failed, asserts its negation
;; and checks again, until unsat: the last check-sat is the one where every
;; other assertion is proved.  After it the replay asks z3 for the unsat core
;; and then, once per guard, the query with that guard false and the others
;; true.  Not unsat with the guard false: the client needs the clause.  This
;; is what deleting the clause and rerunning (the earlier X9, one Verus run per
;; clause) asks, at the cost of one run and seconds of z3; on mm.frame.segment
;; both gave the same 9 clauses (docs/enumeration.md 18.2).
;;
;; Not answers (docs/enumeration.md 19): a client whose last query is not
;; unsat (it failed, or its replay hit a resource limit) needs nothing; a
;; guard whose query is `unknown` for a resource limit is `limit`, neither
;; needed nor not.  A clause needed only by such answers is unknown.
;;
;; Text edits only: the log has literals (`#x..`) a round trip through an
;; s-expression reader would change.  The guarded files and z3's answers are
;; in RUN-DIR/coverage/<m>/; the facts in RUN-DIR/coverage/<m>.rktd:
;;   (client NAME LAST (needed (API CLAUSE) ..) (limit (API CLAUSE) ..))
;;   (clause API CLAUSE checked|unknown|unchecked CLIENT ..)   every clause of every
;;                                     API of the module's own table with ensures
;;   (count-mismatch API CONJUNCTS CLAUSES)   F left out: its conjuncts do not
;;                                     match the table's clauses
;; CLAUSE counts from 1 in the source's ensures.  Resumed: a module whose
;; coverage/<m>/key.sha is its results' key is not run again.
(require racket/file racket/list racket/match racket/string racket/path racket/system racket/port
         racket/runtime-path racket/future file/sha1
         "../model/api.rkt" "../base/forms.rkt" "../base/env.rkt" "../vostd/run.rkt"
         "evaluate.rkt")
(provide coverage)

;; ================================================================ s-expression text

(define (skip-ws s i) (if (and (< i (string-length s)) (char-whitespace? (string-ref s i))) (skip-ws s (add1 i)) i))

;; the end of the s-expression starting at i (a list or an atom), whitespace skipped first
(define (sexp-end s i0)
  (define i (skip-ws s i0))
  (define n (string-length s))
  (define (to-bar k) (if (char=? (string-ref s k) #\|) k (to-bar (add1 k))))
  (define (to-quote k) (if (char=? (string-ref s k) #\") k (to-quote (add1 k))))
  (cond
    [(char=? (string-ref s i) #\()
     (let loop ([j (add1 i)] [depth 1])
       (define c (string-ref s j))
       (cond [(char=? c #\|) (loop (add1 (to-bar (add1 j))) depth)]
             [(char=? c #\") (loop (add1 (to-quote (add1 j))) depth)]
             [(char=? c #\() (loop (add1 j) (add1 depth))]
             [(char=? c #\)) (if (= depth 1) (add1 j) (loop (add1 j) (sub1 depth)))]
             [else (loop (add1 j) depth)]))]
    [(char=? (string-ref s i) #\|) (add1 (to-bar (add1 i)))]
    [else (let loop ([j i]) (if (or (= j n) (memv (string-ref s j) '(#\space #\tab #\newline #\return #\( #\)))) j (loop (add1 j))))]))

;; the top-level children of the list text at i: ((start . end) ...)
(define (children s i)
  (define end (sexp-end s i))
  (let loop ([j (add1 (skip-ws s i))] [acc '()])
    (define k (skip-ws s j))
    (if (>= k (sub1 end)) (reverse acc)
        (let ([e (sexp-end s k)]) (loop e (cons (cons k e) acc))))))

;; ================================================================ the table's ensures

;; The fn forms of a table file and of its bases, first definition of a name
;; first (an overlay's entry before its base's).  A base is absolute or
;; relative to the file that names it.
(define (table-fns file)
  (define dir (path-only (path->complete-path file)))
  (append*
   (for/list ([f (in-list (file->list file))] #:when (pair? f))
     (match f
       [`(base ,p ,_ ...) (table-fns (if (absolute-path? p) p (build-path dir p)))]
       [`(fn ,_ ,_ ...) (list f)]
       [_ '()]))))

(define (fn-field e k) (let ([x (assq k (filter pair? (cddr e)))]) (and x (cdr x))))

;; VIR path "ostd::mm::frame::segment::impl&%3::split" -> the SMT name
;; "ostd!t%mm.t%frame.t%segment.impl&%3.split." (a module segment is t%NAME;
;; impl&%N and the function are not)
(define (smt-name vir-path)
  (define parts (string-split vir-path "::"))
  (define rest (cdr parts))
  (define mods (drop-right rest 1))
  (string-append (car parts) "!"
                 (string-join (append (for/list ([p (in-list mods)])
                                        (if (regexp-match? #rx"^impl&%" p) p (string-append "t%" p)))
                                      (list (last rest)))
                              ".")
                 "."))

;; ensures-counts : table-file -> hash SMT-NAME -> (API N), N the source's ensures clauses
(define (ensures-counts table-file)
  (for/fold ([h (hash)]) ([e (in-list (table-fns table-file))])
    (define vp (let ([x (fn-field e 'vir-path)]) (and x (car x))))
    (define src (or (fn-field e 'source) '()))
    (define ens (let ([x (assq 'ensures (filter pair? src))])
                  (if x (filter (lambda (c) (and (pair? c) (eq? (car c) 'c))) (cdr x)) '())))
    (define k (and vp (smt-name vp)))
    (if (and k (pair? ens) (not (hash-ref h k #f))) (hash-set h k (list (cadr e) (length ens))) h)))

;; ================================================================ guarding a client's SMT file

;; guard-file : text counts guards(mutable hash G -> (API CLAUSE)) mismatches(mutable set) -> text
(define (guard-file text counts guards mismatches)
  (define edits '())   ; (start end replacement), not overlapping
  (define decls '())   ; positions of the declare-fun of an ens% with guards
  (define file-guards '())
  (for ([m (in-list (regexp-match-positions* #px"\\(= \\((ens%[^ ]+) " text #:match-select values))])
    (match-define (list (cons s0 _) (cons ns ne)) m)
    (define info (hash-ref counts (substring text (+ ns 4) ne) #f))
    (when info
      (define body-start (skip-ws text (sexp-end text (+ s0 2))))
      (define body-end (sexp-end text body-start))
      (define cs (if (regexp-match? #px"^\\(and[\\s]" (substring text body-start (min body-end (+ body-start 5))))
                     (cdr (children text body-start))
                     (list (cons body-start body-end))))
      (define k (- (length cs) (cadr info)))
      (cond
        [(< k 0) (set-add! mismatches (list 'count-mismatch (car info) (length cs) (cadr info)))]
        [else
         (define parts
           (for/list ([c (in-list cs)] [j (in-naturals)])
             (define ct (substring text (car c) (cdr c)))
             (if (< j k) ct
                 (let ([g (format "g!~a" (hash-count guards))])
                   (hash-set! guards g (list (car info) (- j k -1)))
                   (set! file-guards (cons g file-guards))
                   (format "(=> ~a ~a)" g ct)))))
         (set! edits (cons (list body-start body-end (string-append "(and " (string-join parts " ") ")")) edits))
         (define d (regexp-match-positions (regexp-quote (string-append "(declare-fun " (substring text ns ne))) text))
         (set! decls (cons (if d (caar d) 0) decls))])))
  (define gs (reverse file-guards))
  ;; the query: the Function-Def block's check-sats
  (define def (regexp-match-positions #px";; Function-Def [^\n]*\n" text))
  (define push (and def (regexp-match-positions #px"\\(push\\)" text (cdar def))))
  (define pop (and push (regexp-match-positions #px"\n\\(pop\\)" text (cdar push))))
  (define assume (format "(check-sat-assuming (~a))" (string-join gs " ")))
  (when pop
    (define sats (regexp-match-positions* #px"\\(check-sat\\)" text (cdar push) (caar pop)))
    (for ([p (in-list sats)] [i (in-naturals 1)])
      (set! edits
            (cons (list (car p) (cdr p)
                        (if (< i (length sats)) assume
                            (string-append
                             "(echo \"@last\")\n " assume "\n (echo \"@core\")\n (get-unsat-core)\n"
                             (apply string-append
                                    (for/list ([g (in-list gs)])
                                      (format " (echo \"@off ~a\")\n (check-sat-assuming (~a))\n (get-info :reason-unknown)\n" g
                                              (string-join (for/list ([h (in-list gs)]) (if (equal? h g) (format "(not ~a)" g) h)) " ")))))))
                  edits)))
    ;; models are not needed, and are long
    (for ([p (in-list (regexp-match-positions* #px"\\(get-model\\)" text (cdar push) (caar pop)))])
      (set! edits (cons (list (car p) (cdr p) "") edits))))
  ;; every guard declared once, before the first ens% declaration that has guards
  (when (pair? decls)
    (set! edits (cons (list (apply min decls) (apply min decls)
                            (apply string-append (for/list ([g (in-list gs)]) (format "(declare-const ~a Bool)\n" g))))
                      edits)))
  (string-append "(set-option :produce-unsat-cores true)\n"
                 (for/fold ([t text]) ([e (in-list (sort edits > #:key car))])
                   (string-append (substring t 0 (car e)) (caddr e) (substring t (cadr e))))))

;; ================================================================ z3's answers

;; read-answer : lines guards -> (client-facts LAST needed limit)
(define (read-answer lines guards)
  (define (after tag) (let ([m (member tag lines)]) (and m (pair? (cdr m)) (cadr m))))
  (define last-result (or (after "@last") "none"))
  (define offs
    (for/list ([l (in-list lines)] [i (in-naturals)] #:when (regexp-match? #rx"^@off " l))
      (define res (if (< (add1 i) (length lines)) (list-ref lines (add1 i)) ""))
      (define why (if (< (+ i 2) (length lines)) (list-ref lines (+ i 2)) ""))
      (list (hash-ref guards (substring l 5))
            res
            (and (equal? res "unknown") (regexp-match? #rx"canceled|resource|rlimit|timeout" why)))))
  (define unsat? (equal? last-result "unsat"))
  (values last-result
          (if unsat? (for/list ([o (in-list offs)] #:unless (equal? (cadr o) "unsat") #:unless (caddr o)) (car o)) '())
          (if unsat? (for/list ([o (in-list offs)] #:when (caddr o)) (car o)) '())))

;; z3 on each file, n at a time; FILE.smt2 -> FILE.out
(define (run-z3 z3 files n)
  (define sema (make-semaphore n))
  (define ts
    (for/list ([f (in-list files)])
      (semaphore-wait sema)
      (thread (lambda ()
                (dynamic-wind
                 void
                 (lambda ()
                   (call-with-output-file (path-replace-extension f #".out") #:exists 'truncate
                     (lambda (o) (parameterize ([current-output-port o] [current-error-port o])
                                   (system* z3 (path->string f))))))
                 (lambda () (semaphore-post sema)))))))
  (for-each thread-wait ts))

(define (z3-program vostd)
  (or (for/first ([p (in-list (list (build-path vostd "tools" "verus" "source" "z3")
                                    (build-path vostd "tools" "verus" "source" "z3.exe")))]
                  #:when (file-exists? p))
        p)
      (find-executable-path "z3")
      (error 'coverage "no z3: neither the checkout's tools/verus/source/z3 nor one on PATH")))

;; ================================================================ a module

(define-runtime-path self-source "coverage.rkt")

(define (coverage-module cfg run-dir m)
  (define dir (build-path run-dir "coverage" m))
  (define facts-file (build-path run-dir "coverage" (string-append m ".rktd")))
  (define results-key (build-path run-dir "results" m "key.sha"))
  (define key (string-append (if (file-exists? results-key) (file->string results-key) "")
                             (call-with-input-file self-source sha1)))
  (define key-file (build-path dir "key.sha"))
  (cond
    [(and (file-exists? key-file) (equal? (file->string key-file) key) (file-exists? facts-file))
     (file->list facts-file)]
    [else
     (when (directory-exists? dir) (delete-directory/files dir))
     (make-directory* dir)
     (define target-file (build-path (config-auto cfg) "targets" (string-append m ".rktd")))
     (define target (read-target target-file))
     (define table-file (build-path run-dir "tables" (string-append m ".rktd")))
     (define cs (file->list (build-path run-dir "clients" (string-append m ".rktd"))))
     (define log-dir (build-path dir "log"))
     (make-directory* log-dir)
     ;; the run, as the evaluation's (its table has the imports the evaluation added)
     (parameterize ([verus-extra-args (list "--log" "smt" "--log-dir" (path->string (path->complete-path log-dir)))])
       (run-clients target-file table-file cs (build-path dir "run")))
     ;; each client's file: the client module's last segment, `__`, the client's name
     (define client-mod (last (string-split (cadr (assq 'module target)) "::")))
     (define rx (pregexp (string-append "^.*" (regexp-quote client-mod) "__(.*)[.]smt2$")))
     (define counts (ensures-counts table-file))
     (define guards (make-hash))
     (define mismatches (mutable-set))
     (define guarded
       (for/list ([f (in-list (directory-list log-dir #:build? #t))]
                  #:when (regexp-match? rx (path->string (file-name-from-path f))))
         (define out (build-path dir (file-name-from-path f)))
         (call-with-output-file out #:exists 'truncate
           (lambda (o) (write-string (guard-file (file->string f) counts guards mismatches) o)))
         out))
     (run-z3 (z3-program (cadr (assq 'vostd target))) guarded (max 1 (quotient (processor-count*) 2)))
     (define per-client
       (for/list ([f (in-list guarded)])
         (define name (string->symbol (cadr (regexp-match rx (path->string (file-name-from-path f))))))
         (define-values (last-result needed limit)
           (read-answer (file->lines (path-replace-extension f #".out")) guards))
         `(client ,name ,(string->symbol last-result) (needed ,@needed) (limit ,@limit))))
     ;; every clause of the module's own APIs with ensures
     (define own (for/list ([e (in-list (table-fns (table-of (config-auto cfg) m)))]) (cadr e)))
     (define clauses
       (sort (remove-duplicates
              (for*/list ([v (in-hash-values counts)] #:when (memq (car v) own) [j (in-range 1 (add1 (cadr v)))])
                (list (car v) j)))
             string<? #:key (lambda (x) (format "~a" x))))
     (define (clients-of key field)
       (for/list ([c (in-list per-client)] #:when (member key (cdr (assq field (cdddr c))))) (cadr c)))
     (define clause-facts
       (for/list ([cl (in-list clauses)])
         (define by (clients-of cl 'needed))
         (define lim (clients-of cl 'limit))
         `(clause ,@cl ,(cond [(pair? by) 'checked] [(pair? lim) 'unknown] [else 'unchecked]) ,@by)))
     (define facts (append (set->list mismatches) per-client clause-facts))
     (write-forms facts-file facts)
     (call-with-output-file key-file #:exists 'truncate (lambda (o) (write-string key o)))
     facts]))

(define (processor-count*) (processor-count))

(define (mutable-set) (make-hash))
(define (set-add! s x) (hash-set! s x #t))
(define (set->list s) (hash-keys s))

;; coverage : run-dir [module-regex] -> ((coverage M (clauses N) (checked K) (unknown U) (unchecked ..) ..) ...)
;; Only modules whose run concluded ((sanity ok)).
(define (coverage run-dir [only #rx""])
  (define manifest (file->value (build-path run-dir "manifest.rktd")))
  (define cfg (read-config (cadr (assq 'config (cdr manifest)))))
  (for/list ([line (in-list (file->list (build-path run-dir "modules.rktd")))]
             #:when (and (regexp-match? only (cadr line)) (member '(sanity ok) (cddr line))))
    (define m (cadr line))
    (printf "~a\n" m)
    (flush-output)
    (define facts (coverage-module cfg run-dir m))
    (define cl (filter (lambda (f) (eq? (car f) 'clause)) facts))
    (define (n s) (count (lambda (f) (eq? (cadddr f) s)) cl))
    `(coverage ,m (clauses ,(length cl)) (checked ,(n 'checked)) (unknown ,(n 'unknown))
               (unchecked ,@(for/list ([f (in-list cl)] #:when (eq? (cadddr f) 'unchecked)) (list (cadr f) (caddr f))))
               ,@(filter (lambda (f) (eq? (car f) 'count-mismatch)) facts))))
