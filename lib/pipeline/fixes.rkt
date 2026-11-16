#lang racket/base
;; Confirmation of hand-written fixes (design.md 3.9, docs/workflow.md F).
;;
;; provable/confirm confirm one kind of change only: a clause added to the
;; culprit's ensures, in its parameters' terms.  Other fixes (a function with
;; no ensures, `dual_spec` made `dual_spec, open`, an open spec function
;; changed, two layers changed together) were confirmed by hand (evaluation.md
;; 8).  This does those steps mechanically.  A fix is data:
;;
;;   (fix ID (groups (M KEY) ...) (why STRING) (replace FILE OLD NEW) ...)
;;
;; FILE relative to the checkout; OLD occurs in the file's original text
;; exactly once (else the fix is bad-edit and not applied: no guessing), and
;; the edits of all fixes do not overlap.
;;
;;   together  all fixes applied to COPY (from its original text each round),
;;             `cargo dv verify --package ostd` (the dependencies, bitflags,
;;             in the same output).  An error on a line of a fix's new text is
;;             that fix's (unproved for a postcondition, compile when Verus did
;;             not get to verify, else other); an error elsewhere is mapped
;;             back to the original line, its function found in the VIR, and
;;             put down to the fixes that edit a function it calls or one of
;;             its module (breaks-proof: confirm.rkt's reaches?).  Those fixes
;;             come out and the round is verified again, until one has no
;;             error; an error put down to no fix stops.
;;   alone     the survivors in slots (no two related fixes in one), each slot
;;             verified the same way: a fix blamed in its slot is not `alone`.
;;   clients   the survivors applied, COPY as the checkout, the target groups'
;;             modules run again (evaluate.rkt, a configuration of those
;;             modules), grouped, compared with the run client by client.
;;
;; RUN-DIR/fixes/NAME/ (NAME: the fixes file's name): rounds.rktd and
;; verus-rN.out (together), alone-K/, config.rktd, env.rktd, after/ (a run
;; directory), and facts.rktd:
;;   (fix ID STATUS [ALONE] (groups (M KEY BEFORE AFTER) ...) CONFIRMED)
;;     STATUS = kept | bad-edit REASON | removed KIND ROUND
;;     ALONE = alone | not-alone KIND    CONFIRMED = confirmed | not-confirmed
;;   (module M (verified BEFORE AFTER) (sanity S) (regressions NAME ...) (new KEY ...))
;; Resumed: the rounds from rounds.rktd, a slot from its own, the clients by
;; evaluate's key.  COPY must be clean; it is restored at the end.
(require racket/file racket/list racket/match racket/string racket/path racket/pretty
         "../base/forms.rkt" "../base/env.rkt" "../vostd/run.rkt" "../vostd/git.rkt"
         "drops.rkt" "confirm.rkt" "evaluate.rkt" "groups.rkt" "compare.rkt")
(provide fixes read-fixes read-no-fixes ostd-results plan-edits map-line blame-fix-errors fix-slots norm-file function-at)

;; ================================================================ data

(struct fix (id groups why edits) #:transparent) ; edits: ((FILE OLD NEW) ...)

;; (no-fix (M KEY) WHY): the writer found no spec-only fix for a group; not run,
;; kept for the record (read-no-fixes)
(define (read-no-fixes file)
  (for/list ([x (in-list (file->list file))] #:when (and (pair? x) (eq? (car x) 'no-fix))) (cdr x)))
(define (read-fixes file)
  (for/list ([x (in-list (file->list file))] #:unless (and (pair? x) (eq? (car x) 'no-fix)))
    (match x
      [`(fix ,id ,more ...)
       (define (part k) (cond [(assq k (filter pair? more)) => cdr] [else '()]))
       (fix id
            (for/list ([g (in-list (part 'groups))])
              (match g [(list (? string? m) (? string? k)) (list m k)]
                [_ (error 'fixes "~a: fix ~a: a group is (MODULE KEY): ~s" file id g)]))
            (let ([w (part 'why)]) (if (pair? w) (car w) ""))
            (for/list ([e (in-list more)] #:when (and (pair? e) (eq? (car e) 'replace)))
              (match e [`(replace ,(? string? f) ,(? string? o) ,(? string? n)) (list f o n)]
                [_ (error 'fixes "~a: fix ~a: (replace FILE OLD NEW): ~s" file id e)])))]
      [_ (error 'fixes "~a: not a (fix ID ..): ~s" file x)])))

;; norm-file : path string -> the path without `./` and `dir/..` (Verus writes
;; `ostd/src/../specs/..`, a fix `ostd/specs/..`)
(define (norm-file s)
  (let loop ([parts (string-split (string-replace s "\\" "/") "/")] [acc '()])
    (cond [(null? parts) (string-join (reverse acc) "/")]
          [(equal? (car parts) ".") (loop (cdr parts) acc)]
          [(and (equal? (car parts) "..") (pair? acc) (not (equal? (car acc) ".."))) (loop (cdr parts) (cdr acc))]
          [else (loop (cdr parts) (cons (car parts) acc))])))

;; ================================================================ edits (pure)

(define (line-of text pos) (add1 (for/sum ([c (in-string text 0 pos)]) (if (char=? c #\newline) 1 0))))
(define (count-lines s) (for/sum ([c (in-string s)]) (if (char=? c #\newline) 1 0)))

;; plan-edits : (FILE -> original text) (fix ...) -> (values files bad)
;;   files: FILE -> (values new-text spans), spans ((ID ORIG-FIRST ORIG-LAST NEW-FIRST NEW-LAST) ...)
;;   bad: ((ID . REASON) ...) the fixes not applied (OLD not once, overlapping an earlier fix)
(define (plan-edits text-of fs)
  ;; find every edit in the original text
  (define found ; ((FILE ID START END NEW) ...) or a bad entry
    (for*/list ([f (in-list fs)] [e (in-list (fix-edits f))])
      (match-define (list file old0 new0) e)
      (define text (text-of file))
      ;; a fix written against a CRLF checkout (Windows, core.autocrlf) means the same
      ;; against an LF one: OLD and NEW take the line ending of the file they edit
      (define (eol s) (let ([lf (string-replace s "\r\n" "\n")])
                        (if (and text (regexp-match? #rx"\r\n" text)) (string-replace lf "\n" "\r\n") lf)))
      (define old (eol old0))
      (define new (eol new0))
      (define hits (if text (regexp-match-positions* (regexp (regexp-quote old)) text) '()))
      (cond [(not text) (list 'bad (fix-id f) (format "no file ~a" file))]
            [(not (= (length hits) 1)) (list 'bad (fix-id f) (format "OLD occurs ~a times in ~a" (length hits) file))]
            [else (list (norm-file file) (fix-id f) (caar hits) (cdar hits) new)])))
  (define bad0 (remove-duplicates (for/list ([x (in-list found)] #:when (eq? (car x) 'bad)) (cons (cadr x) (caddr x))) #:key car))
  ;; a fix with one bad edit is out with all its edits; then overlaps, in the fixes' order
  (define good (filter (lambda (x) (and (not (eq? (car x) 'bad)) (not (assv (cadr x) bad0)))) found))
  (define-values (kept bad1)
    (for/fold ([kept '()] [bad '()]) ([x (in-list good)])
      (define clash (for/first ([k (in-list kept)] #:when (and (equal? (car k) (car x)) (< (caddr x) (cadddr k)) (< (caddr k) (cadddr x)))) k))
      (cond [(assv (cadr x) bad) (values kept bad)]
            [clash (values (filter (lambda (k) (not (equal? (cadr k) (cadr x)))) kept)
                           (cons (cons (cadr x) (format "overlaps fix ~a in ~a" (cadr clash) (car x))) bad))]
            [else (values (cons x kept) bad)])))
  (define kept* (filter (lambda (x) (not (assv (cadr x) bad1))) kept))
  (define files
    (for/hash ([g (in-list (group-by car kept*))])
      (define file (car (car g)))
      (define text (text-of file))
      (define es (sort g < #:key caddr))
      (define-values (out spans _delta)
        (for/fold ([out '()] [spans '()] [delta 0] #:result (values out (reverse spans) delta))
                  ([x (in-list es)] [prev-end (in-list (cons 0 (map cadddr es)))])
          (match-define (list _ id start end new) x)
          (define of (line-of text start))
          (define ol (+ of (count-lines (substring text start end))))
          (define nf (+ of delta))
          (define nl (+ nf (count-lines new)))
          (values (list* new (substring text prev-end start) out)
                  (cons (list id of ol nf nl) spans)
                  (+ delta (- (count-lines new) (count-lines (substring text start end)))))))
      (define last-end (cadddr (last es)))
      (values file (cons (apply string-append (reverse (cons (substring text last-end) out))) spans))))
  (values files (append bad0 bad1)))

;; map-line : spans line -> (values ID-or-#f original-line)
;; A line of the new text: the fix whose new text holds it, or the original line.
(define (map-line spans l)
  (let loop ([ss spans] [delta 0])
    (match ss
      ['() (values #f (- l delta))]
      [(cons (list id of ol nf nl) rest)
       (cond [(< l nf) (values #f (- l delta))]
             [(<= l nl) (values id of)]
             [else (loop rest (+ delta (- (- nl nf) (- ol of))))])])))

;; blame-fix-errors : errors spans-of fn-at reaches? edited-fns verified?
;;   -> (values ((KIND ID ...) ...) unblamed-errors)
;; spans-of: FILE -> spans or #f; fn-at: FILE original-line -> F or #f;
;; edited-fns: ID -> (F ...), the functions a fix's edits are in.
(define (blame-fix-errors errors spans-of fn-at reaches? edited-fns ids verified?)
  (define by (make-hash))
  (define (add! k id) (hash-update! by k (lambda (s) (if (memv id s) s (cons id s))) '()))
  (define unblamed
    (for/fold ([un '()]) ([e (in-list errors)])
      (define kind (cond [(regexp-match? #px"postcondition not satisfied" (car e)) 'unproved]
                         [(not verified?) 'compile] [else 'other]))
      (define direct
        (remove-duplicates
         (for*/list ([loc (in-list (list-ref e 4))]
                     [sp (in-value (spans-of (norm-file (car loc))))] #:when sp
                     [id (in-value (let-values ([(id _o) (map-line sp (cdr loc))]) id))] #:when id)
           id)))
      (define reached
        (if (pair? direct) '()
            (let* ([file (and (list-ref e 1) (norm-file (list-ref e 1)))]
                   [l (list-ref e 2)]
                   [orig (and file l (let ([sp (spans-of file)]) (if sp (let-values ([(_i o) (map-line sp l)]) o) l)))]
                   [g (and orig (fn-at file orig))])
              (if g (for/list ([id (in-list ids)] #:when (ormap (lambda (f) (reaches? g f)) (edited-fns id))) id) '()))))
      (for ([id (in-list direct)]) (add! kind id))
      (for ([id (in-list reached)]) (add! 'breaks-proof id))
      (if (and (null? direct) (null? reached)) (cons e un) un)))
  (values (for/list ([k (in-list '(compile unproved other breaks-proof))] #:when (hash-ref by k #f))
            (cons k (sort (hash-ref by k) (lambda (a b) (string<? (format "~a" a) (format "~a" b))))))
          (reverse unblamed)))

;; function-at : ((F FILE FIRST LAST) ...) file line -> F or #f
;; The function whose body holds the line; else the next one in the file: the
;; VIR's range is the body, and a fix's edit is mostly above it, in the
;; function's `#[verus_spec]`, requires or ensures.
(define (function-at fns file l)
  (or (enclosing-function fns file l)
      (let ([after (filter (lambda (x) (and (equal? (cadr x) file) (> (caddr x) l))) fns)])
        (and (pair? after) (car (argmin caddr after))))))

;; ostd-results : log lines -> (VERIFIED ERRORS) of ostd's own result, or #f: the
;; last result after `-p "ostd"` (`dv verify -p ostd` verifies the dependencies,
;; bitflags, in the same command, before ostd)
(define (ostd-results lines)
  (define after (let ([i (for/last ([l (in-list lines)] [k (in-naturals)] #:when (regexp-match? #px"\"-p\" \"ostd\"" l)) k)])
                  (if i (drop lines i) '())))
  (for/last ([l (in-list after)]
             #:when (regexp-match? #px"verification results:: [0-9]+ verified, [0-9]+ errors" l))
    (match (regexp-match #px"verification results:: ([0-9]+) verified, ([0-9]+) errors" l)
      [(list _ v e) (list (string->number v) (string->number e))])))

;; fix-slots : (ID ...) (ID -> (F ...)) related? -> ((ID ...) ...)
;; Greedy: a fix goes into the first slot none of whose fixes is related to it;
;; a fix with no known function (bitflags, a spec outside the VIR) gets its own.
(define (fix-slots ids fns-of related?)
  (define (rel? a b)
    (define fa (fns-of a)) (define fb (fns-of b))
    (or (null? fa) (null? fb) (for*/or ([f (in-list fa)] [g (in-list fb)]) (or (related? f g) (related? g f)))))
  (for/fold ([ss '()] #:result (map reverse ss)) ([id (in-list ids)])
    (let loop ([before '()] [after ss])
      (cond [(null? after) (append (reverse before) (list (list id)))]
            [(ormap (lambda (x) (rel? x id)) (car after)) (loop (cons (car after) before) (cdr after))]
            [else (append (reverse before) (list (cons id (car after))) (cdr after))]))))

;; ================================================================ running

(define (text-reader copy)
  (define cache (make-hash))
  (lambda (file)
    (hash-ref! cache (norm-file file)
               (lambda () (define p (build-path copy file)) (and (file-exists? p) (file->string p))))))

;; apply the planned files to COPY
(define (write-files! copy files)
  (for ([(file v) (in-hash files)])
    (call-with-output-file (build-path copy file) #:exists 'truncate (lambda (o) (write-string (car v) o)))))

;; rounds : copy fixes dir fn-at reaches? edited-fns target -> rounds
;; The together loop (or one slot's): (round N (applied ID ..) (verified V E) (KIND ID ..) ..), (done N)
(define (rounds copy fs dir fn-at reaches? edited-fns target)
  (make-directory* dir)
  (define rf (build-path dir "rounds.rktd"))
  (define text-of (text-reader copy))
  (let loop ()
    (define rs (if (file-exists? rf) (file->list rf) '()))
    (unless (assq 'done rs)
      (define n (add1 (length rs)))
      (define out (for*/list ([r (in-list rs)] #:when (eq? (car r) 'round) [b (in-list (cddddr r))] [id (in-list (cdr b))]) id))
      (define live (filter (lambda (f) (not (memv (fix-id f) out))) fs))
      (restore-all copy)
      (define-values (files _bad) (plan-edits text-of live))
      (write-files! copy files)
      (define log (build-path dir (format "verus-r~a.out" n)))
      (verify-ostd copy target log)
      (define lines (file->lines log))
      (define-values (_first errors) (parse-verus lines))
      ;; ostd's own result: the dependencies (bitflags) report first, and a crate
      ;; cargo-verus has verified before reports nothing; no ostd result, no round
      (define verified (ostd-results lines))
      (define ids (map fix-id live))
      (define-values (blamed unblamed)
        (blame-fix-errors errors (lambda (f) (let ([v (hash-ref files f #f)]) (and v (cdr v)))) fn-at reaches? edited-fns ids (and verified #t)))
      (restore-all copy)
      (cond
        [(pair? unblamed) (error 'fixes "round ~a: ~a errors put down to no fix (~a); the first: ~s" n (length unblamed) log (car unblamed))]
        [(and (null? blamed) (not (and verified (zero? (cadr verified))))) (error 'fixes "round ~a: no fix blamed, but ostd does not verify (~a)" n log)]
        [else
         (with-output-to-file rf #:exists 'append
           (lambda () (writeln `(round ,n (applied ,@ids) (verified ,@(or verified '(#f #f))) ,@blamed))
             (when (null? blamed) (writeln `(done ,n)))))
         (printf "  round ~a: ~a fixes, ~a\n" n (length ids)
                 (if (null? blamed) (format "ostd ~a verified, 0 errors" (car verified))
                     (string-join (for/list ([b (in-list blamed)]) (format "~a ~a" (car b) (length (cdr b)))) ", ")))
         (loop)])))
  (file->list rf))

(define (removed-in rs)
  (for*/hash ([r (in-list rs)] #:when (eq? (car r) 'round) [b (in-list (cddddr r))] [id (in-list (cdr b))])
    (values id (list (car b) (cadr r)))))

;; a configuration of the run's, its modules only these
(define (module-config run-dir ms file)
  (define manifest (file->value (build-path run-dir "manifest.rktd")))
  (define cfg-file (cadr (assq 'config (cdr manifest))))
  (define dir (let-values ([(d _n _x) (split-path (path->complete-path cfg-file))]) d))
  (define ev (assq 'evaluation (file->list cfg-file)))
  (define (abs p) (path->string (simplify-path (if (absolute-path? p) p (build-path dir p)))))
  (write-forms file
               (list `(evaluation
                       ,@(for/list ([f (in-list (cdr ev))] #:unless (eq? (car f) 'modules))
                           (match f [`(,(and k (or 'auto 'knowledge 'identity 'providers)) ,(? string? p)) `(,k ,(abs p))] [_ f]))
                       (modules ,(format "^(~a)[.]rktd$" (string-join (map regexp-quote ms) "|")))))))

(define (group-clients run-dir m)
  (define mods (group-failures run-dir #f (regexp (format "^~a$" (regexp-quote m)))))
  (for*/hash ([mod (in-list mods)] [g (in-list (cddr mod))] #:when (and (pair? g) (eq? (car g) 'group)))
    (values (cadr g) (cadr (assq 'clients (cddr g))))))

;; fixes : run-dir copy vir fixes-file -> facts
(define (fixes run-dir copy vir fixes-file)
  (define vostd (env-ref 'vostd))
  (define name (path->string (path-replace-extension (file-name-from-path fixes-file) #"")))
  (define out (build-path run-dir "fixes" name))
  (define (o . ps) (apply build-path out ps))
  (when (equal? (simplify-path (path->complete-path copy)) (simplify-path (path->complete-path vostd)))
    (error 'fixes "~a is the environment's checkout; give a copy of it" copy))
  (define commit (cadr (assq 'commit (cdr (file->value (build-path run-dir "manifest.rktd"))))))
  (unless (string-prefix? (git-head copy) commit) (error 'fixes "~a is at ~a, the run at ~a" copy (git-head copy) commit))
  (unless (or (file-exists? (o "rounds.rktd")) (clean-copy? copy)) (error 'fixes "~a has changes: give a clean copy" copy))
  (make-directory* out)
  (define fs (read-fixes fixes-file))
  (define target (or (env-ref 'drops-target-dir #f) (string-append (env-ref 'target-dir) "-drops")))
  (define-values (calls-of range-of trusted? fns) (vir-facts vir))
  (define (fn-at file l) (function-at fns (norm-file file) l))
  (define (reach? f g) (reaches? calls-of f g))
  ;; the functions each fix's edits are in (by the edit's first original line)
  (define text-of (text-reader copy))
  (define-values (planned bad) (plan-edits text-of fs))
  (define edited
    (for*/fold ([h (hash)]) ([(file v) (in-hash planned)] [sp (in-list (cdr v))])
      (define f (fn-at file (cadr sp)))
      (if f (hash-update h (car sp) (lambda (l) (remove-duplicates (cons f l))) '()) h)))
  (define (edited-fns id) (hash-ref edited id '()))
  (define good (filter (lambda (f) (not (assv (fix-id f) bad))) fs))
  (printf "~a fixes, ~a bad-edit\n" (length fs) (length bad))
  (for ([b (in-list bad)]) (printf "  bad-edit ~a: ~a\n" (car b) (cdr b)))
  (dynamic-wind
   void
   (lambda ()
     ;; together
     (printf "together:\n")
     (define rs (rounds copy good out fn-at reach? edited-fns target))
     (define removed (removed-in rs))
     (define survivors (filter (lambda (f) (not (hash-ref removed (fix-id f) #f))) good))
     ;; alone
     (define sl (fix-slots (map fix-id survivors) edited-fns reach?))
     (printf "alone: ~a slots (~a)\n" (length sl) (string-join (map (lambda (s) (number->string (length s))) sl) " "))
     (define alone
       (for/fold ([h (hash)]) ([s (in-list sl)] [k (in-naturals 1)])
         (define sfs (filter (lambda (f) (memv (fix-id f) s)) survivors))
         (printf "slot ~a:\n" k)
         (define r (removed-in (rounds copy sfs (o (format "alone-~a" k)) fn-at reach? edited-fns target)))
         (for/fold ([h h]) ([id (in-list s)]) (hash-set h id (match (hash-ref r id #f) [#f 'alone] [(list kind _) (list 'not-alone kind)])))))
     ;; clients: the survivors applied, the target modules rerun with COPY as the checkout
     (restore-all copy)
     (define-values (files _b) (plan-edits text-of survivors))
     (write-files! copy files)
     (define ms (sort (remove-duplicates (for*/list ([f (in-list survivors)] [g (in-list (fix-groups f))]) (car g))) string<?))
     (module-config run-dir ms (o "config.rktd"))
     (write-forms (o "env.rktd") `((vostd ,(path->string (simplify-path (path->complete-path copy)))) (target-dir ,target)))
     (printf "clients: ~a modules\n" (length ms))
     (parameterize ([current-env-files (cons (simplify-path (path->complete-path (o "env.rktd"))) (env-files))])
       (evaluate (o "config.rktd") (o "after")))
     (restore-all copy)
     ;; facts
     (define before (for/hash ([m (in-list ms)]) (values m (group-clients run-dir m))))
     (define after (for/hash ([m (in-list ms)]) (values m (group-clients (o "after") m))))
     (define cmp (compare-runs run-dir (o "after")))
     (define fix-facts
       (for/list ([f (in-list fs)])
         (define id (fix-id f))
         (define gs (for/list ([g (in-list (fix-groups f))])
                      (list (car g) (cadr g)
                            (hash-ref (hash-ref before (car g) (hash)) (cadr g) 0)
                            (hash-ref (hash-ref after (car g) (hash)) (cadr g) 0))))
         (define st (cond [(assv id bad) => (lambda (b) `(bad-edit ,(cdr b)))]
                          [(hash-ref removed id #f) => (lambda (r) `(removed ,@r))]
                          [else '(kept)]))
         (define a (hash-ref alone id #f))
         `(fix ,id ,@st ,@(if a (list a) '()) (groups ,@gs)
               ,(if (and (eq? a 'alone) (pair? gs) (andmap (lambda (g) (zero? (list-ref g 3))) gs)) 'confirmed 'not-confirmed))))
     (define module-facts
       (for/list ([m (in-list ms)])
         (define (summary dir) (for/first ([l (in-list (file->list (build-path dir "modules.rktd")))] #:when (equal? (cadr l) m)) l))
         (define (ver l) (cond [(and l (assq 'verified (filter pair? (cddr l)))) => cadr] [else 0]))
         (define c (for/first ([x (in-list cmp)] #:when (equal? (cadr x) m)) x))
         (define regs (if c (cdr (or (assq 'regressions (filter pair? (cddr c))) '(regressions))) '()))
         (define new (sort (for/list ([k (in-hash-keys (hash-ref after m))] #:unless (hash-has-key? (hash-ref before m) k)) k) string<?))
         `(module ,m (verified ,(ver (summary run-dir)) ,(ver (summary (o "after"))))
            (sanity ,(let ([l (summary (o "after"))]) (and l (cadr (or (assq 'sanity (filter pair? (cddr l))) '(sanity none))))))
            (regressions ,@regs) (new ,@new))))
     (write-forms (o "facts.rktd") (append fix-facts module-facts))
     (define (tally sel) (for/fold ([h (hash)]) ([x (in-list fix-facts)]) (hash-update h (sel x) add1 0)))
     (printf "fixes: ~a\n" (tally (lambda (x) (caddr x))))
     (printf "confirmed: ~a of ~a\n" (count (lambda (x) (eq? (last x) 'confirmed)) fix-facts) (length fix-facts))
     (for ([m (in-list module-facts)]) (printf "  ~s\n" m))
     fix-facts)
   (lambda () (restore-all copy))))

;; COPY clean in all it is verified with: ostd and the libraries it depends on
;; (a fix may edit verified_libs/bitflags; drops.rkt's restore resets ostd/ only)
(define (clean-copy? copy)
  (parameterize ([current-directory copy] [current-output-port (open-output-nowhere)])
    (system* (git-program) "diff" "--quiet")))
(define (restore-all copy)
  (parameterize ([current-directory copy])
    (unless (system* (git-program) "checkout" "-q" "--" ".") (error 'fixes "~a: git checkout failed" copy))))
(require racket/system racket/port)
