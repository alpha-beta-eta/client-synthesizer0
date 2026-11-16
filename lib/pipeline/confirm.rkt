#lang racket/base
;; Confirmation of what provable.rkt proved (docs/triage.md 8): the checks of
;; workflow F, mechanically, for every clause a culprit F proved once asked.
;;
;; provable.rkt puts all the groups' clauses into their functions' ensures at
;; once; a clause that survives there may rest on another: a clause of the
;; same F before it, or one added to a function F calls (F's proof assumes
;; its callees' ensures).  So each surviving clause is verified again without
;; them:
;;
;;   alone     the survivors in slots: a slot has at most one clause per
;;             function, and no two clauses where one's function calls the
;;             other's (VIR's calls; Verus checks a function against its
;;             callees' specifications only, so clauses not so related do
;;             not touch each other's proofs).  One drops.rkt round loop per
;;             slot in COPY.  A clause that survives its slot is `alone`; one
;;             Verus blames there, `together-only` (it needs one of the
;;             clauses of its function or of the functions it calls: (needs
;;             ID ...), not narrowed further).  An error in a function with no
;;             candidate (an existing proof: fill's loop, once write_val says
;;             more) is put down to the slot's clauses of the functions that
;;             function calls, for the same reason: `breaks-caller` (the
;;             clause holds, but alone it makes a caller's proof fail; with
;;             all of provable's clauses that proof went through).  An error
;;             put down to no clause stops, as before
;;   trusted   what F's proof may rest on that Verus does not check: the
;;             source's `assume` and `admit` in F's body (trusted.rkt's
;;             sites in the body's lines), F's callees that are external_body
;;             (vstd's left out): (rests-on ...).  F's own, not its callees';
;;             and what F calls, not what this clause's proof uses
;;   clients   provable's survivors.patch (ostd verified with all of them:
;;             provable's last round) applied to COPY, and the failed clients
;;             of each module that call one of the functions changed rerun
;;             there (COPY as the checkout, the drops target directory); the
;;             same clients' old results beside them, both grouped
;;             (groups.rkt).  Per proved group: the very failure provable put
;;             in F's terms (its CLIENT and ID) gone or not, and the clients
;;             whose failure of the clause is attributed to F, before and
;;             after (a group's key is the clause: the same clause may fail
;;             after other calls too, write_val's after write_val; an
;;             after-an-error group holds several clauses)
;;
;; RUN-DIR/confirm/: alone-K/ (cand.rktd, rounds.rktd, verus-rN.out per slot),
;; env.rktd (the overlay that makes COPY the checkout), before/ and after/
;; (run directories: manifest, tables, clients, results of the rerun clients),
;; and
;;   facts.rktd
;;     (clause ID F ALONE (slot K) [(needs ID ...)] [(rests-on (assume FILE:LINE DETAIL) .. (external-body G) ..)] TEXT)
;;       ALONE = alone | together-only KIND | breaks-caller     (KIND: drops.rkt's blame)
;;     (group M KEY ID STATUS (before N) (after N) (clients N N) (at CLIENT ID AT) CONFIRMED)
;;       STATUS = fixed | reduced | unchanged | no-clients   (by F's clients, before/after)
;;       AT = fixed | fails | not-run                        (the very failure)
;;       CONFIRMED = confirmed (the clause alone, AT fixed, the module sane)
;;                 | not-confirmed
;;     (module M (clients N) (verified BEFORE AFTER) (sanity S) [(new KEY ...)])
;;       new: groups after that were not before (a failure the change
;;       uncovered or made)
;; COPY must be clean (as for provable); it is restored at the end.  Each
;; slot resumes from its rounds.rktd, the clients by run-module's key.
(require racket/file racket/list racket/match racket/string racket/system
         "../model/api.rkt" "../base/forms.rkt" "../base/env.rkt"
         "../vostd/vir.rkt" "../vostd/git.rkt" "../vostd/trusted.rkt"
         (only-in "../analysis/drops.rkt" vir-calls)
         "groups.rkt" "drops.rkt" "evaluate.rkt")
(provide confirm slots group-status norm-path vir-facts enclosing-function)

;; ================================================================ pure parts

;; norm-path : VIR path string -> the path without crate prefix and twin marker
(define (norm-path p)
  (regexp-replace #rx"^ostd::" (regexp-replace* #rx"_VERUS_VERIFIED_" p "") ""))

;; slots : ((ID . F) ...) (F -> (G ...)) -> ((ID ...) ...)
;; Greedy, in ID order: a clause goes into the first slot with no clause of
;; its function and none of a function it calls or that calls it.
(define (slots cs calls-of)
  (define (related? f g) (or (equal? f g) (member g (calls-of f)) (member f (calls-of g))))
  (define ss
    (for/fold ([ss '()]) ([c (in-list cs)])
      (define f (cdr c))
      (let loop ([before '()] [after ss])
        (cond
          [(null? after) (append (reverse before) (list (list c)))]
          [(ormap (lambda (d) (related? f (cdr d))) (car after)) (loop (cons (car after) before) (cdr after))]
          [else (append (reverse before) (list (append (car after) (list c))) (cdr after))]))))
  (for/list ([s (in-list ss)]) (map car s)))

;; group-status : before after -> fixed | reduced | unchanged | no-clients
(define (group-status before after)
  (cond [(zero? before) 'no-clients]
        [(zero? after) 'fixed]
        [(< after before) 'reduced]
        [else 'unchanged]))

;; ================================================================ VIR

;; vir-facts : VIR file -> (values calls-of range-of trusted?)
;;   calls-of: normalized F -> (normalized G ...), F's direct callees
;;   range-of: normalized F -> (FILE FIRST LAST) of F's body, or #f
;;   trusted?: normalized G -> #t when the function Verus checks is external_body
(define (vir-facts vir)
  (define fns (for/list ([x (in-list (load-vir vir))] #:when (field x 'require)) x))
  (define (path-of f) (format "~a" (field (field f 'name) 'path)))
  (define (twin? f) (regexp-match? #rx"_VERUS_VERIFIED_" (path-of f)))
  ;; the function Verus checks: the twin when there is one
  (define checked
    (for/fold ([h (hash)]) ([f (in-list fns)])
      (define k (norm-path (path-of f)))
      (if (and (hash-ref h k #f) (not (twin? f))) h (hash-set h k f))))
  (define (eb? f) (eq? (field (field f 'attrs) 'is_external_body) 'true))
  ;; the body's span, the outermost one in it: (FILE FIRST-LINE LAST-LINE)
  ;; (VIR's AssertAssume is not what the source says: Verus makes assumes of
  ;; its own, for Tracked arguments; the source's assume and admit are
  ;; trusted.rkt's, found in this range)
  (define (body-range body)
    (let find ([e body])
      (cond
        [(and (pair? e) (memq (car e) '(@ @@)) (pair? (cdr e)) (string? (cadr e)))
         (match (regexp-match #px"^(.*):([0-9]+):[0-9]+: ([0-9]+):[0-9]+" (cadr e))
           [(list _ f a b) (list f (string->number a) (string->number b))]
           [_ #f])]
        [(pair? e) (or (find (car e)) (find (cdr e)))]
        [else #f])))
  (define calls (for/hash ([(k f) (in-hash checked)])
                  (define b (field f 'body))
                  (values k (if (pair? b) (remove-duplicates (map (lambda (c) (norm-path (car c))) (vir-calls b))) '()))))
  (define ranges (for/hash ([(k f) (in-hash checked)]) (values k (and (pair? (field f 'body)) (body-range (field f 'body))))))
  (values (lambda (f) (hash-ref calls f '()))
          (lambda (f) (hash-ref ranges f #f))
          (lambda (g) (let ([x (hash-ref checked g #f)]) (and x (eb? x))))
          ;; every function with a body: (F FILE FIRST LAST)
          (for/list ([(k r) (in-hash ranges)] #:when r) (cons k r))))

;; enclosing-function : ((F FILE FIRST LAST) ...) file line -> F or #f
;; The innermost body that holds the line (a closure's or a nested function's
;; inside its parent's).
(define (enclosing-function fns file line)
  (define in (filter (lambda (x) (and (equal? (cadr x) file) (<= (caddr x) line (cadddr x)))) fns))
  (and (pair? in) (car (argmin (lambda (x) (- (cadddr x) (caddr x))) in))))

;; rests-on : F calls-of body-range-of trusted? sites -> ((assume FILE:LINE DETAIL) .. (external-body G) ..)
;; What F's proof takes on trust: the source's assume and admit in F's body,
;; F's callees that are external_body.  vstd's are left out: vstd is the base
;; every proof stands on, not something this one adds.
(define (rests-on f calls-of range-of trusted? sites)
  (append
   (match (range-of f)
     [(list file a b)
      (for/list ([s (in-list sites)]
                 #:when (memq (cadr s) '(assume admit))
                 #:when (equal? (caddr s) file)
                 #:when (<= a (cadr (list-ref s 5)) b))
        `(,(cadr s) ,(format "~a:~a" file (cadr (list-ref s 5))) ,(list-ref s 4)))]
     [_ '()])
   (for/list ([g (in-list (calls-of f))] #:when (trusted? g) #:unless (regexp-match? #rx"^vstd::" g))
     `(external-body ,g))))

;; ================================================================ confirm

;; confirm : run-dir copy vir [module-regex] [#:dry? B] -> facts
(define (confirm run-dir copy vir [only #rx""] #:dry? [dry? #f])
  (define pdir (build-path run-dir "provable"))
  (define out (build-path run-dir "confirm"))
  (define (o . ps) (apply build-path out ps))
  (for ([f (in-list '("cand.rktd" "rounds.rktd" "facts.rktd" "survivors.patch"))])
    (unless (file-exists? (build-path pdir f))
      (error 'confirm "~a: no ~a (run `provable` first)" pdir f)))
  (define cands (file->list (build-path pdir "cand.rktd")))
  (define prounds (file->list (build-path pdir "rounds.rktd")))
  (unless (assq 'done prounds) (error 'confirm "~a: provable did not finish" pdir))
  (define blamed0 (for*/list ([r (in-list prounds)] #:when (eq? (car r) 'round)
                              [b (in-list (cddddr r))] [i (in-list (cdr b))]) i))
  (define last-verified (cdr (assq 'verified (cddr (findf (lambda (r) (and (eq? (car r) 'round) (= (cadr r) (cadr (assq 'done prounds))))) prounds)))))
  ;; the survivors: (ID . F-normalized), and their groups
  (define survivors (for/list ([c (in-list cands)] [i (in-naturals)] #:unless (memv i blamed0)) i))
  (define (cand-f i) (norm-path (cadr (list-ref cands i))))
  (define (cand-key i) (cons (list-ref (list-ref cands i) 2) (list-ref (list-ref cands i) 7)))
  (define proved-groups ; (M KEY ID F-NAME CLIENT AT-ID)
    (for*/list ([x (in-list (file->list (build-path pdir "facts.rktd")))]
                #:when (and (pair? x) (eq? (car x) 'provable) (eq? (list-ref x 6) 'proved)))
      (match-define `(provable ,m ,key ,client ,at-id ,f ,_ ,text) x)
      (define id (for/first ([i (in-list survivors)] #:when (equal? (cand-key i) (cons (format "~a" f) text))) i))
      (list m key id f client at-id)))
  (define-values (calls-of range-of trusted? fns) (vir-facts vir))
  (define commit (cadr (assq 'commit (cdr (file->value (build-path run-dir "manifest.rktd"))))))
  (define sites (trusted-sites copy commit))
  (define (rests f) (rests-on f calls-of range-of trusted? sites))
  (define sl (slots (for/list ([i (in-list survivors)]) (cons i (cand-f i))) calls-of))
  (define changed (remove-duplicates (map cadddr proved-groups)))
  ;; the clients to rerun: failed ones that call a changed function
  (define modules (sort (remove-duplicates (filter (lambda (m) (regexp-match? only m)) (map car proved-groups))) string<?))
  (define rerun
    (for/hash ([m (in-list modules)])
      (define rf (build-path run-dir "results" m "results.rktd"))
      (define plan (let ([f (build-path run-dir "results" m "plan.rktd")]) (if (file-exists? f) (file->list f) '())))
      (define failed (for/list ([r (in-list (file->list rf))] #:when (and (pair? r) (eq? (car r) 'client) (eq? (caddr r) 'failed))) (cadr r)))
      (values m (for/list ([p (in-list plan)]
                           #:when (and (pair? p) (eq? (car p) 'client) (memq (cadr p) failed))
                           #:when (for/or ([c (in-list (plan-calls p))]) (memq (cadr c) changed)))
                  (cadr p)))))
  (printf "~a clauses survived provable (~a groups), ~a slots (~a); ~a clients to rerun in ~a modules\n"
          (length survivors) (length proved-groups) (length sl) (string-join (map (lambda (s) (number->string (length s))) sl) " ")
          (for/sum ([v (in-hash-values rerun)]) (length v)) (length modules))
  (cond
    [dry?
     (for ([f (in-list (remove-duplicates (map cand-f survivors)))])
       (printf "~a\n  rests on ~s\n" f (rests f)))
     sl]
    [else
     (when (equal? (simplify-path (path->complete-path copy)) (simplify-path (path->complete-path (env-ref 'vostd))))
       (error 'confirm "~a is the environment's checkout; give a copy of it" copy))
     (make-directory* out)
     (define target (or (env-ref 'drops-target-dir #f) (string-append (env-ref 'target-dir) "-drops")))
     (dynamic-wind
      void
      (lambda () (run-confirm run-dir copy out o cands survivors sl proved-groups rerun modules calls-of rests target last-verified fns))
      (lambda () (restore copy)))]))

(define (run-confirm run-dir copy out o cands survivors sl proved-groups rerun modules calls-of rests target last-verified fns)
  (define (cand-f i) (norm-path (cadr (list-ref cands i))))
  ;; ---------------------------------------------------------------- alone
  (define alone ; id -> 'alone or (together-only KIND)
    (for/fold ([h (hash)]) ([s (in-list sl)] [k (in-naturals 1)])
      (define dir (o (format "alone-~a" k)))
      (make-directory* dir)
      (define cs (for/list ([i (in-list s)]) (list-ref cands i)))
      (define cf (build-path dir "cand.rktd"))
      (if (file-exists? cf)
          (unless (equal? (file->list cf) cs)
            (error 'confirm "~a has other candidates than provable's survivors now: remove ~a to start again" cf (o)))
          (write-forms cf cs))
      (unless (or (file-exists? (build-path dir "rounds.rktd")) (clean? copy))
        (error 'confirm "~a has changes in ostd/: give a clean copy" copy))
      (printf "slot ~a: ~a clauses\n" k (length s))
      ;; an error in a function that is no candidate's: the slot's clauses of the
      ;; functions it calls (slots keep related clauses apart for the same reason)
      (define (callers e)
        (define f (and (list-ref e 1) (list-ref e 2) (enclosing-function fns (list-ref e 1) (list-ref e 2))))
        (if f
            (for/list ([j (in-range (length s))] #:when (member (cand-f (list-ref s j)) (calls-of f))) j)
            '()))
      (define rounds (verify-rounds copy cs dir (lambda () (restore copy)) #:callers callers))
      (define bl (for*/hash ([r (in-list rounds)] #:when (eq? (car r) 'round)
                             [b (in-list (cddddr r))] [j (in-list (cdr b))])
                   (values (list-ref s j) (car b))))
      (for/fold ([h h]) ([i (in-list s)])
        (hash-set h i (match (hash-ref bl i #f)
                        [#f 'alone]
                        ;; the clause holds, but alone it makes a caller's existing proof fail
                        ['breaks-caller '(breaks-caller)]
                        [kind (list 'together-only kind)])))))
  ;; ---------------------------------------------------------------- clients
  (restore copy)
  (define patch (path->string (simplify-path (path->complete-path (build-path run-dir "provable" "survivors.patch")))))
  (parameterize ([current-directory copy])
    (unless (system* (git-program) "apply" patch)
      (error 'confirm "~a: cannot apply provable's survivors.patch" copy)))
  (define overlay (o "env.rktd"))
  (write-forms overlay `((vostd ,(path->string (simplify-path (path->complete-path copy)))) (target-dir ,target)))
  (define manifest (file->value (build-path run-dir "manifest.rktd")))
  (define cfg (read-config (cadr (assq 'config (cdr manifest)))))
  (for ([side (in-list '("before" "after"))])
    (for ([d (in-list '("tables" "clients" "results"))]) (make-directory* (o side d)))
    (write-forms (o side "manifest.rktd") (list manifest)))
  (define module-facts
    (for/list ([m (in-list modules)])
      (define names (hash-ref rerun m))
      (define (sel xs) (filter (lambda (x) (or (not (and (pair? x) (eq? (car x) 'client))) (memq (cadr x) names))) xs))
      (define clients (filter (lambda (c) (memq (cadr c) names)) (file->list (build-path run-dir "clients" (string-append m ".rktd")))))
      (define rm (string-append m ".rktd"))
      (for ([side (in-list '("before" "after"))])
        (copy-file (build-path run-dir "tables" rm) (o side "tables" rm) #t)
        (write-forms (o side "clients" rm) clients))
      ;; before: the run's own results of those clients
      (make-directory* (o "before" "results" m))
      (write-forms (o "before" "results" m "results.rktd") (sel (file->list (build-path run-dir "results" m "results.rktd"))))
      (write-forms (o "before" "results" m "plan.rktd") (sel (file->list (build-path run-dir "results" m "plan.rktd"))))
      ;; after: rerun with COPY as the checkout
      (define results
        (if (null? clients)
            '()
            (parameterize ([current-env-files (cons (simplify-path (path->complete-path overlay)) (env-files))])
              (printf "~a: rerunning ~a clients\n" m (length clients))
              (define tf (o "after" "tables" rm))
              (run-module (build-path (config-auto cfg) "targets" rm) tf (read-api-table tf)
                          (o "after" "clients" rm) clients (o "after" "results" m)))))
      (define (verified rs) (count (lambda (r) (and (pair? r) (eq? (car r) 'client) (eq? (caddr r) 'verified))) rs))
      (list m (length clients) (verified (file->list (o "before" "results" m "results.rktd"))) (verified results)
            (cond [(assq 'sanity results) => cadr] [else #f]))))
  (define (counts side)
    (for*/hash ([mod (in-list (group-failures (o side) #f))]
                [g (in-list (cddr mod))] #:when (and (pair? g) (eq? (car g) 'group)))
      ;; the group's clients, and those whose failure is attributed to each culprit
      (values (cons (cadr mod) (cadr g))
              (cons (cadr (assq 'clients (cddr g)))
                    (cond [(assq 'by (cddr g)) => (lambda (b) (for/hash ([p (in-list (cdr b))]) (values (car p) (cadr p))))]
                          [else (hash)])))))
  (define before (counts "before"))
  (define after (counts "after"))
  ;; ---------------------------------------------------------------- facts
  (define sane (for/hash ([mf (in-list module-facts)]) (values (car mf) (eq? (list-ref mf 4) 'ok))))
  (define clause-facts
    (for/list ([i (in-list survivors)])
      (define f (cand-f i))
      (define a (hash-ref alone i))
      (define needs (if (or (eq? a 'alone) (equal? a '(breaks-caller))) '()
                        (for/list ([j (in-list survivors)]
                                   #:unless (= j i)
                                   #:when (or (equal? (cand-f j) f) (member (cand-f j) (calls-of f))))
                          j)))
      (define rs (rests f))
      (define slot (for/first ([s (in-list sl)] [k (in-naturals 1)] #:when (memv i s)) k))
      `(clause ,i ,(string->symbol (list-ref (list-ref cands i) 2)) ,@(if (eq? a 'alone) '(alone) a) (slot ,slot)
               ,@(if (null? needs) '() `((needs ,@needs)))
               ,@(if (null? rs) (quote ()) `((rests-on ,@rs)))
               ,(list-ref (list-ref cands i) 7))))
  (define (after-results m)
    (let ([f (o "after" "results" m "results.rktd")]) (if (file-exists? f) (file->list f) '())))
  (define group-facts
    (for/list ([g (in-list proved-groups)] #:when (hash-has-key? sane (car g)))
      (match-define (list m key id f client at-id) g)
      ;; the failures F is the culprit of: a group's key is the clause, and the
      ;; same clause may fail after other calls too (write_val's after write_val)
      (define-values (bn bf) (let ([x (hash-ref before (cons m key) (cons 0 (hash)))]) (values (car x) (hash-ref (cdr x) f 0))))
      (define-values (an af) (let ([x (hash-ref after (cons m key) (cons 0 (hash)))]) (values (car x) (hash-ref (cdr x) f 0))))
      (define st (group-status bf af))
      ;; the very failure provable put in F's terms: gone after the change?
      (define at
        (match (for/first ([r (in-list (after-results m))] #:when (and (pair? r) (eq? (car r) 'client) (eq? (cadr r) client))) r)
          [#f 'not-run]
          [r (if (for/or ([e (in-list (cdddr r))]) (and (pair? e) (eq? (car e) 'error) (equal? (cadr e) at-id))) 'fails 'fixed)]))
      `(group ,m ,key ,id ,st (before ,bf) (after ,af) (clients ,bn ,an) (at ,client ,at-id ,at)
              ,(if (and id (eq? (hash-ref alone id #f) 'alone) (eq? at 'fixed) (hash-ref sane m #f))
                   'confirmed 'not-confirmed))))
  (define mod-facts
    (for/list ([mf (in-list module-facts)])
      (match-define (list m n vb va s) mf)
      (define new (sort (for/list ([k (in-hash-keys after)] #:when (and (equal? (car k) m) (not (hash-has-key? before k)))) (cdr k)) string<?))
      `(module ,m (clients ,n) (verified ,vb ,va) (sanity ,s) ,@(if (null? new) '() `((new ,@new))))))
  (define facts (append clause-facts group-facts mod-facts))
  (write-forms (o "facts.rktd") facts)
  (define (tally xs sel) (for/fold ([h (hash)]) ([x (in-list xs)]) (hash-update h (sel x) add1 0)))
  (define (show h) (string-join (for/list ([(k n) (in-hash h)]) (format "~a ~a" k n)) ", "))
  (printf "ostd with all of them: ~a verified, ~a errors (provable's last round)\n" (car last-verified) (cadr last-verified))
  (printf "clauses: ~a\n" (show (tally clause-facts (lambda (x) (cadddr x)))))
  (printf "clauses resting on trusted code: ~a\n" (count (lambda (x) (findf (lambda (y) (and (pair? y) (eq? (car y) 'rests-on))) x)) clause-facts))
  (printf "groups: ~a; ~a\n" (show (tally group-facts (lambda (x) (list-ref x 4))))
          (show (tally group-facts last)))
  facts)
