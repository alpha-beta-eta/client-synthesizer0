#lang racket/base
;; Does the culprit prove the fact it does not give? (docs/triage.md 5)
;;
;; For a group whose failure has a culprit F (attribute.rkt; groups.rkt's
;; (at CLIENT ID F)), the failed clause is written in F's terms and added to
;; F's ensures in a copy of the checkout, and ostd is verified (drops.rkt's
;; rounds: what Verus cannot prove is taken out, again, until a round
;; blames nothing).  A clause F proves once it is asked is a fact F has and
;; does not give its callers: the commonest confirmed defect (evaluation.md
;; 7.3, "the layer below has it, this one does not pass it up"), with the
;; change that fixes it.  One F cannot prove is not F's to give from what it
;; knows: the cause is below F (what F calls does not give it either), or the
;; clause is not one F's callers may have.
;;
;; The clause in F's terms: the client's variables at the positions of F's
;; call become F's parameters as F sees them when it returns: an argument
;; passed `&mut` is `final(p)` (`*final(p)` when the client passed `&mut x`),
;; one passed shared is `p` (`*p` for `&x`); the result is F's named result,
;; the ghost result F's `with` output (`x@` for a Tracked); the payload of
;; an if-let on the result, `ret->Ok_0` under `ret is Ok ==> (..)`; a
;; snapshot taken before the call of what is passed `&mut`, `old(p)`.  A
;; clause that reads anything else (a variable F was not given) is not F's
;; (inexpressible).  F that is trusted (external_body) is not tried: an
;; ensures there is an axiom.  Nor is a group whose clause was refuted
;; (refute.rkt) or whose failure is noise.
;;
;; RUN-DIR/provable/: cand.rktd (drops.rkt's candidate form), rounds.rktd,
;; verus-rN.out, survivors.patch (the proved clauses as `git diff`), and
;;   facts.rktd  (provable MODULE KEY CLIENT ID F STATUS [TEXT])
;;   STATUS = proved | unproved | compile | rlimit | other     (Verus, drops.rkt's blame)
;;          | inexpressible | no-ensures | trusted | no-source  (not tried)
;; groups.rkt reads facts.rktd: (proves F) on the group, which then comes first.
(require racket/file racket/list racket/match racket/string
         "../model/api.rkt" "../model/results.rkt" "../base/forms.rkt" "../base/env.rkt"
         "../analysis/attribute.rkt" "../vostd/git.rkt"
         (only-in "../gen/render.rkt" top->text)
         "groups.rkt" "drops.rkt")
(provide provable clause-in-callee unlabelled-group?)

;; clause-in-callee : table plan-form ID -> (values F TEXT-or-#f STATUS)
(define (clause-in-callee table form id)
  (define body (plan-body form))
  (define e (asserted-expr body id))
  (match (and e (culprit table form id))
    [(list f-name cid _)
     (define api (api-ref table f-name))
     ;; (source none): no source record (extract.rkt), as no source at all
     (define src (let ([s (and api (form-ref api 'source #f))]) (and (pair? s) (not (equal? s '(none))) s)))
     (define (s k) (cond [(and (pair? src) (assq k src)) => cdr] [else '()]))
     (define call (plan-stmt body cid))
     (cond
       [(not (and (pair? src) call)) (values f-name #f 'no-source)]
       [(member "external_body" (s 'attrs)) (values f-name #f 'trusted)]
       [(null? (s 'ensures)) (values f-name #f 'no-ensures)]
       [else
        (match-define `(call ,_ ,bind ,_ (args ,as ...) (gargs ,gs ...) ,rest ...) call)
        (define (pname p) (cadr p))
        (define (mut? p) (or (regexp-match? #px"^(Tracked<)?&\\s*(?:'[A-Za-z_]+\\s+)?mut\\b" (caddr p))
                             (and (> (length p) 3) (match (cadddr p) [`(ref ,_ mut) #t] [_ #f]))))
        (define terms (make-hasheq))
        (define (place! xs ps)
          (when (= (length xs) (length ps))
            (for ([a (in-list xs)] [p (in-list ps)])
              (match a
                [`(mutref ,(? symbol? v)) (hash-set! terms v (format "(*final(~a))" (pname p)))]
                [`(,(or 'same 'reref) ,(? symbol? v)) (hash-set! terms v (if (mut? p) (format "final(~a)" (pname p)) (pname p)))]
                [`(ref ,(? symbol? v)) (hash-set! terms v (format "(*~a)" (pname p)))]
                [_ (void)]))))
        (place! as (s 'params))
        (place! gs (s 'with-in))
        (define ret (match (s 'ret) [(list (? string? n) _ ...) n] [_ #f]))
        (when (and (symbol? bind) ret) (hash-set! terms bind ret))
        (match* ((assq 'gret rest) (s 'with-out))
          [(`(gret ,(? symbol? g)) (list (and o `(p ,(? string? n) ,(? string? t) ,_ ...))))
           (hash-set! terms g (if (string-prefix? t "Tracked<") (format "~a@" n) n))]
          [(_ _) (void)])
        ;; snapshots before the call of what F changes; payloads of if-lets on its result
        (define guards '())
        (let walk ([ss body])
          (for ([st (in-list ss)])
            (define sid (and (pair? st) (pair? (cdr st)) (cadr st)))
            (when (string? sid)
              (match st
                ;; vstd's unwrap of F's Option or Result, between the call and the failure
                [`(call ,uid ,(? symbol? x) ,(? (lambda (a) (memq a '(Option::tracked_unwrap Option::unwrap Result::unwrap))) u)
                        (args (,_ ,(? symbol? y))) ,_ ...)
                 #:when (and (id-before? cid uid) (id-before? uid id) (hash-ref terms y #f))
                 (define t (hash-ref terms y))
                 (define ctor (if (eq? u 'Result::unwrap) "Ok" "Some"))
                 (hash-set! terms x (format "~a->~a_0" t ctor))
                 (set! guards (cons (format "~a is ~a" t ctor) guards))]
                ;; a snapshot is of a value: `*v` of a `&mut` reference v (F's final(p)),
                ;; or a value v passed as `&mut v` (F's *final(p)); either is *old(p)
                [`(ghost ,gid ,x ,(and e (or `(deref ,(? symbol? v)) (? symbol? v))) ,_ ...)
                 #:when (id-before? gid cid)
                 (define t (hash-ref terms v #f))
                 (match (and t (regexp-match #px"^(\\(\\*)?final\\(([A-Za-z_][A-Za-z0-9_]*)\\)\\)?$" t))
                   [(list _ star p)
                    (when (if (pair? e) (not star) star)
                      (hash-set! terms x (format "(*old(~a))" p)))]
                   [_ (void)])]
                [`(if-let ,iid ,ctor ,x ,y (then ,tb ...) (else ,eb ...) ,more ...)
                 #:when (and (id-before? cid iid) (id-before? iid id) (eq? y bind) ret)
                 ;; the failure is in the then branch: its id is IID.N, the else's IID.eN
                 (define in-then? (regexp-match? (pregexp (string-append "^" (regexp-quote iid) "[.][0-9]")) id))
                 (cond
                   [in-then?
                    (hash-set! terms x (format "~a->~a_0" ret ctor))
                    (set! guards (cons (format "~a is ~a" ret ctor) guards))]
                   [else
                    (match (assq 'err more)
                      [`(err ,(? symbol? er)) (hash-set! terms er (format "~a->Err_0" ret))]
                      [_ (void)])
                    (set! guards (cons (format "~a is ~a" ret (if (eq? ctor 'Ok) "Err" "None")) guards))])
                 (walk tb) (walk eb)]
                [`(if-let ,_ ,_ ,_ ,_ (then ,tb ...) (else ,eb ...) ,_ ...) (walk tb) (walk eb)]
                [`(if ,_ ,_ (then ,tb ...) (else ,eb ...)) (walk tb) (walk eb)]
                [`(if-not ,_ ,_ ,inner ...) (walk inner)]
                [`(repeat ,_ ,_ ,_ ,inner ...) (walk inner)]
                [_ (void)]))))
        (define vars (expr-vars e))
        (cond
          [(not (andmap (lambda (v) (hash-ref terms v #f)) vars)) (values f-name #f 'inexpressible)]
          [else
           (define text0
             ;; as it stands alone (a template without its parentheses, render.rkt), so
             ;; that a claim and a requires asking the same thing are one candidate
             (top->text (let subst ([x e])
                           (cond [(and (symbol? x) (hash-ref terms x #f)) => (lambda (t) `(src ,t))]
                                 [(pair? x) (cons (subst (car x)) (subst (cdr x)))]
                                 [else x]))))
           ;; guards outermost
           (values f-name
                   (for/fold ([t text0]) ([g (in-list guards)]) (format "~a ==> (~a)" g t))
                   'expressed)])])]
    [_ (values #f #f 'no-culprit)]))

;; provable : run-dir copy [module-regex] [#:dry? B] [#:unlabelled (KNOWLEDGE-DIR ISSUES-DIR VERDICTS-DIR)] -> facts
;; dry?: the groups tried and their clauses in F's terms, nothing verified
;; unlabelled: only the groups `groups` shows with no label (or a stale
;; verdict only, which is to be judged again), with these directories: the
;; new failures of a run, without trying again what is judged or known
(define (unlabelled-group? g)
  (null? (filter (lambda (l) (not (eq? (car l) 'stale-verdict))) (cdr (assq 'labels (cddr g))))))
(define (provable run-dir copy [only #rx""] #:dry? [dry? #f] #:unlabelled [ul #f])
  (define vostd (env-ref 'vostd))
  (define out (build-path run-dir "provable"))
  (define commit (cadr (assq 'commit (cdr (file->value (build-path run-dir "manifest.rktd"))))))
  (unless dry?
    (when (equal? (simplify-path (path->complete-path copy)) (simplify-path (path->complete-path vostd)))
      (error 'provable "~a is the environment's checkout; give a copy of it" copy))
    (unless (string-prefix? (git-head copy) commit)
      (error 'provable "~a is at ~a, the run at ~a" copy (git-head copy) commit))
    (make-directory* out)
    (unless (or (file-exists? (build-path out "rounds.rktd")) (clean? copy))
      (error 'provable "~a has changes in ostd/: give a clean copy" copy)))
  ;; (M KEY CLIENT ID F STATUS TEXT): every group tried, cand ids by (F . TEXT)
  (define tried
    (for*/list ([mod (in-list (if ul
                                  (group-failures run-dir (car ul) only (cadr ul) #:verdicts (caddr ul))
                                  (group-failures run-dir #f only)))]
                [m (in-value (cadr mod))]
                [table (in-value (read-api-table (build-path run-dir "tables" (string-append m ".rktd"))))]
                [plan (in-value (let ([f (build-path run-dir "results" m "plan.rktd")]) (if (file-exists? f) (file->list f) '())))]
                [g (in-list (cddr mod))]
                #:when (and (pair? g) (eq? (car g) 'group))
                #:when (or (not ul) (unlabelled-group? g))
                [labels (in-value (cdr (assq 'labels (cddr g))))]
                #:unless (assoc 'noise labels)
                #:unless (equal? (assq 'refute (cddr g)) '(refute refuted)))
      (match-define `(at ,client ,id ,_ ...) (assq 'at (cddr g)))
      (define form (plan-of plan client))
      (define-values (f text status) (if form (clause-in-callee table form id) (values #f #f 'no-culprit)))
      (define fpath (and f (let ([a (api-ref table f)]) (and a (let ([v (form-ref a 'vir-path #f)]) (and v (car v)))))))
      (define last-span (and text (let* ([a (api-ref table f)] [src (form-ref a 'source)] [ens (cdr (assq 'ensures src))])
                                    (cadr (last ens)))))
      (list m (cadr g) client id f status text fpath last-span)))
  (define expressed (filter (lambda (t) (eq? (list-ref t 5) 'expressed)) tried))
  (define cand-keys (remove-duplicates (for/list ([t (in-list expressed)]) (cons (list-ref t 4) (list-ref t 6)))))
  (define cands
    (for/list ([k (in-list cand-keys)])
      (define t (findf (lambda (t) (equal? (cons (list-ref t 4) (list-ref t 6)) k)) expressed))
      (define span (list-ref t 8))
      (define file (car (regexp-match #px"^[^:]+" span)))
      `(cand ,(or (list-ref t 7) (format "~a" (car k))) ,(format "~a" (car k)) ,file ,span
             ,(format "triage ~a ~a" (list-ref t 0) (list-ref t 1)) "" ,(cdr k) ,(cdr k))))
  (when dry?
    (for ([t (in-list tried)])
      (match-define (list m key client id f status text _ _) t)
      (writeln `(provable ,m ,key ,client ,id ,f ,status ,@(if text (list text) '())))))
  (if dry? tried (verify-and-report out tried cand-keys cands copy)))

(define (verify-and-report out tried cand-keys cands copy)
  (unless (file-exists? (build-path out "cand.rktd"))
    (with-output-to-file (build-path out "cand.rktd") (lambda () (for ([c (in-list cands)]) (writeln c)))))
  (define cands-now (file->list (build-path out "cand.rktd")))
  (unless (equal? cands-now cands)
    (error 'provable "~a has other candidates than the groups give now: remove the directory to start again" out))
  (printf "~a groups tried, ~a candidates\n" (length tried) (length cands))
  (define rounds (if (null? cands) '() (verify-rounds copy cands out (lambda () (restore copy)))))
  (define blamed (for*/hash ([r (in-list rounds)] #:when (eq? (car r) 'round)
                             [b (in-list (cddddr r))] [i (in-list (cdr b))])
                   (values i (car b))))
  (define facts
    (for/list ([t (in-list tried)])
      (match-define (list m key client id f status text _ _) t)
      (define st (if (eq? status 'expressed)
                     (hash-ref blamed (index-of cand-keys (cons f text)) 'proved)
                     status))
      `(provable ,m ,key ,client ,id ,f ,st ,@(if text (list text) '()))))
  (with-output-to-file (build-path out "facts.rktd") #:exists 'truncate
    (lambda () (for ([x (in-list facts)]) (writeln x))))
  (define tally (for/fold ([h (hash)]) ([x (in-list facts)]) (hash-update h (list-ref x 6) add1 0)))
  (printf "~a\n" (string-join (for/list ([(k n) (in-hash tally)]) (format "~a ~a" k n)) ", "))
  facts)
