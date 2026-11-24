#lang racket/base
;; Grouping the failures of an evaluation (evaluate.rkt) by clause, and
;; labelling the groups with call knowledge (design.md 3.9, evaluation.md 7.2).
;;
;; Every failed client's failing clauses (the vacuity assertions, the "may
;; panic" clauses `P ==> may_panic()` (results.rkt: panic-error?) and resource-limit timeouts, which are
;; not judged, left out; the timeouts are counted), with variable names such
;; as v0, x1, o2 blanked so that the same clause in different clients is one
;; group.  A group is labelled with the limitation, not-defect, prefer and
;; assume entries about the API whose requires failed (or the two APIs of a
;; failed relation): only those, since entries about any API the client calls
;; label almost everything and hide the candidates.  A label is a hypothesis
;; to check, not a verdict.  Unlabelled groups are the candidates.
;;
;; Two more hypotheses, to read a run in the right order (time-sinks.md B1):
;; - After a failed assertion Verus assumes it, so a failure after another one
;;   on the same path of a client may only follow from it (a function that
;;   drops a fact fails every call after it).  (first N): in how many of the
;;   group's clients the clause fails with no counted failure before it on
;;   its path; (after (TEXT N) ..): the clauses that failed before it in the
;;   others, the most frequent first.  A group with (first 0) is to be read
;;   after the groups it comes after.
;; - (issue ID) labels: the known issues (issues.rkt) of the module one of
;;   whose witnesses' (fails ..) patterns matches an error of the group.
(require racket/file racket/list racket/match racket/string "../model/knowledge.rkt" "../model/results.rkt" "../model/api.rkt"
         (only-in "../gen/families/goal-shapes.rkt" tied-clauses)
         "../model/issues.rkt" "../model/verdicts.rkt" "../analysis/attribute.rkt")
(provide group-failures id-before? plan-calls run-digest-file record-verdict)

;; record-verdict : run-dir module key judgement reason file [#:issue ID] [#:by? B] -> form
;; Appends a verdict on the group KEY of module M of the run to FILE, with
;; what is mechanical filled in: the culprit (unless by? is #f), the
;; fingerprints of the key's APIs and the culprit at the run's commit, the commit.
(define (record-verdict run-dir m key j reason file #:issue [issue #f] #:by? [by? #t] #:digests [dfile #f])
  (define mod (findf (lambda (x) (equal? (cadr x) m)) (group-failures run-dir #f (pregexp (string-append "^" (regexp-quote m) "$")))))
  (define g (and mod (findf (lambda (g) (and (pair? g) (eq? (car g) 'group) (equal? (cadr g) key))) (cddr mod))))
  (unless g (error 'verdict "no group ~s in ~a of ~a" key m run-dir))
  ;; the culprit of the group's (at CLIENT ID CULPRIT): the failure judged
  (define by (and by? (match (assq 'at (cddr g)) [`(at ,_ ,_ ,c) c] [_ #f])))
  (define digests (read-digest-file (or dfile (run-digest-file run-dir) (error 'verdict "no fingerprints for the run's commit"))))
  (define apis (remove-duplicates (append (key-apis key) (if by (list by) '()))))
  (define commit (cadr (assq 'commit (cdr (file->value (build-path run-dir "manifest.rktd"))))))
  (define form
    `(verdict (group ,key) (module ,m) ,@(if by `((by ,by)) '())
              (judgement ,j) ,@(if issue `((issue ,issue)) '())
              (reason ,reason)
              (specs ,@(for/list ([a (in-list apis)] #:when (hash-ref digests a #f)) (list a (hash-ref digests a))))
              (at ,commit)))
  (write-verdict file form)
  form)

;; run-digest-file : run-dir -> path or #f, the fingerprints of the run's
;; commit: <auto>/digests/<commit>.rktd, auto from its configuration
(define (run-digest-file run-dir)
  (define mf (build-path run-dir "manifest.rktd"))
  (and (file-exists? mf)
       (let* ([m (cdr (file->value mf))]
              [commit (cadr (assq 'commit m))]
              [cfg (cadr (assq 'config m))])
         (and (file-exists? cfg)
              (let* ([ev (file->value cfg)]
                     [auto (match (assq 'auto (cdr ev)) [`(auto ,a) a] [_ #f])]
                     ;; absolute in the configurations `fixes` writes for its after/ runs
                     [dir (and auto (if (absolute-path? auto)
                                        (simplify-path auto)
                                        (let-values ([(base _n _d) (split-path cfg)]) (simplify-path (build-path base auto)))))]
                     [f (and dir (build-path dir "digests" (string-append commit ".rktd")))])
                (and f (file-exists? f) f))))))

;; The APIs a client calls, in order: in a client form, (call API ..); in an
;; elaborated one (plan.rktd), (call ID X API ..); the first symbol naming a
;; path.
(define (calls-in form)
  ;; the elements of a list, also of an improper one (substitutions (M . M))
  (define (elems x) (cond [(pair? x) (cons (car x) (elems (cdr x)))] [else '()]))
  (let walk ([x form])
    (cond
      [(and (pair? x) (eq? (car x) 'call))
       (define api (for/first ([y (in-list (elems (cdr x)))]
                               #:when (and (symbol? y) (regexp-match? #rx"::" (symbol->string y))))
                     y))
       (append (if api (list api) '()) (append-map walk (filter pair? (elems (cdr x)))))]
      [(pair? x) (append-map walk (filter pair? (elems x)))]
      [else '()])))

;; plan-calls : elaborated client (plan.rktd) -> ((ID API . POSITIONS) ...)
;; Its calls, each with the variables in its positions (issues.rkt:
;; fact-key): #aI the Ith argument, #gI the Ith ghost argument, #r the
;; result, #gr the ghost result.  An argument that is not a variable (a spec
;; expression, none) has no variable.
(define (plan-calls form)
  ;; the elements of a list, also of an improper one (substitutions (M . M))
  (define (elems x) (if (pair? x) (cons (car x) (elems (cdr x))) '()))
  (define (subforms x) (for/list ([y (in-list (elems x))] #:when (pair? y)) y))
  (let walk ([x form])
    (match x
      [`(call ,(? string? id) ,res ,(? symbol? api) (args ,as ...) (gargs ,gs ...) ,rest ...)
       (define pos (make-hasheq))
       (for ([a (in-list as)] [i (in-naturals)])
         (match a [`(,(not 'spec) ,(? symbol? v)) (hash-set! pos v (format "#a~a" i))] [_ (void)]))
       (for ([g (in-list gs)] [i (in-naturals)])
         (match g [`(,(not 'spec) ,(? symbol? v)) (hash-set! pos v (format "#g~a" i))] [_ (void)]))
       (when (symbol? res) (hash-set! pos res "#r"))
       (match (assq 'gret rest) [`(gret ,(? symbol? g)) (hash-set! pos g "#gr")] [_ (void)])
       (cons (list* id api pos) (append-map walk (subforms rest)))]
      [(? pair?) (append-map walk (subforms x))]
      [_ '()])))

;; An opaque requires (`clone_requires`) is grouped by the conjuncts that failed
;; inside it (Verus's expansion, results.rkt), the `may_panic()` ones left out.
(define (clause e)
  (define t (assq 'text (cddddr e)))
  (define inside (remove-duplicates (map cadr (filter (lambda (l) (not (panic-leaf? l))) (error-expanded e)))))
  (regexp-replace* #rx"\\b([vxo]|in|g)[0-9]+\\b"
                   (string-append (if t (cadr t) (cadddr e))
                                  ;; the first few: a deep expansion would make every group its own
                                  (cond [(null? inside) ""]
                                        [(> (length inside) 4) (format "  [fails at: ~a; ..]" (string-join (take inside 4) "; "))]
                                        [else (format "  [fails at: ~a]" (string-join inside "; "))]))
                   "_"))

;; claim-statuses : results -> ((claims (STATUS N) ... [(STATUS NAME ...)] ...)) or ()
;; The claims (time-sinks.md B5) apart by how they ended: a claim that does
;; not compile or is ill-formed was written wrong (or names what the client
;; cannot see, design.md 5.4); a vacuous one says nothing; only the failed
;; ones are in the groups.  The names of the first three are listed.
(define (claim-statuses results)
  (define cs (for/list ([r (in-list results)]
                        #:when (and (pair? r) (eq? (car r) 'client) (regexp-match? #rx"^claim_" (symbol->string (cadr r)))))
               (cons (cadr r) (if (and (eq? (result-status r) 'verified) (pair? (result-vacuous r)))
                                  'vacuous
                                  (result-status r)))))
  (define kinds '(verified failed vacuous compile-error ill-formed not-verified))
  (define (of k) (for/list ([c (in-list cs)] #:when (eq? (cdr c) k)) (car c)))
  (if (null? cs)
      '()
      `((claims ,@(for/list ([k (in-list kinds)] #:when (pair? (of k))) (list k (length (of k))))
                ,@(for/list ([k (in-list '(compile-error ill-formed vacuous))] #:when (pair? (of k))) (cons k (of k)))))))

;; group-failures : run-dir knowledge-dir-or-#f module-regex [issues-dir-or-#f]
;;   -> ((module M (timeouts N)
;;        (group TEXT (clients N) (first N) [(after (TEXT N) ...)] (example NAME) (labels (KIND API-or-ID) ...)) ...) ...)
;; Groups are ordered: unlabelled first, then those whose clause fails first
;; in more clients, then by size.
(define (group-failures run-dir kdir [only #rx""] [idir #f] #:verdicts [vdir #f] #:digests [dfile #f] #:members? [members? #f])
  (define results-dir (build-path run-dir "results"))
  (define issues (if idir (read-issues idir) '()))
  (define verdicts (if vdir (read-verdicts vdir) '()))
  (define digests
    (cond [(null? verdicts) (hash)]
          [(or dfile (run-digest-file run-dir)) => read-digest-file]
          [else (error 'groups "no fingerprints for the run's commit (give --digests FILE)")]))
  (for/list ([m (in-list (sort (map path->string (directory-list results-dir)) string<?))]
             #:when (and (regexp-match? only m) (file-exists? (build-path results-dir m "results.rktd"))))
    (define k (if kdir (read-knowledge (build-path kdir (string-append m ".rktd"))) '()))
    (define labels (filter (lambda (e) (memq (car e) '(limitation not-defect prefer assume))) k))
    ;; (ID SUBJECT . FAILS): a witness's patterns say where the witness fails,
    ;; not what the issue looks like elsewhere (`[.]inv[(][)]`), so a failure
    ;; counts for the issue only in a client that also calls the subject, the
    ;; witness's first call (the producer whose spec is at fault)
    (define known
      (for*/list ([i (in-list issues)] [w (in-list (issue-witnesses i))]
                  #:when (equal? (witness-module w) m)
                  [s (in-value (let ([cs (calls-in (witness-client w))]) (and (pair? cs) (car cs))))]
                  #:when s)
        (list* (issue-id i) s (witness-fails w))))
    ;; (ID API KEY): the facts of every module's claim witnesses, since a
    ;; subject's fact is needed wherever it is called
    (define facts
      (for*/list ([i (in-list issues)] [w (in-list (issue-witnesses i))]
                  [f (in-value (witness-fact w))] #:when f)
        (cons (issue-id i) f)))
    (define plans
      (let ([f (build-path results-dir m "plan.rktd")])
        (if (file-exists? f)
            (for/hash ([c (in-list (file->list f))] #:when (and (pair? c) (eq? (car c) 'client)))
              (values (cadr c) c))
            (hash))))
    (define calls-of (for/hash ([(n c) (in-hash plans)]) (values n (calls-in c))))
    ;; fact-issues : client-name error -> (ID ...), the issues whose fact
    ;; (issues.rkt: witness-fact) is what the failed assertion asks for after
    ;; a call of the issue's subject on the same path, in that call's positions
    (define (fact-issues n e)
      (define asserted (match (regexp-match #px"^assert\\((.*)\\);(?:\\s*//.*)?$" (error-text e))
                         [(list _ t) t] [_ #f]))
      (define form (hash-ref plans n #f))
      (if (not (and asserted form (pair? facts)))
          '()
          (remove-duplicates
           (for*/list ([c (in-list (plan-calls form))]
                       #:when (id-before? (car c) (cadr e))
                       [f (in-list facts)]
                       #:when (eq? (cadr f) (cadr c))
                       #:when (equal? (fact-key asserted (cddr c)) (caddr f)))
             (car f)))))
    ;; the clients and the table, for the noise check (goal.rkt's tied-clauses)
    (define clients-of
      (let ([f (build-path run-dir "clients" (string-append m ".rktd"))])
        (if (file-exists? f) (for/hash ([c (in-list (file->list f))]) (values (cadr c) c)) (hash))))
    (define table
      (let ([f (build-path run-dir "tables" (string-append m ".rktd"))])
        (and (file-exists? f) (with-handlers ([exn:fail? (lambda (_) #f)]) (read-api-table f)))))
    (define (tied? n e)
      (define c (hash-ref clients-of n #f))
      (define api (regexp-match #px"// requires of (\\S+)" (error-text e)))
      (define k (regexp-match #px"/([0-9]+)$" (or (error-id e) "")))
      (and c table api k
           (let ([g (api-ref table (string->symbol (cadr api)))])
             (and g (memv (string->number (cadr k)) (tied-clauses c g)) #t))))
    ;; group-key : client-name error -> key, the group a failure belongs to
    ;; (docs/enumeration.md 7.8): a requires clause by its identity (the callee
    ;; and the clause's number), not its text, which differs with the client's
    ;; variables (goal's self_g, chain's x0); a failure after an error (goal's
    ;; after-err clients) by the call that failed; the rest (claims,
    ;; relations) by their text with variables blanked.
    (define (group-key n e)
      (define api (regexp-match #px"// requires of (\\S+)" (error-text e)))
      (define k (regexp-match #px"/([0-9]+)$" (or (error-id e) "")))
      (define err-of (regexp-match #rx"^goal_err_" (symbol->string n)))
      (cond
        [(and err-of api k)
         (define c (hash-ref clients-of n #f))
         (define h (and c (let ([cs (calls-in c)]) (and (pair? cs) (car cs)))))
         (format "after an error of ~a" (or h "?"))]
        [(and api k) (format "requires of ~a /~a" (cadr api) (cadr k))]
        [else (clause e)]))
    (define texts (make-hash))    ; key -> an example of the failing clause's text
    (define tied-count (make-hash)) ; key -> clients where the clause ties a fresh parameter to a produced value
    (define members (make-hash))  ; key -> (requires-identity ...), for the after-an-error groups
    (define groups (make-hash))   ; key -> (client ...)
    (define firsts (make-hash))   ; text -> (client ...), where it fails first on its path
    (define afters (make-hash))   ; text -> hash: earlier text -> count
    (define issue-labels (make-hash)) ; text -> (ID ...)
    (define ats (make-hash))      ; key -> (client id first?), the failure a probe negates
    (define bys (make-hash))      ; key -> hash: culprit API or entry -> clients (attribute.rkt)
    (define (culprit-of n e)
      (define form (hash-ref plans n #f))
      (and form table
           (match (culprit table form (cadr e))
             [(list api _ _) api]
             [c c])))
    ;; the refutation probes of the run (refute.rkt): (client ID) -> refuted | open | ..
    (define refuted
      (let ([f (build-path run-dir "refute" (string-append m ".rktd"))])
        (if (file-exists? f)
            (for/hash ([r (in-list (file->list f))] #:when (and (pair? r) (eq? (car r) 'refute)))
              (values (list (cadr r) (caddr r)) (cadddr r)))
            (hash))))
    ;; provable.rkt's results: key -> (STATUS F [TEXT])
    (define provables
      (let ([f (build-path run-dir "provable" "facts.rktd")])
        (if (file-exists? f)
            (for/hash ([x (in-list (file->list f))] #:when (and (pair? x) (eq? (car x) 'provable) (equal? (cadr x) m)))
              (match-define `(provable ,_ ,key ,_ ,_ ,fn ,st ,text ...) x)
              (values key (list* st fn text)))
            (hash))))
    (define timeouts 0)
    (for ([r (in-list (file->list (build-path results-dir m "results.rktd")))]
          #:when (and (eq? (car r) 'client) (eq? (caddr r) 'failed)))
      (define errs (for/list ([e (in-list (cdddr r))] #:when (and (pair? e) (eq? (car e) 'error))) e))
      (define-values (limits rest)
        (partition (lambda (e) (regexp-match? #rx"rlimit|resource limit|timed out" (cadddr e))) errs))
      (unless (null? limits) (set! timeouts (add1 timeouts)))
      (define counted
        (for/list ([e (in-list rest)]
                   #:unless (panic-error? e)
                   #:unless (regexp-match? #rx"vacuity" (clause e)))
          e))
      (define n (cadr r))
      (for ([e (in-list counted)])
        (define text (group-key n e))
        (hash-ref! texts text (lambda () (clause e)))
        (when (regexp-match? #rx"^after an error of " text)
          (define id (let ([api (regexp-match #px"// requires of (\\S+)" (error-text e))]
                           [k (regexp-match #px"/([0-9]+)$" (or (error-id e) ""))])
                       (format "~a /~a" (cadr api) (cadr k))))
          (hash-update! members text (lambda (l) (if (member id l) l (append l (list id)))) '()))
        (define earlier (filter (lambda (e2) (and (not (eq? e2 e)) (id-before? (cadr e2) (cadr e)))) counted))
        (unless (member n (hash-ref groups text '()))
          (when (tied? n e) (hash-update! tied-count text add1 0))
          (let ([c (culprit-of n e)])
            (when c (hash-update! (hash-ref! bys text (lambda () (make-hash))) c add1 0)))
          (hash-update! groups text (lambda (g) (cons n g)) '()))
        ;; the failure to probe for the group (refute.rkt): one where it fails first
        (when (or (not (hash-ref ats text #f)) (and (null? earlier) (not (caddr (hash-ref ats text)))))
          (hash-set! ats text (list n (cadr e) (null? earlier))))
        (cond
          [(null? earlier)
           (unless (member n (hash-ref firsts text '()))
             (hash-update! firsts text (lambda (g) (cons n g)) '()))]
          [else
           ;; the first failure on the path is what it may follow from
           (define root (for/fold ([a (car earlier)]) ([e2 (in-list (cdr earlier))])
                          (if (id-before? (cadr e2) (cadr a)) e2 a)))
           (define h (hash-ref! afters text (lambda () (make-hash))))
           (hash-update! h (group-key n root) add1 0)])
        (for ([id (in-list (append (for/list ([kn (in-list known)]
                                              #:when (and (memq (cadr kn) (hash-ref calls-of n '()))
                                                          (error-matches? e (cddr kn))))
                                     (car kn))
                                   (fact-issues n e)))])
          (hash-update! issue-labels text (lambda (ids) (if (memq id ids) ids (cons id ids))) '()))))
    (define (labels-of key)
      (define text (hash-ref texts key key))
      (define about
        (match (regexp-match #rx"// (requires of|relation) (.*)$" text)
          [(list _ _ rest) (map string->symbol (regexp-split #rx", " rest))]
          [_ '()]))
      (remove-duplicates (for/list ([l (in-list labels)] #:when (memq (cadr l) about)) (list (car l) (cadr l)))))
    (define gs
      (for/list ([(text clients) (in-hash groups)])
        (define after
          (let ([h (hash-ref afters text #f)])
            (if h
                (let ([ps (sort (hash->list h) > #:key cdr)])
                  `((after ,@(for/list ([p (in-list (take ps (min 3 (length ps))))]) (list (car p) (cdr p))))))
                '())))
        (define tied (hash-ref tied-count text 0))
        (define at (hash-ref ats text))
        (define probe (hash-ref refuted (list (car at) (cadr at)) #f))
        ;; the culprit in the client a judge reads and the probe negates: a verdict
        ;; is on that failure
        (define at-culprit
          (let ([form (hash-ref plans (car at) #f)])
            (and form table (match (culprit table form (cadr at)) [(list api _ _) api] [_ #f]))))
        (define v (and (pair? verdicts) (verdict-for verdicts m text at-culprit)))
        `(group ,text
                ,@(if (equal? (hash-ref texts text text) text) '() `((text ,(hash-ref texts text))))
                ,@(let ([ms (hash-ref members text '())]) (if (null? ms) '() `((clauses ,@ms))))
                (clients ,(length clients)) (first ,(length (hash-ref firsts text '()))) ,@after
                ;; the clients themselves, on request (fixes.rkt counts a group by its members)
                ,@(if members? `((members ,@(reverse clients))) '())
                ,@(if (> tied 0) `((tied ,tied)) '())
                ;; the calls that should have given the fact, by clients (attribute.rkt)
                ,@(let ([h (hash-ref bys text #f)])
                    (if h `((by ,@(for/list ([p (in-list (sort (hash->list h) > #:key cdr))]) (list (car p) (cdr p))))) '()))
                (example ,(last clients))
                (at ,(car at) ,(cadr at) ,@(if at-culprit (list at-culprit) '()))
                ,@(if probe `((refute ,probe)) '())
                ;; the culprit proves the clause once it is asked (provable.rkt): a fact it
                ;; has and does not give, with the clause to add
                ,@(match (hash-ref provables text #f)
                    [`(proved ,fn ,t) `((proves ,fn ,t))]
                    [`(,st ,fn ,_ ...) #:when fn `((provable ,st ,fn))]
                    [_ '()])
                (labels ,@(labels-of text)
                        ;; judged in an earlier round (verdicts.rkt): stale when a spec it read changed
                        ,@(if v
                              `((,(if (eq? (verdict-status v digests) 'current) 'verdict 'stale-verdict)
                                 ,(verdict-judgement v) ,@(if (verdict-issue v) (list (verdict-issue v)) '())))
                              '())
                        ;; the clause is false wherever it is asked (refute.rkt): the
                        ;; client's use is not legal, or the callee's spec says the opposite
                        ,@(if (eq? probe 'refuted) '((refuted)) '())
                        ;; every client's clause ties a fresh parameter to a produced value: noise
                        ,@(if (= tied (length clients)) '((noise tied)) '())
                        ,@(for/list ([id (in-list (reverse (hash-ref issue-labels text '())))]) (list 'issue id))))))
    ;; the culprits of the module: for each call, the groups and clients it is
    ;; the culprit in (the most frequent culprit of a group counts for it)
    (define culprits
      (let ([h (make-hash)])
        (for ([(key ch) (in-hash bys)])
          (define top (car (sort (hash->list ch) > #:key cdr)))
          (hash-update! h (car top) (lambda (gc) (list (add1 (car gc)) (+ (cadr gc) (cdr top)))) '(0 0)))
        (for/list ([p (in-list (sort (hash->list h) > #:key cadr))] #:unless (eq? (car p) 'entry))
          `(,(car p) (groups ,(cadr p)) (clients ,(caddr p))))))
    `(module ,m
       (timeouts ,timeouts)
       ,@(claim-statuses (file->list (build-path results-dir m "results.rktd")))
       ,@(if (null? culprits) '() `((culprits ,@culprits)))
       ,@(sort gs (lambda (a b)
                    ;; a proved fact the culprit does not give first; a stale verdict is
                    ;; to be judged again: as if unlabelled
                    (define (key g) (list (if (assq 'proves (cddr g)) 0 1)
                                          (if (null? (filter (lambda (l) (not (eq? (car l) 'stale-verdict))) (cdr (assq 'labels (cddr g))))) 0 1)
                                          (- (cadr (assq 'first (cddr g))))
                                          (- (cadr (assq 'clients (cddr g))))))
                    (let loop ([ka (key a)] [kb (key b)])
                      (cond [(null? ka) #f]
                            [(< (car ka) (car kb)) #t]
                            [(> (car ka) (car kb)) #f]
                            [else (loop (cdr ka) (cdr kb))])))))))
