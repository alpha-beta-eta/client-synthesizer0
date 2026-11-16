#lang racket/base
;; Known issues as data (design.md 3.11): each issue, the clients that show
;; it (its witnesses) and where they are to fail.  Whether the issue is real
;; is a judgement recorded elsewhere; this only says how to see it again.
;;
;; A file (data/issues/*.rktd) is a sequence of
;;   (issue ID                      a symbol (D3, old-20)
;;     (title STRING)
;;     [(judgement J)]              confirmed (default) | candidate | decision
;;     [(source STRING ...)]        where it is recorded (record.md D3, report #20)
;;     [(fix STRING ...)]           the patches that fix it
;;     (witness (module M)          the module the client runs in ("mm.frame.segment")
;;              (fails F ...)       an error of the client matches one of them: F is
;;                                  (requires API N) (the Nth
;;                                  requires clause of API, as the client asserts it),
;;                                  or (claim) (the claim's assertion)
;;              (client NAME ...))  the client itself
;;     ...
;;     [(no-witness STRING)])       why it has no witness that can run
;;
;; witness-status : witness results -> status
;;   shows | passes | other (fails elsewhere) | vacuous | broken | not-run | not-concluded
;; original-status : (status ...) -> present | gone | undetected | no-witness
;; patched-status  : (status ...) -> fixed | not-fixed | undetected | no-witness
(require racket/list racket/match racket/file racket/string "results.rkt")
(provide (struct-out issue) (struct-out witness)
         read-issues issue-files witness-status error-matches? original-status patched-status
         first-judged-error witness-fact fact-key)

(struct issue (id title judgement sources fixes witnesses no-witness file) #:transparent)
(struct witness (module fails client) #:transparent)

(define (issue-files dir)
  (for/list ([f (in-list (sort (map path->string (directory-list dir)) string<?))]
             #:when (regexp-match? #rx"[.]rktd$" f))
    (build-path dir f)))

;; read-issues : dir-or-file -> (issue ...)
(define (read-issues where)
  (define files (if (directory-exists? where) (issue-files where) (list where)))
  (define all (append* (for/list ([f (in-list files)]) (map (lambda (x) (parse-issue x f)) (file->list f)))))
  (define dup (check-duplicates (map issue-id all)))
  (when dup (error 'issues "issue ~a is given twice" dup))
  all)

(define (parse-issue form file)
  (define (bad fmt . args) (error 'issues "~a: ~a" file (apply format fmt args)))
  (match form
    [`(issue ,(? symbol? id) ,items ...)
     (define (one key [default #f])
       (match (assq key items) [`(,_ ,v) v] [#f default] [x (bad "~a: ~s" id x)]))
     (define (many key) (match (assq key items) [`(,_ ,(? string? v) ...) v] [#f '()] [x (bad "~a: ~s" id x)]))
     (for ([i (in-list items)])
       (unless (and (pair? i) (memq (car i) '(title judgement source fix witness no-witness)))
         (bad "~a: unknown item ~s" id i)))
     (define title (one 'title))
     (unless (string? title) (bad "~a: no (title STRING)" id))
     (define j (one 'judgement 'confirmed))
     (unless (memq j '(confirmed candidate decision)) (bad "~a: judgement ~s" id j))
     ;; an expectation over the rendered text (a string, the earlier tool's) is
     ;; not used: it broke whenever the rendering changed (time-sinks C16); a
     ;; witness with no other expectation is left out and said so
     (define-values (ws text-only)
       (for/fold ([ws '()] [text-only 0] #:result (values (reverse ws) text-only))
                 ([w (in-list items)] #:when (eq? (car w) 'witness))
         (match w
           [`(witness (module ,(? string? m)) (fails ,(? fails-item? fs) ..1) ,(and c `(client ,(? symbol?) ,_ ...)))
            (define ids (filter pair? fs))
            (if (null? ids)
                (values ws (add1 text-only))
                (values (cons (witness m ids c) ws) text-only))]
           [_ (bad "~a: a witness is (witness (module M) (fails (requires API N)|(claim) ...) (client NAME ...)): ~s" id w)])))
     (define nw (or (one 'no-witness)
                    (and (null? ws) (> text-only 0)
                         (format "~a witness(es) expect a text, not a clause: re-express as (requires API N) or (claim)" text-only))))
     (when (and (null? ws) (not (string? nw)))
       (bad "~a: no witness and no (no-witness REASON)" id))
     (issue id title j (many 'source) (many 'fix) ws nw file)]
    [_ (bad "not an issue: ~s" form)]))

;; An expectation is a clause by its identity, which does not depend on how
;; the clause is written (design.md 3.11): (requires API N), the Nth requires
;; clause of API where the client asserts it (its id ends "/N", its line says
;; "requires of API"); (claim), the claim's assertion.  A string (a regular
;; expression over the texts, the earlier tool's) is read but not used.
(define (fails-item? f)
  (match f
    [(? string?) #t]
    [`(requires ,(? symbol?) ,(? exact-positive-integer?)) #t]
    ['(claim) #t]
    [_ #f]))
(define (error-matches? e expectations)
  (for/or ([x (in-list expectations)])
    (match x
      [`(requires ,api ,n)
       (and (string? (error-id e)) (string-suffix? (error-id e) (format "/~a" n))
            (string-contains? (error-text e) (format "// requires of ~a" api)))]
      ['(claim) (string-suffix? (error-text e) "// claim")]
      [_ #f])))

;; The fact a claim witness says its subject does not ensure, so that the
;; issue is recognized where another client needs the same fact after a call
;; of the subject (a later call's requires, docs/triage.md 2).  Its identity is
;; the asserted text in the positions of the subject's call, not in the
;; witness's variables: #aI is the Ith exec argument, #gI the Ith ghost
;; argument, #r the result, #gr the ghost result.  Only a fact about the state
;; after the call: one that mentions a snapshot (old_x) relates two states,
;; and no later requires asks for it.
;;
;; fact-key : TEXT (hash symbol -> string) -> string or #f
;;   the text without spaces, `(*x)` as `x` (auto-deref: the same place),
;;   each variable in the hash replaced by its position; #f if it mentions
;;   a snapshot.
(define (fact-key text pos)
  ;; one space between two words (`r is Ok`), none elsewhere
  (define s0 (regexp-replace* #px"\\s+"
                              (regexp-replace* #px"(?<=[A-Za-z0-9_])\\s+(?=[A-Za-z0-9_])" text "\u1")
                              ""))
  ;; `(*x)` as a receiver or operand, not the parentheses of a call `f(*x)`
  (define s1 (let loop ([s (string-replace s0 "\u1" " ")])
               (define t (regexp-replace* #px"(?<![A-Za-z0-9_)>\\]])\\(\\*([A-Za-z_][A-Za-z0-9_]*)\\)" s "\\1"))
               (if (equal? t s) s (loop t))))
  (and (not (regexp-match? #px"(?<![A-Za-z0-9_.:])old_[A-Za-z0-9_]" s1))
       (regexp-replace* #px"(?<![A-Za-z0-9_.:#])[A-Za-z_][A-Za-z0-9_]*(?![A-Za-z0-9_])" s1
                        (lambda (v) (hash-ref pos (string->symbol v) v)))))

;; witness-fact : witness -> (list API KEY) or #f
;;   API is the call just before the claim's assertion, KEY its fact-key.
(define (witness-fact w)
  (define body
    (match (witness-client w)
      [`(client ,_ ,items ...) (cond [(assq 'body items) => cdr] [else '()])]
      [_ '()]))
  ;; (call API (EXEC ...) (GHOST ...) [-> GR] ..), bound to X or not
  (define (call-pos c x)
    (match c
      [`(call ,(? symbol? api) ,(? list? es) ,(? list? gs) ,rest ...)
       (define pos (make-hasheq))
       (for ([e (in-list es)] [i (in-naturals)] #:when (symbol? e)) (hash-set! pos e (format "#a~a" i)))
       (for ([g (in-list gs)] [i (in-naturals)] #:when (symbol? g)) (hash-set! pos g (format "#g~a" i)))
       (when (symbol? x) (hash-set! pos x "#r"))
       (match (memq '-> rest) [(list _ (? symbol? gr) _ ...) (hash-set! pos gr "#gr")] [_ (void)])
       (cons api pos)]
      [_ #f]))
  (define (tmpl->text parts)
    (let/ec k
      (apply string-append
             (for/list ([p (in-list parts)])
               (match p
                 [(? string?) p]
                 [(? symbol?) (symbol->string p)]
                 [`(deref ,(? symbol? x)) (format "(*~a)" x)]
                 [_ (k #f)])))))
  (and (member '(claim) (witness-fails w))
       (let loop ([ss body] [last #f])
         (match ss
           ['() #f]
           [(cons s more)
            (match s
              [`(do ,c) (loop more (or (call-pos c #f) last))]
              [`(let ,x ,c) (loop more (or (call-pos c x) last))]
              [`(assert ,e "claim")
               (define text (match e [`(src ,(? string? t)) t] [`(tmpl ,parts ...) (tmpl->text parts)] [_ #f]))
               (define key (and last text (fact-key text (cdr last))))
               (and key (list (car last) key))]
              [_ (loop more last)])]))))

;; The first error that is not at a "may panic here" clause (not judged:
;; evaluation.md 7.1), or #f.
(define (first-judged-error r)
  (define es (result-errors r))
  (or (findf (lambda (e) (not (panic-error? e))) es) (and (pair? es) (car es))))

;; witness-status : witness results -> symbol
(define (witness-status w results)
  (define name (cadr (witness-client w)))
  (define sanity (assq 'sanity results))
  (define r (result-of results name))
  (cond
    [(not r) 'not-run]
    [(not (equal? sanity '(sanity ok))) 'not-concluded]
    [else
     (case (result-status r)
       [(verified) (if (null? (result-vacuous r)) 'passes 'vacuous)]
       [(failed not-verified)
        (cond [(for/or ([e (in-list (result-errors r))]) (error-matches? e (witness-fails w))) 'shows]
              ;; the clause may hold only because the path to it is infeasible
              [(pair? (result-vacuous r)) 'vacuous]
              [else 'other])]
       [else 'broken])]))

;; The clause is clear in a witness that verifies or fails only elsewhere
;; (other failures are other issues or noise: the clause after a failure is
;; still checked, Verus only assumes the failed one), with no vacuous path.
(define (clear? s) (memq s '(passes other)))

(define (original-status statuses)
  (cond [(null? statuses) 'no-witness]
        [(memq 'shows statuses) 'present]
        [(andmap clear? statuses) 'gone]
        [else 'undetected]))

(define (patched-status statuses)
  (cond [(null? statuses) 'no-witness]
        [(memq 'shows statuses) 'not-fixed]
        [(andmap clear? statuses) 'fixed]
        [else 'undetected]))
