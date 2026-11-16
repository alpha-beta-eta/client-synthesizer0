#lang racket/base
;; The judgements of trusted code as data (design.md 3.12, evaluation.md 9).
;;
;; data/audit/verdicts/<area>.rktd:
;;   (audit (area "AREA") (report "AREA.md") (at "COMMIT") (scope PREFIX ...))
;;   (verdict "ID" JUDGEMENT SITE ...
;;            [(qualifier "TEXT")] (reason "TEXT") [(note "TEXT")] [(demo "FILE.rs" "FN")]
;;            [(aspect usage)] [(removed "COMMIT" "TEXT")])
;;   SITE = (site KIND "FILE" "ITEM" "DETAIL" (fp "HEX"))      as lib/vostd/trusted.rkt lists them
;;
;;   JUDGEMENT  faithful | too-strong | model-mismatch | weak | unclear | not-compiled
;;   at         the commit the verdicts were last reviewed against
;;   scope      the files (or directories, ending in `/`) the area covers: a
;;              trusted site there without a verdict is unjudged
;;   fp         the site's fingerprint at that review: a judgement is of the
;;              text it saw, and a changed text needs it again
;;   demo       Verus code (data/audit/demos/FILE) whose function FN verifies
;;              exactly when the judgement (too-strong) is demonstrated
;;   aspect     the verdict is about how the sites can be used together (e.g. an
;;              axiom any proof may call), not about each site;
;;              it does not disagree with the sites' own verdicts
;;   removed    since COMMIT the sites are no longer trusted code (the body is
;;              verified, the specification moved to vstd): kept as history, not checked
;; The ID's number is the entry in the area's report (data/audit/AREA.md),
;; where the reasoning is written out.
;;
;; Everything here works on forms; listing the sites of a checkout is
;; lib/vostd/trusted.rkt's, running the demos pipeline/trusted.rkt's.
(require racket/file racket/list racket/match racket/string racket/pretty racket/set)
(provide read-audit audit-area audit-at audit-scope audit-verdicts
         verdict-id verdict-judgement verdict-sites verdict-demo
         check-audit accept-audit write-audit judgements)

(define judgements '(faithful too-strong model-mismatch weak unclear not-compiled))

;; ================================================================ reading

(struct audit (file comment header verdicts))

(define (header-ref a key) (match (assq key (cdr (audit-header a))) [`(,_ ,v) v] [_ #f]))
(define (audit-area a) (header-ref a 'area))
(define (audit-at a) (header-ref a 'at))
(define (audit-scope a) (match (assq 'scope (cdr (audit-header a))) [`(scope ,ps ...) ps] [_ '()]))

(define (verdict-id v) (cadr v))
(define (verdict-judgement v) (caddr v))
(define (verdict-sites v) (filter (lambda (x) (and (pair? x) (eq? (car x) 'site))) (cdddr v)))
(define (verdict-demo v) (match (assq 'demo (filter pair? (cdddr v))) [`(demo ,f ,fn) (list f fn)] [_ #f]))
(define (verdict-removed v) (assq 'removed (filter pair? (cdddr v))))
(define (verdict-aspect? v) (and (assq 'aspect (filter pair? (cdddr v))) #t))
(define (live-verdicts a) (filter (lambda (v) (not (verdict-removed v))) (audit-verdicts a)))

;; a site's identity, as the listing's site-key: (KIND FILE ITEM DETAIL)
(define (site-key s) (take (cdr s) 4))
(define (site-fp s) (cadr (assq (quote fp) (filter pair? (cdr s)))))

;; read-audit : file -> audit; checks what can be checked without a checkout
(define (read-audit file)
  (define text (file->string file))
  (define comment (let ([ls (string-split text "\n" #:trim? #f)])
                    (string-join (takef ls (lambda (l) (or (string-prefix? l ";;") (equal? (string-trim l) "")))) "\n")))
  (define forms (file->list file))
  (define header (or (assq 'audit forms) (error 'audit "~a: no (audit ..)" file)))
  (define vs (filter (lambda (f) (eq? (car f) 'verdict)) forms))
  (for ([v (in-list vs)])
    (unless (memq (verdict-judgement v) judgements)
      (error 'audit "~a: ~a: unknown judgement ~a" file (verdict-id v) (verdict-judgement v)))
    (when (null? (verdict-sites v)) (error 'audit "~a: ~a: no site" file (verdict-id v))))
  (let ([dup (check-duplicates (map verdict-id vs))])
    (when dup (error 'audit "~a: ~a twice" file dup)))
  (audit file comment header vs))

;; ================================================================ checking

(define (in-scope? file scope)
  (for/or ([p (in-list scope)]) (if (string-suffix? p "/") (string-prefix? file p) (equal? file p))))

;; check-audit : (audit ...) (trusted-site ...) [demo-results] -> (fact ...)
;; trusted-site = (trusted KIND FILE ITEM DETAIL (line N) (fp HEX)), from the checkout now.
;; demo-results: hash "FILE.rs" -> hash "FN" -> STATUS, or #f (not run).
;;   (audit AREA (at C) (verdicts N) (judged-sites N) (JUDGEMENT N) ...)
;;   (changed ID KIND FILE ITEM DETAIL (line N) (fp OLD NEW))   the text it judged changed
;;   (gone ID KIND FILE ITEM DETAIL)                            no such site any more
;;   (renamed ID (from KIND FILE ITEM DETAIL) (to KIND FILE ITEM DETAIL) (line N))
;;                                                             a gone site whose text is now under another name
;;   (unjudged AREA KIND FILE ITEM DETAIL (line N))             in the area's scope, no verdict
;;   (disagree KIND FILE ITEM DETAIL (ID JUDGEMENT) ...)        verdicts of one site differ
;;   (demo ID FILE FN STATUS)                                   STATUS of the demo's run; not
;;                                                             verified: the demonstration no longer holds
;;   (outside N (DIR N) ...)                                    sites in no area's scope
(define (check-audit audits sites [demo-results #f])
  (define by-key (for/hash ([s (in-list sites)]) (values (site-key s) s)))
  (define by-fp (for/fold ([h (hash)]) ([s (in-list sites)]) (hash-update h (site-fp s) (lambda (l) (cons s l)) '())))
  (define judged-keys
    (for*/set ([a (in-list audits)] [v (in-list (live-verdicts a))] [s (in-list (verdict-sites v))]) (site-key s)))
  (define (line-of s) (list-ref s 5))
  (define summaries
    (for/list ([a (in-list audits)])
      (define vs (live-verdicts a))
      (define removed (- (length (audit-verdicts a)) (length vs)))
      `(audit ,(audit-area a) (at ,(audit-at a)) (verdicts ,(length vs))
              ,@(if (positive? removed) `((removed ,removed)) '())
              (judged-sites ,(set-count (for*/set ([v vs] [s (verdict-sites v)]) (site-key s))))
              ,@(for/list ([j (in-list judgements)] #:when (memq j (map verdict-judgement vs)))
                  (list j (count (lambda (v) (eq? (verdict-judgement v) j)) vs))))))
  (define drift
    (for*/list ([a (in-list audits)] [v (in-list (live-verdicts a))] [s (in-list (verdict-sites v))])
      (define now (hash-ref by-key (site-key s) #f))
      (cond
        [(and now (equal? (site-fp now) (site-fp s))) #f]
        [now `(changed ,(verdict-id v) ,@(site-key s) ,(line-of now) (fp ,(site-fp s) ,(site-fp now)))]
        [else
         (define same-text (filter (lambda (t) (not (set-member? judged-keys (site-key t))))
                                   (hash-ref by-fp (site-fp s) '())))
         (match same-text
           [(list t) `(renamed ,(verdict-id v) (from ,@(site-key s)) (to ,@(site-key t)) ,(line-of t))]
           [_ `(gone ,(verdict-id v) ,@(site-key s))])])))
  (define renamed-to (for/set ([d (in-list drift)] #:when (and d (eq? (car d) 'renamed))) (cdr (cadddr d))))
  (define unjudged
    (for*/list ([s (in-list sites)]
                #:unless (set-member? judged-keys (site-key s))
                #:unless (set-member? renamed-to (site-key s))
                [a (in-value (findf (lambda (a) (in-scope? (caddr s) (audit-scope a))) audits))]
                #:when a)
      `(unjudged ,(audit-area a) ,@(site-key s) ,(line-of s))))
  (define disagreements
    (let ([h (for*/fold ([h (hash)]) ([a (in-list audits)] [v (in-list (live-verdicts a))] #:unless (verdict-aspect? v)
                                      [s (in-list (verdict-sites v))])
               (hash-update h (site-key s) (lambda (l) (cons (list (verdict-id v) (verdict-judgement v)) l)) '()))])
      (for/list ([(k l) (in-hash h)] #:when (> (length (remove-duplicates (map cadr l))) 1))
        `(disagree ,@k ,@(sort (reverse l) string<? #:key car)))))
  (define demos
    (if demo-results
        (for*/list ([a (in-list audits)] [v (in-list (live-verdicts a))] [d (in-value (verdict-demo v))] #:when d)
          (define st (hash-ref (hash-ref demo-results (car d) (hash)) (cadr d) 'not-run))
          `(demo ,(verdict-id v) ,@d ,st))
        '()))
  (define all-scope (append* (map audit-scope audits)))
  (define outside (filter (lambda (s) (not (in-scope? (caddr s) all-scope))) sites))
  (define (dir-of f) (string-join (take (string-split f "/") (min 4 (sub1 (length (string-split f "/"))))) "/"))
  (append summaries (filter values drift) unjudged
          (sort disagreements string<? #:key (lambda (d) (format "~a" (cdr d))))
          demos
          (list `(outside ,(length outside)
                          ,@(for/list ([g (in-list (group-by (lambda (s) (dir-of (caddr s))) outside))]) (list (dir-of (caddr (car g))) (length g)))))))

;; ================================================================ accepting

;; accept-audit : audit (trusted-site ...) commit only-rx -> (values audit (ID ...))
;; After the changed sites (check-audit) have been judged again: their
;; fingerprints become the current ones, and the file is at the commit.
;; Only verdicts whose ID matches only-rx; gone and renamed sites are edited by hand.
(define (accept-audit a sites commit [only #rx""])
  (define by-key (for/hash ([s (in-list sites)]) (values (site-key s) s)))
  (define accepted '())
  (define vs
    (for/list ([v (in-list (audit-verdicts a))])
      (if (regexp-match? only (verdict-id v))
          (for/list ([x (in-list v)])
            (match x
              [`(site ,_ ...)
               (define now (hash-ref by-key (site-key x) #f))
               (cond [(and now (not (equal? (site-fp now) (site-fp x))))
                      (set! accepted (cons (verdict-id v) accepted))
                      (append (take x 5) (list `(fp ,(site-fp now))))]
                     [else x])]
              [_ x]))
          v)))
  (define header (for/list ([x (in-list (audit-header a))])
                   (match x [`(at ,_) `(at ,commit)] [_ x])))
  (values (audit (audit-file a) (audit-comment a) header vs) (remove-duplicates (reverse accepted))))

(define (write-audit a)
  (call-with-output-file (audit-file a) #:exists 'truncate
    (lambda (o)
      (write-string (audit-comment a) o)
      (unless (string-suffix? (audit-comment a) "\n") (newline o))
      (pretty-write (audit-header a) o)
      (for ([v (in-list (audit-verdicts a))])
        (newline o)
        (parameterize ([pretty-print-columns 110]) (pretty-write v o))))))
