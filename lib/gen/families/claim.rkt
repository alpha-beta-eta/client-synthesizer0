#lang racket/base
;; claim_<API>_<i>: what a comment or a real caller says holds after a call,
;; from the call knowledge (design.md 3.7): the API called under its own
;; requires, then the claim asserted.
(require racket/list racket/match racket/string "../../model/api.rkt" "../../base/forms.rkt" "../probe.rkt" "../../model/knowledge.rkt" "../../model/template.rkt" "common.rkt")
(provide claim-clients claim-source)

;; claim-source : claim text, api, result variable, ghost result variable ->
;; (tmpl PIECE ...), the claim after the call, its holes the client's
;; variables (model/template.rkt; until 2026-11-13 flattened to text, which
;; analyses could not read: docs/enumeration.md 7.2).  *final(p) and final(p)
;; are p's value now, (*p); *old(p) and old(p) the snapshot old_p taken before
;; the call; ret the result, gret the ghost result.
(define (claim-source text0 api r [g #f])
  (define muts (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
                          #:when (match (param-type p) [`(&mut ,_) #t] [_ #f]))
                 (param-name p)))
  ;; A variable the claim binds (forall|r: T|, a closure's |x|) that is named
  ;; like one this substitution brings in (the result r, the ghost result, a
  ;; snapshot old_x, a local) is renamed first, or the substitution would be
  ;; captured: `forall|r: MetaRegionOwners| .. ret.0.relate_regions(r)` became
  ;; `r.0.relate_regions(r)` with r the bound owners.
  (define introduced
    (map symbol->string
         (append (list r) (if g (list g) '())
                 (append* (for/list ([p (in-list muts)])
                            (list (local p) (string->symbol (format "old_~a" (local p)))))))))
  (define text
    (for/fold ([s text0]) ([b (in-list (bound-names text0))] #:when (member b introduced))
      (regexp-replace* (pregexp (format "(?<![.:A-Za-z0-9_])~a(?![A-Za-z0-9_])" (regexp-quote b))) s (string-append b "_b"))))
  ;; the free uses of the parameters, ret and gret, on the text's holes
  ;; (model/template.rkt; docs/representation.md 4.5): `x.ret`, a bound `ret`
  ;; or a name containing one are not replaced
  (define params (map param-name (append (api-params api) (api-ghost-params api))))
  (define (lx p) (local p))
  `(tmpl
    ,@(for/list ([piece (in-list (cdr (source->template text (append params '(ret gret)))))])
        (match piece
          [(? string? s) s]
          ['ret r]
          ['gret (or g "gret")]
          [(or `(old ,p) `(deref (old ,p))) (if (memq p muts) (string->symbol (format "old_~a" (lx p))) (lx p))]
          [(or `(final ,p) `(deref (final ,p))) (if (memq p muts) `(deref ,(lx p)) (lx p))]
          [p (lx p)]))))

;; The names a claim binds: between bars (|x: T, y| of forall, exists, choose,
;; closures), and in the pattern of `matches` (`matches Either::Right(r)`).
(define (bound-names text)
  (remove-duplicates
   (append
    (for*/list ([m (in-list (regexp-match* #px"\\|([^|]*)\\|" text #:match-select cadr))]
                [part (in-list (string-split m ","))]
                [n (in-value (regexp-match #px"^\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*(:|$)" part))]
                #:when n)
      (cadr n))
    (for*/list ([m (in-list (regexp-match* #px"\\bmatches\\s+[A-Za-z0-9_:]+\\s*\\(([^()]*)\\)" text #:match-select cadr))]
                [part (in-list (string-split m ","))]
                [n (in-value (regexp-match #px"^\\s*(?:ref\\s+)?(?:mut\\s+)?([a-z_][A-Za-z0-9_]*)\\s*$" part))]
                #:when (and n (not (equal? (cadr n) "_"))))
      (cadr n)))))

;; entry-field : knowledge entry key -> the field's contents, or '()
(define (entry-field e k)
  (or (for/first ([x (in-list (cdddr e))] #:when (and (pair? x) (eq? (car x) k))) (cdr x)) '()))

;; claim-clients : table knowledge -> (client ...)
;; claim_<API>_<i>: the API called under its own requires (lifted, as in its
;; probe), with snapshots of its `&mut` arguments, then the claim asserted.
(define (claim-clients table k)
  (for/list ([e (in-list (knowledge-entries k 'claim))] [i (in-naturals)]
             #:when (api-ref table (cadr e)))
    (define api (api-ref table (cadr e)))
    (define probe (probe-client api))
    (define call-stmt (car (cdr (assq 'body (cddr probe)))))
    (define r (match call-stmt [`(let ,x ,_) x] [_ 'r]))
    (define g (match call-stmt [`(,_ ... (call ,_ ,_ ,_ -> ,g ,_ ...)) g] [_ #f]))
    (define snaps
      (for/list ([p (in-list (append (api-params api) (api-ghost-params api)))]
                 #:when (match (param-type p) [`(&mut ,_) #t] [_ #f]))
        (define x (local (param-name p)))
        `(ghost ,(string->symbol (format "old_~a" x)) (deref ,x))))
    `(client ,(string->symbol (format "claim_~a_~a" (regexp-replace* #rx"[^A-Za-z0-9_]" (symbol->string (cadr e)) "_") i))
             (source ,(format "claim on ~a: ~a" (cadr e) (caddr e)))
             (type-params ,@(cdr (assq 'type-params (cddr probe))))
             (params ,@(cdr (assq 'params (cddr probe))))
             (allow-open)
             ;; the claim's own proof steps, in its names (docs/representation.md 4.5):
             ;; (proof "lemma_x(ret, self);" ..) before the assertion, (by bit_vector) on it
             (body ,@snaps ,call-stmt
                   ,@(for/list ([t (in-list (entry-field e 'proof))]) `(proof-text ,(claim-source t api r g)))
                   ,(match (entry-field e 'by)
                      [(list m) `(assert ,(claim-source (caddr e) api r g) "claim" (by ,m))]
                      [_ `(assert ,(claim-source (caddr e) api r g) "claim")]))
             ;; what every real caller holds (the knowledge's assume entries), as in chain
             ,@(let ([as (knowledge-assumptions k api)]) (if (null? as) '() `((requires ,@as)))))))
