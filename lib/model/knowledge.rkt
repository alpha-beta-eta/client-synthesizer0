#lang racket/base
;; Call knowledge (auto/knowledge/FORMAT.md, design.md 结论37): what an LLM
;; extracted from comments, real callers and domain material about how a
;; module's APIs are used, and its uses in client synthesis:
;;   role        which value may be passed where (enum.rkt's roles)
;;   protocol    call sequences real callers use: seeds of chains
;;   claim       what comments promise after a call: a client asserting it
;;   assume      what a real caller may take for granted at the seed call
;;   prefer, limitation, not-defect   labels for failures (pipeline/groups.rkt)
;;   must-close  (must-close TYPE (why ..)): a datatype whose values a client must
;;               pass on by value (a lock guard: its drop restores the lock's
;;               invariant, which a guard left to go out of scope never shows).
;;               A person's decision from extraction's must-close candidates;
;;               until 2026-11-16 it was the only content of the hand overlays
;;               (auto/manual/), which client-synthesizer0 does not have.
(require racket/list racket/match racket/string racket/file
         "api.rkt" "template.rkt")
(provide rename-self read-knowledge knowledge-entries knowledge-roles knowledge-var-roles
         knowledge-assumptions knowledge-protocols knowledge-must-close)

;; (TYPE ...)
(define (knowledge-must-close k)
  (for/list ([e (in-list (knowledge-entries k 'must-close))]) (cadr e)))

;; read-knowledge : path-or-#f -> (entry ...); a missing file is no knowledge.
;; Not entries: (module ..), and what records the review against vostd,
;; (at COMMIT) and (spec-digests ..) (design.md 3.7, lib/model/knowledge-drift.rkt).
(define meta-forms '(module at spec-digests))
(define (read-knowledge file)
  (if (and file (file-exists? file))
      (filter (lambda (e) (and (pair? e) (not (memq (car e) meta-forms)))) (file->list file))
      '()))

(define (knowledge-entries k kind) (filter (lambda (e) (eq? (car e) kind)) k))

(define (local x) (if (eq? x 'self) 'self_ x))

;; ((API PARAM ROLE) ...)
(define (knowledge-roles k)
  (for/list ([e (in-list (knowledge-entries k 'role))]) (list (cadr e) (caddr e) (cadddr e))))

;; The roles of the client parameters of a client seeded with api: its own.
(define (knowledge-var-roles k api)
  (for/list ([r (in-list (knowledge-roles k))]
             #:when (and (eq? (car r) (api-name api)) (not (memq (cadr r) '(ret gret)))))
    (list (local (cadr r)) (caddr r))))

;; The assumptions at a call of api, as client requires: ((tmpl PIECE ...) ...),
;; templates whose holes are api's parameters by their names in a client
;; (`self` is self_; model/template.rkt), so that a client renames them on
;; the structure (flow: G's parameters by G's arguments) and analyses see the
;; variables (docs/enumeration.md 7.2; until 2026-11-13 opaque (src "..")).
;; In requires, `old(p)` of a `&mut` parameter is what it is.
(define (knowledge-assumptions k api)
  (define ps (map param-name (append (api-params api) (api-ghost-params api))))
  (for/list ([e (in-list (knowledge-entries k 'assume))] #:when (eq? (cadr e) (api-name api)))
    (template-map (source->template (caddr e) ps) local)))

;; ((NAME (API ...)) ...)
(define (knowledge-protocols k)
  (for/list ([e (in-list (knowledge-entries k 'protocol))])
    (list (cadr e) (cdr (assq 'calls (cddr e))))))

(define (rename-self s) (regexp-replace* #px"\\bself\\b" s "self_"))
