#lang racket/base
;; The families of clients (design.md 3.6), one module each in families/, and
;; their registry.  Every family is generated from one context: the API table,
;; the entries to use (those `probe` found ok), the call knowledge, the
;; round-trip declarations, and the options.
;;
;;   family     module              asks
;;   goal       families/goal       can a caller who got G's arguments from real calls
;;                                  satisfy each clause of G's requires?
;;   claim      families/claim      does what a comment or a real caller relies on hold?
;;   protocol   families/protocol   does a call sequence of a real caller verify?
;;
;; goal needs nothing but the table; claim and protocol are the call knowledge's
;; hypotheses (design.md 3.7).  The earlier families (repeat, flow, chain, and
;; goal's hand-listed shapes) asked questions goal now asks by one rule:
;; repeat is goal's R3, flow its R1, chain's useful sequences its plans
;; (docs/enumeration.md 7, 9).
(require racket/list "families/protocol.rkt" "families/claim.rkt" "families/goal.rkt")
(provide (struct-out family) (struct-out context) families family-ref family-names)

;; context: what every family is generated from.
;;   table       the API table (with the providers of lib/providers/vstd.rktd)
;;   names       the entries to use
;;   knowledge   the module's call knowledge (model/knowledge.rkt), or '()
;;   identity    round-trip declarations (identity and roundtrip forms), or '()
;;   protocol-names  names, with the entries of other modules a protocol calls
;;   elided-lifetimes?  may a free lifetime be the elided '_ (design.md 3.5)
(struct context (table names knowledge identity protocol-names elided-lifetimes?))

;; family: a name, the question it asks, whether it needs call knowledge, and
;; its generator (context -> (client ...)).
(struct family (name question needs-knowledge? generate))

(define families
  (list
   (family 'goal "can a caller who got G's arguments from real calls satisfy each clause of G's requires" #f
           (lambda (c) (generate-goals (context-table c) (context-names c)
                                       #:knowledge (context-knowledge c)
                                       #:identity (context-identity c)
                                       #:elided-lifetimes? (context-elided-lifetimes? c))))
   (family 'claim "does what a comment or a real caller relies on hold" #t
           (lambda (c) (claim-clients (context-table c) (context-knowledge c))))
   (family 'protocol "does a call sequence of a real caller verify" #t
           (lambda (c) (generate-protocol-chains (context-table c) (context-protocol-names c) (context-knowledge c)
                                                 #:identity (context-identity c))))))

(define family-names (map family-name families))

(define (family-ref name)
  (or (findf (lambda (f) (eq? (family-name f) name)) families)
      (error 'family-ref "no family ~a (the families: ~a)" name family-names)))
