#lang racket/base
;; Source text with holes (model/template.rkt; docs/representation.md 4.2, 4.5), the
;; claims written on them, and what render adds around bindings (use_type_invariant, B2)
;; and for a claim's proof steps (D3).
(require rackunit racket/string racket/file racket/runtime-path (only-in racket/list take)
         "../lib/model/template.rkt" "../lib/model/spec.rkt" "../lib/model/api.rkt"
         "../lib/check/client.rkt" "../lib/gen/render.rkt" (only-in "../lib/gen/probe.rkt" probe-client))

;; holes: free uses only, not fields, paths, or names the text binds
(check-equal? (source->template "mappings.filter(|m: Mapping| start <= m.va_range.start < end) == Set::< Mapping, >::empty()"
                                '(mappings start end m))
              '(tmpl "" mappings ".filter(|m: Mapping| " start " <= m.va_range.start < " end ") == Set::< Mapping, >::empty()"))
(check-equal? (source->template "perm matches Some(p) ==> self.wf(*p)" '(perm p self))
              '(tmpl "" perm " matches Some(p) ==> " self ".wf(*p)"))
(check-equal? (source->template "*final(self) == *old(self) && old(x).len() == ret" '(self x ret))
              '(tmpl "" (deref (final self)) " == " (deref (old self)) " && " (old x) ".len() == " ret ""))
;; a name that is only part of another, or a function of the same name, is no hole
(check-equal? (source->template "ret_count(r) == r.ret" '(r ret)) '(tmpl "ret_count(" r ") == " r ".ret"))

;; substitution and None: a template's None gets its type
(define api `(fn m::f (function "m::f") (generics) (params (x exec usize))
                 (ghost with (perm tracked (Option Perm)))
                 (requires ,(source->template "perm matches Some(p) ==> p.x == x" '(x perm)))))
(define inst (requires-instance api '(y) '((none))))
(check-equal? inst '((tmpl "" (const None::<Perm>) " matches Some(p) ==> p.x == " y "")))
(check-equal? (expr->text (car inst)) "(None::<Perm> matches Some(p) ==> p.x == y)")

;; claims: on the holes (`.ret` and `ret_x` stay), &mut parameters through their snapshots
(require (only-in "../lib/gen/families/claim.rkt" claim-source))
(define capi '(fn m::g (method g) (generics) (params (self exec (&mut S)) (n exec usize)) (ret usize)))
;; a template (docs/enumeration.md 7.2): the client's variables in its holes,
;; rendered as the text was
(define ct (claim-source "ret == old(self).ret_x + n && final(self).ret == ret" capi 'r))
(check-equal? (template-vars ct) '(r old_self_ n self_))
(check-equal? (top->text ct) "r == old_self_.ret_x + n && (*self_).ret == r")

;; use_type_invariant where a value of an invariant type is bound; proof steps and `by`
(define-runtime-path apis "../data/auto/apis")
(define spin (build-path apis "sync.spin.rktd"))
(when (file-exists? spin)
  (define t (read-api-table spin))
  (check-true (has-type-invariant? t '(SpinLockGuard |'a| T G)))
  (check-false (has-type-invariant? t 'usize))
  (define lock (for/first ([n (in-list (table-names t))] #:when (regexp-match? #rx"impl&%[0-9]+::lock$" (symbol->string n))) n))
  (when lock
    (define probe (probe-client (api-ref t lock)))
    (define call-stmt (cadr (assq 'body (cddr probe))))
    (define r (cadr call-stmt))
    (define c `(client c (type-params ,@(cdr (assq 'type-params (cddr probe))))
                       (params ,@(cdr (assq 'params (cddr probe))))
                       (allow-open)
                       (body ,call-stmt
                             (proof-text "assert(true);")
                             (assert (src "true") "claim" (by bit_vector)))))
    (define e (check-client t c))
    (check-equal? (car e) 'client (format "~s" e))
    (define-values (text _) (parameterize ([client-module "sync::spin::cs_clients"]) (render-module t (list e))))
    (define-values (elsewhere _2) (parameterize ([client-module "sync::rwarc::cs_clients"]) (render-module t (list e))))
    (check-false (string-contains? elsewhere "use_type_invariant") elsewhere)
    (check-true (string-contains? text "proof { use_type_invariant(self_); }") text)
    (check-true (string-contains? text (format "proof { use_type_invariant(&~a); }" r)) text)
    (check-true (string-contains? text "proof { assert(true); }") text)
    (check-true (string-contains? text "assert(true) by (bit_vector); // claim") text)
    ;; (negate ID): only that assertion negated (refute.rkt, docs/triage.md 3)
    (define body (cdr (assq 'body (cddr e))))
    (define ne (check-client t `(client c ,@(cddr c) (negate "s3"))))
    (check-equal? (cdr (assq 'body (cddr ne))) (append (take body 2) (list `(assert "s3" (not (src "true")) "claim" (by bit_vector)))))
    (check-equal? (car (check-client t `(client c ,@(cddr c) (negate "s9")))) 'ill-formed)))
