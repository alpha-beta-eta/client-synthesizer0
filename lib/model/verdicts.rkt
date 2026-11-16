#lang racket/base
;; Verdicts on groups of failures, kept across rounds (docs/triage.md 4).
;;
;; A group is judged once; the verdict holds while the specifications it was
;; judged on do not change.  A file (data/verdicts/*.rktd) is a sequence of
;;   (verdict (group KEY)            the group's key as groups.rkt writes it
;;                                   ("requires of API /N", "after an error of API", a claim's text)
;;            [(module M)]           only in that module (default: wherever the key is)
;;            [(by API)]             only where API is the culprit (attribute.rkt) of the
;;                                   group's representative failure (groups.rkt: (at CLIENT ID API)),
;;                                   the one read and probed
;;            (judgement J)          defect | not-defect | noise | by-design | known | needs-lemma | decision
;;            [(issue ID)]           the known issue it is (data/issues)
;;            (reason STRING)
;;            (specs (API "HEX") ...) the fingerprints (vostd/spec-digest.rkt) of what was read:
;;                                   the callee of the clause, the culprit
;;            (at "COMMIT"))         the commit judged at
;; A verdict is current where every API in specs has the same fingerprint
;; now, stale where one changed or is gone: then the group is to be judged
;; again (groups.rkt puts stale verdicts among the unjudged).
(require racket/list racket/match racket/file racket/string "../base/forms.rkt")
(provide (struct-out verdict) read-verdicts verdict-for verdict-status read-digest-file key-apis write-verdict)

(struct verdict (key module by judgement issue reason specs at file) #:transparent)

(define judgements '(defect not-defect noise by-design known needs-lemma decision))

(define (read-verdicts where)
  (define files (if (directory-exists? where)
                    (for/list ([f (in-list (sort (map path->string (directory-list where)) string<?))]
                               #:when (regexp-match? #rx"[.]rktd$" f))
                      (build-path where f))
                    (list where)))
  (append*
   (for/list ([f (in-list files)])
     (for/list ([x (in-list (file->list f))])
       (define (bad) (error 'verdicts "~a: not a verdict: ~s" f x))
       (match x
         [`(verdict ,items ...)
          (define (one k [d #f]) (match (assq k items) [`(,_ ,v) v] [#f d] [_ (bad)]))
          (define j (one 'judgement))
          (unless (and (string? (one 'group)) (memq j judgements) (string? (one 'reason)) (string? (one 'at))) (bad))
          (define specs (match (assq 'specs items)
                          [`(specs (,(? symbol?) ,(? string?)) ...) (cdr (assq 'specs items))]
                          [_ (bad)]))
          (verdict (one 'group) (one 'module) (one 'by) j (one 'issue) (one 'reason) specs (one 'at) f)]
         [_ (bad)])))))

;; verdict-for : (verdict ...) module key culprit-or-#f -> verdict or #f
;; The last that applies (a later file, a later line, overrides).
(define (verdict-for vs m key culprit)
  (for/last ([v (in-list vs)]
             #:when (equal? (verdict-key v) key)
             #:when (or (not (verdict-module v)) (equal? (verdict-module v) m))
             #:when (or (not (verdict-by v)) (eq? (verdict-by v) culprit)))
    v))

;; verdict-status : verdict (hash API -> HEX) -> current | stale
(define (verdict-status v digests)
  (if (for/and ([s (in-list (verdict-specs v))]) (equal? (hash-ref digests (car s) #f) (cadr s)))
      'current
      'stale))

;; read-digest-file : file -> hash API -> HEX
(define (read-digest-file f)
  (for/hash ([x (in-list (file->list f))] #:when (and (pair? x) (eq? (car x) 'digest)))
    (values (cadr x) (caddr x))))

;; key-apis : key -> (API ...), the APIs a group's key names
(define (key-apis key)
  (match (regexp-match #px"^(?:requires of|after an error of) (\\S+)" key)
    [(list _ a) (list (string->symbol a))]
    [_ (match (regexp-match #px"// (?:requires of|relation) (.*)$" key)
         [(list _ rest) (map string->symbol (regexp-split #rx", " rest))]
         [_ '()])]))

;; write-verdict : file verdict-form -> void, appended
(define (write-verdict file form)
  (call-with-output-file file #:exists 'append
    (lambda (o) ((dynamic-require 'racket/pretty 'pretty-write) form o))))
