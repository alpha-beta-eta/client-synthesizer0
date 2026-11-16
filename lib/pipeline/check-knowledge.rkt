#lang racket/base
;; Checking knowledge files against the API tables and against the vostd
;; checkout (design.md 3.7, evaluation.md 5.3, 5.4).
;;
;; For each KNOWLEDGE-DIR/<m>.rktd: that it reads, the entries whose API is
;; not in the module's table, the protocols whose calls are in no table, and
;; the claim clients that are not well-formed, and the claims and assumptions
;; whose text does not parse, names what the API does not have, or is written
;; as Verus rejects (knowledge-text.rkt: `(bad-text KIND API TEXT PROBLEM ..)`).
;; Whether a claim holds, or type-checks, only Verus tells.
;;
;; And its drift (model/knowledge-drift.rkt), against the checkout of the
;; module's target (AUTO-DIR/targets/<m>.rktd) and the fingerprints of its
;; commit (AUTO-DIR/digests/<commit>.rktd, vostd/spec-digest.rkt): the commit
;; the file was reviewed at, where its anchors are now, and the APIs whose
;; specification changed since the review.  Knowledge may lag the checkout
;; (design.md principle 5): these facts are for reading again, not errors.
(require racket/file racket/list racket/match racket/path racket/string
         "../model/api.rkt" "../check/client.rkt" "../model/knowledge.rkt" (only-in "../gen/families/claim.rkt" claim-clients)
         "../base/forms.rkt" "../model/knowledge-drift.rkt" "../vostd/git.rkt" "../base/env.rkt"
         "../check/knowledge-text.rkt")
(provide check-knowledge update-knowledge! left-out-reasons)

(define (table-of auto m)
  (for/first ([d (in-list '("fixes" "apis"))]
              #:when (file-exists? (build-path auto d (string-append m ".rktd"))))
    (path->complete-path (build-path auto d (string-append m ".rktd")))))

(define (module-of a)
  (match (regexp-match #rx"^(.*?)::(impl&%[0-9]+::)?[^:]+$" (symbol->string a))
    [(list _ path _) (regexp-replace* #rx"::" path ".")]
    [_ #f]))

;; ================================================================ drift

;; The checkout of module m's target, its HEAD, and the fingerprints of that
;; commit: (values vostd head digests-or-#f).
(define (checkout-of auto m)
  (define target (build-path auto "targets" (string-append m ".rktd")))
  (define vostd (and (file-exists? target) (cadr (assq 'vostd (read-target target)))))
  (define head (and vostd (git-head vostd)))
  (define ddir (build-path auto "digests"))
  (define digests
    (and head (directory-exists? ddir)
         (for/or ([f (in-list (directory-list ddir #:build? #t))]
                  #:when (regexp-match? #rx"[.]rktd$" (path->string f)))
           (define-values (h c) (read-digests f))
           (and (same-commit? c head) h))))
  (values vostd head digests))

;; placed : text vostd -> ((REF . STATUS) ...), STATUS from relocate, or 'none
(define (placed text vostd)
  (for/list ([r (in-list (vostd-refs text))])
    (match-define (list _ _ _ path line snippet) r)
    (cons r (if snippet (relocate (and vostd (git-lines vostd #f path)) line snippet) 'none))))

;; drift-facts : auto m file entries -> (fact ...)
(define (drift-facts auto m file k)
  (define-values (vostd head digests) (checkout-of auto m))
  (define forms (file->list file))
  (define at (cond [(assq 'at forms) => cadr] [else #f]))
  (define recorded (cond [(assq 'spec-digests forms) => (lambda (x) (for/hash ([d (in-list (cdr x))]) (values (car d) (cadr d))))]
                         [else (hash)]))
  (define ps (placed (file->string file) vostd))
  (define (count-of pred) (count (lambda (x) (pred (cdr x))) ps))
  (define (moved? s) (and (pair? s) (eq? (car s) 'moved)))
  (define (ambiguous? s) (and (pair? s) (eq? (car s) 'ambiguous)))
  (define changed
    (for/list ([a (in-list (knowledge-apis k))]
               #:when (and digests (hash-ref recorded a #f) (hash-ref digests a #f)
                           (not (equal? (hash-ref recorded a) (hash-ref digests a)))))
      `(spec-changed ,a ,(for/list ([e (in-list k)]
                                    #:when (if (eq? (car e) 'protocol) (memq a (knowledge-apis (list e))) (eq? (cadr e) a)))
                           (if (eq? (car e) 'protocol) `(protocol ,(cadr e)) (car e))))))
  (define unrecorded
    (if digests (count (lambda (a) (and (hash-ref digests a #f) (not (hash-ref recorded a #f)))) (knowledge-apis k)) 0))
  `((reviewed-at ,(or at 'none)) (checkout ,(or head 'none))
    ,@(if (and head (not digests)) `((no-digests ,head)) '())
    (anchors (same ,(count-of (lambda (s) (eq? s 'same)))) (moved ,(count-of moved?)) (lost ,(count-of (lambda (s) (eq? s 'lost))))
             (ambiguous ,(count-of ambiguous?)) (none ,(count-of (lambda (s) (eq? s 'none)))))
    ,@(for/list ([x (in-list ps)] #:when (eq? (cdr x) 'lost))
        `(lost ,(list-ref (car x) 3) ,(list-ref (car x) 4) ,(list-ref (car x) 5)))
    ,@(for/list ([x (in-list ps)] #:when (ambiguous? (cdr x)))
        `(ambiguous ,(list-ref (car x) 3) ,(list-ref (car x) 4) ,(list-ref (car x) 5) ,(cdr (cdr x))))
    ,@changed
    ,@(if (positive? unrecorded) `((unrecorded ,unrecorded)) '())))

;; update-knowledge! : auto-dir knowledge-dir module-regex #:fix? #:accept? -> (fact ...)
;; Writes the files: with fix?, the line numbers of moved anchors; with
;; accept? (after the file has been read again against the checkout), the
;; checkout's commit and the fingerprints of the APIs the entries name, and
;; anchors for the references without one, at the lines they cite now.  The
;; rest of the text, comments included, is kept.
(define (update-knowledge! auto kdir [only #rx""] #:fix? [fix? #f] #:accept? [accept? #f])
  (for*/list ([f (in-list (sort (map path->string (directory-list kdir)) string<?))]
              #:when (and (regexp-match? #rx"[.]rktd$" f) (regexp-match? only f)))
    (define m (path->string (path-replace-extension f #"")))
    (define file (build-path kdir f))
    (define-values (vostd head digests) (checkout-of auto m))
    (define text (file->string file))
    (define ps (placed text vostd))
    (define t1 (rewrite-refs text
                             (for/list ([x (in-list ps)])
                               (cons (car x) (match (cdr x) [`(moved ,n) #:when fix? n] [_ #f])))
                             (lambda (r) (and accept? vostd (anchor-text (git-lines vostd #f (list-ref r 3)) (list-ref r 4))))))
    (define t2 (if (and accept? head digests)
                   (splice-meta t1 head (for/list ([a (in-list (knowledge-apis (read-knowledge file)))] #:when (hash-ref digests a #f))
                                          (cons a (hash-ref digests a))))
                   t1))
    (cond
      [(and accept? (not digests)) `(knowledge ,m (not-accepted (no-digests ,head)))]
      [(equal? t2 text) `(knowledge ,m unchanged)]
      [else (call-with-output-file file #:exists 'truncate (lambda (o) (write-string t2 o)))
            `(knowledge ,m (written ,@(if fix? '(moved-anchors) '()) ,@(if accept? `((reviewed-at ,head)) '())))])))

;; ================================================================ checking

;; check-knowledge : auto-dir knowledge-dir providers-file module-regex
;;   (providers-file: usually lib/providers/vstd.rktd, model/api.rkt's vstd-providers)
;;   -> ((knowledge M (entries (KIND N) ...) STRUCTURE DRIFT ...) ...)
;;   STRUCTURE: ok, or (unknown-api KIND API) .. (protocol-outside NAME (API ..)) ..
;;              (ill-formed-claim NAME) ..
;;   then notes: (protocol-left-out NAME (API REASON) ..), a protocol calling APIs the
;;              extraction left out for REASON (left-out.rktd), not generated;
;;              (uses-closed ..)
;;   DRIFT: (reviewed-at C) (checkout C) [(no-digests C)] (anchors ..) (lost ..) ..
;;          (ambiguous ..) .. (spec-changed API (KIND ..)) .. [(unrecorded N)]
;;   or (knowledge M (unreadable MESSAGE)), (knowledge M (no-table))
;; left-out-reasons : auto-dir -> hash API-name -> REASON, the functions the
;; extraction left out (AUTO/left-out.rktd, by VIR path: `ostd::`, the
;; verified twin's `_VERUS_VERIFIED_` taken off, as the tables name them)
(define (left-out-reasons auto)
  (define f (build-path auto "left-out.rktd"))
  (if (file-exists? f)
      (for/hash ([x (in-list (file->list f))] #:when (and (pair? x) (string? (car x)) (pair? (cdr x))))
        (values (string->symbol (regexp-replace* #rx"_VERUS_VERIFIED_" (regexp-replace #rx"^ostd::" (car x) "") ""))
                (cadr x)))
      (hash)))
(define (check-knowledge auto kdir providers [only #rx""])
  (for*/list ([f (in-list (sort (map path->string (directory-list kdir)) string<?))]
              #:when (and (regexp-match? #rx"[.]rktd$" f) (regexp-match? only f)))
    (define m (path->string (path-replace-extension f #"")))
    (define k (with-handlers ([exn:fail? (lambda (e) (exn-message e))])
                (read-knowledge (build-path kdir f))))
    (cond
      [(string? k) `(knowledge ,m (unreadable ,k))]
      [(not (table-of auto m)) `(knowledge ,m (no-table))]
      [else
       (define tmp (make-temporary-file "know~a.rktd"))
       (write-forms tmp `((base ,(path->string (table-of auto m))) (base ,(path->string (path->complete-path providers)))))
       (define t (read-api-table tmp))
       (delete-file tmp)
       ;; a table may be an overlay on another (base ..): read it as such
       (define (in-some-table? a)
         (or (api-ref t a)
             (let ([o (module-of a)])
               (and o (table-of auto o) (api-ref (read-api-table (table-of auto o)) a) #t))))
       ;; the module's datatypes by their last segment (extract.rkt's (datatype PATH ..))
       (define datatypes
         (let ([f (build-path auto "apis" (string-append m ".rktd"))])
           (if (file-exists? f)
               (for/list ([x (in-list (file->list f))] #:when (and (pair? x) (eq? (car x) 'datatype)))
                 (string->symbol (last (string-split (symbol->string (cadr x)) "::"))))
               '())))
       (define unknown
         (append
          (for/list ([e (in-list k)] #:unless (memq (car e) '(protocol must-close)) #:unless (api-ref t (cadr e)))
            `(unknown-api ,(car e) ,(cadr e)))
          (for/list ([ty (in-list (knowledge-must-close k))] #:unless (memq ty datatypes))
            `(unknown-type must-close ,ty))))
       ;; a protocol calling an API no table has: a problem (a wrong name, an entry
       ;; lost), unless the extraction left the API out for a reason it recorded
       ;; (left-out.rktd: a closure parameter, a type it cannot write); then the
       ;; protocol is not generated, a limit of the tables, noted and not a problem
       (define reasons (left-out-reasons auto))
       (define-values (outside left)
         (for/fold ([out '()] [lo '()] #:result (values (reverse out) (reverse lo)))
                   ([p (in-list (knowledge-protocols k))])
           (define missing (filter (lambda (a) (not (in-some-table? a))) (cadr p)))
           (define unexplained (filter (lambda (a) (not (hash-ref reasons a #f))) missing))
           (cond
             [(null? missing) (values out lo)]
             [(pair? unexplained) (values (cons `(protocol-outside ,(car p) ,unexplained) out) lo)]
             [else (values out (cons `(protocol-left-out ,(car p)
                                                         ,@(for/list ([a (in-list (remove-duplicates missing))])
                                                             (list a (hash-ref reasons a))))
                                     lo))])))
       (define ill (for*/list ([c (in-list (claim-clients t k))] [r (in-value (check-client t c))]
                               #:when (eq? (car r) 'ill-formed))
                     `(ill-formed-claim ,(cadr r))))
       ;; the texts of claims and assumptions, parsed (knowledge-text.rkt)
       (define texts (for/list ([e (in-list k)]
                                #:when (and (memq (car e) '(claim assume)) (api-ref t (cadr e)) (string? (caddr e))))
                       e))
       (define trees (parse-texts (env-program 'item-index) (map caddr texts)))
       (define bad (for*/list ([(e tree) (in-parallel texts trees)]
                               [ps (in-value (text-problems (api-ref t (cadr e)) tree))]
                               #:when (pair? ps))
                     `(bad-text ,(car e) ,(cadr e) ,(caddr e) ,@ps)))
       ;; claims that call a closed spec function: notes for judging them, not problems
       (define closed (for*/list ([(e tree) (in-parallel texts trees)]
                                  #:when (eq? (car e) 'claim)
                                  [cs (in-value (closed-uses t tree))]
                                  #:when (pair? cs))
                        `(uses-closed ,(cadr e) ,(caddr e) ,@cs)))
       `(knowledge ,m
                   (entries ,@(for/list ([kind (in-list '(role protocol claim assume must-close prefer limitation not-defect))])
                                (list kind (length (knowledge-entries k kind)))))
                   ,@(if (and (null? unknown) (null? outside) (null? ill) (null? bad)) '(ok) (append unknown outside ill bad))
                   ,@left
                   ,@closed
                   ,@(drift-facts auto m (build-path kdir f) k))])))
