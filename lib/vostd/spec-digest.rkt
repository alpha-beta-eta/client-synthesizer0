#lang racket/base
;; Fingerprints of the APIs' specifications at a vostd commit (design.md 3.7).
;;
;; The fingerprint is of the source text, not of VIR (whose printing changes
;; with Verus, so that every fingerprint would change with it): the
;; function's doc comments and attributes above it (with `#[verus_spec(..)]`),
;; its signature, and the `requires`/`ensures` up to the body; for a method of
;; a trait impl, the same for the trait's declaration too, which carries the
;; specification.  Indentation and blank lines do not count.  So a changed
;; requires/ensures, a removed `external_body`, a changed doc comment change
;; it; a changed body does not.  VIR only locates the functions.
(require racket/file racket/list racket/string racket/match file/sha1
         "vir.rkt" "git.rkt")
(provide spec-digests spec-text)

(define vprefix "_VERUS_VERIFIED_")

;; spec-text : lines start end -> string
;; Lines are 1-based; start..end is the signature.  Upwards: doc comments
;; and attributes, counting brackets so that a `#[trigger]` inside
;; `#[verus_spec(..)]` does not end it (inside an attribute, every line is
;; taken; outside, a doc comment, the start of an attribute, or a line that
;; ends one).  Downwards: up to the line that opens the body (ends with `{`)
;; or ends a declaration without one (`;`).
(define (spec-text lines start end)
  (define (line i) (string-trim (vector-ref lines (sub1 i))))
  (define (depth l)                     ; closing minus opening brackets
    (for/sum ([c (in-string l)]) (case c [(#\] #\)) 1] [(#\[ #\() -1] [else 0])))
  (define top
    (let loop ([i (sub1 start)] [open 0])
      (cond [(< i 1) (add1 i)]
            [else
             (define l (line i))
             (define o (+ open (depth l)))
             (cond [(positive? open) (loop (sub1 i) (max o 0))]
                   [(or (string-prefix? l "///") (string-prefix? l "//!")) (loop (sub1 i) 0)]
                   [(string-prefix? l "#[") (loop (sub1 i) (max o 0))]
                   [(regexp-match? #rx"[])]$" l) (loop (sub1 i) (max o 0))]
                   [else (add1 i)])])))
  (define bottom
    (let loop ([i end])
      (cond [(> i (vector-length lines)) (vector-length lines)]
            [(regexp-match? #rx"[{;]$" (line i)) i]
            [else (loop (add1 i))])))
  (string-join (for/list ([i (in-range top (add1 bottom))] #:unless (equal? (line i) "")) (line i)) "\n"))

;; The span of a VIR item: (FILE START-LINE END-LINE) or #f.
(define (span-of x)
  (match (and (pair? x) (memq (car x) '(@ @@)) (string? (cadr x))
              (regexp-match #px"^(.*):([0-9]+):[0-9]+: ([0-9]+):[0-9]+ \\(#[0-9]+\\)$" (cadr x)))
    [(list _ _ a b) (list (car (span-file+line (cadr x))) (string->number a) (string->number b))]
    [_ #f]))

;; spec-digests : vir table-dir vostd commit -> ((commit C) (digest API HEX) ...)
;; One digest per table entry (with a (vir-path ..)) whose source is found;
;; sources are read with `git show COMMIT:path`, so the checkout may be at
;; another commit.
(define (spec-digests vir tdir vostd commit)
  (define items (load-vir vir))
  (define fns (for/list ([x (in-list items)] #:when (eq? (car (unwrap x)) 'Function)) x))
  (define by-path (for/hash ([f (in-list fns)]) (values (format "~a" (field (field f 'name) 'path)) f)))
  ;; The span's lines may be off (a VIR exported from a checkout with a
  ;; client module declared: one line more above, design.md 4.2): the
  ;; function is the nearest line with `fn NAME` to the span's start; a
  ;; generated function (`arrow_1`) has none, and the span is taken as it is.
  (define (text-of f)
    (define name (regexp-replace (regexp-quote vprefix)
                                 (last (string-split (format "~a" (field (field f 'name) 'path)) "::")) ""))
    (define rx (pregexp (format "\\bfn ~a\\b" (regexp-quote name))))
    (match (span-of f)
      [(list file a b)
       (define ls (git-lines vostd commit file))
       (define (at? j) (and ls (<= 1 j (vector-length ls)) (regexp-match? rx (vector-ref ls (sub1 j)))))
       (define at (or (for/first ([d (in-range 0 60)] #:when (or (at? (- a d)) (at? (+ a d))))
                        (if (at? (- a d)) (- a d) (+ a d)))
                      a))
       (and ls (<= (+ at (- b a)) (vector-length ls)) (spec-text ls at (+ at (- b a))))]
      [_ #f]))
  ;; the function and, for a trait impl's method, the trait's declaration
  (define (texts path)
    (define f (or (hash-ref by-path path #f)
                  (let ([s (string-split path "::")])
                    (hash-ref by-path (string-join (append (drop-right s 1) (list (string-append vprefix (last s)))) "::") #f))))
    (define k (and f (field f 'kind)))
    (define decl (match k
                   [(list 'FunctionKind 'TraitMethodImpl _ ...)
                    (hash-ref by-path (format "~a" (field (field k 'method) 'path)) #f)]
                   [_ #f]))
    (define ts (filter values (list (and f (text-of f)) (and decl (text-of decl)))))
    (and (pair? ts) (string-join ts "\n----\n")))
  (cons `(commit ,commit)
        (for*/list ([tf (in-list (sort (map path->string (directory-list tdir)) string<?))]
                    #:when (regexp-match? #rx"[.]rktd$" tf)
                    [e (in-list (file->list (build-path tdir tf)))]
                    #:when (and (pair? e) (eq? (car e) 'fn) (assq 'vir-path (cddr e)))
                    [t (in-value (texts (cadr (assq 'vir-path (cddr e)))))]
                    #:when t)
          `(digest ,(cadr e) ,(substring (sha1 (open-input-string t)) 0 12)))))
