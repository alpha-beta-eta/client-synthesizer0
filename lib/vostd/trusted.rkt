#lang racket/base
;; Trusted code in vostd (design.md 3.12, evaluation.md 9): every place Verus
;; takes on trust, with an identity that does not depend on line numbers, so
;; that a judgement of it (data/audit/verdicts/) follows it across commits.
;;
;;   (trusted KIND "FILE" "ITEM" "DETAIL" (line N) (fp "HEX"))
;;
;;   KIND    assume | admit                     a statement, in the function ITEM
;;           external-body | external           an attribute, on the item ITEM
;;           axiom | assume-specification       an item
;;   FILE    relative to the checkout, with `/`
;;   ITEM    the item's path in its file: impls as `Type` or `<Type as Trait>`,
;;           traits, modules and functions by name, joined by `::`
;;           (`<Frame as NonNullPtr>::into_raw`); an assume_specification as
;;           `[PATH]`
;;   DETAIL  for assume: the proposition, whitespace collapsed; else "".  When
;;           two sites would have the same (KIND FILE ITEM DETAIL), the later
;;           get "#2", "#3" appended to DETAIL.
;;   N       the line, for reading; not part of the identity
;;   fp      the fingerprint of what the judgement is about: the whole item
;;           (attributes, signature, specification, body) for attributes and
;;           items, the enclosing function for assume and admit; comments,
;;           the contents of string literals and whitespace do not count.
;;           A trait method's specification in the trait declaration is not
;;           part of the fingerprint of an impl's method.
;;
;; The source is read through a small lexer (comments, strings, characters
;; masked) and a scan of the braces; a block in a signature (`ensures match x
;; { .. }`) is told from a body by what follows its closing brace.
(require racket/list racket/match racket/string file/sha1 racket/port racket/system "git.rkt")
(provide trusted-sites scan-source mask-source default-trusted-dirs site-key)

(define default-trusted-dirs '("ostd" "verified_libs"))

;; ================================================================ lexing

(define (ident-char? c) (or (char-alphabetic? c) (char-numeric? c) (char=? c #\_)))

;; mask-source : string -> string of the same length: comments, the contents of
;; string literals and character literals replaced by spaces (newlines kept)
(define (mask-source text)
  (define n (string-length text))
  (define out (string-copy text))
  (define (at i) (if (< i n) (string-ref text i) #\nul))
  (define (blank! a b)
    (for ([i (in-range a (min b n))] #:unless (char=? (string-ref text i) #\newline))
      (string-set! out i #\space)))
  (let loop ([i 0])
    (when (< i n)
      (define c (at i))
      (cond
        [(and (char=? c #\/) (char=? (at (add1 i)) #\/))
         (define e (let l ([j i]) (if (or (>= j n) (char=? (at j) #\newline)) j (l (add1 j)))))
         (blank! i e) (loop e)]
        [(and (char=? c #\/) (char=? (at (add1 i)) #\*))
         (define e (let l ([j (+ i 2)] [d 1])
                     (cond [(>= j n) n]
                           [(and (char=? (at j) #\*) (char=? (at (add1 j)) #\/))
                            (if (= d 1) (+ j 2) (l (+ j 2) (sub1 d)))]
                           [(and (char=? (at j) #\/) (char=? (at (add1 j)) #\*)) (l (+ j 2) (add1 d))]
                           [else (l (add1 j) d)])))
         (blank! i e) (loop e)]
        ;; raw strings r"..", r#".."#, br".."
        [(and (char=? c #\r) (not (and (> i 0) (ident-char? (at (sub1 i))) (not (char=? (at (sub1 i)) #\b))))
              (regexp-match-positions #px"^r(#*)\"" text i))
         => (lambda (m)
              (define hashes (- (cdadr m) (caadr m)))
              (define close (string-append "\"" (make-string hashes #\#)))
              (define start (cdar m))
              (define e (let l ([j start])
                          (cond [(>= j n) n]
                                [(and (<= (+ j (string-length close)) n)
                                      (string=? (substring text j (+ j (string-length close))) close))
                                 j]
                                [else (l (add1 j))])))
              (blank! start e)
              (loop (+ e (string-length close))))]
        [(char=? c #\")
         (define e (let l ([j (add1 i)])
                     (cond [(>= j n) n] [(char=? (at j) #\\) (l (+ j 2))] [(char=? (at j) #\") j] [else (l (add1 j))])))
         (blank! (add1 i) e) (loop (add1 e))]
        [(char=? c #\')
         (match (regexp-match-positions #px"^'(?:\\\\(?:u\\{[0-9a-fA-F]+\\}|x[0-9a-fA-F]{2}|.)|[^\\\\'\n])'" text i)
           [(list (cons s e)) (blank! (add1 s) (sub1 e)) (loop e)]
           [_ (loop (add1 i))])]
        [else (loop (add1 i))])))
  out)

;; ================================================================ items

;; An item: its header (attributes, signature, specification) from hstart to
;; hend (the `{` or `;`), its end (after the `}` or `;`), and the items it is in.
(struct item (hstart hend end parents [label #:mutable]) #:transparent)

;; After a closing brace, these continue the header or expression it was in:
;; the brace closed a block inside a signature, an expression, a literal.
(define continuation-rx
  #px"^\\s*(?:[-,)\\]{;.?=&|^+*/<>!%:]|else\\b|as\\b|requires\\b|ensures\\b|recommends\\b|decreases\\b|returns\\b|via\\b|when\\b|opens_invariants\\b|no_unwind\\b|invariant\\b|default_ensures\\b)")

;; items-of : masked -> (item ...), labels set
(define (items-of m)
  (define n (string-length m))
  (define items '())
  (let loop ([i 0] [hstart 0] [stack '()] [frames '()])
    ;; stack: the open brackets ( [ {; frames: the open braces, (item-proto ...)
    (when (< i n)
      (define c (string-ref m i))
      (case c
        [(#\( #\[) (loop (add1 i) hstart (cons c stack) frames)]
        [(#\) #\]) (loop (add1 i) hstart (if (pair? stack) (cdr stack) stack) frames)]
        [(#\{)
         (define it (item hstart i #f (map car frames) #f))
         (loop (add1 i) (add1 i) (cons c stack) (cons (cons it hstart) frames))]
        [(#\})
         (cond
           [(null? frames) (loop (add1 i) (add1 i) (if (pair? stack) (cdr stack) stack) frames)]
           [else
            (define it (car (car frames)))
            (define continues? (regexp-match? continuation-rx m (add1 i)))
            (unless continues? (set! items (cons (struct-copy item it [end (add1 i)]) items)))
            (loop (add1 i) (if continues? (cdr (car frames)) (add1 i))
                  (if (pair? stack) (cdr stack) stack) (cdr frames))])]
        [(#\;)
         (cond
           [(and (pair? stack) (not (eqv? (car stack) #\{))) (loop (add1 i) hstart stack frames)]
           [else
            (set! items (cons (item hstart i (add1 i) (map car frames) #f) items))
            (loop (add1 i) (add1 i) stack frames)])]
        [else (loop (add1 i) hstart stack frames)])))
  ;; the parents were captured as the open items; the recorded copies have
  ;; ends, find them by their header
  (for ([it (in-list items)]) (set-item-label! it (label-of (substring m (item-hstart it) (item-hend it)))))
  (define by-header (for/hash ([it (in-list items)]) (values (cons (item-hstart it) (item-hend it)) it)))
  (for/list ([it (in-list (reverse items))])
    (struct-copy item it
                 [parents (filter values (for/list ([p (in-list (item-parents it))])
                                           (hash-ref by-header (cons (item-hstart p) (item-hend p)) #f)))])))

;; the text inside the bracket group that opens at s[open-end - 1]
(define (bracketed s open-end open close)
  (let l ([j open-end] [d 1])
    (cond [(>= j (string-length s)) (substring s open-end)]
          [(char=? (string-ref s j) open) (l (add1 j) (add1 d))]
          [(char=? (string-ref s j) close) (if (= d 1) (substring s open-end j) (l (add1 j) (sub1 d)))]
          [else (l (add1 j) d)])))

(define (collapse s) (string-normalize-spaces s))

;; strip-attributes : header -> header without leading attributes
(define (strip-attributes h)
  (let loop ([h (string-trim h)])
    (cond
      [(regexp-match-positions #px"^#!?\\[" h)
       => (lambda (p)
            (define e (let l ([j (cdar p)] [d 1])
                        (cond [(>= j (string-length h)) j]
                              [(char=? (string-ref h j) #\[) (l (add1 j) (add1 d))]
                              [(char=? (string-ref h j) #\]) (if (= d 1) (add1 j) (l (add1 j) (sub1 d)))]
                              [else (l (add1 j) d)])))
            (loop (string-trim (substring h e))))]
      [else h])))

;; remove-generics : string -> string without <..> groups (not `->`, `=>`)
(define (remove-generics s)
  (define o (open-output-string))
  (for/fold ([d 0] [prev #\space]) ([c (in-string s)])
    (cond [(and (char=? c #\<)) (values (add1 d) c)]
          [(and (char=? c #\>) (positive? d) (not (memv prev '(#\- #\=)))) (values (sub1 d) c)]
          [else (when (zero? d) (write-char c o)) (values d c)]))
  (collapse (get-output-string o)))

(define modifiers-rx
  #px"^(?:(?:pub(?:\\s*\\([^)]*\\))?|const|unsafe|async|extern(?:\\s+\"[^\"]*\")?|open|closed|spec|proof|exec|broadcast|axiom|uninterp|tracked|default|ghost)\\s+)*")

;; label-of : header -> (KIND . NAME) or #f, KIND = fn | impl | item
(define (label-of header)
  (define h (strip-attributes (collapse header)))
  (define after (substring h (cdar (regexp-match-positions modifiers-rx h))))
  (define after-pub (substring h (cdar (regexp-match-positions #px"^(?:pub(?:\\s*\\([^)]*\\))?\\s+)?" h))))
  (cond
    [(regexp-match #px"^(?:const|static)\\s+(?:mut\\s+)?([A-Za-z_][A-Za-z0-9_]*)\\s*:" after-pub)
     => (lambda (m) (cons 'item (cadr m)))]
    [(regexp-match #px"^fn\\s+(\\$?[A-Za-z_][A-Za-z0-9_]*)" after) => (lambda (m) (cons 'fn (cadr m)))]
    [(regexp-match? #px"^impl\\b" after)
     (define body (remove-generics (string-trim (substring after 4))))
     (define no-where (string-trim (car (regexp-split #px"\\bwhere\\b" body))))
     (match (regexp-match #px"^(.*?)\\s+for\\s+(.*)$" no-where)
       [(list _ tr ty) (cons 'impl (format "<~a as ~a>" (string-trim ty) (string-trim tr)))]
       [_ (cons 'impl no-where)])]
    [(regexp-match #px"^(?:trait|mod|struct|enum|union|const|static|type)\\s+(?:mut\\s+)?([A-Za-z_][A-Za-z0-9_]*)" after)
     => (lambda (m) (cons 'item (cadr m)))]
    [(regexp-match-positions #px"^assume_specification\\s*" after)
     => (lambda (p)
          (define s (substring after (cdar p)))
          ;; skip the generics, which may contain brackets (`I: SliceIndex<[T]>`)
          (define rest (if (regexp-match? #rx"^<" s)
                           (substring s (+ 2 (string-length (bracketed s 1 #\< #\>))))
                           s))
          (match (regexp-match-positions #px"^\\s*\\[" rest)
            [(list (cons _ e)) (cons 'item (string-append "[" (collapse (bracketed rest e #\[ #\])) "]"))]
            [_ #f]))]
    [else #f]))

(define (item-kind it) (and (item-label it) (car (item-label it))))
(define (item-name it) (and (item-label it) (cdr (item-label it))))

(define (path-of it)
  (string-join (filter values (append (map item-name (reverse (item-parents it))) (list (item-name it)))) "::"))

;; ================================================================ sites

(define (fingerprint m it)
  (substring (sha1 (open-input-string (collapse (substring m (item-hstart it) (item-end it))))) 0 12))

;; the item whose header contains position p (the innermost)
(define (item-with-header items p)
  (for/fold ([best #f]) ([it (in-list items)] #:when (and (<= (item-hstart it) p) (< p (item-hend it))))
    (if (or (not best) (> (item-hstart it) (item-hstart best))) it best)))

;; the innermost function whose body contains p (else the innermost item)
(define (enclosing items p)
  (define in (filter (lambda (it) (and (< (item-hend it) p) (< p (item-end it)))) items))
  (define (innermost l) (for/fold ([b #f]) ([it (in-list l)]) (if (or (not b) (> (item-hstart it) (item-hstart b))) it b)))
  (or (innermost (filter (lambda (it) (eq? (item-kind it) 'fn)) in)) (innermost in)))

(define (balanced-from m open)        ; m[open] is `(`: the text inside
  (let l ([j (add1 open)] [d 1])
    (cond [(>= j (string-length m)) (substring m (add1 open))]
          [(char=? (string-ref m j) #\() (l (add1 j) (add1 d))]
          [(char=? (string-ref m j) #\)) (if (= d 1) (substring m (add1 open) j) (l (add1 j) (sub1 d)))]
          [else (l (add1 j) d)])))

(define (line-at m p) (add1 (for/sum ([c (in-string m 0 p)]) (if (char=? c #\newline) 1 0))))

;; scan-source : FILE text -> (site ...), site = (KIND FILE ITEM DETAIL LINE FP)
(define (scan-source file text)
  (define m (mask-source (string-replace text "\r" "")))
  (define items (items-of m))
  (define (attr-sites)
    (for*/list ([p (in-list (regexp-match-positions* #px"#\\[" m))]
                [inside (in-value (let ([e (regexp-match-positions #px"\\]" m (cdr p))])
                                    (substring m (cdr p) (if e (caar e) (cdr p)))))]
                [kind (in-value (cond [(regexp-match? #px"\\bexternal_body\\b" inside) 'external-body]
                                      [(regexp-match? #px"^\\s*verifier\\s*(?:::\\s*external|\\(\\s*external\\s*\\))\\s*$" inside) 'external]
                                      [else #f]))]
                #:when kind
                [it (in-value (item-with-header items (car p)))]
                #:when it)
      (list kind it "" (car p))))
  (define (item-sites)
    (for*/list ([k (in-list '((axiom . #px"\\baxiom\\s+fn\\b") (assume-specification . #px"\\bassume_specification\\b")))]
                [p (in-list (regexp-match-positions* (cdr k) m))]
                [it (in-value (item-with-header items (car p)))]
                #:when it)
      (list (car k) it "" (car p))))
  (define (stmt-sites)
    (for*/list ([k (in-list '((assume . #px"\\bassume\\s*\\(") (admit . #px"\\badmit\\s*\\(")))]
                [p (in-list (regexp-match-positions* (cdr k) m))]
                [it (in-value (enclosing items (car p)))]
                #:unless (and it (regexp-match? #px"fn\\s+(?:assume|admit)\\s*$"
                                                (substring m (max 0 (- (car p) 20)) (car p)))))
      (define open (sub1 (cdr p)))
      (list (car k) it (if (eq? (car k) 'assume) (collapse (balanced-from m open)) "") (car p))))
  (define raw (sort (append (attr-sites) (item-sites) (stmt-sites)) < #:key cadddr))
  ;; an item marked twice by the same kind (external_body in two attributes) once
  (define unique (remove-duplicates raw (lambda (a b) (and (eq? (car a) (car b)) (memq (car a) '(external-body external axiom assume-specification))
                                                           (eq? (cadr a) (cadr b))))))
  (for/fold ([seen (hash)] [acc '()] #:result (reverse acc)) ([s (in-list unique)])
    (match-define (list kind it detail p) s)
    (define path (if it (path-of it) "?"))
    (define key (list kind path detail))
    (define k (add1 (hash-ref seen key 0)))
    (values (hash-set seen key k)
            (cons (list kind file path (if (= k 1) detail (string-trim (format "~a #~a" detail k))) (line-at m p)
                        (if it (fingerprint m it) "-"))
                  acc))))

;; ================================================================ a checkout

(define git git-program)
(define (path->string* p) (if (path? p) (path->string p) p))

;; the .rs files under the directories, at the commit (git ls-tree) or in the
;; working tree (#f; git ls-files, so untracked client modules are not read)
(define (rust-files vostd commit dirs)
  (define out
    (with-output-to-string
      (lambda ()
        (apply system* (git) "-C" (path->string* vostd)
               (append (if commit (list "ls-tree" "-r" "--name-only" commit "--") (list "ls-files" "--"))
                       dirs)))))
  (sort (filter (lambda (f) (regexp-match? #rx"[.]rs$" f)) (string-split out "\n")) string<?))

;; trusted-sites : vostd commit-or-#f [dirs] -> ((trusted KIND FILE ITEM DETAIL (line N) (fp HEX)) ...)
(define (trusted-sites vostd commit [dirs default-trusted-dirs])
  (append*
   (for/list ([f (in-list (rust-files vostd commit dirs))])
     (define lines (git-lines vostd commit f))
     (if lines
         (for/list ([s (in-list (scan-source f (string-join (vector->list lines) "\n")))])
           (match-define (list kind file path detail line fp) s)
           `(trusted ,kind ,file ,path ,detail (line ,line) (fp ,fp)))
         '()))))

;; site-key : (trusted ..) -> (KIND FILE ITEM DETAIL)
(define (site-key t) (take (cdr t) 4))
