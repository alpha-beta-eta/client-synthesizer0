#lang racket/base
;; Repairing a table with rustc's suggestions (design.md, 结论36).
;;
;; `probe` the table; for the entries with compile errors, apply the
;; suggestions of the errors that are unambiguous and mechanical:
;;   - an import (`perhaps you want to import it`, `consider importing this
;;     struct ...`, one candidate only): the `use` line joins the table's uses,
;;     unless it would bring in a name another use line already brings in;
;;   - a missing bound (`consider restricting type parameter `P` with trait
;;     `B``, or `... where P: B`): B joins P's bounds in the entry.
;; The repairs go into an overlay table, (base TABLE) plus the changed uses and
;; entries, which is probed again, up to three rounds, until nothing changes.
;; A round with fewer `ok` entries than the one before (e.g. a use line that
;; breaks the module) is discarded.  Everything else is left to the LLM or a
;; person, who repairs the table in the same way: an overlay, then `probe`.
;;
;; Writes into OUT-DIR: probe-N/ (each round's run), table-N.rktd (the overlay
;; probed in round N, N >= 2), table.rktd (the last kept overlay, if any) and
;; probe.rktd (the facts of the last kept round).
(require racket/list racket/match racket/string racket/file racket/pretty
         "../model/api.rkt" "../base/forms.rkt" "probe.rkt")
(provide repair-table import-suggestion use-brings choose-uses)

(define rounds 3)

;; repair-table : target-file table-file out-dir -> (fact ...)
;; The probe facts of the last kept round, then (repaired (uses ..) (bounds ..)).
(define (repair-table target-file table-file out-dir)
  (make-directory* out-dir)
  (define base (path->string (path->complete-path table-file)))
  ;; the table as read, with its own (base ..) followed: the entries the overlay changes
  (define original (read-api-table table-file))
  ;; uses, bounds, paths: the repairs in file; prev: the round before, (list facts file uses bounds paths)
  (let loop ([n 1] [file table-file] [uses '()] [bounds (hash)] [paths (hash)] [prev #f])
    (define facts (probe-table target-file file (build-path out-dir (format "probe-~a" n))))
    (define (keep) (finish out-dir facts (and (> n 1) file) uses bounds paths))
    (cond
      [(and prev (< (count-ok facts) (count-ok (car prev))))
       (apply finish out-dir prev)]
      [else
       (define-values (uses* bounds* paths*) (suggestions facts (read-api-table table-file) uses bounds paths))
       (if (or (= n rounds) (and (equal? uses* uses) (equal? bounds* bounds) (equal? paths* paths)))
           (keep)
           (let ([next (build-path out-dir (format "table-~a.rktd" (add1 n)))])
             (write-overlay next base original uses* bounds* paths*)
             (loop (add1 n) next uses* bounds* paths* (list facts (and (> n 1) file) uses bounds paths))))])))

(define (count-ok facts) (count (lambda (f) (eq? (caddr f) 'ok)) facts))

(define (finish out-dir facts file uses bounds paths)
  (write-forms (build-path out-dir "probe.rktd") facts)
  (define kept (build-path out-dir "table.rktd"))
  (cond [file (copy-file file kept #t)]
        [(file-exists? kept) (delete-file kept)])
  (append facts
          `((repaired (uses ,@uses)
                      (bounds ,@(for/list ([k (in-list (sort (hash-keys bounds) symbol<?))])
                                  (cons k (hash-ref bounds k))))
                      (paths ,@(for/list ([k (in-list (sort (hash-keys paths) symbol<?))])
                                 (cons k (hash-ref paths k))))))))

;; suggestions : facts table uses bounds paths -> (values uses bounds paths)
;; uses: the use lines added so far; bounds: api name -> ((T BOUND ...) ...) added so far;
;; paths: api name -> ((OLD . NEW) ...), a path through a private module and its
;; public re-export (`crate::specs::mm::page_table::owners::INC_LEVELS` ->
;; `crate::specs::mm::page_table::INC_LEVELS`, E0603 with rustc's `consider
;; importing this .. through its public re-export instead`).
(define (suggestions facts table uses bounds paths)
  (define existing (api-table-uses table))
  (define-values (new-uses new-bounds new-paths)
    (for*/fold ([us '()] [bs bounds] [ps paths])
               ([f (in-list facts)] #:when (eq? (caddr f) 'compile-error)
                [e (in-list (cdddr f))] #:when (and (pair? e) (eq? (car e) 'error))
                [h (in-list (cddddr e))] #:when (and (pair? h) (eq? (car h) 'help)))
      (define api (api-ref table (cadr f)))
      (match (cdr h)
        [(list heading code ...)
         (cond
           [(import-suggestion heading code) => (lambda (u) (values (cons u us) bs ps))]
           [(and api (re-export-suggestion heading code (cadddr e) e))
            => (lambda (rw)
                 (values us bs (hash-update ps (cadr f) (lambda (old) (if (member rw old) old (append old (list rw)))) '())))]
           [(bound-suggestions heading code (cadddr e))
            => (lambda (pbs)
                 (values us
                         (for/fold ([bs bs]) ([pb (in-list pbs)]
                                              #:when (and api (assq (car pb) (api-generics api))
                                                          (not (member (cdr pb) (cdr (assq (car pb) (api-generics api)))))))
                           (hash-update bs (cadr f)
                                        (lambda (old)
                                          (define cur (cond [(assq (car pb) old) => cdr] [else '()]))
                                          (if (member (cdr pb) cur)
                                              old
                                              (cons (cons (car pb) (append cur (list (cdr pb))))
                                                    (filter (lambda (x) (not (eq? (car x) (car pb)))) old))))
                                        '()))
                         ps))]
           [else (values us bs ps)])]
        [_ (values us bs ps)])))
  (values (choose-uses existing (append uses (reverse new-uses))) new-bounds new-paths))

;; (OLD . NEW) or #f: for E0603 (a private module) with the suggestion to go
;; through the public re-export, given as the error's line rewritten: the
;; differing part of the two lines, widened to whole paths.
(define (re-export-suggestion heading code message e)
  (define t (assq 'text (filter pair? e)))
  (and (regexp-match? #px"^\\[E0603\\]" message)
       (regexp-match? #px"through its public re-export( instead)?$" heading)
       t (list? code) (= (length code) 1) (string? (car code))
       (not (regexp-match? #px"^\\s*use " (car code)))
       (path-rewrite (cadr t) (car code))))

(define (path-rewrite text code)
  (define a (regexp-replace #px",\\s*$" (string-trim text) ""))
  (define b (regexp-replace #px",\\s*$" (string-trim code) ""))
  (define la (string-length a)) (define lb (string-length b))
  (define pre (let loop ([i 0]) (if (and (< i la) (< i lb) (char=? (string-ref a i) (string-ref b i))) (loop (add1 i)) i)))
  (define suf (let loop ([i 0]) (if (and (< i (- la pre)) (< i (- lb pre))
                                         (char=? (string-ref a (- la 1 i)) (string-ref b (- lb 1 i))))
                                    (loop (add1 i)) i)))
  (define (path-char? c) (or (char-alphabetic? c) (char-numeric? c) (memv c '(#\_ #\:))))
  (define (widen s e str)
    (define s2 (let loop ([s s]) (if (and (> s 0) (path-char? (string-ref str (sub1 s)))) (loop (sub1 s)) s)))
    (define e2 (let loop ([e e]) (if (and (< e (string-length str)) (path-char? (string-ref str e))) (loop (add1 e)) e)))
    (substring str s2 e2))
  (define old (widen pre (- la suf) a))
  (define new (widen pre (- lb suf) b))
  (and (regexp-match? #px"^[A-Za-z0-9_]+(::[A-Za-z0-9_]+)+$" old)
       (regexp-match? #px"^[A-Za-z0-9_]+(::[A-Za-z0-9_]+)+$" new)
       (not (equal? old new))
       (cons old new)))

;; choose-uses : existing-lines candidate-lines -> lines
;; A use line is kept only when no other line brings in the same name.
;; A suggestion through the client module itself (`use crate::mm::page_table::
;; cs_clients::array_ptr::ArrayPtr;`: rustc suggests the shortest path, and
;; the client module imports `use vstd_extra::array_ptr;`) is valid only there,
;; while the table is used from other modules too: it is written through that
;; import (`use vstd_extra::array_ptr::ArrayPtr;`), or dropped.
(define (choose-uses existing candidates0)
  (define (through-client u)
    (match (regexp-match #px"^use [A-Za-z0-9_:]*::cs_clients::([A-Za-z0-9_]+)((?:::[A-Za-z0-9_]+)*);$" u)
      [(list _ first rest)
       (for/first ([e (in-list existing)]
                   #:when (regexp-match? (pregexp (format "^use [A-Za-z0-9_:]+::~a;$" first)) e))
         (format "~a~a;" (substring e 0 (sub1 (string-length e))) rest))]
      [_ u]))
  (define candidates (remove-duplicates (filter values (map through-client candidates0))))
  (define taken (filter values (map use-brings existing)))
  (for/list ([u (in-list candidates)]
             #:unless (or (member u existing)
                          (member (use-brings u) taken)
                          (> (count (lambda (v) (equal? (use-brings v) (use-brings u))) candidates) 1)))
    u))

;; The name a `use a::b::C;` line brings in (C), or #f for a glob.
(define (use-brings u) (let ([m (regexp-match #px"([A-Za-z0-9_]+);$" u)]) (and m (cadr m))))

;; A `use` line suggested as the fix, or #f.  Of several candidates, one from
;; this crate (it is what the surrounding code means, e.g. mm's `Infallible`),
;; else core, else alloc, else vstd; vstd's XImpl traits are used through X.
(define (import-suggestion heading code)
  (define uses (and (list? code) (pair? code)
                    (andmap (lambda (u) (regexp-match? #px"^use [A-Za-z0-9_:]+;$" u)) code)
                    code))
  (cond
    [(not uses) #f]
    [(regexp-match? #px"perhaps you want to import it$|^consider importing this [a-z ]+$|^consider importing this [a-z]+ through its public re-export$" heading)
     (and (= (length uses) 1) (car uses))]
    [(regexp-match? #px"^consider importing one of these [a-z]+( instead)?$|perhaps you want to import one of them$" heading)
     (define cands (filter (lambda (u) (not (member (regexp-replace #px"Impl;$" u ";") (remove u uses)))) uses))
     (for*/first ([prefix (in-list '("use crate::" "use core::" "use alloc::" "use vstd::"))]
                  [u (in-list cands)] #:when (string-prefix? u prefix))
       u)]
    [else #f]))

;; ((T . BOUND) ...) suggested as the fix, or #f.
(define (bound-suggestions heading code message)
  (cond
    ;; E0310: `the parameter type `M` may not live long enough`, `+ 'static`
    [(and (regexp-match? #px"^consider adding an explicit lifetime bound$" heading)
          (match code [(list (pregexp #px"^\\s*[:+]\\s*'static\\s*$")) #t] [_ #f])
          (regexp-match #px"the parameter type `([A-Za-z0-9_]+)` may not live long enough" message))
     => (lambda (m) (list (cons (string->symbol (cadr m)) 'static)))]
    [(regexp-match #px"^consider (?:further )?restricting type parameter `([A-Za-z0-9_]+)` with trait" heading)
     => (lambda (m)
          (match code
            [(list c) (let ([b (bound (regexp-replace #px"^\\s*[:+]\\s*" c ""))])
                        (and b (list (cons (string->symbol (cadr m)) b))))]
            [_ #f]))]
    [(regexp-match? #px"^consider restricting the type parameters? to satisfy the trait bounds?$" heading)
     (match code
       [(list c)
        (define clauses (regexp-match* #px"([A-Za-z0-9_]+): ([A-Za-z0-9_:<>, ]+?)(?=,\\s*[A-Za-z0-9_]+:|$)"
                                       (regexp-replace #px"^\\s*where\\s+" c "") #:match-select cdr))
        (define pbs (for/list ([cl (in-list clauses)])
                      (define b (bound (cadr cl)))
                      (and b (cons (string->symbol (car cl)) b))))
        (and (pair? pbs) (andmap values pbs) pbs)]
       [_ #f])]
    [else #f]))

;; "core::marker::Send" -> Send; "a::ValueInvariant<T>" -> (ValueInvariant T); else #f.
;; The trait is named by its last segment, as in the extracted tables; when that
;; is not in scope, the next round's error suggests the import.
(define (bound s)
  (match (regexp-match #px"^(?:[A-Za-z0-9_]+::)*([A-Za-z0-9_]+)(?:<([A-Za-z0-9_, ]+)>)?$" (string-trim s))
    [(list _ n #f) (string->symbol n)]
    [(list _ n args) `(,(string->symbol n) ,@(map (lambda (a) (string->symbol (string-trim a))) (string-split args ",")))]
    [_ #f]))

;; The overlay: (base TABLE), the added uses, and the entries with added bounds
;; or rewritten paths.
(define (write-overlay file base original uses bounds [paths (hash)])
  (define entries (for/hash ([n (in-list (table-names original))]) (values n (api-ref original n))))
  (call-with-output-file file #:exists 'truncate
    (lambda (o)
      (fprintf o ";; Repairs of ~a by rustc's suggestions (repair.rkt).\n" base)
      (pretty-write `(base ,base) o)
      (unless (null? uses) (pretty-write `(uses ,@uses) o))
      (for ([name (in-list (sort (remove-duplicates (append (hash-keys bounds) (hash-keys paths))) symbol<?))]
            #:when (hash-ref entries name #f))
        (pretty-write (rewrite-paths (add-bounds (hash-ref entries name) (hash-ref bounds name '()))
                                     (hash-ref paths name '()))
                      o)))))

;; Every symbol of the entry's requires that is OLD (a constant, a called
;; function, or such a name with a turbofish) becomes NEW.
(define (rewrite-paths entry rws)
  (define (sym s)
    (define t (symbol->string s))
    (or (for/or ([rw (in-list rws)])
          (cond [(equal? t (car rw)) (string->symbol (cdr rw))]
                [(string-prefix? t (string-append (car rw) "::<"))
                 (string->symbol (string-append (cdr rw) (substring t (string-length (car rw)))))]
                [else #f]))
        s))
  (define (walk x) (cond [(symbol? x) (sym x)] [(pair? x) (cons (walk (car x)) (walk (cdr x)))] [else x]))
  (if (null? rws)
      entry
      (for/list ([f (in-list entry)])
        (match f
          [`(,(and k (or (quote requires) (quote ensures))) ,es ...) `(,k ,@(map walk es))]
          [_ f]))))

(define (add-bounds entry add)
  (for/list ([f (in-list entry)])
    (match f
      [`(generics ,gs ...)
       `(generics ,@(for/list ([g (in-list gs)])
                      (cond [(assq (car g) add) => (lambda (a) (append g (cdr a)))]
                            [else g])))]
      [_ f])))
