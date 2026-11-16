#lang racket/base
;; Is the environment (base/env.rkt) ready: the checkout at the tables' commit
;; and clean, its dv submodule and Verus, the helper programs, and the
;; Asterinas commits that call knowledge cites.  Facts, one per entry:
;;   (env-files FILE ...)
;;   (vostd DIR ok|missing (head H) (tables-at C ...) same|differs (changes N) (dv ok|missing) (tools/verus ok|missing))
;;   (verus VERSION (bin DIR|PATH))  the project's install (verus-bin) or the one on PATH
;;   (target-dir DIR ok|absent)        absent is fine: Cargo makes it
;;   (item-index EXE ok|missing)       needed by scan and extract only
;;   (asterinas DIR ok|missing (commits (C ok|missing) ...))
(require racket/file racket/list racket/string racket/port racket/system racket/runtime-path
         "../base/env.rkt" "../model/api.rkt" "../vostd/git.rkt"
         (only-in "evaluate.rkt" verus-version))
(provide check-env)

(define-runtime-path root "../..")

(define git git-program)
(define (git-ok? dir . args)
  (parameterize ([current-output-port (open-output-nowhere)] [current-error-port (open-output-nowhere)])
    (apply system* (git) "-C" dir args)))
(define (git-out dir . args)
  (with-output-to-string
    (lambda () (parameterize ([current-error-port (open-output-nowhere)]) (apply system* (git) "-C" dir args)))))

(define (rktd-files . dirs)
  (for*/list ([d (in-list dirs)] [p (in-value (build-path root d))] #:when (directory-exists? p)
              [f (in-list (directory-list p #:build? #t))]
              #:when (regexp-match? #rx"[.]rktd$" (path->string f)))
    f))

;; the commits the API tables record
(define (tables-at)
  (sort (remove-duplicates (append-map table-commits (rktd-files "data/auto/apis" "data/apis"))) string<?))

;; the Asterinas commits cited by `upstream` sources
(define (cited-commits)
  (sort (remove-duplicates
         (append* (for/list ([f (in-list (rktd-files "data/auto/knowledge"))])
                    (map cadr (regexp-match* #px"\\(upstream \"[^\"]*@([0-9a-f]{7,})" (file->string f)
                                             #:match-select values)))))
        string<?))

(define (check-env)
  (define vostd (env-ref 'vostd))
  (define v? (directory-exists? vostd))
  ;; not a git checkout: reported, not an error (git-head refuses an empty HEAD)
  (define head (and v? (with-handlers ([exn:fail? (lambda (e) 'none)]) (git-head vostd))))
  (define at (tables-at))
  (define ast (env-ref 'asterinas))
  (define a? (directory-exists? ast))
  (list
   `(env-files ,@(map path->string (env-files)))
   (if v?
       `(vostd ,vostd ok (head ,head) (tables-at ,@at)
               ,(cond [(null? at) 'no-tables] [(andmap (lambda (c) (same-commit? c head)) at) 'same] [else 'differs])
               (changes ,(length (filter (lambda (l) (not (string=? l "")))
                                         (string-split (git-out vostd "status" "--porcelain") "\n"))))
               (dv ,(if (file-exists? (build-path vostd "dv" "Cargo.toml")) 'ok 'missing))
               (tools/verus ,(if (directory-exists? (build-path vostd "tools" "verus" "source")) 'ok 'missing)))
       `(vostd ,vostd missing (tables-at ,@at)))
   `(verus ,(if v? (verus-version vostd) "unknown")
           (bin ,(let ([b (env-ref 'verus-bin #f)]) (if (and b (directory-exists? b)) b 'PATH))))
   `(target-dir ,(env-ref 'target-dir) ,(if (directory-exists? (env-ref 'target-dir)) 'ok 'absent))
   `(item-index ,(env-program 'item-index) ,(if (file-exists? (env-program 'item-index)) 'ok 'missing))
   `(asterinas ,ast ,(if a? 'ok 'missing)
               (commits ,@(for/list ([c (in-list (cited-commits))])
                            (list c (if (and a? (git-ok? ast "cat-file" "-e" (string-append c "^{commit}"))) 'ok 'missing)))))))
