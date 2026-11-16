#lang racket/base
;; Where the vostd checkout, Cargo's target directory, the helper programs and
;; the Asterinas repository are: nothing else in the repository names a path
;; outside it.
;;
;; env.rktd at the repository's root has the defaults (under work/); the
;; machine's own paths are in env.local.rktd next to it (not in git); the file
;; the variable CS_ENV names (another checkout, such as a patched one) comes
;; before both.  An entry in an earlier file wins.  Relative paths are
;; relative to the file that has them.
;;   (vostd DIR)          the vostd checkout clients are run in (a git worktree)
;;   (target-dir DIR)     Cargo's target directory for the runs
;;   (drops-target-dir DIR) Cargo's target directory for `drops`' copy of the
;;                        checkout (pipeline/drops.rkt); default target-dir + "-drops"
;;   (item-index EXE)     verus_syn's item index (vostd/extract.rkt)
;;   (asterinas DIR)      a clone of upstream Asterinas, read for call knowledge
;;                        (`upstream` sources cite FILE:LINE @COMMIT)
;;   (verus-bin DIR)      where `cargo dv bootstrap` installed Verus (cargo-verus,
;;                        verus, rust_verify) when run with CARGO_INSTALL_ROOT;
;;                        the runs give it as CARGO_VERUS_PATH and first on PATH.
;;                        Without it, or when it does not exist, the Verus on PATH
;;                        (~/.cargo/bin).
;;   (verus-threads N)    Verus's --num-threads for the runs (a number, not a path);
;;                        without it estimated from the memory (vostd/run.rkt).
;;
;; A target file (vostd/run.rkt) says where the client module goes in the
;; checkout; read-target adds vostd and target-dir from the environment unless
;; the target names its own.
(require racket/file racket/runtime-path)
(provide current-env-files env-files env-ref env-program verus-environment read-target)

(define-runtime-path default-file "../../env.rktd")
(define-runtime-path local-file "../../env.local.rktd")

;; CS_ENV, relative to the directory the command was started in: resolved
;; once, when this module is loaded.  Resolved later it was taken relative to
;; whatever the current directory was then (the checkout, inside run-verus),
;; and a relative CS_ENV failed only there (2026-11-11).
(define cs-env-file (let ([e (getenv "CS_ENV")]) (and e (path->complete-path e))))

;; the files in order, the first one's entries first
(define (env-files)
  (define e cs-env-file)
  (map simplify-path
       (append (if e (list e) '())
               (if (file-exists? local-file) (list local-file) '())
               (list default-file))))

(define current-env-files (make-parameter #f))

(define cache (make-hash))

(define (read-env file)
  (hash-ref! cache file
             (lambda ()
               (unless (file-exists? file) (error 'env "no environment file ~a" file))
               (define-values (dir _name _d) (split-path file))
               (for/list ([e (in-list (file->list file))])
                 (list (car e) (if (string? (cadr e))
                                   (path->string (simplify-path (path->complete-path (cadr e) dir)))
                                   (cadr e)))))))

;; the entries of the environment files, with the paths made complete
(define (env) (apply append (map read-env (or (current-env-files) (env-files)))))

;; env-ref : symbol [default] -> string (a path), or the entry's value when not a string
(define (env-ref key [default (lambda () (error 'env "~a: no ~a" (or (current-env-files) (env-files)) key))])
  (cond [(assq key (env)) => cadr]
        [(procedure? default) (default)]
        [else default]))

;; env-program : symbol -> string
;; A program's path; on Windows `.exe` is added when the entry does not name
;; an existing file but the entry with `.exe` does.
(define (env-program key)
  (define p (env-ref key))
  (define exe (string-append p ".exe"))
  (if (and (eq? (system-type) 'windows) (not (file-exists? p)) (file-exists? exe)) exe p))

;; verus-environment : environment-variables -> environment-variables
;; A copy with the project's Verus (verus-bin) as CARGO_VERUS_PATH and first
;; on PATH, when there is one.
(define (verus-environment base)
  (define e (environment-variables-copy base))
  (define bin (env-ref 'verus-bin #f))
  (when (and bin (directory-exists? bin))
    (environment-variables-set! e #"CARGO_VERUS_PATH" (string->bytes/utf-8 bin))
    (define path (or (environment-variables-ref e #"PATH") #""))
    (environment-variables-set! e #"PATH" (bytes-append (string->bytes/utf-8 bin)
                                                        (if (eq? (system-type) 'windows) #";" #":")
                                                        path)))
  e)

;; read-target : target-file -> ((key value) ...)
(define (read-target file)
  (define t (file->list file))
  (append t (for/list ([k (in-list '(vostd target-dir))] #:unless (assq k t))
              (list k (env-ref k)))))
