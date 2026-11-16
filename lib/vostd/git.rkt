#lang racket/base
;; Reading a vostd checkout through git: its commit, and a file at a commit.
(require racket/string racket/port racket/system racket/file)
(provide git-head git-lines same-commit? (rename-out [git git-program]))

;; git.exe only on Windows: under WSL the Windows PATH is appended, and its
;; git.exe cannot see the Linux file system (/root/..)
(define (git) (or (and (eq? (system-type) 'windows) (find-executable-path "git.exe"))
                  (find-executable-path "git")))
(define (path->string* p) (if (path? p) (path->string p) p))

;; git-head : dir -> "4ec330ec2", the checkout's HEAD, abbreviated
(define (git-head dir)
  (define h (string-trim (with-output-to-string (lambda () (system* (git) "-C" (path->string* dir) "rev-parse" "--short" "HEAD")))))
  (when (equal? h "") (error 'git-head "~a: no commit (is it a git checkout? which git: ~a)" dir (git)))
  h)

;; same-commit? : two abbreviations of possibly different lengths (never empty)
(define (same-commit? a b)
  (and (string? a) (string? b) (not (equal? a "")) (not (equal? b ""))
       (or (string-prefix? a b) (string-prefix? b a))))

;; git-lines : vostd commit-or-#f path -> (vector line ...) or #f
;; The file at the commit (`git show`), or in the working tree for #f;
;; carriage returns dropped (vostd's sources are CRLF).  Cached.
(define cache (make-hash))
(define (git-lines vostd commit path)
  (hash-ref! cache (list (path->string* vostd) commit path)
             (lambda ()
               (define text
                 (if commit
                     (let ([out (open-output-string)])
                       (and (parameterize ([current-output-port out] [current-error-port (open-output-nowhere)])
                              (system* (git) "-C" (path->string* vostd) "show" (format "~a:~a" commit path)))
                            (get-output-string out)))
                     (let ([f (build-path vostd path)]) (and (file-exists? f) (file->string f)))))
               (and text (list->vector (map (lambda (l) (string-trim l "\r" #:left? #f))
                                            (string-split text "\n" #:trim? #f)))))))
