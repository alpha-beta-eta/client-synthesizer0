#lang racket/base
;; The environment files (lib/base/env.rkt): paths relative to the file that
;; has them, the machine's file before the defaults, and a target's own vostd
;; and target-dir before the environment's.
(require racket/file rackunit "../lib/base/env.rkt")

(define dir (make-temporary-directory))
(define (write-file name text) (call-with-output-file (build-path dir name) (lambda (o) (write-string text o))))
(define (in-dir . ps) (path->string (simplify-path (apply build-path dir ps))))
(make-directory (build-path dir "m"))
(write-file "env.rktd" "(vostd \"work/vostd\") ; a comment\n(target-dir \"work/t\")\n(asterinas \"work/asterinas\")\n")
;; an absolute path (on every system) stays as it is
(define abs-t (path->string (simplify-path (build-path (find-system-path 'temp-dir) "cs-t"))))
(write-file "m/local.rktd" (format "(asterinas \"../elsewhere/asterinas\")\n(target-dir ~s)\n(verus-threads 16)\n" abs-t))

(parameterize ([current-env-files (list (build-path dir "m" "local.rktd") (build-path dir "env.rktd"))])
  (check-equal? (env-ref 'vostd) (in-dir "work" "vostd"))
  (check-equal? (env-ref 'asterinas) (in-dir "elsewhere" "asterinas"))
  (check-equal? (env-ref 'target-dir) abs-t)
  ;; a number is not a path
  (check-equal? (env-ref 'verus-threads) 16)
  (check-exn exn:fail? (lambda () (env-ref 'item-index)))
  (write-file "plain.rktd" "(package \"ostd\")\n")
  (write-file "own.rktd" "(package \"ostd\")\n(vostd \"X:/patched\")\n")
  (check-equal? (read-target (build-path dir "plain.rktd"))
                `((package "ostd") (vostd ,(in-dir "work" "vostd")) (target-dir ,(env-ref 'target-dir))))
  (check-equal? (read-target (build-path dir "own.rktd"))
                `((package "ostd") (vostd "X:/patched") (target-dir ,(env-ref 'target-dir)))))

(delete-directory/files dir)
