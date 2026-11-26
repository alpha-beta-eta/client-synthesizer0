#lang racket/base
;; splice-meta (model/knowledge-drift.rkt) on a file with CR-LF line ends: the
;; (at ..) and (spec-digests ..) forms are found by their offsets, which must be
;; character offsets (a port counting lines counts CR-LF as one position, and
;; the splice landed one character early per line before the form, 2026-11-26),
;; and the file keeps its line ends.
(require rackunit racket/string racket/port "../lib/model/knowledge-drift.rkt")

(define lf (string-append
            "(module \"mm.heap.slot\")\n"
            "(at \"1111111\")\n"
            "(spec-digests\n  (a::f \"000000000000\"))\n"
            ";; a comment\n"
            "(claim a::f \"ret == 1\" (from (comment \"x.rs:3\" \"y\")) (why \"z\"))\n"))
(define (crlf s) (string-replace s "\n" "\r\n"))
(define digests '((a::f . "aaaaaaaaaaaa") (a::g . "bbbbbbbbbbbb")))

(define out-lf (splice-meta lf "2222222" digests))
(define out-crlf (splice-meta (crlf lf) "2222222" digests))
;; the same result, with the file's own line ends
(check-equal? out-crlf (crlf out-lf))
;; readable, and the new forms replaced the old ones
(define forms (with-input-from-string out-crlf (lambda () (for/list ([x (in-port read)]) x))))
(check-equal? (cadr (assq 'at forms)) "2222222")
(check-equal? (length (filter (lambda (f) (memq (car f) '(at spec-digests))) forms)) 2)
(check-equal? (car (list-ref forms 3)) 'claim)
