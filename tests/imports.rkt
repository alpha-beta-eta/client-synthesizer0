#lang racket/base
;; Imports a run's table makes that rustc reports private (pipeline/evaluate.rkt).
(require rackunit racket/file "../lib/pipeline/module-run.rkt")

(define dir (make-temporary-file "cs-imports-~a" 'directory))
(display-lines-to-file
 '("use vstd::prelude::*;"
   "use super::page_table::*;"
   "use crate::mm::page_table::cursor::*;"
   "verus! {"
   "}")
 (build-path dir "clients.rs"))
(define forms
  '((base "a.rktd")
    (uses "use crate::mm::page_table::cursor::*;" "use crate::mm::frame::*;")))
(define (results . u) (append '((run) (verification none)) u))

;; E0603 at the table's own use line: taken out
(check-equal? (private-uses (results '(unattributed "[E0603] module `cursor` is private" "ostd/src/mm/cs_clients.rs:3"))
                            dir forms)
              '("use crate::mm::page_table::cursor::*;"))
;; at a line that is not the table's own (a base's, the placement's): kept
(check-equal? (private-uses (results '(unattributed "[E0603] module `x` is private" "ostd/src/mm/cs_clients.rs:2"))
                            dir forms)
              '())
;; another error at that line, or a line out of the file: nothing
(check-equal? (private-uses (results '(unattributed "[E0432] unresolved import" "ostd/src/mm/cs_clients.rs:3")) dir forms) '())
(check-equal? (private-uses (results '(unattributed "[E0603] module `x` is private" "ostd/src/mm/cs_clients.rs:99")) dir forms) '())

(check-equal? (without-uses forms '("use crate::mm::page_table::cursor::*;"))
              '((base "a.rktd") (uses "use crate::mm::frame::*;")))
(check-equal? (without-uses '((base "a.rktd") (uses "use a::*;")) '("use a::*;"))
              '((base "a.rktd")))
(check-equal? (without-uses forms '()) forms)

(delete-directory/files dir)
