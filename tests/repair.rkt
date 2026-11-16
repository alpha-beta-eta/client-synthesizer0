#lang racket/base
;; Choosing the imports rustc suggests (analysis/repair.rkt).
(require rackunit "../lib/analysis/repair.rkt")

(define existing '("use vstd::prelude::*;" "use super::*;" "use vstd_extra::array_ptr;"))
;; through the client module, written through the client's own import of the module
(check-equal? (choose-uses existing '("use crate::mm::page_table::cs_clients::array_ptr::ArrayPtr;"))
              '("use vstd_extra::array_ptr::ArrayPtr;"))
;; through the client module with no such import: dropped
(check-equal? (choose-uses existing '("use crate::mm::page_table::cs_clients::other::X;")) '())
;; others as they are; two for the same name: neither
(check-equal? (choose-uses existing '("use crate::sync::SpinGuardian;")) '("use crate::sync::SpinGuardian;"))
(check-equal? (choose-uses existing '("use a::X;" "use b::X;")) '())
