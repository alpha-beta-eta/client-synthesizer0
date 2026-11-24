#lang racket/base
;; The client module's imports beside the module (vostd/extract.rkt placement).
(require rackunit racket/file "../lib/vostd/extract.rkt")

(define root (make-temporary-file "cs-placement-~a" 'directory))
(define (put rel text)
  (define p (build-path root rel))
  (make-directory* (let-values ([(d _n _m) (split-path p)]) d))
  (display-to-file text p #:exists 'truncate))

(put "ostd/Cargo.toml" #<<EOF
[package]
name = "ostd"

[dependencies]
vstd = { path = "../vstd" }
vstd_extra = { path = "../vstd_extra" }
smallvec = "1"
align-ext = "0.1"

[target.x86_64-unknown-none.dependencies]
x86_64 = "0.14"

[dev-dependencies]
rand = "0.8"
EOF
     )
(put "ostd/src/cpu/mod.rs" "pub mod set;\n")
(put "ostd/src/cpu/set.rs" #<<EOF
use core::sync::atomic::AtomicU64;
use smallvec::SmallVec;
use align_ext::AlignExt;
use vstd_extra::ownership::Inv;
use super::CpuId;
pub struct CpuSet;
EOF
     )

;; the dependencies by the names the code uses, without vstd, vstd_extra and dev-dependencies
(check-equal? (sort (crate-dependencies root "ostd/src/cpu/set.rs") string<?)
              '("align_ext" "smallvec" "x86_64"))

;; a dependency's path starts at the root (`::smallvec`): beside the module,
;; vstd_extra's prelude brings in a `smallvec` module too (E0659); the rest verbatim
(define uses (cadr (assq 'uses (placement root "cpu::set" "ostd/src/cpu/set.rs"))))
(check-not-false (member "use ::smallvec::SmallVec;" uses))
(check-not-false (member "use ::align_ext::AlignExt;" uses))
(check-not-false (member "use core::sync::atomic::AtomicU64;" uses))
(check-not-false (member "use vstd_extra::ownership::Inv;" uses))
(check-not-false (member "use super::CpuId;" uses))
(check-false (member "use smallvec::SmallVec;" uses))

(delete-directory/files root)
