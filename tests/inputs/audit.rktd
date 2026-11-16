;; Verdicts of tests/inputs/trusted-v1.rs, checked against trusted-v2.rs
;; (tests/golden.rkt, audit-check): one of each fact check-audit reports.

(audit (area "t") (report "t.md") (at "1111111") (scope "t.rs"))

;; changed: the ensures changed; its demo verified
(verdict "t#1" too-strong
 (site external-body "t.rs" "Frame::max_paddr" "" (fp "ba2e9e65143e"))
 (reason "r1")
 (demo "d.rs" "demo_max"))

;; unchanged: a comment and a blank line added
(verdict "t#2" faithful
 (site assume "t.rs" "Frame::eq" "self.ptr_inv()" (fp "568e365a66de"))
 (site assume "t.rs" "Frame::eq" "other.ptr_inv()" (fp "568e365a66de"))
 (reason "r2"))

;; renamed: the same text under the renamed trait
(verdict "t#3" faithful
 (site external-body "t.rs" "<Frame as NonNullPtr>::ALIGN_BITS" "" (fp "d9a60ce2b864"))
 (reason "r3"))

;; renamed, and its demo no longer verifies
(verdict "t#4" too-strong
 (site assume "t.rs" "<Frame as NonNullPtr>::into_raw" "self.inv()" (fp "d08d4f91a873"))
 (reason "r4")
 (demo "d.rs" "demo_forge"))

;; gone
(verdict "t#5" faithful
 (site external "t.rs" "<Frame as Send>" "" (fp "48a8cbfa3c86"))
 (reason "r5"))

;; an aspect does not disagree with the site's own verdict
(verdict "t#6" weak
 (site axiom "t.rs" "axiom_insert" "" (fp "7562c6098f8d"))
 (reason "r6"))
(verdict "t#7" too-strong
 (site axiom "t.rs" "axiom_insert" "" (fp "7562c6098f8d"))
 (reason "r7")
 (aspect usage))

;; disagree
(verdict "t#8" faithful
 (site assume-specification "t.rs" "[SmallVec::<A>::index]" "" (fp "7092fee1d88e"))
 (reason "r8"))
(verdict "t#9" weak
 (site assume-specification "t.rs" "[SmallVec::<A>::index]" "" (fp "7092fee1d88e"))
 (reason "r9"))

;; the second admit is unjudged
(verdict "t#10" faithful
 (site admit "t.rs" "wait" "" (fp "f1c4ea85bc69"))
 (reason "r10"))

;; removed: not checked
(verdict "t#11" weak
 (site external-body "t.rs" "raw_as_ref" "" (fp "000000000000"))
 (reason "r11")
 (removed "2222222" "verified now"))
