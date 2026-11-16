(module "mm.frame")
(at "1111111")
(spec-digests
  (Frame::size "000000000000"))

;; A knowledge file for the drift tests (tests/golden.rkt): references into
;; tests/inputs/spec-v1.rs, read against spec-v2.rs, where five lines were
;; added at the top and `external_body` was removed from `size`.

(claim Frame::reference_count "ret == slot_own.ref_count()"
  (from (comment "tests/inputs/spec-v1.rs:2" "/// Gets the reference count of the frame.")
        (comment "tests/inputs/spec-v1.rs:4"))
  (why "the doc comment"))

(limitation Frame::size "external_body: the size is not verified"
  (from (comment "tests/inputs/spec-v1.rs:20" "#[verifier::external_body]"))
  (why "the attribute"))
