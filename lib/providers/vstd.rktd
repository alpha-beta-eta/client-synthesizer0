;; Providers from vstd: proof functions that take a ghost value out of a
;; resource, which the generator calls when a tracked argument has no variable
;; to come from (design.md 3.3; lib/gen/enum.rkt, gen/families/chain.rkt and
;; protocol.rkt name them).  They belong to vstd, not to a vostd commit, so the
;; table has no (at ..).  `evaluate` and `knowledge` add it on top of each
;; module's table unless told to use another (providers FILE).

;; Option::tracked_unwrap: the tracked value inside a tracked Option
(fn Option::tracked_unwrap
  (mode proof)
  (method tracked_unwrap)
  (generics (T))
  (params (self tracked (Option T)))
  (ret T)
  (requires (is self Some)))
