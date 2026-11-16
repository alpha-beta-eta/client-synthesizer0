;; Where the checkout, the build cache, the helper programs and Asterinas are (lib/base/env.rkt).
;; Defaults; a machine's own paths go in env.local.rktd (not in git); the file CS_ENV names comes first.
;; Relative paths are relative to the file.  `racket cli.rkt env` checks them.
(vostd "work/vostd")                    ; vostd checkout (a git worktree at the tables' commit), tools/verus inside
(target-dir "work/t")                   ; Cargo's target directory for the runs
(item-index "work/bin/item-index")      ; verus_syn's item index (scan, extract); `.exe` is added on Windows
(asterinas "work/asterinas")            ; upstream Asterinas, read for call knowledge
(verus-bin "work/verus-bin/bin")        ; Verus installed by `CARGO_INSTALL_ROOT=work/verus-bin cargo dv bootstrap`
