# Specification defects in vostd at eb1a9d044: the `cpu`, `util`, `boot` and `task` modules

This report extends [defects-eb1a9d044.md](defects-eb1a9d044.md) (the `mm` and `sync` modules, R1–R98) to the
other parts of `ostd` that vostd has verified specifications for: `cpu` (`CpuId`, `CpuSet`, `AtomicCpuSet`),
`util` (`RangeAllocator`, `range_difference`, `Either`), `boot` (`MemoryRegion`, `MemoryRegionArray`) and
`task` (`AtomicCpuId`, `disable_preempt`, the atomic-mode guards). Same commit (`eb1a9d044`, Verus
`0.2026.11.20.5ef50d5`), same method and same definition of a defect: a generated client, which calls the
public API the way a real caller in another module does, cannot be verified; a change to the **specification
only** makes it verify; the changed functions still verify, and all changes together leave `ostd` at 0 errors
(1650 verified). Whether callers need the fact is a judgement.

`arch`, `trap`, `timer` and the rest of `ostd` were left out: `arch` is mostly hardware register encodings
spread over three architectures (only x86 is in the build), and the others have at most one `ensures`.

## Summary

| | |
|---|---|
| APIs in the tables | 92 (10 modules) |
| Clients | 194: 99 verified, 91 failed, 4 compile errors |
| Failure groups | 67 |
| **New defects** | **12 (R99–R110)**, all confirmed, in `util::either` and `boot::memory_region` |
| Choices for the maintainers | 2 causes in `cpu::set` (17 groups) |
| `ostd` with all new changes | 1650 verified, 0 errors |

Both defect families have one shape: **a fact is stated only through a spec function the caller cannot
unfold**. `#[verus_verify(dual_spec)]` without `open` makes the spec twin closed; for `Either` it also leaves the
exec functions with no ensures at all. A caller in another module then knows that `MemoryRegion::new(b, l, t)`
returns `Self::new(b, l, t)`, but not that its `base()` is `b`.

## New defects

All patches are in [`vostd-eval-notes/defects-2026-11-24/`](../../vostd-eval-notes/defects-2026-11-24/), one per
issue, and together in `all-confirmed-x1-eb1a9d044.patch`. Each verifies alone, and its failing groups go to 0.

### R99–R102. `Either::{left, right, is_left, is_right}` have no ensures

`ostd/src/util/either.rs`: the four methods are a bare `#[verus_verify(dual_spec)]`. That adds only
`when_used_as_spec`; the exec functions have no `ensures`, and the spec twins are closed. A caller learns
nothing from `left()` — not even that `Left(l).left() == Some(l)`. Upstream's xarray uses exactly these
(`child_node.left().unwrap()`, `.and_then(|e| e.right())`, `entry.is_right()`, in `kernel/libs/xarray`).

Fix: the pattern `MemoryRegionType::is_physical` already uses, for each of the four:

```diff
-    #[verus_verify(dual_spec)]
+    #[verus_verify(dual_spec, open)]
+    #[verus_spec(returns self.left())]
     /// Converts to the left value, if any.
     pub fn left(self) -> Option<L> {
```

### R103–R107. `MemoryRegion`'s constructors and getters say nothing a caller can read

`ostd/src/boot/memory_region.rs`: `new`, `base`, `len`, `end`, `typ` are bare `dual_spec`, so their spec twins
are closed; `framebuffer` and `module` return `Self::new(..)` through that closed `new`; and the type invariant
`base + len <= usize::MAX` is private. The fields are private, so the spec functions cannot be made `pub open`;
the fix is `ensures` on the exec functions, each proved inside the module.

The callers that need it are the boot parsers (`finish_memory_regions` upstream, `arch/x86/boot/mod.rs:94`;
`linux_boot`/`multiboot` in vostd): they push `MemoryRegion::new(..)`, `framebuffer(..)` and `module(..)`, and
must then prove `into_non_overlapping`'s requires, which are stated in `r.base()`, `r.len()` and `r.typ()`.
Consumers read the values back (`meta.rs`, the frame allocator, the io allocators).

- **R103** `new`: `ret.base() == base`, `ret.len() == len`, `ret.typ() == typ`, `ret.end() == base + len`.
- **R104** `framebuffer`: `ret.base() == fb.address`, `ret.len() == ((fb.width * fb.height * fb.bpp + 7) / 8) as usize`
  (the documented "rounded up to whole bytes"), `ret.typ() == MemoryRegionType::Framebuffer`.
- **R105** `module`: `ret.typ() == Reclaimable`, `ret.len() == bytes.len()`, `ret.base()` the physical address.
- **R106** `end`: `ret == self.base() + self.len()` (callers use both forms; `into_non_overlapping`'s own
  ensures mix them).
- **R107** `base`: `ret + self.len() <= usize::MAX`, the private type invariant (with `use_type_invariant` in
  the body), which a caller needs to compute `base()..end()`.

### R108–R110. `MemoryRegionArray`'s length bound and the shape of `into_non_overlapping`'s result

- **R108** `deref`: `ret@.len() <= LEN`. The type invariant `count <= LEN` is private and the view closed, so
  a caller holding an array it did not build cannot bound its length — and `push`'s ensures cover only
  `len < LEN` and `len == LEN`, so it cannot use the documented "on error, the set is unchanged" either.
  (Found by `provable` and `confirm` without a hand-written fix.)
- **R109** `into_non_overlapping`: the same `ret@.len() <= LEN` for its result.
- **R110** `into_non_overlapping`: every output region is page-aligned
  (`base() % PAGE_SIZE == 0 && len() % PAGE_SIZE == 0`), and `ret@[i - 1].end() == ret@[i].base()`. Today
  alignment is stated only through the closed `aligned` (which is also `is_partition`'s trigger), and
  contiguity as `base() + len()`, unrelated to the closed `end()`. The frame allocator asserts page alignment
  of every region; the io allocators walk `end()` against the next `base()`. The fix adds the two ensures and a
  proof block of two `assert forall`s at the return.

## Choices for the maintainers

Not counted as defects: no spec-only fix exists within a few proof lines.

- **`CpuSet::count` and `count_spec`** (7 groups). `count` returns the closed `count_spec()` (the sum of the
  words' popcounts), and nothing relates it to the view `self@`. So no caller outside the module knows the
  number of CPUs in any set — not after `new_empty`, `new_full`, `add`, `remove`, `clear` or `add_all`
  (upstream's `id_set.rs` doc example and ktests check exactly these). The fact `count_spec() == self@.len()`
  under `inv()` needs an induction over the words; the choice is an open `count_spec` defined from the view
  (with `count`'s loop re-proved), or a public lemma.
- **`AtomicCpuSet::load` does not give `ret.inv()`** (10 groups). Every `CpuSet` method used on a loaded set
  (`contains`, `remove`, `is_full`, ..., and `iter`) requires `inv()`, which `load` does not ensure; the TLB
  shootdown (`tlb.rs`), the RCU monitor (`is_full`) and the scheduler (`iter`) all do this. `AtomicCpuSet`
  has no ghost model of its words and `store` accepts sets without `inv()`, so no ensures can provide it.
  Options: a ghost model, `load` clearing the tail bits (a code change), or dropping `contains`'s `self.inv()`
  requires (its proof does not use it).

## Trusted code (audit)

Five trusted sites in these modules (none in `util` or `boot`), audited in `data/audit/cpu_task.md`:
four faithful; one **model mismatch**: `num_cpus` (`external_body`) is specified as the constant `cpu_count()`,
but reads `static mut NUM_CPUS`, which is 1 until `init_on_bsp` sets it, so the spec holds only for calls after
CPU initialization. Also noted: `disable_preempt` is `external_body` over an `unimplemented!()` stub, so every
proof through it holds only "if it returns".

## How this round was run

The tables were extracted from the same VIR as the previous report (`^ostd::(mm|sync|cpu|util|boot|task)`;
the 35 old tables unchanged). The call knowledge of the 10 new modules (149 entries: 65 claims, 35 protocols,
the rest roles, assumptions, limitations and not-defects) was written from vostd's comments and ktests and from upstream callers at `12374d133`, and checked against
the source (`knowledge`: all anchors found). One synthesizer fix was needed to scan them (a crate dependency's
`use` copied from `cpu/set.rs` collided with a prelude glob: `use ::smallvec::..`), and one to read Verus's
output (its summary line glued into an error's location line).

| step | result |
|---|---|
| clients | 194: 99 verified, 91 failed, 4 compile errors (generator gaps in cross-module protocols) |
| groups | 67; refuted 0; `provable` proved 4 clauses, `confirm` confirmed them alone |
| ensures checked by some client | 17 of 51 |
| judged | 19 defect groups (12 fixes, all confirmed), 17 for the maintainers (one already labelled a limitation), 31 otherwise (noise, not needed, by design, needs a lemma) |
| known issues regression | R1–R98 unchanged (58 present, 6 gone, 34 undetected); R99–R110 present |
