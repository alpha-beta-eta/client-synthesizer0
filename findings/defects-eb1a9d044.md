# Specification defects in vostd at eb1a9d044, compared with 8e4b202d6

This report lists the specification defects that
[client-synthesizer0](../README.md) finds in the `mm` and `sync` modules of `ostd` at vostd commit
`eb1a9d044` (2026-11-19, Verus `0.2026.11.20.5ef50d5`, rustc 1.100.0), and compares them with the previous
report, [defects-8e4b202d6.md](defects-8e4b202d6.md) (90 entries, R1–R92).

What counts as a defect is the same as in the previous report: a generated client, which calls the public API
the way a real caller does, cannot be verified; a change to the **specification only** (ensures, loop
invariants, a few proof lines; no `assume`, `admit`, `external_body`, weakened `requires` or ensures on an
`external_body` function) makes it verify; the changed functions still verify, and all changes together leave
`ostd` at 0 errors (1650 verified). Whether callers need the fact is a judgement.

## Summary

| | 8e4b202d6 report | eb1a9d044 (this report) |
|---|---|---|
| Previously recorded issues | 92 (R1–R92; R36, R50 were not in the report) | **9 fixed upstream**, 3 partly fixed, 80 still present (below) |
| New defects | | **6** (R93–R98), all confirmed |
| Choices for the maintainers | listed | 12 groups with unchanged causes, plus 2 new |
| `ostd` with all new changes | 1527 verified, 0 errors | 1650 verified, 0 errors |

Upstream fixed most of the `VmReader`/`VmWriter` gaps (vostd #899, #924, #927), the `NonNullPtr` permission
relations (#897, #909) and `Mutex::lock` (#907). The new defects are all *frame conditions on the error
path*: an API that fails early, or a `Segment::slice` that touches only some slots, does not say that the rest of
`MetaRegionOwners` is unchanged, so after the call a caller can no longer use the frames it holds.

## The previous entries at eb1a9d044

Each previous issue has witness clients that are re-run on the new commit (`regress`). A witness that still
fails where it should means the issue is still there; one that passes means it was fixed. 34 witnesses no
longer type-check against the new signatures (`ReprPerm` removed, page-table `Cursor` lost its parameter `A`,
`VmSpace` lost its lifetime, `NonNullPtrRef` folded into `NonNullPtr`); for those, this round's own clients
are matched to the issue by the failing clause, and the source diff was read.

**Fixed upstream (9):**

| Entry | What changed upstream |
|---|---|
| R5 | `VmReader/VmWriter::cursor` now ensure `r == self.cursor` (#899) |
| R6 | `has_remain`/`has_avail` now ensure `r == remain() > 0` / `avail() > 0` |
| R7 | `limit` now states the exact new length |
| R10 | `collect` now ensures the buffer's length |
| R11 | fallible `read_val`/`write_val` now ensure `Err` when the buffer is too short |
| R64 | `Mutex::lock` now ensures `ret.rel_mutex(*self)` (#907) |
| R42 | `<Frame as NonNullPtr>::ref_rel_perm` now ties the `FrameRef` to the permission (#897) |
| R67 | `Either`'s `ref_rel_perm` is defined side-wise, as proposed (#909) |
| R71 | `Frame`'s `rel_perm` now includes the pointer and the metadata permission, as proposed (#897) |

R42, R67 and R71 were checked by reading the diff (their witnesses no longer compile and no client of this
round fails at those clauses); the other six by their witnesses passing.

**Partly fixed (3):** R1 (the views are now exported by `read`, `write`, `read_val`, `write_val`, but not by
`write_once`), R3 (Ok-when-it-fits now ensured by the infallible `read_val`/`write_val`, not by `write_once`),
R9 (`n == min(..)` now ensured by `read_fallible`/`write_fallible`; `write_val`/`read_val` still do not export
the full advance).

**Still present, the witness still fails (49):** R2, R4, R8, R16, R36, R37, R38, R39, R40, R41, R43, R44,
R45, R46, R47, R48, R49, R50, R51, R52, R53, R54, R55, R56, R57, R58, R61, R62, R63, R65, R66, R68, R69, R72,
R73, R74, R75, R77, R79, R81, R82, R83, R84, R86, R87, R88, R89, R91, R92. The fixes in the previous report
still describe them; line numbers moved.

**Still present by this round's clients, witness needs rewriting (31):** R12–R15, R17–R35, R59, R60, R70,
R76, R78, R80, R85, R90. Clients generated at eb1a9d044 fail at the same clauses (for example R17:
`VmSpace::cursor`/`cursor_mut` still ensure only `c.inv()`; R31/R32: `UniqueFrame::from_unused`/`repurpose`
still do not forward `in_list_perm`/`inv()`; R12–R14: the page-table cursor wrappers still drop
`find_next_impl`'s, `jump`'s and `query`'s frame facts). They were not re-confirmed by a fix on this commit.

## New defects

### R93. `VmReader::skip_in_place` does not give back `owner.mem_view is Some`

`skip_in_place` requires `old(owner).mem_view is Some`; its body only calls `owner.advance`, which keeps the
view, but the ensures say only `read_view_initialized() ==> read_view_initialized()`. A caller holding a
reader whose view is not initialized cannot call `skip_in_place` twice under its own requires.

Failing client: `skip_in_place(n); skip_in_place(m);` fails at
`assert((owner.mem_view is Some)); // requires of skip_in_place` (clause 3).

```diff
--- a/ostd/src/mm/io.rs
+++ b/ostd/src/mm/io.rs
@@ -1685,6 +1685,7 @@
             final(owner).inv(),
             final(self).wf(*final(owner)),
             old(owner).read_view_initialized() ==> final(owner).read_view_initialized(),
+            final(owner).mem_view is Some,
             final(self).cursor.vaddr == old(self).cursor.vaddr + nbytes,
```

Evidence: verifies alone; the failing group goes from 1 client to 0.

### R94. `Segment::slice` gives no frame condition on the other slot owners

`slice` increments the reference counts of the sliced frames only, but its ensures do not say that the slot
owners outside the slice are unchanged, so a caller holding other frames (or the rest of the segment) loses all
facts about them. This is the pattern of R74 (`Segment::drop`/`clone`), which upstream has not changed either.

Failing clients: two claims on `slice`, "slot owners outside `[start, end)` are unchanged" and "slot owners
other than the bumped indices are unchanged".

Fix: [R94.patch](../../vostd-eval-notes/defects-2026-11-22/R94.patch) (two ensures, the same two facts as loop
invariants of the bump loop, two assertions in the loop body tying `frame_to_index(paddr)` to the bumped index,
and a proof block after the loop converting the loop's index form to the ensures' form). Verifies alone; both
groups go from 1 to 0.

### R95–R98. The page-table cursor's failed calls do not say that `regions` is unchanged

`Cursor::jump`, `Cursor::query`, `Cursor::find_next`, `CursorMut::take_next` (and the `CursorMut` and
`VmSpace` wrappers of them) return `Err`/`None` without touching `MetaRegionOwners` — `jump` and `query` from an
early range check, `find_next`/`take_next` when no split happened — but none of them says so. After a failed
call a caller cannot use a frame it holds (`clone_requires(*regions)`) or open another cursor
(`relates_owner(.., *regions)`). Last round the same fact was confirmed for cursor creation (R16).

Failing client (one of 30, all of the same shape):

```rust
fn goal_err_..._jump_..._clone_item<'a, C: PageTableConfig>(self_: &mut Cursor<'a, C>, mut va: usize,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>, Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>, item_g: &'a C::Item, Ghost(pa_g): Ghost<usize>)
    requires
        old(self_).invariants(*old(owner), *old(regions), *old(guards)),
        item_g.clone_requires(*old(regions)), ..
{
    proof { assume(!self_.jump_panic_condition(va)); } // no panic
    let mut r = self_.jump(va);
    if let Ok(mut x) = r {
    } else {
        assert(item_g.clone_requires(*regions)); // requires of Cursor::clone_item   <- fails
        let w_g = Cursor::<C>::clone_item(item_g);
    }
}
```

| Entry | Functions | Fix |
|---|---|---|
| R95 | `Cursor::jump`, `CursorMut::jump`, `VmSpace` `Cursor`/`CursorMut::jump` | `res is Err ==> *final(regions) == *old(regions)` in each ([R95.patch](../../vostd-eval-notes/defects-2026-11-22/R95.patch)) |
| R96 | `Cursor::query`, `CursorMut::query`, `VmSpace` `Cursor`/`CursorMut::query` | the same for `query` ([R96.patch](../../vostd-eval-notes/defects-2026-11-22/R96.patch)) |
| R97 | `find_next_impl`, `Cursor::find_next`, `CursorMut::find_next`, `VmSpace` `find_next` | a loop invariant in `find_next_impl` (`!split_happened ==>` slots and slot owners unchanged; the loop exits only with `va >= end`, and `split_happened ==> va < end`), its `res is None` ensures, and forwarding with an extensional-equality proof ([R97.patch](../../vostd-eval-notes/defects-2026-11-22/R97.patch)) |
| R98 | `CursorMut::take_next` | `res is None ==> *final(regions) == *old(regions)`, proved in the early `return None` branch from R97's `find_next_impl` facts ([R98.patch](../../vostd-eval-notes/defects-2026-11-22/R98.patch)) |

Evidence: the innermost fixes (`Cursor::jump`, `Cursor::query`, `find_next_impl`) verify alone; each wrapper
verifies together with the fix of the function it calls (`fixes` `with`, or alone over those fixes as a base).
With all of them `ostd` verifies with 0 errors, and 27 of the 30 failing clients pass; the other 3 fail after
`CursorMut::map` returns `Err`, which is not an early failure (see below). The groups these clients belong to
also contain clients that fail for their own reasons (a fresh cursor not tied to the owner), so the
confirmation here is per client, not per group.

All six changes together: [all-confirmed-eb1a9d044.patch](../../vostd-eval-notes/defects-2026-11-22/all-confirmed-eb1a9d044.patch).

## Choices for the maintainers

These need a change to trusted code, a model, or a proof budget; they are not counted as defects.

- **`UniqueFrame::transmute` / `repurpose`** (6 groups): the `external_body` `transmute`'s open
  `transmute_spec` (marked FIXME) does not give pointer equality, so a transmuted or repurposed frame cannot be
  shown to satisfy `ptr_inv()`/`inv()` (same as last round).
- **`Iterator::next` for the page-table `Cursor`** is `external_body` with `unimplemented!()` and no spec; after
  `next` the cursor invariants needed by `jump` are lost.
- **`lock_range` and `Cursor::new`**: "locks held before stay held" would rest on the `assume` that admits
  `lock_range`'s postconditions.
- **`dfs_mark_stray_and_unlock`** (`external_body`) ensures its result equals a ghost argument the caller
  chooses, which no requires ties to the subtree's mapping count.
- **`MappedItem::clone`** gives no well-formedness of the clone, so a cloned item cannot be converted to raw
  (`item_into_raw`) or mapped; the fact would come from `Frame::clone_ensures`.
- **New: `Segment::slice` / `Segment::clone` and `relate_regions`.** Both preserve `relate_regions` (only
  reference counts change, within bounds). For `clone` an ensures `self.relate_regions(new_perm)` with a loop
  invariant verifies; for `slice` both attempts (a per-slot loop invariant, and a smaller invariant with the
  rest proved after the loop) exceed `slice`'s default rlimit. Raising the rlimit is a choice.
- **New: `CursorMut::map` on `Err`** replaced an existing mapping, so "regions unchanged" does not hold; a
  precise frame condition needs new invariants through `map_loop`/`replace_cur_entry`.
- `take_next` and `VmSpace::CursorMut::unmap` now say they may panic for any `len >= page_size(2)`
  (`allowed_to_panic_if(len >= page_size(2))`), i.e. for every length of 2 MiB or more.

## Trusted code (audit)

22 trusted sites changed, 22 disappeared and 6 are new since 8e4b202d6. Removed upstream: the RCU read-token
`assume`s (#922, one was too strong), `<Frame as NonNullPtr>::into_raw`'s `assume(self.inv())` (too strong),
the paging-constants axiom `axiom_current_paging_consts_hardcoded` (too strong, #855), and several alignment
`assume`s now proved. No site became too strong. Still too strong: among others `Segment::from`'s
`assume(frame.inv())`, `arc_into_raw`/`arc_from_raw` (copyable `ArcPointsTo`), and the `Either` alignment
axiom (`lemma_align_bits_properties` has no `min >= 1` premise; with `Box<u8>` on both sides it proves
`false` from library types only). One disagreement between two existing judgements is unresolved
(`VirtPtr::write_volatile`).

## How this round was run

vostd `8e4b202d6` → `eb1a9d044` (48 commits), Verus `68d8005` → `5ef50d5`, Asterinas `dc583d659` →
`12374d133`. The tables were re-extracted from VIR (35 modules), the call knowledge of all 34 modules was
re-read against the new source and upstream (re-anchored, entries for constants and moved trait methods
rewritten or removed, 22 io claims removed because upstream now ensures them, 4 io protocols added from the new
ktests), and all families were regenerated:

| | 8e4b202d6 (r1 / r2) | eb1a9d044 (r3) |
|---|---|---|
| clients | 2961 / 2904 | 2867 |
| verified / failed / compile errors | 1462 / 1486 / 13 (r1), 1504 / 1387 / 13 (r2) | 1556 / 1283 / 28 |
| failure groups | 735 | 661 (186 new or re-judged) |
| ensures clauses checked by some client | | 255 of 948 |

The new vostd needed five fixes in the synthesizer (each its own commit with tests): Verus-generated
`clone_clause_autoderived` items, associated constants (in `impl`s and in traits), trait paths through the now
private `sync::rcu`, `rename-by-key` across changed generic arguments, and — the one that mattered most —
recognizing `allowed_to_panic_if(P)` (vostd #951) as a "may panic here" clause; before that fix every client
asserted these clauses instead of assuming `!P`, and 147 more clients now verify.
