# Specification defects in vostd, found by client synthesis

This document lists specification defects in [vostd](https://github.com/asterinas/vostd) found with
[client-synthesizer0](../README.md), at vostd commit `8e4b202d6` (Verus `0.2026.11.08.68d8005`), in the
`mm` and `sync` modules of `ostd`. There are 90 entries. Each says what fact a specification fails to
give, shows a client that cannot be verified because of it, and says how to change the specification so
that it can.

## What a "defect" here is

The tool generates *clients*: small verified functions that call the public API the way a real caller
does, under the API's own `requires` (and the caller-side assumptions recorded for the module, such as "the
reference count does not saturate"). A client asserts what it needs before each call (the callee's
`requires`, clause by clause) or what a function's documentation promises (a *claim*). When such an
assertion fails, the specification either does not give a fact that callers need, or the client asks for
something it should not.

An entry is listed here only when all of the following hold, checked mechanically:

1. A client fails to verify on the unchanged code (shown in each entry, with the failing assertion).
2. A change to the **specification only** (an `ensures` clause, `dual_spec` made `open`, a conjunct of an
   open spec function, or a few proof lines in a body: an `assert`, a lemma call, a loop invariant) makes
   it verify. No `assume`, `admit` or `external_body` is added, no `requires` is weakened, and no
   `external_body` function gets an `ensures`.
3. The changed function still verifies **on its own**: the change is applied alone (or together with the
   changes it builds on, which are named), and the whole `ostd` crate verifies with 0 errors.
4. All the changes in this document applied together: `ostd` verifies with 0 errors (1527 verified), and
   the clients of the failing groups pass (a client that only timed out is not counted as passing).

Whether callers *need* the fact is a judgement, not something the tool checks. We kept only facts that a
caller of the public API cannot obtain otherwise and that the function's body already establishes; you may
still judge some of them unnecessary.

## What is not here

- **Choices for the maintainers**: failures whose fix would change a trusted specification
  (`external_body`, an axiom, an `assume`), add a `requires` to a public API, or change the model (for
  example `UniqueFrame::transmute`'s `transmute_spec`, the TLB model, `MappedItem::clone` in `kspace`).
- Candidates whose proposed change did not verify, or whose clients still fail with it.
- Failures that are the client's own fault (the generator's), which we reviewed and set aside.

## How to read an entry

- **How to fix**: a diff against `8e4b202d6`, in the document's text (no patch file). Line numbers are
  those of `8e4b202d6`.
- **A client that fails**: the generated client, as it was verified (`cs_clients` is a sibling module of
  the one under test, so it sees only what any other module sees). `// requires of F` marks an assertion
  of `F`'s requires before calling it; `// claim` marks a documented property. The tool's own checks
  that a path is not vacuous (`assert(false)` at the ends of paths) are left out here.
- **Evidence**: whether the change verifies alone, or together with the changes it builds on (linked;
  those that are not entries themselves are in the appendix), and how many failing clients pass with it.
- **Note**: what to look at before taking the change: an existing `assume` the changed function's proof
  rests on, or a part of the change that is not a specification (a verifier attribute).
- **Upstream**: vostd `main` has moved since `8e4b202d6`. Where the changed code is no longer the same in
  `main`, the entry says so; the defect may have been addressed there (we did not check).

Several entries are about the same pattern, for example a function that hands back an owner or a cursor
but does not say that what the caller already knew about it still holds (a *frame condition*), or a wrapper
that does not pass on what the function it wraps now ensures.

## Index

| Issue | Where | The missing fact |
|---|---|---|
| [R57](#r57) | `mm/dma/dma_coherent.rs` | The public DmaCoherent::reader and DmaStream::reader drop reader_perm@.read_view_initialized(), which reader_inner ensures and DmaStreamSlice::reader exports. |
| [R58](#r58) | `mm/dma/dma_coherent.rs` | The public DmaCoherent::writer and DmaStream::writer drop the kernel-range bounds of the cursor, which writer_inner ensures and the sibling reader() forwards. |
| [R75](#r75) | `mm/dma/dma_coherent.rs` | The public DmaCoherent::nbytes and DmaStream::nbytes ensure nothing about their result, although nbytes_inner returns segment.size() == end_paddr() - start_padd… |
| [R82](#r82) | `mm/dma/dma_stream.rs` | DmaStream::read_inner_vmio and write_inner_vmio always return Err and never change their writer/reader (their bodies only call avail/remain), but ensure the Err… |
| [R83](#r83) | `mm/dma/dma_stream.rs` | DmaStream::reader does not say its reader's length is page-aligned, although reader_inner creates it with from_kernel_space(ptr, segment.size()) and the inner i… |
| [R41](#r41) | `mm/frame/frame_ref.rs` | FrameRef::deref proves the type invariant inner@.ptr_inv() with use_type_invariant but its ensures exposes only the closed view, so ptr_inv() of the dereference… |
| [R42](#r42) | `mm/frame/frame_ref.rs` | NonNullPtr::raw_as_ref for Frame builds the FrameRef at raw (equal to permission.slot_perm.ptr() by ptr_perm_match) with permission.slot_perm and Some(&permissi… |
| [R71](#r71) | `mm/frame/frame_ref.rs` | NonNullPtr::from_raw for Frame sets ptr from raw (tied to perm.slot_perm.ptr() by ptr_perm_match) and stores Some(perm.metadata_perm), but the trait ensures onl… |
| [R43](#r43) | `mm/frame/linked_list.rs` | LinkedList::contains calls lazy_get_id, which ensures size/front/back are unchanged, a minted id is kept and the id is non-zero, but contains forwards none of i… |
| [R44](#r44) | `mm/frame/linked_list.rs` | take_current ensures final(regions) == old(regions).insert_slot_owner(paddr, ..) at the taken slot, but pop_front and pop_back forward no frame condition, so al… |
| [R45](#r45) | `mm/frame/linked_list.rs` | CursorMut::current_meta only borrows regions.slots immutably and keeps the cursor, yet ensures neither final(regions) == old(regions), final(regions).inv(), nor… |
| [R46](#r46) | `mm/frame/linked_list.rs` | CursorMut::current_meta returns a borrow of the current link's meta but does not say it equals meta_value_at of the current index, so the caller cannot read the… |
| [R47](#r47) | `mm/frame/linked_list.rs` | Link::deref and Link::deref_mut return a reference to self.meta but have no ensures; ensure the referent is self.meta. |
| [R48](#r48) | `mm/frame/linked_list.rs` | Link::new builds a Link with the given meta and no next/prev but has no ensures; ensure those fields. |
| [R72](#r72) | `mm/frame/linked_list.rs` | CursorMut::as_list returns self.list but has no ensures, so the returned list is unknown; ensure it is the list's value at entry (self.list is a &mut field, so … |
| [R73](#r73) | `mm/frame/linked_list.rs` | CursorMut::move_prev, like move_next (list-10), only assigns self.current but does not ensure the list reference is unchanged; ensure it. |
| [R81](#r81) | `mm/frame/linked_list.rs` | Default::default for LinkedList returns Self::new(), whose fields are now ensured (list-4), but default itself has no ensures, so the empty list's fields are lo… |
| [R88](#r88) | `mm/frame/linked_list.rs` | CursorMut::insert_before changes regions only at the inserted frame's slot owner (the in_list store); slots are only borrowed immutably and the neighbours' link… |
| [R85](#r85) | `mm/frame/meta.rs` | MetaSlot::get_from_unused fails only when get_slot rejects the paddr (iff !valid_frame_paddr) or the CAS from REF_COUNT_UNUSED fails (iff the old ref count diff… |
| [R51](#r51) | `mm/frame/mod.rs` | Frame::into_raw ensures raw_permission.inv() and r == start_paddr_spec() but not raw_permission.slot_vaddr() == frame_to_meta(r), which Frame::from_raw requires… |
| [R52](#r52) | `mm/frame/segment.rs` | Segment::into_raw ensures raw_perms@ == self.raw_perms() only, and with size()/start_paddr()/end_paddr() closed the length, alignment, bounds and per-frame slot… |
| [R53](#r53) | `mm/frame/segment.rs` | Segment::split ensures only (r.0, r.1) == split_spec(offset) with split_spec closed, so callers get neither the halves' inv() (proved alone by provable) nor the… |
| [R54](#r54) | `mm/frame/segment.rs` | Segment::split (closed split_spec) does not say the halves keep self's relation to a region, which holds since they take self's permissions [..k] and [k..] over… |
| [R55](#r55) | `mm/frame/segment.rs` | Segment::from(Frame) is specified only by the closed from_spec, so the one-frame segment has no visible inv() or range; the impl gets ensures r.inv() and its ra… |
| [R56](#r56) | `mm/frame/segment.rs` | Segment::next has only the Iterator spec through the closed remaining(), so callers learn nothing about the yielded frame, the advanced start or self.inv() afte… |
| [R74](#r74) | `mm/frame/segment.rs` | Segment::drop/clone give no frame condition on the slot owners outside the segment's frames, though each Frame::drop / inc_frame_ref_count underneath changes on… |
| [R86](#r86) | `mm/frame/segment.rs` | Segment::clone does not say that each of its frames' ref counts rose by exactly one, though each inc_frame_ref_count step ensures +1 for its own slot (inc_frame… |
| [R87](#r87) | `mm/frame/segment.rs` | Segment::drop ensures only regions.inv() and frame conditions, though each Frame::drop in its loop ensures rc > 1 ==> rc - 1 for its own slot and changes no oth… |
| [R29](#r29) | `mm/frame/unique.rs` | UniqueFrame::from_unused builds its owner with repr_perm Some and slot_index = frame_to_index(paddr) of a valid frame, but does not export owner.inv(), which ev… |
| [R30](#r30) | `mm/frame/unique.rs` | UniqueFrame::from_unused drops the frame condition that MetaSlot::get_from_unused gives (final == old.insert_slot_owner(paddr, ..), slots untouched), so callers… |
| [R31](#r31) | `mm/frame/unique.rs` | MetaSlot::get_from_unused leaves the claimed slot with in_list_perm.value() == 0, but UniqueFrame::from_unused does not forward it (nor owner.slot_index == fram… |
| [R32](#r32) | `mm/frame/unique.rs` | UniqueFrame::repurpose builds new_owner with repr_perm Some and the old valid slot index but does not export new_owner.inv(), which every later UniqueFrame oper… |
| [R33](#r33) | `mm/frame/unique.rs` | UniqueFrame::repurpose mutably borrows only slot_owners[idx] (and never slots), but does not ensure the other slot_owners and the slots are unchanged. |
| [R34](#r34) | `mm/frame/unique.rs` | UniqueFrame::repurpose does not relate its result to self although transmute_spec gives the same slot_vaddr and new_owner.slot_index is meta_to_index(self.slot_… |
| [R35](#r35) | `mm/frame/unique.rs` | UniqueFrame::reset_as_unused only touches the slot owner at owner.slot_index (like its sibling drop, which ensures this) but does not ensure slots and the other… |
| [R37](#r37) | `mm/frame/unique.rs` | Frame::from_unique mutably borrows only slot_owners[idx] with idx == owner.slot_index but ensures only that slots and the slot_owners domain are unchanged, not … |
| [R38](#r38) | `mm/frame/unique.rs` | Frame::from_unique stores ref_count 1 and leaves usage untouched, but does not export either, so the new Frame fails Frame::clone's clone_requires (ref_count > … |
| [R39](#r39) | `mm/frame/unique.rs` | Frame::from_unique builds the Frame from unique.ptr but does not ensure res.ptr == unique.ptr, so a caller does not know the shared frame is the same page. |
| [R40](#r40) | `mm/frame/unique.rs` | UniqueFrame::try_from_shared says nothing about its result: on Ok the CAS set ref_count to REF_COUNT_UNIQUE and the frame's pointer and recombined full metadata… |
| [R84](#r84) | `mm/frame/unique.rs` | UniqueFrame::try_from_shared does not say when it succeeds, though its CAS on the slot's ref_count_perm (vstd compare_exchange) yields Ok exactly when the old r… |
| [R49](#r49) | `mm/frame/untyped.rs` | Segment::reader and Segment::writer get read_view_initialized()/has_write_view() of the owner from VmReader/VmWriter::from_kernel_space but do not ensure them; … |
| [R1](#r1) | `mm/io.rs` | VmReader::read restores both owners' views (advance keeps the initialized ReadView, split keeps the WriteView) but does not export final(owner_r).read_view_init… |
| [R2](#r2) | `mm/io.rs` | VmReader::read only moves the two cursors but does not export that end and ghost_id of reader and writer are unchanged, so write, read_val and write_val (which … |
| [R3](#r3) | `mm/io.rs` | The infallible write_val, write_once and read_val return Err only when the buffer is shorter than size_of::<T>(), but unlike read_once they do not export that e… |
| [R4](#r4) | `mm/io.rs` | Clone for VmReader copies cursor, end and ghost_id but has no ensures, so a clone is not known to equal the original or to satisfy inv(). |
| [R5](#r5) | `mm/io.rs` | VmReader::cursor (and VmWriter::cursor) return self.cursor but have no ensures saying so. |
| [R6](#r6) | `mm/io.rs` | VmReader::has_remain and VmWriter::has_avail return remain() > 0 / avail() > 0 but have no ensures relating the result to remain_spec/avail_spec. |
| [R7](#r7) | `mm/io.rs` | VmReader::limit and VmWriter::limit set the length to exactly min(old length, max) but ensure only upper bounds. |
| [R8](#r8) | `mm/io.rs` | VmWriter::fill_zeros returns Ok(min(len, avail)) (Ok(0) when that is 0) but ensures only n <= len and n <= avail. |
| [R9](#r9) | `mm/io.rs` | read_fallible returns Ok only after copying the whole min(remain, avail) (a shorter copy is Err) but ensures only n <= remain and n <= avail on Ok, so write_fal… |
| [R10](#r10) | `mm/io.rs` | VmReader::collect allocates a buffer of remain() bytes and returns it on Ok but does not export its length. |
| [R11](#r11) | `mm/io.rs` | The fallible read_val and write_val return Err(InvalidArgs) when the buffer is shorter than size_of::<T>() (documented) but do not export it. |
| [R21](#r21) | `mm/io.rs` | VmReader::from_user_space builds its VmIoOwner with is_fallible true but does not ensure it, and VmSpace::reader does not export remain() == len or the owner's … |
| [R89](#r89) | `mm/io.rs` | VmReader::from_kernel_space builds its owner with is_fallible: false but does not ensure !owner@.is_fallible (VmWriter's version does), so Segment::reader canno… |
| [R92](#r92) | `mm/io.rs` | VmReader/VmWriter limit and skip return the reborrowed self but state their facts only on the returned reference r, not that *final(r) == *final(self), so after… |
| [R76](#r76) | `mm/kspace/kvirt_area.rs` | KVirtArea::map_untracked_frames (like map_frames, fixed by misc-4) gets range.end - range.start == area_size from kvirt_alloc_range_bounds before its loop and n… |
| [R62](#r62) | `mm/page_prop.rs` | PageProperty::new_user/new_absent return only their closed dual_spec spec fn, so callers learn neither the fields nor inv(); state the fields and inv() as ensur… |
| [R12](#r12) | `mm/page_table/cursor/mod.rs` | Cursor::find_next drops find_next_impl's frame facts (barrier_va, guard_level, monotone va, unchanged mappings, found va below old va + len), and page_table Cur… |
| [R13](#r13) | `mm/page_table/cursor/mod.rs` | Cursor::jump keeps barrier_va and guard_level (loop invariants) and returns Err before touching the cursor or owner, but ensures none of it; CursorMut::jump and… |
| [R14](#r14) | `mm/page_table/cursor/mod.rs` | Cursor::query keeps va, barrier_va and guard_level and returns Err outside the barrier, but states only va and only 'in barrier implies Ok'; page_table CursorMu… |
| [R15](#r15) | `mm/page_table/cursor/mod.rs` | Cursor::query returns cur_va_range(), which contains the cursor va, but cur_va_range does not ensure va < end and query states the range only when a mapping is … |
| [R16](#r16) | `mm/page_table/cursor/mod.rs` | Cursor::new returns Err before touching regions and ensures the owner relation, item_not_mapped and non-saturation preservation, but CursorMut::new, PageTable::… |
| [R24](#r24) | `mm/page_table/cursor/mod.rs` | page_table CursorMut::map moves the cursor past the mapped slot and returns the replaced fragment at the old va (replace_cur_entry ensures it) but states neithe… |
| [R25](#r25) | `mm/page_table/cursor/mod.rs` | page_table CursorMut::map advances the cursor to align_up(va, page_size(level)) = va + page_size(level) (va is asserted aligned) but does not state it. |
| [R26](#r26) | `mm/page_table/cursor/mod.rs` | CursorMut::take_next ensures barrier_va preservation but not guard_level preservation, which map's item_wf needs on the same cursor. |
| [R78](#r78) | `mm/page_table/cursor/mod.rs` | page_table CursorMut::query wraps Cursor::query, which now ensures slots and the slot_owners domain unchanged (cursor-4), but does not forward either fact. |
| [R90](#r90) | `mm/page_table/cursor/mod.rs` | page_table Cursor::query ensures the returned range contains the old cursor va (kept fix cursor-5), but page_table CursorMut::query and VmSpace CursorMut::query… |
| [R27](#r27) | `mm/page_table/mod.rs` | create_user_page_table keeps the kernel page table related to kernel_owner in the new regions but does not ensure it, so VmSpace::new cannot create a second use… |
| [R79](#r79) | `mm/page_table/mod.rs` | PageTable::cursor_mut and cursor return a CursorOwner with as_page_table_owner() == owner and continuations[3].path() == the owner's path, but the view equality… |
| [R61](#r61) | `mm/page_table/node/child.rs` | ChildRef::from_pte returns Frame(pte.paddr(), level, pte.prop()) but ensures only res.invariants, whose ChildRef wf does not tie the frame's paddr/level/prop to… |
| [R59](#r59) | `mm/page_table/node/entry.rs` | Entry::alloc_if_none requires parent_owner.metaregion_sound_node(regions) but does not give it back after allocating, though its body re-establishes it (as spli… |
| [R60](#r60) | `mm/page_table/node/entry.rs` | Entry::split_if_mapped_huge makes the entry point at the new node but, unlike alloc_if_none and replace, does not ensure final(self).wf/invariants with the new … |
| [R17](#r17) | `mm/vm_space.rs` | VmSpace::cursor and cursor_mut keep only c.inv() of the owner and drop PageTable::cursor(_mut)'s '!cond implies Err', the success-branch facts (cursor invariant… |
| [R18](#r18) | `mm/vm_space.rs` | VmSpace::cursor drops PageTable::cursor's as_page_table_owner() == owner for the returned cursor owner, which ties the cursor view to the walked page table. |
| [R19](#r19) | `mm/vm_space.rs` | VmSpace::reader and writer never change the VmSpaceOwner (new_vm_io_id is a spec function) and return Some exactly with Ok, but ensure only final(owner).inv() a… |
| [R20](#r20) | `mm/vm_space.rs` | VmReader/VmWriter::from_user_space fix cursor and end from (vaddr, len), but VmSpace::reader/writer do not export remain()/avail() == len, nor (writer) that a c… |
| [R22](#r22) | `mm/vm_space.rs` | CursorMut::flusher only returns &mut self.flusher but does not ensure pt_cursor is unchanged, so the cursor invariants are lost after flushing through it. |
| [R23](#r23) | `mm/vm_space.rs` | VmSpace CursorMut::map requires tlb_model.inv() and keeps it (issue_tlb_flush_with and dispatch_tlb_flush preserve it) but does not ensure it, so a second map o… |
| [R28](#r28) | `mm/vm_space.rs` | VmSpace CursorMut::unmap's ensures never constrain the returned count although the loop keeps num_unmapped == removed.len() with every removed mapping starting … |
| [R70](#r70) | `mm/vm_space.rs` | VmSpace::default calls VmSpace::new, which ensures final(regions).inv(), but default itself has no ensures, so neither new nor default can follow a default. |
| [R80](#r80) | `mm/vm_space.rs` | VmSpace CursorMut::map drops page_table CursorMut::map's barrier_va preservation and its va advance by page_size(level) (cursor-16); a UFrame item has level 1 a… |
| [R64](#r64) | `sync/mutex.rs` | Mutex::lock has no ensures although try_lock ensures ret.rel_mutex(*self) and wait_until forwards the closure's ensures; give the closure that ensures and forwa… |
| [R65](#r65) | `sync/mutex.rs` | MutexGuard::deref_mut does not say the guard's closed rel_mutex is unchanged, so after writing through the guard the caller loses which mutex it belongs to. |
| [R66](#r66) | `sync/rcu/mod.rs` | RcuOptionReadGuard::compare_exchange does not forward the inner RcuReadGuardInner::compare_exchange ensures new_ptr is Some && r is Err ==> r->Err_0 is Some. |
| [R67](#r67) | `sync/rcu/non_null/either.rs` | Either's ref_rel_perm is defined as true, so raw_as_ref/ref_as_raw lose the side and the per-side L/R::ref_rel_perm that their bodies get from L/R::raw_as_ref a… |
| [R91](#r91) | `sync/rcu/non_null/mod.rs` | On failure RcuReadGuardInner::compare_exchange returns from_raw(into_raw(new_ptr)), but NonNullPtr only says both are rel_perm-related to the same permission, n… |
| [R77](#r77) | `sync/rwlock.rs` | RwLockUpgradeableGuard::upgrade has no ensures tying the write guard's value to the upread guard's value, which try_upgrade keeps (it builds the write permissio… |
| [R68](#r68) | `sync/spin.rs` | SpinLock::wf is the public well-formedness predicate for wrappers, but SpinLock::new does not ensure it (res.wf() verifies). |
| [R69](#r69) | `sync/spin.rs` | SpinLock::wf equals its closed type invariant, and lock/try_lock (which hold &self) never export it, so a wrapper cannot re-establish wf for an existing lock; e… |
| [R63](#r63) | `verified_libs/bitflags/src/lib.rs` | The bitflags macro's insert/set/toggle/clear/sub ensure only bits-level facts while union_spec/difference_spec/symmetric_difference_spec/empty_spec are closed, … |


## `mm/dma/dma_coherent.rs`

<a id="r57"></a>

### R57. The public DmaCoherent::reader and DmaStream::reader drop reader_perm@.read_view_initialized(), which reader_inner ensures and DmaStreamSlice::reader exports.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/dma/dma_stream.rs, from line 864 @@
             r is Ok ==> {
                 &&& r.unwrap().inv()
                 &&& reader_perm@ is Some
                 &&& reader_perm@->0.inv()
                 &&& reader_perm@->0.is_kernel
                 &&& reader_perm@->0.has_read_view()
+                &&& reader_perm@->0.read_view_initialized()
                 &&& r.unwrap().wf(reader_perm@->0)
                 &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
                 &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
             },
     )]
     pub fn reader<'a>(&'a self) -> core::result::Result<VmReader<'a, Infallible>, Error> {
```

```diff
@@ ostd/src/mm/dma/dma_coherent.rs, from line 411 @@
         ensures
             self.inner.wf(),
             r.inv(),
             reader_perm@.inv(),
             reader_perm@.is_kernel,
             reader_perm@.has_read_view(),
+            reader_perm@.read_view_initialized(),
             r.wf(reader_perm@),
             KERNEL_BASE_VADDR <= r.cursor.range@.start,
             r.cursor.range@.end <= KERNEL_END_VADDR,
     )]
     pub fn reader<'a>(&'a self) -> VmReader<'a, Infallible> {
         let inner = self.read_inner();
```

**A client that fails** (module `mm.dma.dma_coherent`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__dma__dma_coherent__impl__6__reader_0<'a, M: AnyUFrameMeta + OwnerOf>(
    self_: &'a DmaCoherent<M>,
)
    requires
        self_.inner.wf(),
{
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with  => Tracked(gr))] self_.reader());
    assert(gr.read_view_initialized()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr.read_view_initialized()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 15 failing clients in 5 groups of failures pass.

<a id="r58"></a>

### R58. The public DmaCoherent::writer and DmaStream::writer drop the kernel-range bounds of the cursor, which writer_inner ensures and the sibling reader() forwards.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/dma/dma_stream.rs, from line 917 @@
                 &&& r.unwrap().inv()
                 &&& writer_perm@ is Some
                 &&& writer_perm@->0.inv()
                 &&& writer_perm@->0.is_kernel
                 &&& writer_perm@->0.has_write_view()
                 &&& r.unwrap().wf(writer_perm@->0)
+                &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
+                &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
             },
     )]
     pub fn writer<'a>(&'a self) -> core::result::Result<VmWriter<'a, Infallible>, Error> {
         let inner = self.read_inner();
 
         if matches!(inner.direction, DmaDirection::FromDevice) {
```

```diff
@@ ostd/src/mm/dma/dma_coherent.rs, from line 297 @@
             writer_owner@.inv(),
             writer_owner@.is_kernel,
             writer_owner@.has_write_view(),
             r.wf(writer_owner@),
             KERNEL_BASE_VADDR <= r.cursor.range@.start,
             r.cursor.range@.end <= KERNEL_END_VADDR,
+            r.cursor.vaddr == r.cursor.range@.start,
+            r.end.vaddr == r.cursor.range@.end,
     )]
     fn writer_inner<'a>(
         this: RwLockReadGuard<'a, DmaCoherentInnerAtomic<M>, PreemptDisabled>,
     ) -> VmWriter<'a, Infallible> {
         proof_decl! {
             let ghost id: nat;
@@ ostd/src/mm/dma/dma_coherent.rs, from line 442 @@
             self.inner.wf(),
             r.inv(),
             writer_perm@.inv(),
             writer_perm@.is_kernel,
             writer_perm@.has_write_view(),
             r.wf(writer_perm@),
+            KERNEL_BASE_VADDR <= r.cursor.range@.start,
+            r.cursor.range@.end <= KERNEL_END_VADDR,
+            r.cursor.vaddr == r.cursor.range@.start,
+            r.end.vaddr == r.cursor.range@.end,
     )]
     pub fn writer<'a>(&'a self) -> VmWriter<'a, Infallible> {
         let inner = self.read_inner();
         proof_with!(=> Tracked(writer_perm));
         let writer = Self::writer_inner(inner);
         proof_with!(|= Tracked(writer_perm));
```

**A client that fails** (module `mm.dma.dma_coherent`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__dma__dma_coherent__impl__6__reader_2<'a, M: AnyUFrameMeta + OwnerOf>(
    self_: &'a DmaCoherent<M>,
)
    requires
        self_.inner.wf(),
{
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with  => Tracked(gr))] self_.reader());
    assert(r.cursor.vaddr == r.cursor.range@.start && r.end.vaddr == r.cursor.range@.end); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.cursor.vaddr == r.cursor.range@.start && r.end.vaddr == r.cursor.range@.end); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 5 failing clients in 4 groups of failures pass.

<a id="r75"></a>

### R75. The public DmaCoherent::nbytes and DmaStream::nbytes ensure nothing about their result, although nbytes_inner returns segment.size() == end_paddr() - start_paddr() (Segment::size's ensures) and the inner invariant's segment.inv() makes both ends page-aligned; prove r % PAGE_SIZE == 0 in nbytes_inner and forward it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/dma/dma_stream.rs, from line 538 @@
     /// ## Postconditions
     /// - The returned byte count matches the size of the inner segment.
     #[inline(always)]
     #[verus_spec(r =>
         requires
             this@.inv(),
+        ensures
+            r % PAGE_SIZE == 0,
         returns
             this@.data.segment.size(),
     )]
     fn nbytes_inner(this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>) -> usize {
+        proof {
+            vstd::arithmetic::div_mod::lemma_sub_mod_noop(
+                this@.data.segment.end_paddr() as int,
+                this@.data.segment.start_paddr() as int,
+                PAGE_SIZE as int,
+            );
+        }
         this.segment.size()
     }
 
     /// Returns a reader to read data from it using a read guard.
     ///
     /// # Verified Properties
@@ ostd/src/mm/dma/dma_stream.rs, from line 835 @@
     #[inline(always)]
     #[verus_spec(r =>
         requires
             self.inner.wf(),
         ensures
             self.inner.wf(),
+            r % PAGE_SIZE == 0,
     )]
     pub fn nbytes(&self) -> usize {
         let inner = self.read_inner();
         Self::nbytes_inner(&inner)
     }
 
```

```diff
@@ ostd/src/mm/dma/dma_coherent.rs, from line 227 @@
 
     /// Returns the number of bytes from a read guard.
     #[inline(always)]
     #[verus_spec(r =>
         requires
             this@.inv(),
+        ensures
+            r % PAGE_SIZE == 0,
         returns
             this@.data.segment.size(),
     )]
     fn nbytes_inner(this: &RwLockReadGuard<DmaCoherentInnerAtomic<M>, PreemptDisabled>) -> usize {
+        proof {
+            vstd::arithmetic::div_mod::lemma_sub_mod_noop(
+                this@.data.segment.end_paddr() as int,
+                this@.data.segment.start_paddr() as int,
+                PAGE_SIZE as int,
+            );
+        }
         this.segment.size()
     }
 
     /// Returns a reader to read data from it using a read guard.
     #[inline(always)]
     #[verus_spec(r =>
@@ ostd/src/mm/dma/dma_coherent.rs, from line 392 @@
     #[inline(always)]
     #[verus_spec(r =>
         requires
             self.inner.wf(),
         ensures
             self.inner.wf(),
+            r % PAGE_SIZE == 0,
     )]
     pub fn nbytes(&self) -> usize {
         let inner = self.read_inner();
         Self::nbytes_inner(&inner)
     }
 
```

**A client that fails** (module `mm.dma.dma_stream`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__dma__dma_stream__impl__8__paddr_2<M: AnyUFrameMeta + OwnerOf>(
    self_: &DmaStream<M>,
)
    requires
        self_.inner.wf(),
{
    let mut r = self_.paddr();
    assert(r % crate::mm::PAGE_SIZE == 0); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r % crate::mm::PAGE_SIZE == 0); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 6 failing clients in 2 groups of failures pass.

## `mm/dma/dma_stream.rs`

<a id="r82"></a>

### R82. DmaStream::read_inner_vmio and write_inner_vmio always return Err and never change their writer/reader (their bodies only call avail/remain), but ensure the Err and the unchanged buffer only for one direction; ensure both unconditionally.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/dma/dma_stream.rs, from line 949 @@
             old(writer).inv(),
         ensures
             this@.data.direction == DmaDirection::ToDevice ==> {
                 &&& r == Err::<(), Error>(Error::AccessDenied)
                 &&& *final(writer) == *old(writer)
             },
+            r is Err,
+            *final(writer) == *old(writer),
     )]
     pub fn read_inner_vmio(
         this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
         offset: usize,
         writer: &mut VmWriter<'_>,
     ) -> core::result::Result<(), Error> {
@@ ostd/src/mm/dma/dma_stream.rs, from line 977 @@
             old(reader).inv(),
         ensures
             this@.data.direction == DmaDirection::FromDevice ==> {
                 &&& r == Err::<(), Error>(Error::AccessDenied)
                 &&& *final(reader) == *old(reader)
             },
+            r is Err,
+            *final(reader) == *old(reader),
     )]
     pub fn write_inner_vmio(
         this: &RwLockReadGuard<DmaStreanInnerAtomic<M>, PreemptDisabled>,
         offset: usize,
         reader: &mut VmReader<'_>,
     ) -> core::result::Result<(), Error> {
```

**A client that fails** (module `mm.dma.dma_stream`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__dma__dma_stream__impl__8__read_inner_vmio_26<'a, M: AnyUFrameMeta + OwnerOf>(
    this: &'a RwLockReadGuard<'a, AtomicDataWithOwner<DmaStreamInner<M>, DmaStreamInnerInvariant>, PreemptDisabled>,
    mut offset: usize,
    writer: &mut VmWriter<'a, Fallible>,
)
    requires
        old(writer).inv(),
{
    let ghost old_writer = (*writer);
    let mut r = DmaStream::<M>::read_inner_vmio(this, offset, writer);
    assert((*writer) == old_writer); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*writer) == old_writer); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 4 failing clients in 4 groups of failures pass.

<a id="r83"></a>

### R83. DmaStream::reader does not say its reader's length is page-aligned, although reader_inner creates it with from_kernel_space(ptr, segment.size()) and the inner invariant's segment.inv() makes both segment ends page-aligned; prove remain_spec() % PAGE_SIZE == 0 in reader_inner (as dma2-1 does for nbytes) and forward it from reader.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/dma/dma_stream.rs, from line 569 @@
             reader_owner@.is_kernel,
             reader_owner@.has_read_view(),
             reader_owner@.read_view_initialized(),
             r.wf(reader_owner@),
             KERNEL_BASE_VADDR <= r.cursor.range@.start,
             r.cursor.range@.end <= KERNEL_END_VADDR,
+            r.remain_spec() % PAGE_SIZE == 0,
     )]
     fn reader_inner<'a>(
         this: RwLockReadGuard<'a, DmaStreanInnerAtomic<M>, PreemptDisabled>,
     ) -> VmReader<'a, Infallible> {
         proof_decl! {
             let ghost id: nat;
@@ ostd/src/mm/dma/dma_stream.rs, from line 597 @@
         }
 
         let reader = unsafe {
             proof_with!(Ghost(id) => Tracked(reader_owner));
             VmReader::from_kernel_space(ptr, len)
         };
+        proof {
+            vstd::arithmetic::div_mod::lemma_sub_mod_noop(
+                this@.data.segment.end_paddr() as int,
+                this@.data.segment.start_paddr() as int,
+                PAGE_SIZE as int,
+            );
+            assert(reader.remain_spec() == len);
+        }
         proof_with!(|= Tracked(reader_owner));
         reader
     }
 
     /// Returns a writer to write data to it using a read guard.
     ///
@@ ostd/src/mm/dma/dma_stream.rs, from line 867 @@
                 &&& reader_perm@->0.inv()
                 &&& reader_perm@->0.is_kernel
                 &&& reader_perm@->0.has_read_view()
                 &&& r.unwrap().wf(reader_perm@->0)
                 &&& KERNEL_BASE_VADDR <= r.unwrap().cursor.range@.start
                 &&& r.unwrap().cursor.range@.end <= KERNEL_END_VADDR
+                &&& r.unwrap().remain_spec() % PAGE_SIZE == 0
             },
     )]
     pub fn reader<'a>(&'a self) -> core::result::Result<VmReader<'a, Infallible>, Error> {
         let inner = self.read_inner();
 
         if matches!(inner.direction, DmaDirection::ToDevice) {
```

**A client that fails** (module `mm.dma.dma_stream`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__dma__dma_stream__impl__8__reader_14<'a, M: AnyUFrameMeta + OwnerOf>(
    self_: &'a DmaStream<M>,
)
    requires
        self_.inner.wf(),
{
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with  => Tracked(gr))] self_.reader());
    assert(r is Ok ==> r.unwrap().remain_spec() % crate::mm::PAGE_SIZE == 0); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r is Ok ==> r.unwrap().remain_spec() % crate::mm::PAGE_SIZE == 0); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

## `mm/frame/frame_ref.rs`

<a id="r41"></a>

### R41. FrameRef::deref proves the type invariant inner@.ptr_inv() with use_type_invariant but its ensures exposes only the closed view, so ptr_inv() of the dereferenced Frame is lost; export it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/frame_ref.rs, from line 123 @@
     }
 }
 
 impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> Deref for FrameRef<'_, M> {
     type Target = Frame<M>;
 
-    #[verus_spec(r => ensures *r == (Frame { tracked_metadata_perm: Tracked(None), ..self@ }))]
+    #[verus_spec(r => ensures *r == (Frame { tracked_metadata_perm: Tracked(None), ..self@ }), r.ptr_inv())]
     fn deref(&self) -> &Self::Target {
         proof {
             use_type_invariant(self);
         }
         &self.inner
     }
```

**A client that fails** (module `mm.frame.frame_ref`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__frame_ref__impl__4__deref_0<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    self_: &'a FrameRef<'a, M>,
)
{
    let mut r = self_.deref();
    assert(r.ptr_inv()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.ptr_inv()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r42"></a>

### R42. NonNullPtr::raw_as_ref for Frame builds the FrameRef at raw (equal to permission.slot_perm.ptr() by ptr_perm_match) with permission.slot_perm and Some(&permission.metadata_perm), but ensures only res.inv(), so the result's pointer and permissions are unrelated to raw and permission; ensure them.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/frame_ref.rs, from line 273 @@
         }
     }
 
     unsafe fn raw_as_ref<'a>(
         raw: NonNull<Self::Target>,
         Tracked(permission): Tracked<&'a Self::Permission>,
-    ) -> Self::Ref<'a> {
+    ) -> (res: Self::Ref<'a>)
+        ensures
+            res@.ptr == permission.slot_perm.ptr(),
+            res.slot_vaddr() == permission.slot_vaddr(),
+            res.slot_vaddr() == raw.as_ptr().addr(),
+            res.frac_metadata_perm() == permission.metadata_perm,
+            res@.tracked_slot_perm@ == permission.slot_perm,
+    {
         Self::Ref {
             inner: ManuallyDrop::new(
                 Frame {
                     ptr: raw.as_ptr().cast_const().cast(),
                     _marker: PhantomData,
                     #[cfg(verus_keep_ghost_body)]
```

**A client that fails** (module `mm.frame.frame_ref`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__frame_ref__impl__5__raw_as_ref_9<'a, M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static>(
    mut raw: NonNull<PhantomData<Frame<M>>>,
    Tracked(permission): Tracked<&'a FrameRawPerms>,
)
    requires
        <Frame<M> as crate::mm::frame::frame_ref::NonNullPtr>::ptr_perm_match(raw.as_ptr(), (*permission)),
        permission.inv(),
{
    let mut r = unsafe { <Frame<M> as crate::mm::frame::frame_ref::NonNullPtr>::raw_as_ref(raw, Tracked(permission)) };
    assert(r.slot_vaddr() == raw.as_ptr().addr()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.slot_vaddr() == raw.as_ptr().addr()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 5 failing clients in 5 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r71"></a>

### R71. NonNullPtr::from_raw for Frame sets ptr from raw (tied to perm.slot_perm.ptr() by ptr_perm_match) and stores Some(perm.metadata_perm), but the trait ensures only rel_perm, which for Frame omits the pointer and the presence of the metadata permission, so ret.inv() and its address are lost; an ensures on the impl method cannot compile (it clashes with the inherent Frame::from_raw), so add both facts to Frame's open rel_perm, which into_raw also satisfies from self.inv().

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/frame_ref.rs, from line 308 @@
         ptr.cast_const().cast::<MetaSlot>() == perm.slot_perm.ptr()
     }
 
     open spec fn rel_perm(self, perm: Self::Permission) -> bool {
         &&& perm.slot_perm == self.slot_perm()
         &&& perm.metadata_perm == self.frac_metadata_perm()
+        &&& self.ptr == perm.slot_perm.ptr()
+        &&& self.tracked_metadata_perm@ is Some
     }
 }
 
 impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>> FrameRef<'a, M> {
     pub open spec fn start_paddr_spec(self) -> Paddr {
         self@.start_paddr_spec()
```

**A client that fails** (module `mm.frame.frame_ref`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__frame_ref__impl__5__from_raw_2<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static>(
    mut raw: NonNull<PhantomData<Frame<M>>>,
    Tracked(perm): Tracked<FrameRawPerms>,
)
    requires
        <Frame<M> as crate::mm::frame::frame_ref::NonNullPtr>::ptr_perm_match(raw.as_ptr(), perm),
        perm.inv(),
{
    let tracked mut perm = perm;
    let mut r = unsafe { <Frame<M> as crate::mm::frame::frame_ref::NonNullPtr>::from_raw(raw, Tracked(perm)) };
    assert(r.inv()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.inv()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 6 failing clients in 5 groups of failures pass.

**Note.** the new rel_perm conjuncts are proved in NonNullPtr::into_raw from its existing assume(self.inv()) (frame_ref.rs:249); this adds conjuncts to the open spec function `rel_perm` of `Frame`'s `NonNullPtr` implementation; please check that no trusted (`external_body`) contract relies on the old definition.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

## `mm/frame/linked_list.rs`

<a id="r43"></a>

### R43. LinkedList::contains calls lazy_get_id, which ensures size/front/back are unchanged, a minted id is kept and the id is non-zero, but contains forwards none of it; forward these facts.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 466 @@
             old(self).wf(*owner),
             owner.relate_region(*regions),
         ensures
             (valid_frame_paddr(frame) && exists|i: int| 0 <= i < owner.list.len()
                 && #[trigger] meta_to_index(owner.list[i].slot_vaddr) == frame_to_index(frame))
                 ==> r,
+            old(self).list_id != 0 ==> *final(self) == *old(self),
+            final(self).size == old(self).size && final(self).front == old(self).front
+                && final(self).back == old(self).back,
+            r ==> final(self).list_id != 0,
+            valid_frame_paddr(frame) ==> regions.contains(frame_to_index(frame)),
         returns
             valid_frame_paddr(frame)
                 && regions.slot_owners[frame_to_index(frame)].in_list_perm.value()
                     == final(self).list_id,
     )]
     pub fn contains(&mut self, frame: Paddr) -> bool {
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__2__contains_24<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &mut LinkedList<M>,
    mut frame: usize,
    Tracked(regions): Tracked<&MetaRegionOwners>,
    Tracked(owner): Tracked<&LinkedListOwner<M>>,
)
    requires
        regions.inv(),
        old(self_).wf((*owner)),
        owner.relate_region((*regions)),
        crate::specs::mm::embedding::list_store::list_registry_ok::<M>(*regions, *owner),
{
    let ghost old_self_ = (*self_);
    let mut r = (#[verus_spec(with Tracked(regions), Tracked(owner))] self_.contains(frame));
    assert(old_self_.list_id != 0 ==> (*self_) == old_self_); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(old_self_.list_id != 0 ==> (*self_) == old_self_); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 4 failing clients in 4 groups of failures pass.

<a id="r44"></a>

### R44. take_current ensures final(regions) == old(regions).insert_slot_owner(paddr, ..) at the taken slot, but pop_front and pop_back forward no frame condition, so all other slots (and the slot permissions) lose their facts; forward it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 308 @@
                 &&& frame.wf(fo)
                 &&& frame.wf_with_region(fo, *final(regions))
                 &&& frame.frame_link_inv(fo, *final(regions))
             }),
             r is None ==> *final(owner) == *old(owner)
                 && *final(self) == *old(self) && *final(regions) == *old(regions),
+            (*final(regions)).slots == (*old(regions)).slots,
+            frame_owner@ matches Some(fo) ==> (forall|i: int| #![trigger (*final(regions)).slot_owners[i]] i != fo.slot_index ==> (*final(regions)).slot_owners[i] == (*old(regions)).slot_owners[i]),
+            forall|k: int| ((*old(owner)).list.len() == 0 || (k != crate::specs::mm::frame::mapping::meta_to_index((*old(owner)).list[0].slot_vaddr) && ((*old(owner)).list.len() > 1 ==> k != crate::specs::mm::frame::mapping::meta_to_index((*old(owner)).list[1].slot_vaddr)))) ==> (*final(regions)).slots[k] == (*old(regions)).slots[k] && (*final(regions)).slot_owners[k] == (*old(regions)).slot_owners[k],
     )]
     pub fn pop_front(&mut self) -> Option<UniqueFrame<Link<M>>> {
         let tracked owner0 = LinkedListOwner::tracked_take(owner);
         let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner0);
         let tracked mut returned_owner: Option<UniqueFrameOwner<Link<M>>>;
 
@@ ostd/src/mm/frame/linked_list.rs, from line 420 @@
                 &&& frame.wf(fo)
                 &&& frame.wf_with_region(fo, *final(regions))
                 &&& frame.frame_link_inv(fo, *final(regions))
             }),
             r is None ==> *final(owner) == *old(owner)
                 && *final(self) == *old(self) && *final(regions) == *old(regions),
+            (*final(regions)).slots == (*old(regions)).slots,
+            frame_owner@ matches Some(fo) ==> (forall|i: int| #![trigger (*final(regions)).slot_owners[i]] i != fo.slot_index ==> (*final(regions)).slot_owners[i] == (*old(regions)).slot_owners[i]),
+            forall|k: int| ((*old(owner)).list.len() == 0 || (k != crate::specs::mm::frame::mapping::meta_to_index((*old(owner)).list[(*old(owner)).list.len() - 1].slot_vaddr) && ((*old(owner)).list.len() > 1 ==> k != crate::specs::mm::frame::mapping::meta_to_index((*old(owner)).list[(*old(owner)).list.len() - 2].slot_vaddr)))) ==> (*final(regions)).slots[k] == (*old(regions)).slots[k] && (*final(regions)).slot_owners[k] == (*old(regions)).slot_owners[k],
     )]
     pub fn pop_back(&mut self) -> Option<UniqueFrame<Link<M>>> {
         let tracked owner0 = LinkedListOwner::tracked_take(owner);
         let tracked mut cursor_own = CursorOwner::tracked_back_owner(owner0);
         let tracked mut returned_owner: Option<UniqueFrameOwner<Link<M>>>;
 
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__2__pop_front_11<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &mut LinkedList<M>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
)
    requires
        old(regions).inv(),
        old(self_).wf_region((*old(owner)), (*old(regions))),
        old(owner).relate_region((*old(regions))),
{
    let ghost old_self_ = (*self_);
    let ghost old_regions = (*regions);
    let ghost old_owner = (*owner);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(regions), Tracked(owner) => Tracked(gr))] self_.pop_front());
    assert(gr matches Some(fo) ==> (forall|i: int| #![trigger (*regions).slot_owners[i]] i != fo.slot_index ==> (*regions).slot_owners[i] == old_regions.slot_owners[i])); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr matches Some(fo) ==> (forall|i: int| #![trigger (*regions).slot_owners[i]] i != fo.slot_index ==> (*regions).slot_owners[i] == old_regions.slot_owners[i])); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 19 failing clients in 7 groups of failures pass.

<a id="r45"></a>

### R45. CursorMut::current_meta only borrows regions.slots immutably and keeps the cursor, yet ensures neither final(regions) == old(regions), final(regions).inv(), nor wf_region after the call, so the cursor and regions cannot be used again; ensure them.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 856 @@
         ensures
             final(owner).index == old(owner).index,
             final(owner).list_own.list == old(owner).list_own.list,
             final(owner).list_own.list_id == old(owner).list_own.list_id,
             *final(self) == *old(self),
             res.is_some() == (0 <= final(owner).index < final(owner).length()),
+            res is Some ==> (final(self).wf_region((*final(owner)), (*final(regions)))),
+            res is None ==> (final(regions).inv()),
+            (*final(regions)) == (*old(regions)),
+            res is None ==> (*final(owner)) == (*old(owner)) && (*final(regions)) == (*old(regions)),
+            res is Some ==> (final(regions).inv()),
             final(regions).slots.dom() == old(regions).slots.dom(),
             final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
     {
         // Verus does not support option.map very well.
         // self.current.map(|current| {
         //     let link_mut = unsafe { &mut *(current.ptr.addr() as *mut Link<M>) };
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__3__current_meta_20<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &mut CursorMut<'a, M>,
    Tracked(owner): Tracked<&mut CursorOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        old(self_).wf_region((*old(owner)), (*old(regions))),
        old(owner).wf_with_region((*old(regions))),
        old(regions).inv(),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions))] self_.current_meta());
    assert((*regions) == old_regions); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*regions) == old_regions); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 22 failing clients in 8 groups of failures pass.

<a id="r46"></a>

### R46. CursorMut::current_meta returns a borrow of the current link's meta but does not say it equals meta_value_at of the current index, so the caller cannot read the metadata; ensure it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 858 @@
             final(owner).list_own.list == old(owner).list_own.list,
             final(owner).list_own.list_id == old(owner).list_own.list_id,
             *final(self) == *old(self),
             res.is_some() == (0 <= final(owner).index < final(owner).length()),
             final(regions).slots.dom() == old(regions).slots.dom(),
             final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            res matches Some(m) ==> *m == (*old(owner)).list_own.meta_value_at((*old(regions)), (*old(owner)).index).meta,
     {
         // Verus does not support option.map very well.
         // self.current.map(|current| {
         //     let link_mut = unsafe { &mut *(current.ptr.addr() as *mut Link<M>) };
         //     &mut link_mut.meta
         // })
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__3__current_meta_38<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &mut CursorMut<'a, M>,
    Tracked(owner): Tracked<&mut CursorOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        old(self_).wf_region((*old(owner)), (*old(regions))),
        old(owner).wf_with_region((*old(regions))),
        old(regions).inv(),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions))] self_.current_meta());
    assert(r matches Some(m) ==> *m == old_owner.list_own.meta_value_at(old_regions, old_owner.index).meta); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Some(m) ==> *m == old_owner.list_own.meta_value_at(old_regions, old_owner.index).meta); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r47"></a>

### R47. Link::deref and Link::deref_mut return a reference to self.meta but have no ensures; ensure the referent is self.meta.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 1676 @@
     pub meta: M,
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Deref for Link<M> {
     type Target = M;
 
-    fn deref(&self) -> &Self::Target {
+    fn deref(&self) -> (r: &Self::Target)
+        ensures
+            *r == self.meta,
+    {
         &self.meta
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> DerefMut for Link<M> {
-    fn deref_mut(&mut self) -> &mut Self::Target {
+    fn deref_mut(&mut self) -> (r: &mut Self::Target)
+        ensures
+            *r == old(self).meta,
+    {
         &mut self.meta
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Link<M> {
     /// Creates a new linked list metadata.
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__5__deref_3<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &Link<M>,
)
{
    let mut r = self_.deref();
    assert(*r == self_.meta); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(*r == self_.meta); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

<a id="r48"></a>

### R48. Link::new builds a Link with the given meta and no next/prev but has no ensures; ensure those fields.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 1689 @@
         &mut self.meta
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Link<M> {
     /// Creates a new linked list metadata.
-    pub const fn new(meta: M) -> Self {
+    pub const fn new(meta: M) -> (r: Self)
+        ensures
+            r.meta == meta,
+            r.next is None,
+            r.prev is None,
+    {
         Self { next: None, prev: None, meta }
     }
 }
 
 // SAFETY: If `M::on_drop` reads the page using the provided `VmReader`,
 // the safety is upheld by the one who implements `AnyFrameMeta` for `M`.
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__7__new_2<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    mut meta: M,
)
{
    let mut r = Link::<M>::new(meta);
    assert(r.meta == meta && r.next is None && r.prev is None); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.meta == meta && r.next is None && r.prev is None); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r72"></a>

### R72. CursorMut::as_list returns self.list but has no ensures, so the returned list is unknown; ensure it is the list's value at entry (self.list is a &mut field, so the postcondition must say *old(self.list)).

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 1468 @@
 
             owner0.insert_owner_spec_implies_model_spec(flink, *owner);
         }
     }
 
     /// Provides a reference to the linked list.
-    pub fn as_list(&self) -> &LinkedList<M> {
+    pub fn as_list(&self) -> (r: &LinkedList<M>)
+        ensures
+            *r == *old(self.list),
+    {
         self.list
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
     /// Releases every frame owned by the list.
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__3__as_list_5<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &'a CursorMut<'a, M>,
)
{
    let mut r = self_.as_list();
    assert(*r == *self_.list); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(*r == *self_.list); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r73"></a>

### R73. CursorMut::move_prev, like move_next (list-10), only assigns self.current but does not ensure the list reference is unchanged; ensure it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 771 @@
             owner.wf_with_region(*regions),
             old(self).wf_region(owner, *regions),
         ensures
             owner.move_prev_owner_spec()@ == owner@.move_prev_spec(),
             owner.move_prev_owner_spec().wf_with_region(*regions),
             final(self).wf_region(owner.move_prev_owner_spec(), *regions),
+            (*final(self)).list == (*old(self)).list,
     {
         proof {
             owner.list_own.lemma_relate_region_shape(*regions);
             if self.current is Some {
                 owner.list_own.lemma_relate_region_at_index(*regions, owner.index);
                 owner.list_own.lemma_relate_region_at_facts(*regions, owner.index);
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__3__move_next_18<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &mut CursorMut<'a, M>,
    Tracked(owner): Tracked<CursorOwner<M>>,
    Tracked(regions): Tracked<&'a MetaRegionOwners>,
)
    requires
        owner.wf_with_region((*regions)),
        old(self_).wf_region(owner, (*regions)),
{
    let tracked mut owner = owner;
    let ghost old_self_ = (*self_);
    (#[verus_spec(with Tracked(owner), Tracked(regions))] self_.move_next());
    assert((*self_).list == old_self_.list); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).list == old_self_.list); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 1 group of failures pass.

<a id="r81"></a>

### R81. Default::default for LinkedList returns Self::new(), whose fields are now ensured (list-4), but default itself has no ensures, so the empty list's fields are lost; forward them.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 183 @@
     pub const fn new() -> Self {
         Self { front: None, back: None, size: 0, list_id: 0 }
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Default for LinkedList<M> {
-    fn default() -> Self {
+    fn default() -> (r: Self)
+        ensures
+            r.size == 0,
+            r.front is None,
+            r.back is None,
+            r.list_id == 0,
+    {
         Self::new()
     }
 }
 
 #[verus_verify]
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__0__new_0<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
)
{
    let mut r = LinkedList::<M>::new();
    assert(r.size == 0 && r.front is None && r.back is None && r.list_id == 0); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.size == 0 && r.front is None && r.back is None && r.list_id == 0); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies together with [list-4](#fix-list-4), which it builds on (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 1 group of failures pass.

<a id="r88"></a>

### R88. CursorMut::insert_before changes regions only at the inserted frame's slot owner (the in_list store); slots are only borrowed immutably and the neighbours' links are written through the list owner's metadata_perms, but neither insert_before nor push_front/push_back ensures this frame condition; ensure it in insert_before and forward it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 250 @@
         ensures
             final(self).wf_region(*final(owner), *final(regions)),
             final(owner).inv(),
             final(owner).relate_region(*final(regions)),
             final(regions).inv(),
             final(owner).list == old(owner).list.insert(0, final(frame_own).meta_own),
+            forall|l: LinkedListOwner<M>|
+                #![trigger l.relate_region(*final(regions))]
+                l.inv() && l.relate_region(*old(regions)) && l.list_id != final(owner).list_id
+                    ==> l.relate_region(*final(regions)),
+            old(owner).list_id != 0 && crate::specs::mm::embedding::list_store::list_registry_ok::<M>(*old(regions), *old(owner))
+                ==> crate::specs::mm::embedding::list_store::list_registry_ok::<M>(*final(regions), *final(owner)),
             old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
             final(owner).list_id != 0,
             final(frame_own).meta_own.slot_vaddr == old(frame_own).meta_own.slot_vaddr,
             final(frame_own).meta_own.in_list == final(owner).list_id,
+            final(regions).slots == old(regions).slots,
+            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            forall|i: int|
+                #![trigger final(regions).slot_owners[i]]
+                i != old(frame_own).slot_index ==> final(regions).slot_owners[i]
+                    == old(regions).slot_owners[i],
     )]
     pub fn push_front(&mut self, frame: UniqueFrame<Link<M>>) {
         let current = self.front;
         let tracked owner0 = LinkedListOwner::tracked_take(owner);
         let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner0);
         let mut cursor = CursorMut { list: self, current };
@@ ostd/src/mm/frame/linked_list.rs, from line 268 @@
         cursor.insert_before(frame);
 
         proof {
             *owner = cursor_own.list_own;
             owner.lemma_relate_region_implies_inv(*regions);
         }
+        proof {
+            let s = old(frame_own).slot_index;
+            assert forall|l: LinkedListOwner<M>|
+                #![trigger l.relate_region(*regions)]
+                l.inv() && l.relate_region(*old(regions)) && l.list_id != owner.list_id
+                    implies l.relate_region(*regions) by {
+                l.lemma_relate_region_shape(*old(regions));
+                assert forall|i: int|
+                    #![trigger l.list[i]]
+                    0 <= i < l.list.len() implies {
+                        &&& regions.contains(meta_to_index(l.list[i].slot_vaddr))
+                        &&& regions.slot_owners[meta_to_index(l.list[i].slot_vaddr)]
+                            == old(regions).slot_owners[meta_to_index(l.list[i].slot_vaddr)]
+                    } by {
+                    l.lemma_relate_region_at_index(*old(regions), i);
+                    l.lemma_relate_region_at_facts(*old(regions), i);
+                }
+                l.lemma_relate_region_preserved_external_change(*old(regions), *regions);
+            }
+            let ol = *old(owner);
+            if ol.list_id != 0 && crate::specs::mm::embedding::list_store::list_registry_ok::<M>(*old(regions), ol) {
+                let lo = *owner;
+                assert(lo.list_id == ol.list_id);
+                lo.lemma_relate_region_shape(*regions);
+                assert forall|i: int|
+                    #![trigger meta_to_index(lo.list[i].slot_vaddr)]
+                    0 <= i < lo.list.len() implies regions.slot_owners[meta_to_index(
+                        lo.list[i].slot_vaddr,
+                    )].in_list_perm.value() == lo.list_id by {
+                    lo.lemma_relate_region_at_index(*regions, i);
+                    lo.lemma_relate_region_at_facts(*regions, i);
+                }
+                assert forall|idx: int|
+                    #![trigger regions.slot_owners[idx]]
+                    regions.contains(idx) && regions.slot_owners[idx].in_list_perm.value()
+                        == lo.list_id implies exists|i: int|
+                        0 <= i < lo.list.len() && #[trigger] meta_to_index(lo.list[i].slot_vaddr)
+                            == idx by {
+                    if idx == s {
+                        assert(lo.list[0] == frame_own.meta_own);
+                        assert(meta_to_index(lo.list[0].slot_vaddr) == idx);
+                    } else {
+                        assert(old(regions).slot_owners[idx] == regions.slot_owners[idx]);
+                        assert(old(regions).contains(idx));
+                        let j = choose|j: int|
+                            0 <= j < ol.list.len() && #[trigger] meta_to_index(ol.list[j].slot_vaddr)
+                                == idx;
+                        assert(lo.list[j + 1] == ol.list[j]);
+                        assert(meta_to_index(lo.list[j + 1].slot_vaddr) == idx);
+                    }
+                }
+            }
+        }
     }
 
     /// Pops a frame from the front of the linked list.
     /// # Verified Properties
     /// ## Preconditions
     /// The list must be well-formed, with the pointers to its links' metadata slots
@@ ostd/src/mm/frame/linked_list.rs, from line 364 @@
             // Id preserved when already minted; a fresh (empty) list adopts a
             // non-zero id.
             old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
             final(owner).list_id != 0,
             final(frame_own).meta_own.slot_vaddr == old(frame_own).meta_own.slot_vaddr,
             final(frame_own).meta_own.in_list == final(owner).list_id,
+            final(regions).slots == old(regions).slots,
+            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            forall|i: int|
+                #![trigger final(regions).slot_owners[i]]
+                i != old(frame_own).slot_index ==> final(regions).slot_owners[i]
+                    == old(regions).slot_owners[i],
     )]
     pub fn push_back(&mut self, frame: UniqueFrame<Link<M>>) {
         let tracked owner0 = LinkedListOwner::tracked_take(owner);
         let tracked mut cursor_own = CursorOwner::tracked_cursor_mut_at_owner(
             owner0,
             owner0.list.len() as int,
@@ ostd/src/mm/frame/linked_list.rs, from line 1210 @@
             // (necessarily empty) list adopts a freshly-minted non-zero id.
             old(owner).list_own.list_id != 0 ==> final(owner).list_own.list_id == old(
                 owner,
             ).list_own.list_id,
             final(owner).list_own.list_id != 0,
             final(owner).index == old(owner).index + 1,
+            meta_to_index(final(frame_own).meta_own.slot_vaddr) == old(frame_own).slot_index,
             final(frame_own).meta_own.slot_vaddr == old(frame_own).meta_own.slot_vaddr,
             final(frame_own).meta_own.in_list == final(owner).list_own.list_id,
             final(owner)@ == old(owner)@.insert(final(frame_own).meta_own@),
+            final(regions).slots == old(regions).slots,
+            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            forall|i: int|
+                #![trigger final(regions).slot_owners[i]]
+                i != old(frame_own).slot_index ==> final(regions).slot_owners[i]
+                    == old(regions).slot_owners[i],
     {
         hide(<MetaRegionOwners as Inv>::inv);
         let ghost owner0 = *owner;
         let ghost regions0 = *regions;
         let ghost nn = owner.index as int;
 
```

**A client that fails** (module `mm.frame.linked_list`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__linked_list__impl__2__push_front_8<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    self_: &mut LinkedList<M>,
    mut frame: UniqueFrame<Link<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
    Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>,
)
    requires
        old(self_).wf_region((*old(owner)), (*old(regions))),
        old(owner).relate_region((*old(regions))),
        frame.inv(),
        old(frame_own).inv(),
        frame.wf_with_region((*old(frame_own)), (*old(regions))),
        frame.frame_link_inv((*old(frame_own)), (*old(regions))),
        old(regions).inv(),
{
    let ghost old_self_ = (*self_);
    let ghost old_regions = (*regions);
    let ghost old_owner = (*owner);
    let ghost old_frame_own = (*frame_own);
    (#[verus_spec(with Tracked(regions), Tracked(owner), Tracked(frame_own))] self_.push_front(frame));
    assert((*regions).slots == old_regions.slots); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*regions).slots == old_regions.slots); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 11 failing clients in 6 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

## `mm/frame/meta.rs`

<a id="r85"></a>

### R85. MetaSlot::get_from_unused fails only when get_slot rejects the paddr (iff !valid_frame_paddr) or the CAS from REF_COUNT_UNUSED fails (iff the old ref count differs), but no layer says a valid paddr with ref count REF_COUNT_UNUSED yields Ok; ensure it in get_from_unused and forward it in UniqueFrame::from_unused and Frame::from_unused.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 74 @@
         requires
             old(regions).contains(frame_to_index(paddr)),
             old(regions).slot_owner(paddr).usage is Unused,
             old(regions).inv(),
             <M as OwnerOf>::wf(metadata, meta_own_in),
         ensures
+            crate::specs::arch::valid_frame_paddr(paddr) && old(regions).slot_owner(paddr).ref_count()
+                == crate::mm::frame::meta::REF_COUNT_UNUSED ==> res is Ok,
             res matches Ok(res) ==> {
                 &&& owner@ is Some
                 &&& res.wf(owner@->0)
                 &&& res.wf_with_region(owner@->0, *final(regions))
                 &&& owner@->0.meta_own == meta_own_in
                 &&& res.meta_value(owner@->0) == metadata
```

```diff
@@ ostd/src/mm/frame/meta.rs, from line 410 @@
                     *old(regions),
                     *final(regions),
                     *final(repr_perm),
                     permissions@->0,
                 )
             },
+            valid_frame_paddr(paddr) && old(regions).slot_owner(paddr).ref_count()
+                == REF_COUNT_UNUSED ==> res is Ok,
     )]
     pub(super) fn get_from_unused<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
         paddr: Paddr,
         metadata: M,
         as_unique_ptr: bool,
     ) -> Result<*const Self, GetFrameError> {
```

```diff
@@ ostd/src/mm/frame/mod.rs, from line 208 @@
                 &&& typed_meta_wf::<M>(res.slot_perm(), res.metadata_perm(), *final(repr_perm))
                 &&& M::from_repr_spec(res.metadata_perm().storage_perm.value(), *final(repr_perm)) == metadata
                 &&& res.inv()
                 &&& res.start_paddr_spec() == paddr
                 &&& res.wf_with_region(*final(regions))
             },
-            r is Err ==> *final(regions) == *old(regions)
+            r is Err ==> *final(regions) == *old(regions),
+            crate::specs::arch::valid_frame_paddr(paddr) && old(regions).slot_owner(paddr).ref_count()
+                == crate::mm::frame::meta::REF_COUNT_UNUSED ==> r is Ok,
     )]
     pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError> {
         #[verus_spec(with
             Tracked(regions),
             Tracked(repr_perm) => Tracked(permissions)
         )]
```

**A client that fails** (module `mm.frame`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__impl__5__from_unused_0<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut paddr: usize,
    mut metadata: M,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(repr_perm): Tracked<&mut <M as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        old(regions).inv(),
{
    let ghost old_regions = (*regions);
    let ghost old_repr_perm = (*repr_perm);
    let mut r = (#[verus_spec(with Tracked(regions), Tracked(repr_perm))] Frame::<M>::from_unused(paddr, metadata));
    assert(valid_frame_paddr(paddr) && old_regions.slot_owner(paddr).ref_count() == REF_COUNT_UNUSED ==> r is Ok); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(valid_frame_paddr(paddr) && old_regions.slot_owner(paddr).ref_count() == REF_COUNT_UNUSED ==> r is Ok); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

## `mm/frame/mod.rs`

<a id="r51"></a>

### R51. Frame::into_raw ensures raw_permission.inv() and r == start_paddr_spec() but not raw_permission.slot_vaddr() == frame_to_meta(r), which Frame::from_raw requires; the clause is proved alone by provable.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/mod.rs, from line 489 @@
             -> raw_permission: Tracked<FrameRawPerms>,
         requires
             self.inv(),
         ensures
             r == self.start_paddr_spec(),
             raw_permission@.inv(),
+            (raw_permission@.slot_vaddr() == crate::mm::frame::meta::mapping::frame_to_meta(r)),
     )]
     pub(in crate::mm) fn into_raw(mut self) -> Paddr {
         broadcast use group_page_meta;
 
         proof_decl!{
             let tracked perm = FrameRawPerms {
```

**A client that fails** (module `mm.frame`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn flow_mm__frame__impl__7__into_raw_mm__frame__impl__9__from_raw_0<M: AnyFrameMeta + Repr<MetaSlotStorage>, M_g: AnyFrameMeta + Repr<MetaSlotStorage>>(
    mut self_: Frame<M>,
)
    requires
        self_.inv(),
{
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with  => Tracked(gr))] self_.into_raw());
    assert(crate::specs::arch::valid_frame_paddr(r)); // requires of mm::frame::impl&%9::from_raw
    assert((gr.slot_vaddr() == crate::mm::frame::meta::mapping::frame_to_meta(r))); // requires of mm::frame::impl&%9::from_raw
    assert(gr.inv()); // requires of mm::frame::impl&%9::from_raw
    let mut w = unsafe { (#[verus_spec(with Tracked(gr))] Frame::<M_g>::from_raw(r)) };
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((gr.slot_vaddr() == crate::mm::frame::meta::mapping::frame_to_meta(r))); // requires of mm::frame::impl&%9::from_raw`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 12 failing clients in 2 groups of failures pass.

## `mm/frame/segment.rs`

<a id="r52"></a>

### R52. Segment::into_raw ensures raw_perms@ == self.raw_perms() only, and with size()/start_paddr()/end_paddr() closed the length, alignment, bounds and per-frame slot addresses of the returned permissions in terms of the returned range (what Segment::from_raw requires) are not visible; the clauses are proved alone by provable.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 811 @@
             -> raw_perms: Tracked<Seq<FrameRawPerms>>,
         requires
             self.inv(),
         ensures
             r == self.range(),
             raw_perms@ == self.raw_perms(),
+            (raw_perms@.len() == ((r.end - r.start) / (crate::arch::mm::PAGE_SIZE as int))),
+            ((r.start <= r.end) && (r.end <= crate::mm::MAX_PADDR)),
+            (forall|i: int| #![trigger raw_perms@.spec_index(i)] (((0 <= i) && (i < raw_perms@.len())) ==> ((raw_perms@.spec_index(i).slot_vaddr() == crate::mm::frame::meta::mapping::frame_to_meta_spec((((r.start as int) + (i * (crate::arch::mm::PAGE_SIZE as int))) as usize))) && raw_perms@.spec_index(i).inv()))),
+            ((r.start % crate::arch::mm::PAGE_SIZE) == 0),
+            ((r.end % crate::arch::mm::PAGE_SIZE) == 0),
     )]
     pub(crate) fn into_raw(mut self) -> Range<Paddr> {
         let range = self.range.clone();
 
         proof_decl!{
             let tracked raw_perms = self.tracked_perms.tracked_take();
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn flow_mm__frame__segment__impl__3__into_raw_mm__frame__segment__impl__1__from_raw_0<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf, M_g: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut self_: Segment<M>,
)
    requires
        self_.inv(),
{
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with  => Tracked(gr))] self_.into_raw());
    assert(((r.start % crate::arch::mm::PAGE_SIZE) == 0)); // requires of mm::frame::segment::impl&%1::from_raw
    assert(((r.end % crate::arch::mm::PAGE_SIZE) == 0)); // requires of mm::frame::segment::impl&%1::from_raw
    assert(((r.start <= r.end) && (r.end <= crate::mm::MAX_PADDR))); // requires of mm::frame::segment::impl&%1::from_raw
    assert((gr.len() == ((r.end - r.start) / (crate::arch::mm::PAGE_SIZE as int)))); // requires of mm::frame::segment::impl&%1::from_raw
    assert((forall|i: int| #![trigger gr.spec_index(i)] (((0 <= i) && (i < gr.len())) ==> ((gr.spec_index(i).slot_vaddr() == crate::mm::frame::meta::mapping::frame_to_meta_spec((((r.start as int) + (i * (crate::arch::mm::PAGE_SIZE as int))) as usize))) && gr.spec_index(i).inv())))); // requires of mm::frame::segment::impl&%1::from_raw
    let mut w = unsafe { (#[verus_spec(with Tracked(gr))] Segment::<M_g>::from_raw(r)) };
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((gr.len() == ((r.end - r.start) / (crate::arch::mm::PAGE_SIZE as int)))); // requires of mm::frame::segment::impl&%1::from_raw`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 10 failing clients in 2 groups of failures pass.

<a id="r53"></a>

### R53. Segment::split ensures only (r.0, r.1) == split_spec(offset) with split_spec closed, so callers get neither the halves' inv() (proved alone by provable) nor their ranges, both of which the body establishes directly.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 591 @@
     #[verus_spec(r =>
         requires
             self.inv(),
             offset % PAGE_SIZE != 0 ==> may_panic(),
             !(0 < offset && offset < self.size()) ==> may_panic(),
         ensures
+            r.0.inv() && r.1.inv(),
+            r.0.start_paddr() == self.start_paddr(),
+            r.0.end_paddr() == self.start_paddr() + offset,
+            r.1.start_paddr() == self.start_paddr() + offset,
+            r.1.end_paddr() == self.end_paddr(),
             (r.0, r.1) == self.split_spec(offset),
     )]
     #[verifier::spinoff_prover]
     pub fn split(mut self, offset: usize) -> (Self, Self) {
         assert!(offset % PAGE_SIZE == 0);
         assert!(0 < offset && offset < self.size());
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__segment__impl__3__split_0<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut self_: Segment<M>,
    mut offset: usize,
)
    requires
        self_.inv(),
        (((offset % crate::arch::mm::PAGE_SIZE) != 0) ==> vstd_extra::panic::may_panic()),
        (!(((0 < offset) && (offset < self_.size()))) ==> vstd_extra::panic::may_panic()),
{
    proof { assume(!(((offset % crate::arch::mm::PAGE_SIZE) != 0))); } // no panic
    proof { assume(!(!(((0 < offset) && (offset < self_.size()))))); } // no panic
    let mut r = self_.split(offset);
    assert(r.0.inv() && r.1.inv()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.0.inv() && r.1.inv()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 35 failing clients in 7 groups of failures pass.

<a id="r54"></a>

### R54. Segment::split (closed split_spec) does not say the halves keep self's relation to a region, which holds since they take self's permissions [..k] and [k..] over the same frames; a ghost snapshot of self and an index-shift fact for the right half let the solver carry relate_regions over.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 592 @@
         requires
             self.inv(),
             offset % PAGE_SIZE != 0 ==> may_panic(),
             !(0 < offset && offset < self.size()) ==> may_panic(),
         ensures
             (r.0, r.1) == self.split_spec(offset),
+            forall|r_b: MetaRegionOwners| self.relate_regions(r_b) ==> r.0.relate_regions(r_b) && r.1.relate_regions(r_b),
     )]
     #[verifier::spinoff_prover]
     pub fn split(mut self, offset: usize) -> (Self, Self) {
         assert!(offset % PAGE_SIZE == 0);
         assert!(0 < offset && offset < self.size());
+        let ghost self0 = self;
 
         let tracked mut left_perms = self.tracked_perms.tracked_take();
         let tracked right_perms = seq_tracked_split_at(
             &mut left_perms,
             (offset / PAGE_SIZE) as int,
         );
         let old = ManuallyDrop::new(self);
         let at = old.range.start + offset;
+        proof {
+            let k = (offset / PAGE_SIZE) as int;
+            assert(offset == k * PAGE_SIZE);
+            assert forall|i: int|
+                #![trigger frame_to_index((at + i * PAGE_SIZE) as usize)]
+                0 <= i < right_perms.len() implies {
+                    &&& frame_to_index((at + i * PAGE_SIZE) as usize) == frame_to_index(
+                        (self0.range().start + (i + k) * PAGE_SIZE) as usize,
+                    )
+                    &&& right_perms[i] == self0.raw_perms()[i + k]
+                } by {
+                    assert((at + i * PAGE_SIZE) as usize == (self0.range().start + (i + k) * PAGE_SIZE) as usize);
+                }
+        }
 
         (
             Self {
                 range: old.range.start..at,
                 _marker: core::marker::PhantomData,
                 #[cfg(verus_keep_ghost_body)]
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__segment__impl__3__split_23<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut self_: Segment<M>,
    mut offset: usize,
)
    requires
        self_.inv(),
        (((offset % crate::arch::mm::PAGE_SIZE) != 0) ==> vstd_extra::panic::may_panic()),
        (!(((0 < offset) && (offset < self_.size()))) ==> vstd_extra::panic::may_panic()),
{
    proof { assume(!(((offset % crate::arch::mm::PAGE_SIZE) != 0))); } // no panic
    proof { assume(!(!(((0 < offset) && (offset < self_.size()))))); } // no panic
    let mut r = self_.split(offset);
    assert(forall|r_b: MetaRegionOwners| self_.relate_regions(r_b) ==> r.0.relate_regions(r_b) && r.1.relate_regions(r_b)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(forall|r_b: MetaRegionOwners| self_.relate_regions(r_b) ==> r.0.relate_regions(r_b) && r.1.relate_regions(r_b)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r55"></a>

### R55. Segment::from(Frame) is specified only by the closed from_spec, so the one-frame segment has no visible inv() or range; the impl gets ensures r.inv() and its range from the frame's start address (the body already works under its existing assume(frame.inv())), with group_page_meta for frame_to_meta(meta_to_frame(v)) == v.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 874 @@
         }
     }
 }
 
 #[verus_verify]
 impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> From<Frame<M>> for Segment<M> {
-    fn from(frame: Frame<M>) -> Self {
+    fn from(frame: Frame<M>) -> (r: Self)
+        ensures
+            r.inv(),
+            r.start_paddr() == frame.start_paddr_spec(),
+            r.end_paddr() == frame.start_paddr_spec() + PAGE_SIZE,
+    {
+        broadcast use group_page_meta;
+
         assume(frame.inv());
 
         let mut frame = frame;
         let pa = frame.start_paddr();
         proof_decl!{
             let tracked frame_perm =
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__segment__impl__5__from_7<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    mut frame: Frame<M>,
)
{
    let mut r = <Segment<M> as From<Frame<M>>>::from(frame);
    assert(r.inv() && r.start_paddr() == frame.start_paddr_spec() && r.end_paddr() == frame.start_paddr_spec() + PAGE_SIZE); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.inv() && r.start_paddr() == frame.start_paddr_spec() && r.end_paddr() == frame.start_paddr_spec() + PAGE_SIZE); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

**Note.** the changed function's proof rests on an existing `assume` at `ostd/src/mm/frame/segment.rs:881` (`frame.inv()`).

<a id="r56"></a>

### R56. Segment::next has only the Iterator spec through the closed remaining(), so callers learn nothing about the yielded frame, the advanced start or self.inv() afterwards; the impl gets ensures for these, which the body (from_raw's ensures, pop_front, start += PAGE_SIZE) establishes.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 902 @@
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Iterator for Segment<M> {
     type Item = Frame<M>;
 
     #[verifier::rlimit(200)]
-    fn next(&mut self) -> Option<Self::Item> {
+    fn next(&mut self) -> (r: Option<Self::Item>)
+        ensures
+            final(self).inv(),
+            final(self).end_paddr() == old(self).end_paddr(),
+            old(self).start_paddr() < old(self).end_paddr() ==> r is Some,
+            forall|rg: MetaRegionOwners|
+                #![trigger final(self).relate_regions(rg)]
+                old(self).relate_regions(rg) ==> final(self).relate_regions(rg),
+            r matches Some(f) ==> {
+                &&& f.inv()
+                &&& f.start_paddr_spec() == old(self).start_paddr()
+                &&& final(self).start_paddr() == old(self).start_paddr() + PAGE_SIZE
+            },
+    {
         proof {
             // This is a verification limitation that the `#[verifier::type_invariant]` can not be broken.
             // It is still sound because `Segment` is always exposed with `inv`.
             assume(self.inv());
         }
 
@@ ostd/src/mm/frame/segment.rs, from line 927 @@
             // when creating the `Segment` object.
             let frame = unsafe {
                 #[verus_spec(with Tracked(perm))]
                 Frame::<M>::from_raw(self.range.start)
             };
             self.range.start += PAGE_SIZE;
+            proof {
+                let s0 = *old(self);
+                assert(self.raw_perms() == s0.raw_perms().drop_first());
+                assert(self.inv());
+                assert(self.len() == s0.len() - 1);
+                assert forall|r: MetaRegionOwners|
+                    #![trigger self.relate_regions(r)]
+                    s0.relate_regions(r) implies self.relate_regions(r) by {
+                    assert forall|i: int|
+                        #![trigger frame_to_index((self.range().start + i * PAGE_SIZE) as usize)]
+                        0 <= i < self.len() implies {
+                            &&& frame_to_index((self.range().start + i * PAGE_SIZE) as usize)
+                                == frame_to_index((s0.range().start + (i + 1) * PAGE_SIZE) as usize)
+                            &&& self.raw_perms()[i] == s0.raw_perms()[i + 1]
+                        } by {
+                        assert((self.range().start + i * PAGE_SIZE) as usize
+                            == (s0.range().start + (i + 1) * PAGE_SIZE) as usize);
+                    }
+                }
+            }
             Some(frame)
         } else {
             None
         }
     }
 }
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__segment__impl__6__next_21<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    self_: &mut Segment<M>,
)
{
    let ghost old_self_ = (*self_);
    let mut r = self_.next();
    assert((*self_).inv()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).inv()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 13 failing clients in 8 groups of failures pass.

**Note.** the changed function's proof rests on an existing `assume` at `ostd/src/mm/frame/segment.rs:912` (`self.inv()`).

<a id="r74"></a>

### R74. Segment::drop/clone give no frame condition on the slot owners outside the segment's frames, though each Frame::drop / inc_frame_ref_count underneath changes only its own slot (insert_slot_owner); kept as a loop invariant and exported (drop also exports slots and the owner domain unchanged); the slice half, whose loop hit rlimit, is moved to frame2-2/frame2-3.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 118 @@
         res: Self,
     ) -> bool {
         &&& res.range() == self.range()
         &&& res.inv()
         &&& new_perm.inv()
         &&& res.relate_regions(new_perm)
+        &&& forall|i: int|
+            #![trigger new_perm.slot_owners[i]]
+            (i < frame_to_index(self.start_paddr()) || frame_to_index(self.end_paddr()) <= i)
+                ==> new_perm.slot_owners[i] == old_perm.slot_owners[i]
     }
 
     #[verifier::rlimit(200)]
     fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self) {
         let mut paddr = self.range.start;
         proof_decl! {
@@ ostd/src/mm/frame/segment.rs, from line 134 @@
             invariant
                 perm.inv(),
                 self.inv(),
                 self.relate_regions(*old(perm)),
                 perm.slots == old(perm).slots,
                 perm.slot_owners.dom() == old(perm).slot_owners.dom(),
+                forall|i: int|
+                    #![trigger perm.slot_owners[i]]
+                    (i < frame_to_index(self.range.start) || frame_to_index(self.range.end) <= i)
+                        ==> perm.slot_owners[i] == old(perm).slot_owners[i],
                 raw_perms.len() == (paddr - self.range.start) / (PAGE_SIZE as int),
                 forall|i: int|
                     #![trigger raw_perms[i]]
                     0 <= i < raw_perms.len() ==> {
                         let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                         &&& raw_perms[i].slot_perm == perm.slots[idx]
@@ ostd/src/mm/frame/segment.rs, from line 990 @@
                     &&& old(regions).ref_count(idx) == 1 ==> {
                         &&& old(regions).slot_owners[idx].in_list_perm.value() == 0
                     }
                 },
         ensures
             final(regions).inv(),
+            final(regions).slots == old(regions).slots,
+            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            forall|i: int|
+                #![trigger final(regions).slot_owners[i]]
+                (i < frame_to_index(self.start_paddr()) || frame_to_index(self.end_paddr()) <= i)
+                    ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
     )]
     pub fn drop(self) {
         let ghost n = self.len();
         let mut paddr = self.range.start;
         let tracked mut raw_perms = self.tracked_perms.get().tracked_unwrap();
 
@@ ostd/src/mm/frame/segment.rs, from line 1034 @@
                     #![trigger frame_idx_at(self.range.start, j)]
                     k <= j < n ==> regions.contains(frame_idx_at(self.range.start, j))
                         && regions.slot_owners[frame_idx_at(self.range.start, j)] == old(
                         regions,
                     ).slot_owners[frame_idx_at(self.range.start, j)],
                 regions.slot_owners.dom() == old(regions).slot_owners.dom(),
+                regions.slots == old(regions).slots,
+                forall|i: int|
+                    #![trigger regions.slot_owners[i]]
+                    (i < frame_to_index(self.range.start) || frame_to_index(self.range.end) <= i)
+                        ==> regions.slot_owners[i] == old(regions).slot_owners[i],
                 self.relate_regions(*old(regions)),
                 forall|i: int|
                     #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
                     0 <= i < n ==> {
                         let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                         &&& old(regions).slot_owners[idx].storage_perm().is_init()
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__segment__impl__0__clone_6<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    self_: &Segment<M>,
    Tracked(perm): Tracked<&mut MetaRegionOwners>,
)
    requires
        self_.clone_requires((*old(perm))),
        forall|pa: usize| #![trigger crate::specs::mm::frame::mapping::frame_to_index(pa)] self_.start_paddr() <= pa < self_.end_paddr() && pa % crate::arch::mm::PAGE_SIZE == 0 ==> old(perm).ref_count(crate::specs::mm::frame::mapping::frame_to_index(pa)) + 1 < crate::mm::frame::meta::REF_COUNT_MAX,
{
    let ghost old_perm = (*perm);
    let mut r = self_.clone(Tracked(perm));
    assert(forall|i: int| #![trigger (*perm).slot_owners[i]] (i < frame_to_index(self_.start_paddr()) || frame_to_index(self_.end_paddr()) <= i) ==> (*perm).slot_owners[i] == old_perm.slot_owners[i]); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(forall|i: int| #![trigger (*perm).slot_owners[i]] (i < frame_to_index(self_.start_paddr()) || frame_to_index(self_.end_paddr()) <= i) ==> (*perm).slot_owners[i] == old_perm.slot_owners[i]); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 4 failing clients in 4 groups of failures pass.

<a id="r86"></a>

### R86. Segment::clone does not say that each of its frames' ref counts rose by exactly one, though each inc_frame_ref_count step ensures +1 for its own slot (inc_frame_reference_region_spec) and the frames are distinct (relate_regions); carry it as a clone loop invariant and ensure it in the impl in paddr form, which is what a second clone_requires needs.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 121 @@
         &&& res.inv()
         &&& new_perm.inv()
         &&& res.relate_regions(new_perm)
     }
 
     #[verifier::rlimit(200)]
-    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self) {
+    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self)
+        ensures
+            forall|pa: Paddr|
+                #![trigger frame_to_index(pa)]
+                (self.start_paddr() <= pa < self.end_paddr() && pa % PAGE_SIZE == 0)
+                    ==> final(perm).ref_count(frame_to_index(pa)) == old(perm).ref_count(
+                    frame_to_index(pa),
+                ) + 1,
+    {
         let mut paddr = self.range.start;
         proof_decl! {
             let tracked mut raw_perms = Seq::<FrameRawPerms>::tracked_empty();
         }
 
         loop
             invariant
                 perm.inv(),
                 self.inv(),
                 self.relate_regions(*old(perm)),
                 perm.slots == old(perm).slots,
+                forall|i: int|
+                    #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
+                    0 <= i < raw_perms.len() ==> perm.ref_count(
+                        frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
+                    ) == old(perm).ref_count(
+                        frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
+                    ) + 1,
                 perm.slot_owners.dom() == old(perm).slot_owners.dom(),
                 raw_perms.len() == (paddr - self.range.start) / (PAGE_SIZE as int),
                 forall|i: int|
                     #![trigger raw_perms[i]]
                     0 <= i < raw_perms.len() ==> {
                         let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
@@ ostd/src/mm/frame/segment.rs, from line 203 @@
                 );
             }
 
             paddr += PAGE_SIZE;
         }
 
+        proof {
+            assert forall|pa: Paddr|
+                #![trigger frame_to_index(pa)]
+                (self.start_paddr() <= pa < self.end_paddr() && pa % PAGE_SIZE == 0)
+                    implies perm.ref_count(frame_to_index(pa)) == old(perm).ref_count(
+                    frame_to_index(pa),
+                ) + 1 by {
+                let i = (pa - self.range.start) / (PAGE_SIZE as int);
+                assert((self.range.start + i * PAGE_SIZE) as usize == pa);
+                assert(0 <= i < raw_perms.len());
+            }
+        }
+
         Self {
             range: self.range.start..self.range.end,
             _marker: core::marker::PhantomData,
             #[cfg(verus_keep_ghost_body)]
             tracked_perms: Tracked(Some(raw_perms)),
         }
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__segment__impl__0__clone_5<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    self_: &Segment<M>,
    Tracked(perm): Tracked<&mut MetaRegionOwners>,
)
    requires
        self_.clone_requires((*old(perm))),
        forall|pa: usize| #![trigger crate::specs::mm::frame::mapping::frame_to_index(pa)] self_.start_paddr() <= pa < self_.end_paddr() && pa % crate::arch::mm::PAGE_SIZE == 0 ==> old(perm).ref_count(crate::specs::mm::frame::mapping::frame_to_index(pa)) + 1 < crate::mm::frame::meta::REF_COUNT_MAX,
{
    let ghost old_perm = (*perm);
    let mut r = self_.clone(Tracked(perm));
    assert(self_.start_paddr() < self_.end_paddr() ==> (*perm).slot_owner(self_.start_paddr()).ref_count() == old_perm.slot_owner(self_.start_paddr()).ref_count() + 1); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(self_.start_paddr() < self_.end_paddr() ==> (*perm).slot_owner(self_.start_paddr()).ref_count() == old_perm.slot_owner(self_.start_paddr()).ref_count() + 1); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

<a id="r87"></a>

### R87. Segment::drop ensures only regions.inv() and frame conditions, though each Frame::drop in its loop ensures rc > 1 ==> rc - 1 for its own slot and changes no other slot; carry the per-frame decrement as a drop loop invariant (with loop ensures k == n) and ensure it, in index form and for the first frame.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/segment.rs, from line 990 @@
                     &&& old(regions).ref_count(idx) == 1 ==> {
                         &&& old(regions).slot_owners[idx].in_list_perm.value() == 0
                     }
                 },
         ensures
             final(regions).inv(),
+            forall|i: int|
+                #![trigger frame_to_index((self.start_paddr() + i * PAGE_SIZE) as usize)]
+                0 <= i < self.len() && old(regions).ref_count(
+                    frame_to_index((self.start_paddr() + i * PAGE_SIZE) as usize),
+                ) > 1 ==> final(regions).ref_count(
+                    frame_to_index((self.start_paddr() + i * PAGE_SIZE) as usize),
+                ) == old(regions).ref_count(
+                    frame_to_index((self.start_paddr() + i * PAGE_SIZE) as usize),
+                ) - 1,
+            self.start_paddr() < self.end_paddr() && old(regions).slot_owner(
+                self.start_paddr(),
+            ).ref_count() > 1 ==> final(regions).slot_owner(self.start_paddr()).ref_count()
+                == old(regions).slot_owner(self.start_paddr()).ref_count() - 1,
     )]
     pub fn drop(self) {
         let ghost n = self.len();
         let mut paddr = self.range.start;
         let tracked mut raw_perms = self.tracked_perms.get().tracked_unwrap();
 
@@ ostd/src/mm/frame/segment.rs, from line 1044 @@
                         let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                         &&& old(regions).slot_owners[idx].storage_perm().is_init()
                         &&& old(regions).ref_count(idx) == 1 ==> {
                             &&& old(regions).slot_owners[idx].in_list_perm.value() == 0
                         }
                     },
+                forall|i: int|
+                    #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
+                    0 <= i < k && old(regions).ref_count(
+                        frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
+                    ) > 1 ==> regions.ref_count(
+                        frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
+                    ) == old(regions).ref_count(
+                        frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
+                    ) - 1,
+            ensures
+                k == n,
             decreases n - k,
         {
             if paddr >= self.range.end {
                 break;
             }
             proof {
@@ ostd/src/mm/frame/segment.rs, from line 1068 @@
             paddr += PAGE_SIZE;
 
             proof {
                 k = k + 1;
             }
         }
+        proof {
+            if self.range.start < self.range.end {
+                assert((self.range.start + 0 * PAGE_SIZE) as usize == self.range.start);
+                assert(frame_to_index((self.range.start + 0 * PAGE_SIZE) as usize)
+                    == frame_to_index(self.range.start));
+                assert(0 < n);
+            }
+        }
     }
 }
 
 /*impl<M: AnyFrameMeta> TryFrom<Segment<dyn AnyFrameMeta>> for Segment<M> {
     type Error = Segment<dyn AnyFrameMeta>;
 
```

**A client that fails** (module `mm.frame.segment`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__segment__impl__8__drop_11<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    mut self_: Segment<M>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        old(regions).inv(),
        self_.inv(),
        self_.relate_regions((*old(regions))),
        (forall|i: int| #![trigger crate::specs::mm::frame::mapping::frame_to_index((((self_.__VERUS_SPEC_start_paddr() as int) + (i * (crate::arch::mm::PAGE_SIZE as int))) as usize))] (((0 <= i) && (i < self_.len())) ==> ((*old(regions)).slot_owners.spec_index(crate::specs::mm::frame::mapping::frame_to_index((((self_.__VERUS_SPEC_start_paddr() as int) + (i * (crate::arch::mm::PAGE_SIZE as int))) as usize))).storage_perm().is_init() && (((*old(regions)).ref_count(crate::specs::mm::frame::mapping::frame_to_index((((self_.__VERUS_SPEC_start_paddr() as int) + (i * (crate::arch::mm::PAGE_SIZE as int))) as usize))) == 1) ==> ((*old(regions)).slot_owners.spec_index(crate::specs::mm::frame::mapping::frame_to_index((((self_.__VERUS_SPEC_start_paddr() as int) + (i * (crate::arch::mm::PAGE_SIZE as int))) as usize))).in_list_perm.value() == 0))))),
        forall|i: int| #![trigger crate::specs::mm::frame::mapping::frame_to_index((self_.start_paddr() + i * crate::arch::mm::PAGE_SIZE) as usize)] 0 <= i < self_.len() ==> old(regions).slot_owners[crate::specs::mm::frame::mapping::frame_to_index((self_.start_paddr() + i * crate::arch::mm::PAGE_SIZE) as usize)].in_list_perm.value() == 0,
{
    let ghost old_regions = (*regions);
    (#[verus_spec(with Tracked(regions))] self_.drop());
    assert(self_.start_paddr() < self_.end_paddr() && old_regions.slot_owner(self_.start_paddr()).ref_count() > 1 ==> (*regions).slot_owner(self_.start_paddr()).ref_count() == old_regions.slot_owner(self_.start_paddr()).ref_count() - 1); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(self_.start_paddr() < self_.end_paddr() && old_regions.slot_owner(self_.start_paddr()).ref_count() > 1 ==> (*regions).slot_owner(self_.start_paddr()).ref_count() == old_regions.slot_owner(self_.start_paddr()).ref_count() - 1); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

## `mm/frame/unique.rs`

<a id="r29"></a>

### R29. UniqueFrame::from_unused builds its owner with repr_perm Some and slot_index = frame_to_index(paddr) of a valid frame, but does not export owner.inv(), which every later UniqueFrame operation requires.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 82 @@
                 &&& res.wf(owner@->0)
                 &&& res.wf_with_region(owner@->0, *final(regions))
                 &&& owner@->0.meta_own == meta_own_in
                 &&& res.meta_value(owner@->0) == metadata
                 &&& res.inv()
                 &&& res.start_paddr_spec() == paddr
+                &&& owner@->0.inv()
             },
             res is Err ==> {
                 &&& owner@ is None
                 &&& *final(regions) == *old(regions)
             },
             final(regions).inv(),
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn flow_mm__frame__unique__impl__2__from_unused_mm__frame__unique__impl__2__meta_0<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut paddr: usize,
    mut metadata: M,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in): Tracked<M::Owner>,
    Tracked(repr_perm_in): Tracked<<M as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        old(regions).contains(crate::specs::mm::frame::mapping::frame_to_index(paddr)),
        (old(regions).slot_owner(paddr).usage is Unused),
        old(regions).inv(),
        <M as vstd_extra::ownership::OwnerOf>::wf(metadata, meta_own_in),
{
    let tracked mut meta_own_in = meta_own_in;
    let tracked mut repr_perm_in = repr_perm_in;
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(regions), Tracked(meta_own_in), Tracked(repr_perm_in) => Tracked(gr))] UniqueFrame::<M>::from_unused(paddr, metadata));
    if let Ok(mut x) = r {
        let tracked mut gro = gr.tracked_unwrap();
        assert(gro.inv()); // requires of mm::frame::unique::impl&%2::meta
        assert(x.inv()); // requires of mm::frame::unique::impl&%2::meta
        assert(x.wf(gro)); // requires of mm::frame::unique::impl&%2::meta
        assert(x.meta_wf(gro)); // requires of mm::frame::unique::impl&%2::meta
        let mut w = (#[verus_spec(with Tracked(&gro))] x.meta());
    } else {
    }
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gro.inv()); // requires of mm::frame::unique::impl&%2::meta`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 33 failing clients in 7 groups of failures pass.

<a id="r30"></a>

### R30. UniqueFrame::from_unused drops the frame condition that MetaSlot::get_from_unused gives (final == old.insert_slot_owner(paddr, ..), slots untouched), so callers holding other frames lose their facts.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 88 @@
             },
             res is Err ==> {
                 &&& owner@ is None
                 &&& *final(regions) == *old(regions)
             },
             final(regions).inv(),
+            final(regions).slots == old(regions).slots,
+            forall|i: int| #![trigger final(regions).slot_owners[i]]
+                i != frame_to_index(paddr) ==> final(regions).slot_owners[i]
+                    == old(regions).slot_owners[i],
     )]
     pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError> {
         let tracked mut repr_perm = repr_perm_in;
         #[verus_spec(with
             Tracked(regions),
             Tracked(&mut repr_perm) => Tracked(permissions)
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__2__from_unused_4<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut paddr: usize,
    mut metadata: M,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in): Tracked<M::Owner>,
    Tracked(repr_perm_in): Tracked<<M as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        old(regions).contains(crate::specs::mm::frame::mapping::frame_to_index(paddr)),
        (old(regions).slot_owner(paddr).usage is Unused),
        old(regions).inv(),
        <M as vstd_extra::ownership::OwnerOf>::wf(metadata, meta_own_in),
{
    let tracked mut meta_own_in = meta_own_in;
    let tracked mut repr_perm_in = repr_perm_in;
    let ghost old_regions = (*regions);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(regions), Tracked(meta_own_in), Tracked(repr_perm_in) => Tracked(gr))] UniqueFrame::<M>::from_unused(paddr, metadata));
    assert((*regions).slots == old_regions.slots); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*regions).slots == old_regions.slots); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 4 failing clients in 3 groups of failures pass.

<a id="r31"></a>

### R31. MetaSlot::get_from_unused leaves the claimed slot with in_list_perm.value() == 0, but UniqueFrame::from_unused does not forward it (nor owner.slot_index == frame_to_index(paddr)), which reset_as_unused/drop/repurpose/from_unique require.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 79 @@
         ensures
             res matches Ok(res) ==> {
                 &&& owner@ is Some
                 &&& res.wf(owner@->0)
                 &&& res.wf_with_region(owner@->0, *final(regions))
                 &&& owner@->0.meta_own == meta_own_in
+                &&& owner@->0.slot_index == frame_to_index(paddr)
+                &&& final(regions).slot_owners[owner@->0.slot_index].in_list_perm.value() == 0
                 &&& res.meta_value(owner@->0) == metadata
                 &&& res.inv()
                 &&& res.start_paddr_spec() == paddr
             },
             res is Err ==> {
                 &&& owner@ is None
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__2__from_unused_2<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut paddr: usize,
    mut metadata: M,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in): Tracked<M::Owner>,
    Tracked(repr_perm_in): Tracked<<M as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        old(regions).contains(crate::specs::mm::frame::mapping::frame_to_index(paddr)),
        (old(regions).slot_owner(paddr).usage is Unused),
        old(regions).inv(),
        <M as vstd_extra::ownership::OwnerOf>::wf(metadata, meta_own_in),
{
    let tracked mut meta_own_in = meta_own_in;
    let tracked mut repr_perm_in = repr_perm_in;
    let ghost old_regions = (*regions);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(regions), Tracked(meta_own_in), Tracked(repr_perm_in) => Tracked(gr))] UniqueFrame::<M>::from_unused(paddr, metadata));
    assert(r is Ok ==> (*regions).slot_owner(paddr).in_list_perm.value() == 0); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r is Ok ==> (*regions).slot_owner(paddr).in_list_perm.value() == 0); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r32"></a>

### R32. UniqueFrame::repurpose builds new_owner with repr_perm Some and the old valid slot index but does not export new_owner.inv(), which every later UniqueFrame operation requires.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 175 @@
             owner.inv(),
             <M1 as OwnerOf>::wf(metadata, meta_own_in),
         ensures
             res.wf(new_owner@),
             res.wf_with_region(new_owner@, *final(regions)),
             new_owner@.meta_own == meta_own_in,
+            new_owner@.inv(),
             res.meta_value(new_owner@) == metadata,
             final(regions).inv(),
     )]
     pub fn repurpose<M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
         mut self,
         metadata: M1,
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn flow_mm__frame__unique__impl__2__repurpose_mm__frame__unique__impl__2__repurpose_2<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf, M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf, M1_g: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut self_: UniqueFrame<M>,
    mut metadata: M1,
    Tracked(owner): Tracked<UniqueFrameOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in): Tracked<M1::Owner>,
    Tracked(repr_perm_in): Tracked<<M1 as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
    mut metadata_g: M1_g,
    Tracked(meta_own_in_g): Tracked<M1_g::Owner>,
    Tracked(repr_perm_in_g): Tracked<<M1_g as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        self_.wf_with_region(owner, (*old(regions))),
        (old(regions).slot_owners[self_.index()].in_list_perm.value() == 0),
        old(regions).inv(),
        self_.inv(),
        owner.inv(),
        <M1 as vstd_extra::ownership::OwnerOf>::wf(metadata, meta_own_in),
        <M1_g as vstd_extra::ownership::OwnerOf>::wf(metadata_g, meta_own_in_g),
{
    let tracked mut owner = owner;
    let tracked mut meta_own_in = meta_own_in;
    let tracked mut repr_perm_in = repr_perm_in;
    let tracked mut meta_own_in_g = meta_own_in_g;
    let tracked mut repr_perm_in_g = repr_perm_in_g;
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(meta_own_in), Tracked(repr_perm_in) => Tracked(gr))] self_.repurpose(metadata));
    assert(r.wf_with_region(gr, (*regions))); // requires of mm::frame::unique::impl&%2::repurpose
    assert((regions.slot_owners[r.index()].in_list_perm.value() == 0)); // requires of mm::frame::unique::impl&%2::repurpose
    assert(regions.inv()); // requires of mm::frame::unique::impl&%2::repurpose
    assert(r.inv()); // requires of mm::frame::unique::impl&%2::repurpose
    assert(gr.inv()); // requires of mm::frame::unique::impl&%2::repurpose
    assert(<M1_g as vstd_extra::ownership::OwnerOf>::wf(metadata_g, meta_own_in_g)); // requires of mm::frame::unique::impl&%2::repurpose
    proof_decl! { let tracked mut gr_g; }
    let mut w = (#[verus_spec(with Tracked(gr), Tracked(regions), Tracked(meta_own_in_g), Tracked(repr_perm_in_g) => Tracked(gr_g))] r.repurpose(metadata_g));
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr.inv()); // requires of mm::frame::unique::impl&%2::repurpose`

With the changes this client still failed: its other failures are other issues or the client's own (its status here is for the clause above only).

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 1 group of failures pass.

<a id="r33"></a>

### R33. UniqueFrame::repurpose mutably borrows only slot_owners[idx] (and never slots), but does not ensure the other slot_owners and the slots are unchanged.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 176 @@
             <M1 as OwnerOf>::wf(metadata, meta_own_in),
         ensures
             res.wf(new_owner@),
             res.wf_with_region(new_owner@, *final(regions)),
             new_owner@.meta_own == meta_own_in,
             res.meta_value(new_owner@) == metadata,
+            final(regions).slots == old(regions).slots,
+            forall|i: int| #![trigger final(regions).slot_owners[i]]
+                i != owner.slot_index ==> final(regions).slot_owners[i]
+                    == old(regions).slot_owners[i],
             final(regions).inv(),
     )]
     pub fn repurpose<M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
         mut self,
         metadata: M1,
     ) -> UniqueFrame<M1> {
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__2__repurpose_7<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf, M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut self_: UniqueFrame<M>,
    mut metadata: M1,
    Tracked(owner): Tracked<UniqueFrameOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in): Tracked<M1::Owner>,
    Tracked(repr_perm_in): Tracked<<M1 as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        self_.wf_with_region(owner, (*old(regions))),
        (old(regions).slot_owners[self_.index()].in_list_perm.value() == 0),
        old(regions).inv(),
        self_.inv(),
        owner.inv(),
        <M1 as vstd_extra::ownership::OwnerOf>::wf(metadata, meta_own_in),
{
    let tracked mut owner = owner;
    let tracked mut meta_own_in = meta_own_in;
    let tracked mut repr_perm_in = repr_perm_in;
    let ghost old_regions = (*regions);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(meta_own_in), Tracked(repr_perm_in) => Tracked(gr))] self_.repurpose(metadata));
    assert(forall|i: int| #![trigger (*regions).slot_owners[i]] i != owner.slot_index ==> (*regions).slot_owners[i] == old_regions.slot_owners[i]); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(forall|i: int| #![trigger (*regions).slot_owners[i]] i != owner.slot_index ==> (*regions).slot_owners[i] == old_regions.slot_owners[i]); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 1 group of failures pass.

<a id="r34"></a>

### R34. UniqueFrame::repurpose does not relate its result to self although transmute_spec gives the same slot_vaddr and new_owner.slot_index is meta_to_index(self.slot_vaddr()) == owner.slot_index.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 177 @@
         ensures
             res.wf(new_owner@),
             res.wf_with_region(new_owner@, *final(regions)),
             new_owner@.meta_own == meta_own_in,
             res.meta_value(new_owner@) == metadata,
             final(regions).inv(),
+            res.slot_vaddr() == self.slot_vaddr(),
+            res.start_paddr_spec() == self.start_paddr_spec(),
+            new_owner@.slot_index == owner.slot_index,
     )]
     pub fn repurpose<M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
         mut self,
         metadata: M1,
     ) -> UniqueFrame<M1> {
         proof_decl! {
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__2__repurpose_6<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf, M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut self_: UniqueFrame<M>,
    mut metadata: M1,
    Tracked(owner): Tracked<UniqueFrameOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in): Tracked<M1::Owner>,
    Tracked(repr_perm_in): Tracked<<M1 as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        self_.wf_with_region(owner, (*old(regions))),
        (old(regions).slot_owners[self_.index()].in_list_perm.value() == 0),
        old(regions).inv(),
        self_.inv(),
        owner.inv(),
        <M1 as vstd_extra::ownership::OwnerOf>::wf(metadata, meta_own_in),
{
    let tracked mut owner = owner;
    let tracked mut meta_own_in = meta_own_in;
    let tracked mut repr_perm_in = repr_perm_in;
    let ghost old_regions = (*regions);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(meta_own_in), Tracked(repr_perm_in) => Tracked(gr))] self_.repurpose(metadata));
    assert(gr.slot_index == owner.slot_index && (*regions).slot_owners[owner.slot_index].in_list_perm.value() == 0); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr.slot_index == owner.slot_index && (*regions).slot_owners[owner.slot_index].in_list_perm.value() == 0); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 2 groups of failures pass.

<a id="r35"></a>

### R35. UniqueFrame::reset_as_unused only touches the slot owner at owner.slot_index (like its sibling drop, which ensures this) but does not ensure slots and the other slot_owners are unchanged.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 387 @@
             owner.inv(),
             regions.inv(),
             self.wf_with_region(owner, *old(regions)),
             old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0,
         ensures
             final(regions).inv(),
+            final(regions).slots == old(regions).slots,
+            forall|i: int| #![trigger final(regions).slot_owners[i]]
+                i != owner.slot_index ==> final(regions).slot_owners[i]
+                    == old(regions).slot_owners[i],
     )]
     pub fn reset_as_unused(mut self) {
         let mut this = self;
 
         proof_decl! {
             let tracked mut owner = owner;
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn protocol_from_unused_reset_from_unused_99cc277c<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut paddr: usize,
    mut metadata: M,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in): Tracked<M::Owner>,
    Tracked(repr_perm_in): Tracked<<M as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
    mut self_: UniqueFrame<M>,
    Tracked(owner): Tracked<UniqueFrameOwner<M>>,
    Tracked(regions_1): Tracked<&mut MetaRegionOwners>,
    mut paddr_2: usize,
    mut metadata_2: M,
    Tracked(regions_2): Tracked<&mut MetaRegionOwners>,
    Tracked(meta_own_in_2): Tracked<M::Owner>,
    Tracked(repr_perm_in_2): Tracked<<M as vstd_extra::cast_ptr::Repr<MetaSlotStorage>>::ReprPerm>,
)
    requires
        old(regions).contains(crate::specs::mm::frame::mapping::frame_to_index(paddr)),
        (old(regions).slot_owner(paddr).usage is Unused),
        old(regions).inv(),
        <M as vstd_extra::ownership::OwnerOf>::wf(metadata, meta_own_in),
        <M as vstd_extra::ownership::OwnerOf>::wf(metadata_2, meta_own_in_2),
{
    let tracked mut meta_own_in = meta_own_in;
    let tracked mut repr_perm_in = repr_perm_in;
    let tracked mut owner = owner;
    let tracked mut meta_own_in_2 = meta_own_in_2;
    let tracked mut repr_perm_in_2 = repr_perm_in_2;
    proof_decl! { let tracked mut o0; }
    let mut v0 = (#[verus_spec(with Tracked(regions), Tracked(meta_own_in), Tracked(repr_perm_in) => Tracked(o0))] UniqueFrame::<M>::from_unused(paddr, metadata));
    if let Ok(mut x0) = v0 {
        let tracked mut g1 = o0.tracked_unwrap();
        assert(x0.inv()); // requires of mm::frame::unique::impl&%4::reset_as_unused
        assert(g1.inv()); // requires of mm::frame::unique::impl&%4::reset_as_unused
        assert(regions.inv()); // requires of mm::frame::unique::impl&%4::reset_as_unused
        assert(x0.wf_with_region(g1, (*regions))); // requires of mm::frame::unique::impl&%4::reset_as_unused
        assert((regions.slot_owners[g1.slot_index].in_list_perm.value() == 0)); // requires of mm::frame::unique::impl&%4::reset_as_unused
        (#[verus_spec(with Tracked(g1), Tracked(regions))] x0.reset_as_unused());
        assert(regions.contains(crate::specs::mm::frame::mapping::frame_to_index(paddr))); // requires of mm::frame::unique::impl&%2::from_unused
        assert((regions.slot_owner(paddr).usage is Unused)); // requires of mm::frame::unique::impl&%2::from_unused
        assert(regions.inv()); // requires of mm::frame::unique::impl&%2::from_unused
        assert(<M as vstd_extra::ownership::OwnerOf>::wf(metadata_2, meta_own_in_2)); // requires of mm::frame::unique::impl&%2::from_unused
        proof_decl! { let tracked mut o2; }
        let mut v2 = (#[verus_spec(with Tracked(regions), Tracked(meta_own_in_2), Tracked(repr_perm_in_2) => Tracked(o2))] UniqueFrame::<M>::from_unused(paddr, metadata_2));
        if let Ok(mut x2) = v2 {
        } else {
        }
    } else {
    }
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(regions.contains(crate::specs::mm::frame::mapping::frame_to_index(paddr))); // requires of mm::frame::unique::impl&%2::from_unused`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r37"></a>

### R37. Frame::from_unique mutably borrows only slot_owners[idx] with idx == owner.slot_index but ensures only that slots and the slot_owners domain are unchanged, not the other slot_owners.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 560 @@
         ensures
             res.inv(),
             final(regions).inv(),
             res.wf_with_region(*final(regions)),
             final(regions).slots == old(regions).slots,
             final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            forall|i: int| #![trigger final(regions).slot_owners[i]]
+                i != owner.slot_index ==> final(regions).slot_owners[i]
+                    == old(regions).slot_owners[i],
     )]
     pub fn from_unique(unique: UniqueFrame<M>) -> Self {
         let tracked mut owner = owner;
         let ptr = unique.ptr;
         let ghost idx = meta_to_index(unique.slot_vaddr());
         proof {
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__6__from_unique_22<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut unique: UniqueFrame<M>,
    Tracked(owner): Tracked<UniqueFrameOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        unique.inv(),
        owner.inv(),
        old(regions).inv(),
        unique.wf_with_region(owner, (*old(regions))),
        (old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0),
        old(regions).slot_owners[owner.slot_index].paths_in_pt.is_empty(),
{
    let tracked mut owner = owner;
    let ghost old_regions = (*regions);
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions))] Frame::<M>::from_unique(unique));
    assert(forall|i: int| i != owner.slot_index ==> (*regions).slot_owners[i] == old_regions.slot_owners[i]); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(forall|i: int| i != owner.slot_index ==> (*regions).slot_owners[i] == old_regions.slot_owners[i]); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 1 group of failures pass.

<a id="r38"></a>

### R38. Frame::from_unique stores ref_count 1 and leaves usage untouched, but does not export either, so the new Frame fails Frame::clone's clone_requires (ref_count > 0, != REF_COUNT_UNUSED).

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 556 @@
             owner.inv(),
             old(regions).inv(),
             unique.wf_with_region(owner, *old(regions)),
             old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0,
         ensures
             res.inv(),
+            final(regions).slot_owners[res.index()].ref_count() == 1,
+            final(regions).slot_owners[owner.slot_index].ref_count() == 1,
+            final(regions).slot_owners[owner.slot_index].usage
+                == old(regions).slot_owners[owner.slot_index].usage,
             final(regions).inv(),
             res.wf_with_region(*final(regions)),
             final(regions).slots == old(regions).slots,
             final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
     )]
     pub fn from_unique(unique: UniqueFrame<M>) -> Self {
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__6__from_unique_12<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut unique: UniqueFrame<M>,
    Tracked(owner): Tracked<UniqueFrameOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        unique.inv(),
        owner.inv(),
        old(regions).inv(),
        unique.wf_with_region(owner, (*old(regions))),
        (old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0),
        old(regions).slot_owners[owner.slot_index].paths_in_pt.is_empty(),
{
    let tracked mut owner = owner;
    let ghost old_regions = (*regions);
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions))] Frame::<M>::from_unique(unique));
    assert((*regions).slot_owners[owner.slot_index].ref_count() == 1); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*regions).slot_owners[owner.slot_index].ref_count() == 1); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

<a id="r39"></a>

### R39. Frame::from_unique builds the Frame from unique.ptr but does not ensure res.ptr == unique.ptr, so a caller does not know the shared frame is the same page.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 558 @@
             unique.wf_with_region(owner, *old(regions)),
             old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0,
         ensures
             res.inv(),
             final(regions).inv(),
             res.wf_with_region(*final(regions)),
+            res.ptr == unique.ptr,
+            res.start_paddr_spec() == unique.start_paddr_spec(),
             final(regions).slots == old(regions).slots,
             final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
     )]
     pub fn from_unique(unique: UniqueFrame<M>) -> Self {
         let tracked mut owner = owner;
         let ptr = unique.ptr;
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__6__from_unique_11<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut unique: UniqueFrame<M>,
    Tracked(owner): Tracked<UniqueFrameOwner<M>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        unique.inv(),
        owner.inv(),
        old(regions).inv(),
        unique.wf_with_region(owner, (*old(regions))),
        (old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0),
        old(regions).slot_owners[owner.slot_index].paths_in_pt.is_empty(),
{
    let tracked mut owner = owner;
    let ghost old_regions = (*regions);
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions))] Frame::<M>::from_unique(unique));
    assert(r.start_paddr_spec() == unique.start_paddr_spec()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.start_paddr_spec() == unique.start_paddr_spec()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r40"></a>

### R40. UniqueFrame::try_from_shared says nothing about its result: on Ok the CAS set ref_count to REF_COUNT_UNIQUE and the frame's pointer and recombined full metadata permission give u.inv() with the same start_paddr; on Err the failed CAS leaves the slot (hence regions) unchanged and returns frame itself.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 608 @@
             frame.inv(),
             old(regions).inv(),
             frame.wf_with_region(*old(regions)),
         ensures
             final(regions).slots == old(regions).slots,
             final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            res matches Ok(u) ==> {
+                &&& u.inv()
+                &&& u.ptr == frame.ptr
+                &&& u.start_paddr_spec() == frame.start_paddr_spec()
+                &&& final(regions).slot_owners[frame.index()].ref_count() == REF_COUNT_UNIQUE
+            },
+            res matches Err(f) ==> {
+                &&& f == frame
+                &&& *final(regions) == *old(regions)
+            },
     )]
     pub fn try_from_shared(mut frame: Frame<M>) -> Result<Self, Frame<M>> {
         let ghost idx = meta_to_index(frame.slot_vaddr());
         proof {
             broadcast use group_page_meta;
 
@@ ostd/src/mm/frame/unique.rs, from line 642 @@
                         tracked_slot_perm: frame.tracked_slot_perm,
                         #[cfg(verus_keep_ghost_body)]
                         tracked_metadata_perm: Tracked(Some(metadata_perms)),
                     },
                 )
             },
-            Err(_) => Err(frame),
+            Err(_) => {
+                proof {
+                    vstd_extra::auxiliary::axiom_permission_u64_ext_eq(
+                        regions.slot_owners[idx].ref_count_perm,
+                        old(regions).slot_owners[idx].ref_count_perm,
+                    );
+                }
+                Err(frame)
+            },
         }
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> From<UniqueFrame<M>> for Frame<M> {
     #[verifier::external_body]
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__7__try_from_shared_16<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut frame: Frame<M>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        frame.inv(),
        old(regions).inv(),
        frame.wf_with_region((*old(regions))),
        old(regions).slot_owners[frame.index()].ref_count() < crate::mm::frame::meta::REF_COUNT_MAX,
{
    let ghost old_regions = (*regions);
    let mut r = (#[verus_spec(with Tracked(regions))] UniqueFrame::<M>::try_from_shared(frame));
    assert(r is Err ==> (*regions) == old_regions); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r is Err ==> (*regions) == old_regions); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 5 failing clients in 5 groups of failures pass.

<a id="r84"></a>

### R84. UniqueFrame::try_from_shared does not say when it succeeds, though its CAS on the slot's ref_count_perm (vstd compare_exchange) yields Ok exactly when the old ref count is 1; ensure (res is Ok) == (old ref_count == 1) spec-only.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/unique.rs, from line 606 @@
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
         requires
             frame.inv(),
             old(regions).inv(),
             frame.wf_with_region(*old(regions)),
         ensures
+            (res is Ok) == (old(regions).slot_owners[frame.index()].ref_count() == 1),
             final(regions).slots == old(regions).slots,
             final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
     )]
     pub fn try_from_shared(mut frame: Frame<M>) -> Result<Self, Frame<M>> {
         let ghost idx = meta_to_index(frame.slot_vaddr());
         proof {
```

**A client that fails** (module `mm.frame.unique`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__unique__impl__7__try_from_shared_18<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
    mut frame: Frame<M>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
)
    requires
        frame.inv(),
        old(regions).inv(),
        frame.wf_with_region((*old(regions))),
        old(regions).slot_owners[frame.index()].ref_count() < crate::mm::frame::meta::REF_COUNT_MAX,
{
    let ghost old_regions = (*regions);
    let mut r = (#[verus_spec(with Tracked(regions))] UniqueFrame::<M>::try_from_shared(frame));
    assert((r is Ok) == (old_regions.slot_owners[frame.index()].ref_count() == 1)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((r is Ok) == (old_regions.slot_owners[frame.index()].ref_count() == 1)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

## `mm/frame/untyped.rs`

<a id="r49"></a>

### R49. Segment::reader and Segment::writer get read_view_initialized()/has_write_view() of the owner from VmReader/VmWriter::from_kernel_space but do not ensure them; forward them.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/untyped.rs, from line 109 @@
             r.inv(),
             owner@.inv(),
             r.wf(owner@),
             r.cursor.vaddr == paddr_to_vaddr(self.start_paddr()),
             r.remain_spec() == self.size(),
             owner@.is_kernel,
+            owner@.read_view_initialized(),
     )]
     pub fn reader(&self) -> VmReader<'_, Infallible> {
         proof_decl! {
             let ghost id: nat;
             let tracked owner: VmIoOwner;
         }
@@ ostd/src/mm/frame/untyped.rs, from line 152 @@
             owner@.inv(),
             r.wf(owner@),
             r.cursor.vaddr == paddr_to_vaddr(self.start_paddr()),
             r.avail_spec() == self.size(),
             owner@.is_kernel,
             !owner@.is_fallible,
+            owner@.has_write_view(),
     )]
     pub fn writer(&self) -> VmWriter<'_, Infallible> {
         proof_decl! {
             let ghost id: nat;
             let tracked owner: VmIoOwner;
         }
```

**A client that fails** (module `mm.frame.untyped`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__untyped__impl__0__writer_0<'a, M: AnyUFrameMeta + OwnerOf>(
    self_: &'a Segment<M>,
)
    requires
        self_.inv(),
{
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with  => Tracked(gr))] self_.writer());
    assert(gr.has_write_view()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr.has_write_view()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 13 failing clients in 5 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

## `mm/io.rs`

<a id="r1"></a>

### R1. VmReader::read restores both owners' views (advance keeps the initialized ReadView, split keeps the WriteView) but does not export final(owner_r).read_view_initialized() and final(owner_w).has_write_view(), so write, read_val, write_val (which wrap it) and write_once (which advances its owner) cannot export them either and no reader/writer can be used twice.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 315 @@
             old(self).wf(*old(owner)),
             old(owner).has_write_view(),
         ensures
             final(self).inv(),
             final(owner).inv(),
             final(self).wf(*final(owner)),
+            final(owner).has_write_view(),
             match r {
                 Ok(_) => {
                     &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                 },
                 Err(_) => {
@@ ostd/src/mm/io.rs, from line 534 @@
             final(self).inv(),
             final(reader).inv(),
             final(owner_w).inv(),
             final(owner_r).inv(),
             final(self).wf(*final(owner_w)),
             final(reader).wf(*final(owner_r)),
+            final(owner_w).has_write_view(),
+            final(owner_r).read_view_initialized(),
             r == vstd::math::min(old(self).avail_spec() as int, old(reader).remain_spec() as int),
             final(self).avail_spec() == old(self).avail_spec() - r as usize,
             final(self).cursor.vaddr == old(self).cursor.vaddr + r as usize,
             final(reader).remain_spec() == old(reader).remain_spec() - r as usize,
             final(reader).cursor.vaddr == old(reader).cursor.vaddr + r as usize,
     )]
@@ ostd/src/mm/io.rs, from line 581 @@
             // cursor is aligned for `T`.
             old(self).cursor.vaddr % core::mem::align_of::<T>() != 0 ==> may_panic(),
         ensures
             final(self).inv(),
             final(owner).inv(),
             final(self).wf(*final(owner)),
+            final(owner).has_write_view(),
             match r {
                 Ok(_) => {
                     &&& old(self).cursor.vaddr % core::mem::align_of::<T>() == 0
                     &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                 },
@@ ostd/src/mm/io.rs, from line 776 @@
             old(owner_r).read_view_initialized(),
         ensures
             final(self).inv(),
             final(writer).inv(),
             final(self).wf(*final(owner_r)),
             final(writer).wf(*final(owner_w)),
+            final(owner_r).read_view_initialized(),
+            final(owner_w).has_write_view(),
             r == vstd::math::min(old(self).remain_spec() as int, old(writer).avail_spec() as int),
             final(self).remain_spec() == old(self).remain_spec() - r as usize,
             final(self).cursor.vaddr == old(self).cursor.vaddr + r as usize,
             final(writer).avail_spec() == old(writer).avail_spec() - r as usize,
             final(writer).cursor.vaddr == old(writer).cursor.vaddr + r as usize,
             consumed_w@.inv(),
@@ ostd/src/mm/io.rs, from line 876 @@
             old(self).wf(*old(owner)),
             old(owner).read_view_initialized(),
         ensures
             final(self).inv(),
             final(owner).inv(),
             final(self).wf(*final(owner)),
+            final(owner).read_view_initialized(),
             match r {
                 Ok(_) => {
                     &&& final(self).remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                 },
                 Err(_) => {
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__2__read_val_31<'a, T: Pod>(
    self_: &mut VmReader<'a, Infallible>,
    Tracked(owner): Tracked<&mut VmIoOwner>,
)
    requires
        old(self_).inv(),
        old(self_).wf((*old(owner))),
        old(owner).read_view_initialized(),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let mut r = (#[verus_spec(with Tracked(owner))] self_.read_val::<T>());
    assert((*owner).read_view_initialized()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*owner).read_view_initialized()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 34 failing clients in 14 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r2"></a>

### R2. VmReader::read only moves the two cursors but does not export that end and ghost_id of reader and writer are unchanged, so write, read_val and write_val (which wrap it) cannot export them either, unlike read_once and the fallible copies.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 323 @@
                     &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                 },
                 Err(_) => {
                     *old(self) == *final(self)
                 },
-            }
+            },
+            final(self).end == old(self).end,
+            final(self).ghost_id == old(self).ghost_id,
     )]
     pub fn write_val<T: Pod>(&mut self, new_val: &T) -> Result<()> {
         let len = core::mem::size_of::<T>();
         if self.avail() < len {
             return Err(Error::InvalidArgs);
         }
@@ ostd/src/mm/io.rs, from line 539 @@
             final(reader).wf(*final(owner_r)),
             r == vstd::math::min(old(self).avail_spec() as int, old(reader).remain_spec() as int),
             final(self).avail_spec() == old(self).avail_spec() - r as usize,
             final(self).cursor.vaddr == old(self).cursor.vaddr + r as usize,
             final(reader).remain_spec() == old(reader).remain_spec() - r as usize,
             final(reader).cursor.vaddr == old(reader).cursor.vaddr + r as usize,
+            final(self).end == old(self).end,
+            final(reader).end == old(reader).end,
+            final(self).ghost_id == old(self).ghost_id,
+            final(reader).ghost_id == old(reader).ghost_id,
     )]
     pub fn write(&mut self, reader: &mut VmReader<'_, Infallible>) -> usize {
         proof_decl! {
             let tracked mut _discarded_consumed_w: VmIoOwner;
         }
         #[verus_spec(with Tracked(owner_r), Tracked(owner_w) => Tracked(_discarded_consumed_w))]
@@ ostd/src/mm/io.rs, from line 785 @@
             final(writer).avail_spec() == old(writer).avail_spec() - r as usize,
             final(writer).cursor.vaddr == old(writer).cursor.vaddr + r as usize,
             consumed_w@.inv(),
             consumed_w@.range.start == old(owner_w).range.start,
             consumed_w@.range.end == old(owner_w).range.start + r as usize,
             consumed_w@.has_write_view(),
+            final(self).end == old(self).end,
+            final(writer).end == old(writer).end,
+            final(self).ghost_id == old(self).ghost_id,
+            final(writer).ghost_id == old(writer).ghost_id,
     )]
     pub fn read(&mut self, writer: &mut VmWriter<'_, Infallible>) -> usize {
         let copy_len = self.remain().min(writer.avail());
         proof_decl! {
             let tracked mut consumed_w_owner_inner: VmIoOwner;
         }
@@ ostd/src/mm/io.rs, from line 884 @@
                     &&& final(self).remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                 },
                 Err(_) => {
                     *old(self) == *final(self)
                 },
-            }
+            },
+            final(self).end == old(self).end,
+            final(self).ghost_id == old(self).ghost_id,
     )]
     pub fn read_val<T: Pod>(&mut self) -> Result<T> {
         let len = core::mem::size_of::<T>();
         if self.remain() < len {
             Err(Error::InvalidArgs)
         } else {
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__0__write_10<'a>(
    self_: &mut VmWriter<'a, Infallible>,
    reader: &mut VmReader<'a, Infallible>,
    Tracked(owner_w): Tracked<&mut VmIoOwner>,
    Tracked(owner_r): Tracked<&mut VmIoOwner>,
)
    requires
        old(self_).inv(),
        old(reader).inv(),
        old(self_).wf((*old(owner_w))),
        old(reader).wf((*old(owner_r))),
        old(owner_w).has_write_view(),
        old(owner_r).read_view_initialized(),
{
    let ghost old_self_ = (*self_);
    let ghost old_reader = (*reader);
    let ghost old_owner_w = (*owner_w);
    let ghost old_owner_r = (*owner_r);
    let mut r = (#[verus_spec(with Tracked(owner_w), Tracked(owner_r))] self_.write(reader));
    assert((*self_).end == old_self_.end && (*reader).end == old_reader.end && (*self_).ghost_id == old_self_.ghost_id && (*reader).ghost_id == old_reader.ghost_id); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).end == old_self_.end && (*reader).end == old_reader.end && (*self_).ghost_id == old_self_.ghost_id && (*reader).ghost_id == old_reader.ghost_id); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r3"></a>

### R3. The infallible write_val, write_once and read_val return Err only when the buffer is shorter than size_of::<T>(), but unlike read_once they do not export that enough space (and, for write_once, alignment) implies Ok.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 312 @@
             Tracked(owner): Tracked<&mut VmIoOwner>,
         requires
             old(self).inv(),
             old(self).wf(*old(owner)),
             old(owner).has_write_view(),
         ensures
+            old(self).avail_spec() >= core::mem::size_of::<T>() ==> r is Ok,
             final(self).inv(),
             final(owner).inv(),
             final(self).wf(*final(owner)),
             match r {
                 Ok(_) => {
                     &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
@@ ostd/src/mm/io.rs, from line 590 @@
                     &&& final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>()
                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>()
                 },
                 Err(_) => {
                     *old(self) == *final(self)
                 },
-            }
+            },
+            old(self).avail_spec() >= core::mem::size_of::<T>() && old(self).cursor.vaddr % core::mem::align_of::<T>() == 0 ==> r is Ok,
     )]
     pub fn write_once<T: PodOnce>(&mut self, new_val: &T) -> Result<()> {
         if self.avail() < core::mem::size_of::<T>() {
             return Err(Error::InvalidArgs);
         }
         let cursor = self.cursor.cast::<T>();
@@ ostd/src/mm/io.rs, from line 873 @@
             Tracked(owner): Tracked<&mut VmIoOwner>,
         requires
             old(self).inv(),
             old(self).wf(*old(owner)),
             old(owner).read_view_initialized(),
         ensures
+            old(self).remain_spec() >= core::mem::size_of::<T>() ==> r is Ok,
             final(self).inv(),
             final(owner).inv(),
             final(self).wf(*final(owner)),
             match r {
                 Ok(_) => {
                     &&& final(self).remain_spec() == old(self).remain_spec() - core::mem::size_of::<T>()
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__2__read_val_15<'a, T: Pod>(
    self_: &mut VmReader<'a, Infallible>,
    Tracked(owner): Tracked<&mut VmIoOwner>,
)
    requires
        old(self_).inv(),
        old(self_).wf((*old(owner))),
        old(owner).read_view_initialized(),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let mut r = (#[verus_spec(with Tracked(owner))] self_.read_val::<T>());
    assert(old_self_.remain_spec() >= core::mem::size_of::<T>() ==> r is Ok); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(old_self_.remain_spec() >= core::mem::size_of::<T>() ==> r is Ok); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

<a id="r4"></a>

### R4. Clone for VmReader copies cursor, end and ghost_id but has no ensures, so a clone is not known to equal the original or to satisfy inv().

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 645 @@
 impl<Fallibility> Clone for VmReader<'_, Fallibility> {
     /// [`Clone`] can be implemented for [`VmReader`]
     /// because it either points to untyped memory or represents immutable references.
     ///
     /// Note that we cannot implement [`Clone`] for [`VmWriter`]
     /// because it can represent mutable references, which must remain exclusive.
-    fn clone(&self) -> Self {
+    fn clone(&self) -> (res: Self)
+        ensures
+            res.cursor == self.cursor,
+            res.end == self.end,
+            res.ghost_id == self.ghost_id,
+    {
         Self { ghost_id: self.ghost_id, cursor: self.cursor, end: self.end, phantom: PhantomData }
     }
 }
 
 #[verus_verify]
 impl<'a> VmReader<'a, Infallible> {
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__1__clone_4<'a, Fallibility>(
    self_: &'a VmReader<'a, Fallibility>,
)
{
    let mut r = self_.clone();
    assert(r.cursor == self_.cursor && r.end == self_.end && r.ghost_id == self_.ghost_id); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.cursor == self_.cursor && r.end == self_.end && r.ghost_id == self_.ghost_id); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r5"></a>

### R5. VmReader::cursor (and VmWriter::cursor) return self.cursor but have no ensures saying so.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1565 @@
     #[verifier::when_used_as_spec(remain_spec)]
     pub fn remain(&self) -> usize {
         self.end.addr() - self.cursor.addr()
     }
 
     /// Returns the cursor pointer, which refers to the address of the next byte to read.
+    #[verus_spec(r =>
+        ensures
+            r == self.cursor,
+    )]
     pub fn cursor(&self) -> VirtPtr {
         self.cursor
     }
 
     /// Returns whether there is remaining data to read.
     #[verus_spec(
@@ ostd/src/mm/io.rs, from line 1699 @@
     #[verifier::when_used_as_spec(avail_spec)]
     pub fn avail(&self) -> usize {
         self.end.addr() - self.cursor.addr()
     }
 
     /// Returns the cursor pointer, which refers to the address of the next byte to write.
+    #[verus_spec(r =>
+        ensures
+            r == self.cursor,
+    )]
     pub fn cursor(&self) -> VirtPtr {
         self.cursor
     }
 
     /// Returns if it has available space to write.
     #[verus_spec(
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__4__cursor_0<'a, Fallibility>(
    self_: &'a VmReader<'a, Fallibility>,
)
{
    let mut r = self_.cursor();
    assert(r == self_.cursor); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r == self_.cursor); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 1 group of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r6"></a>

### R6. VmReader::has_remain and VmWriter::has_avail return remain() > 0 / avail() > 0 but have no ensures relating the result to remain_spec/avail_spec.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1570 @@
     /// Returns the cursor pointer, which refers to the address of the next byte to read.
     pub fn cursor(&self) -> VirtPtr {
         self.cursor
     }
 
     /// Returns whether there is remaining data to read.
-    #[verus_spec(
+    #[verus_spec(r =>
         requires
             self.inv(),
+        ensures
+            r == (self.remain_spec() > 0),
     )]
     pub fn has_remain(&self) -> bool {
         self.remain() > 0
     }
 
     /// Limits the length of remaining data.
@@ ostd/src/mm/io.rs, from line 1704 @@
     /// Returns the cursor pointer, which refers to the address of the next byte to write.
     pub fn cursor(&self) -> VirtPtr {
         self.cursor
     }
 
     /// Returns if it has available space to write.
-    #[verus_spec(
+    #[verus_spec(r =>
         requires
             self.inv(),
+        ensures
+            r == (self.avail_spec() > 0),
     )]
     pub fn has_avail(&self) -> bool {
         self.avail() > 0
     }
 
     /// Limits the length of available space.
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__5__has_avail_3<'a, Fallibility>(
    self_: &'a VmWriter<'a, Fallibility>,
)
    requires
        self_.inv(),
{
    let mut r = self_.has_avail();
    assert(r == (self_.avail_spec() > 0)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r == (self_.avail_spec() > 0)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r7"></a>

### R7. VmReader::limit and VmWriter::limit set the length to exactly min(old length, max) but ensure only upper bounds.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1587 @@
     #[verus_spec(r =>
         requires
             old(self).inv(),
         ensures
             r.inv(),
             r.remain_spec() <= max_remain,
+            r.remain_spec() == vstd::math::min(old(self).remain_spec() as int, max_remain as int),
             r.remain_spec() <= old(self).remain_spec(),
             r.cursor == old(self).cursor,
             r.ghost_id == old(self).ghost_id,
     )]
     pub fn limit(&mut self, max_remain: usize) -> &mut Self {
         if max_remain < self.remain() {
@@ ostd/src/mm/io.rs, from line 1721 @@
     #[verus_spec(r =>
         requires
             old(self).inv(),
         ensures
             r.inv(),
             r.avail_spec() <= max_avail,
+            r.avail_spec() == vstd::math::min(old(self).avail_spec() as int, max_avail as int),
             r.avail_spec() <= old(self).avail_spec(),
             r.cursor == old(self).cursor,
             r.ghost_id == old(self).ghost_id,
     )]
     pub fn limit(&mut self, max_avail: usize) -> &mut Self {
         if max_avail < self.avail() {
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__5__limit_6<'a, Fallibility>(
    self_: &mut VmWriter<'a, Fallibility>,
    mut max_avail: usize,
)
    requires
        old(self_).inv(),
{
    let ghost old_self_ = (*self_);
    let mut r = self_.limit(max_avail);
    assert(r.avail_spec() == vstd::math::min(old_self_.avail_spec() as int, max_avail as int)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.avail_spec() == vstd::math::min(old_self_.avail_spec() as int, max_avail as int)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r8"></a>

### R8. VmWriter::fill_zeros returns Ok(min(len, avail)) (Ok(0) when that is 0) but ensures only n <= len and n <= avail.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1864 @@
             {
                 let n = match r { Ok(n) => n, Err((_, n)) => n };
                 &&& n <= len
                 &&& n <= old(self).avail_spec()
                 &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
             },
+            r matches Ok(n) ==> n == vstd::math::min(len as int, old(self).avail_spec() as int),
     )]
     pub fn fill_zeros(&mut self, len: usize) -> core::result::Result<usize, (Error, usize)> {
         let len_to_set = self.avail().min(len);
         if len_to_set == 0 {
             return Ok(0);
         }
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__6__fill_zeros_23<'a>(
    self_: &mut VmWriter<'a, Fallible>,
    mut len: usize,
)
    requires
        old(self_).inv(),
{
    let ghost old_self_ = (*self_);
    let mut r = self_.fill_zeros(len);
    assert(r matches Ok(n) ==> n == vstd::math::min(len as int, old_self_.avail_spec() as int)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Ok(n) ==> n == vstd::math::min(len as int, old_self_.avail_spec() as int)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r9"></a>

### R9. read_fallible returns Ok only after copying the whole min(remain, avail) (a shorter copy is Err) but ensures only n <= remain and n <= avail on Ok, so write_fallible, the fallible read_val/write_val and collect cannot export the full advance on success.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1066 @@
         ensures
             final(self).inv(),
             final(self).end == old(self).end,
             final(self).ghost_id == old(self).ghost_id,
             final(self).cursor.range == old(self).cursor.range,
             r is Err ==> *final(self) == *old(self),
+            r is Ok ==> final(self).cursor.vaddr == old(self).cursor.vaddr + core::mem::size_of::<T>(),
     )]
     pub fn read_val<T: Pod>(&mut self) -> Result<T> {
         let len = core::mem::size_of::<T>();
         if self.remain() < len {
             Err(Error::InvalidArgs)
         } else {
@@ ostd/src/mm/io.rs, from line 1103 @@
     /// via [`axiom_slice_in_kernel`] — the natural trust boundary where a
     /// native Rust slice meets the tracked-memory model.
     #[verus_spec(r =>
         requires
             old(self).inv(),
         ensures
+            r is Ok ==> final(self).remain_spec() == 0,
             final(self).inv(),
             final(self).end == old(self).end,
             final(self).ghost_id == old(self).ghost_id,
             final(self).cursor.range == old(self).cursor.range,
             r is Err ==> *final(self) == *old(self),
     )]
@@ ostd/src/mm/io.rs, from line 1820 @@
         ensures
             final(self).inv(),
             final(self).end == old(self).end,
             final(self).ghost_id == old(self).ghost_id,
             final(self).cursor.range == old(self).cursor.range,
             r is Err ==> *final(self) == *old(self),
+            r is Ok ==> final(self).avail_spec() == old(self).avail_spec() - core::mem::size_of::<T>(),
     )]
     pub fn write_val<T: Pod>(&mut self, new_val: &T) -> Result<()> {
         let len = core::mem::size_of::<T>();
         if self.avail() < len {
             return Err(Error::InvalidArgs);
         }
@@ ostd/src/mm/io.rs, from line 2065 @@
                         let n = match r { Ok(n) => n, Err((_, n)) => n };
                         &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
                         &&& final(writer).cursor.vaddr == old(writer).cursor.vaddr + n
                         &&& n <= old(self).remain_spec()
                         &&& n <= old(writer).avail_spec()
                     },
+                    r matches Ok(n) ==> n == vstd::math::min(old(self).remain_spec() as int, old(writer).avail_spec() as int),
             )]
             fn read_fallible(
                 &mut self,
                 writer: &mut VmWriter<'_, $writer_fallibility>,
             ) -> core::result::Result<usize, (Error, usize)> {
                 let copy_len = self.remain().min(writer.avail());
@@ ostd/src/mm/io.rs, from line 2119 @@
                         let n = match r { Ok(n) => n, Err((_, n)) => n };
                         &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
                         &&& final(reader).cursor.vaddr == old(reader).cursor.vaddr + n
                         &&& n <= old(self).avail_spec()
                         &&& n <= old(reader).remain_spec()
                     },
+                    r matches Ok(n) ==> n == vstd::math::min(old(self).avail_spec() as int, old(reader).remain_spec() as int),
             )]
             fn write_fallible(
                 &mut self,
                 reader: &mut VmReader<'_, $reader_fallibility>,
             ) -> core::result::Result<usize, (Error, usize)> {
                 reader.read_fallible(self)
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__3__collect_22<'a>(
    self_: &mut VmReader<'a, Fallible>,
)
    requires
        old(self_).inv(),
{
    let ghost old_self_ = (*self_);
    let mut r = self_.collect();
    assert(r is Ok ==> (*self_).remain_spec() == 0); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r is Ok ==> (*self_).remain_spec() == 0); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 10 failing clients in 8 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r10"></a>

### R10. VmReader::collect allocates a buffer of remain() bytes and returns it on Ok but does not export its length.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1108 @@
         ensures
             final(self).inv(),
             final(self).end == old(self).end,
             final(self).ghost_id == old(self).ghost_id,
             final(self).cursor.range == old(self).cursor.range,
             r is Err ==> *final(self) == *old(self),
+            r matches Ok(v) ==> v@.len() == old(self).remain_spec(),
     )]
     pub fn collect(&mut self) -> Result<alloc::vec::Vec<u8>> {
         let len = self.remain();
         let mut buf = alloc::vec![0u8; len];
 
         let ptr = {
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__3__collect_21<'a>(
    self_: &mut VmReader<'a, Fallible>,
)
    requires
        old(self_).inv(),
{
    let ghost old_self_ = (*self_);
    let mut r = self_.collect();
    assert(r matches Ok(v) ==> v@.len() == old_self_.remain_spec()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Ok(v) ==> v@.len() == old_self_.remain_spec()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r11"></a>

### R11. The fallible read_val and write_val return Err(InvalidArgs) when the buffer is shorter than size_of::<T>() (documented) but do not export it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1061 @@
     /// returns `Err` and the reader's cursor is rolled back to its original
     /// position.
     #[verus_spec(r =>
         requires
             old(self).inv(),
         ensures
+            old(self).remain_spec() < core::mem::size_of::<T>() ==> r is Err,
             final(self).inv(),
             final(self).end == old(self).end,
             final(self).ghost_id == old(self).ghost_id,
             final(self).cursor.range == old(self).cursor.range,
             r is Err ==> *final(self) == *old(self),
     )]
@@ ostd/src/mm/io.rs, from line 1815 @@
     /// - On success, the cursor advances by `size_of::<T>()`.
     /// - On error, the cursor is at its original position (writer state preserved).
     #[verus_spec(r =>
         requires
             old(self).inv(),
         ensures
+            old(self).avail_spec() < core::mem::size_of::<T>() ==> r is Err,
             final(self).inv(),
             final(self).end == old(self).end,
             final(self).ghost_id == old(self).ghost_id,
             final(self).cursor.range == old(self).cursor.range,
             r is Err ==> *final(self) == *old(self),
     )]
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__3__read_val_18<'a, T: Pod>(
    self_: &mut VmReader<'a, Fallible>,
)
    requires
        old(self_).inv(),
{
    let ghost old_self_ = (*self_);
    let mut r = self_.read_val::<T>();
    assert(old_self_.remain_spec() < core::mem::size_of::<T>() ==> r is Err); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(old_self_.remain_spec() < core::mem::size_of::<T>() ==> r is Err); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

<a id="r21"></a>

### R21. VmReader::from_user_space builds its VmIoOwner with is_fallible true but does not ensure it, and VmSpace::reader does not export remain() == len or the owner's range, is_kernel and is_fallible.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 377 @@
             self.reader_success_cond(vaddr, len) ==> r is Ok && reader_owner@ is Some,
             r is Ok && reader_owner@ is Some ==> {
                 &&& r.unwrap().wf(reader_owner@->0)
                 &&& reader_owner@->0.mem_view is None
                 &&& reader_owner@->0.inv()
             },
+            r matches Ok(rd) ==> rd.remain_spec() == len && (reader_owner@ matches Some(o) ==> (o.range == Range { start: vaddr, end: (vaddr + len) as usize } && !o.is_kernel && o.is_fallible)),
             // Range bound is necessary for success: the body's `checked_add`
             // guard rejects any out-of-range request before constructing a
             // reader. `nat` arithmetic subsumes the overflow case.
             r is Ok ==> (vaddr as nat) + (len as nat) <= MAX_USERSPACE_VADDR as nat,
     )]
     pub fn reader(&self, vaddr: Vaddr, len: usize) -> Result<VmReader<'a, Fallible>> {
```

```diff
@@ ostd/src/mm/io.rs, from line 1029 @@
         ensures
             r.inv_wf(),
             owner@.id == id,
             owner@.range == ptr.range@,
             owner@.mem_view is None,
             !owner@.is_kernel,
+            owner@.is_fallible,
             r.cursor == ptr,
             r.end == ptr.wrapping_add_spec(len),
             r.end.range@ == ptr.range@,
             ptr.inv() && ptr.range@.start == ptr.vaddr
                 && len == ptr.range@.end - ptr.range@.start ==> {
                 &&& r.inv()
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__0__reader_44<'a>(
    self_: &'a VmSpace<'a>,
    mut vaddr: usize,
    mut len: usize,
    Tracked(owner): Tracked<&mut VmSpaceOwner>,
)
    requires
        old(owner).inv(),
{
    let ghost old_owner = (*owner);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner) => Tracked(gr))] self_.reader(vaddr, len));
    assert(r matches Ok(r_b) ==> r_b.remain_spec() == len && (gr matches Some(o) ==> (o.range == (vaddr..(vaddr + len) as usize) && !o.is_kernel && o.is_fallible))); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Ok(r_b) ==> r_b.remain_spec() == len && (gr matches Some(o) ==> (o.range == (vaddr..(vaddr + len) as usize) && !o.is_kernel && o.is_fallible))); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r89"></a>

### R89. VmReader::from_kernel_space builds its owner with is_fallible: false but does not ensure !owner@.is_fallible (VmWriter's version does), so Segment::reader cannot forward it; ensure it in from_kernel_space and Segment::reader.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/frame/untyped.rs, from line 103 @@
     #[verus_spec(r =>
         with
             -> owner: Tracked<VmIoOwner>,
         requires
             self.inv(),
         ensures
+            !owner@.is_fallible,
             r.inv(),
             owner@.inv(),
             r.wf(owner@),
             r.cursor.vaddr == paddr_to_vaddr(self.start_paddr()),
             r.remain_spec() == self.size(),
             owner@.is_kernel,
```

```diff
@@ ostd/src/mm/io.rs, from line 679 @@
         with
             Ghost(id): Ghost<nat>,
             -> owner: Tracked<VmIoOwner>,
         ensures
             r.inv_wf(),
             owner@.id == id,
+            !owner@.is_fallible,
             owner@.is_kernel,
             r.cursor == ptr,
             r.end == ptr.wrapping_add_spec(len),
             r.cursor.range@ == ptr.range@,
             r.end.range@ == ptr.range@,
             ptr.inv() && ptr.range@.start == ptr.vaddr
```

**A client that fails** (module `mm.frame.untyped`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__frame__untyped__impl__0__reader_2<'a, M: AnyUFrameMeta + OwnerOf>(
    self_: &'a Segment<M>,
)
    requires
        self_.inv(),
{
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with  => Tracked(gr))] self_.reader());
    assert(!gr.is_fallible); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(!gr.is_fallible); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r92"></a>

### R92. VmReader/VmWriter limit and skip return the reborrowed self but state their facts only on the returned reference r, not that *final(r) == *final(self), so after `v.limit(n)` / `v.skip(n)` the caller knows nothing about v itself (not even inv()) and cannot chain a second call on it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/io.rs, from line 1590 @@
         ensures
             r.inv(),
             r.remain_spec() <= max_remain,
             r.remain_spec() <= old(self).remain_spec(),
             r.cursor == old(self).cursor,
             r.ghost_id == old(self).ghost_id,
+            *final(r) == *final(self),
     )]
     pub fn limit(&mut self, max_remain: usize) -> &mut Self {
         if max_remain < self.remain() {
             self.end = self.cursor.wrapping_add(max_remain);
         }
         self
@@ ostd/src/mm/io.rs, from line 1615 @@
         ensures
             r.inv(),
             r.cursor.vaddr == old(self).cursor.vaddr + nbytes,
             r.remain_spec() == old(self).remain_spec() - nbytes,
             r.end == old(self).end,
             r.ghost_id == old(self).ghost_id,
+            *final(r) == *final(self),
     )]
     pub fn skip(&mut self, nbytes: usize) -> &mut Self {
         assert!(nbytes <= self.remain());
         self.cursor = self.cursor.wrapping_add(nbytes);
         self
     }
@@ ostd/src/mm/io.rs, from line 1724 @@
         ensures
             r.inv(),
             r.avail_spec() <= max_avail,
             r.avail_spec() <= old(self).avail_spec(),
             r.cursor == old(self).cursor,
             r.ghost_id == old(self).ghost_id,
+            *final(r) == *final(self),
     )]
     pub fn limit(&mut self, max_avail: usize) -> &mut Self {
         if max_avail < self.avail() {
             self.end = self.cursor.wrapping_add(max_avail);
         }
         self
@@ ostd/src/mm/io.rs, from line 1749 @@
         ensures
             r.inv(),
             r.cursor.vaddr == old(self).cursor.vaddr + nbytes,
             r.avail_spec() == old(self).avail_spec() - nbytes,
             r.end == old(self).end,
             r.ghost_id == old(self).ghost_id,
+            *final(r) == *final(self),
     )]
     pub fn skip(&mut self, nbytes: usize) -> &mut Self {
         assert!(nbytes <= self.avail());
         self.cursor = self.cursor.wrapping_add(nbytes);
         self
     }
```

**A client that fails** (module `mm.io`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__io__impl__4__limit_33<'a, Fallibility>(
    self_: &mut VmReader<'a, Fallibility>,
    mut max_remain: usize,
)
    requires
        old(self_).inv(),
{
    let ghost old_self_ = (*self_);
    let mut r = self_.limit(max_remain);
    assert((*self_).remain_spec() <= max_remain); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).remain_spec() <= max_remain); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 5 failing clients in 4 groups of failures pass.

## `mm/kspace/kvirt_area.rs`

<a id="r76"></a>

### R76. KVirtArea::map_untracked_frames (like map_frames, fixed by misc-4) gets range.end - range.start == area_size from kvirt_alloc_range_bounds before its loop and never changes range, but its ensures omit the area size.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/kspace/kvirt_area.rs, from line 734 @@
                     prop,
                 ),
         ensures
             final(regions).inv(),
             res.inv(),
             !Self::map_untracked_frames_panic_condition(area_size, map_offset, &pa_range),
+            res.range.end - res.range.start == area_size,
     )]
     #[verifier::spinoff_prover]
     #[allow(private_interfaces)]
     pub unsafe fn map_untracked_frames<A: InAtomicMode + 'a, 'a>(
         area_size: usize,
         map_offset: usize,
```

**A client that fails** (module `mm.kspace.kvirt_area`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__kspace__kvirt_area__impl__6__map_frames_0<'a, A: InAtomicMode>(
    mut area_size: usize,
    mut map_offset: usize,
    mut frames: Vec<Frame<MetaSlotStorage>>,
    mut prop: PageProperty,
    Tracked(owner): Tracked<KVirtAreaOwner>,
    Tracked(root_guard): Tracked<PageTableGuard<'a, KernelPtConfig>>,
    Tracked(entry_owners): Tracked<&mut Map<usize, EntryOwner<KernelPtConfig>>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        !(prop.flags.contains(PageFlags::AVAIL1())),
        (KVirtArea::map_frames_bounds_panic_condition(area_size, map_offset, frames.len()) ==> vstd_extra::panic::may_panic()),
        (crate::mm::kspace::kvirt_area::kvirt_alloc_oom_condition(area_size) ==> vstd_extra::panic::may_panic()),
        old(regions).inv(),
        owner.inv(),
        owner.pt_owner.metaregion_sound((*old(regions))),
        owner.pt_owner.0.value().node().relate_guard(root_guard),
        (forall|i: int| (((0 <= i) && (i < vstd::std_specs::vec::spec_vec_len::<Frame<MetaSlotStorage>, Global>((&frames)))) ==> (((*old(entry_owners)).contains_key((#[trigger] crate::mm::frame::meta::mapping::meta_to_frame_spec(vstd::std_specs::vec::VecAdditionalSpecFns::spec_index((&frames), i).slot_vaddr()))) && (*old(entry_owners)).spec_index((#[trigger] crate::mm::frame::meta::mapping::meta_to_frame_spec(vstd::std_specs::vec::VecAdditionalSpecFns::spec_index((&frames), i).slot_vaddr()))).inv()) && crate::mm::kspace::kvirt_area::frame_entry_wf::<MetaSlotStorage>(vstd::std_specs::vec::VecAdditionalSpecFns::spec_index((&frames), i), prop, (*old(entry_owners)).spec_index((#[trigger] crate::mm::frame::meta::mapping::meta_to_frame_spec(vstd::std_specs::vec::VecAdditionalSpecFns::spec_index((&frames), i).slot_vaddr()))))))),
        (forall|i: int| (((0 <= i) && (i < frames.len())) ==> CursorMut::<KernelPtConfig, A>::item_slot_in_regions(crate::mm::kspace::MappedItem::Tracked((#[trigger] frames[i]), prop), (*old(regions))))),
        !crate::mm::kspace::kvirt_area::kvirt_alloc_oom_condition(area_size),
{
    let tracked mut owner = owner;
    let tracked mut root_guard = root_guard;
    let ghost old_entry_owners = (*entry_owners);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!(KVirtArea::map_frames_bounds_panic_condition(area_size, map_offset, frames.len()))); } // no panic
    proof { assume(!(crate::mm::kspace::kvirt_area::kvirt_alloc_oom_condition(area_size))); } // no panic
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(root_guard), Tracked(entry_owners), Tracked(regions), Tracked(guards))] KVirtArea::map_frames::<A>(area_size, map_offset, frames, prop));
    assert(r.range.end - r.range.start == area_size); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.range.end - r.range.start == area_size); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 1 group of failures pass.

## `mm/page_prop.rs`

<a id="r62"></a>

### R62. PageProperty::new_user/new_absent return only their closed dual_spec spec fn, so callers learn neither the fields nor inv(); state the fields and inv() as ensures (the bit facts are proved in the body by compute_only).

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_prop.rs, from line 18 @@
 }
 
 #[verus_verify]
 impl PageProperty {
     /// Creates a new `PageProperty` with the given flags and cache policy for the user.
     #[verus_verify(dual_spec)]
-    #[verus_spec(returns Self::new_user(flags, cache))]
+    #[verus_spec(r =>
+        ensures
+            r.flags == flags,
+            r.cache == cache,
+            r.priv_flags == PrivilegedPageFlags::USER(),
+            (flags.bits() & PageFlags::all().bits()) == flags.bits() ==> r.inv(),
+        returns Self::new_user(flags, cache)
+    )]
     pub fn new_user(flags: PageFlags, cache: CachePolicy) -> Self {
+        proof! {
+            assert((PrivilegedPageFlags::USER().bits() & PrivilegedPageFlags::all().bits())
+                == PrivilegedPageFlags::USER().bits()) by (compute_only);
+        }
         Self {
             flags,
             cache,
             priv_flags: PrivilegedPageFlags::USER(),
         }
     }
 
     /// Creates a page property that implies an invalid page without mappings.
     #[verus_verify(dual_spec)]
-    #[verus_spec(returns Self::new_absent())]
+    #[verus_spec(r =>
+        ensures
+            r.flags.is_empty(),
+            r.cache == CachePolicy::Writeback,
+            r.priv_flags.is_empty(),
+            r.inv(),
+        returns Self::new_absent()
+    )]
     pub fn new_absent() -> Self {
+        proof! {
+            assert((0u8 & PageFlags::all().bits()) == 0u8) by (compute_only);
+            assert((0u8 & PrivilegedPageFlags::all().bits()) == 0u8) by (compute_only);
+        }
         Self {
             flags: PageFlags::empty(),
             cache: CachePolicy::Writeback,
             priv_flags: PrivilegedPageFlags::empty(),
         }
     }
```

**A client that fails** (module `mm.page_prop`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_prop__impl__7__new_absent_5(
)
{
    let mut r = PageProperty::new_absent();
    assert(r.flags.is_empty() && r.cache == crate::mm::page_prop::CachePolicy::Writeback && r.priv_flags.is_empty() && r.inv()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.flags.is_empty() && r.cache == crate::mm::page_prop::CachePolicy::Writeback && r.priv_flags.is_empty() && r.inv()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

## `mm/page_table/cursor/mod.rs`

<a id="r12"></a>

### R12. Cursor::find_next drops find_next_impl's frame facts (barrier_va, guard_level, monotone va, unchanged mappings, found va below old va + len), and page_table CursorMut::find_next and both VmSpace find_next wrappers drop these and the Some/None facts in turn; each layer now forwards them.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 561 @@
             final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
             res is Some ==> {
                 &&& res->0 == final(self).0.va
                 &&& final(owner).level <= final(owner).guard_level
                 &&& final(owner).in_barrier_va()
             },
+            final(self).0.barrier_va == old(self).0.barrier_va,
+            final(self).0.guard_level == old(self).0.guard_level,
+            final(self).0.va >= old(self).0.va,
+            final(owner)@.mappings == old(owner)@.mappings,
+            res is Some ==> final(self).0.va < old(self).0.va + len,
+            res is None ==> final(self).0.va >= old(self).0.va + len,
+            res is Some ==> final(owner)@.present(),
     )]
     pub fn find_next(&mut self, len: usize) -> Option<Vaddr> {
-        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
-        self.0.find_next(len)
+        let res = #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
+        self.0.find_next(len);
+        proof {
+            if res is Some {
+                owner.lemma_cur_entry_frame_present();
+            }
+        }
+        res
     }
 
     // [FIXED] BUG FOUND BY FV: missing panic documentation. https://github.com/asterinas/asterinas/pull/3007
     /// Jumps to the virtual address.
     ///
     /// If the target address is out of the range, this method will return `Err`.
@@ ostd/src/mm/vm_space.rs, from line 731 @@
             final(self).pt_cursor.0.invariants(*final(owner), *final(regions), *final(guards)),
             res is Some ==> {
                 &&& res->0 == final(self).pt_cursor.0.va
                 &&& final(owner).level <= final(owner).guard_level
                 &&& final(owner).in_barrier_va()
             },
+            final(self).pt_cursor.0.barrier_va == old(self).pt_cursor.0.barrier_va,
+            final(self).pt_cursor.0.guard_level == old(self).pt_cursor.0.guard_level,
+            final(self).pt_cursor.0.va >= old(self).pt_cursor.0.va,
+            final(owner)@.mappings == old(owner)@.mappings,
+            res is Some ==> final(self).pt_cursor.0.va < old(self).pt_cursor.0.va + len,
+            res is None ==> final(self).pt_cursor.0.va >= old(self).pt_cursor.0.va + len,
+            res is Some ==> final(owner)@.present(),
     )]
     pub fn find_next(&mut self, len: usize) -> Option<Vaddr> {
-        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
-        self.pt_cursor.find_next(len)
+        let res = #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
+        self.pt_cursor.find_next(len);
+        proof {
+            if res is Some {
+                owner.lemma_cur_entry_frame_present();
+            }
+        }
+        res
     }
 
     // [FIXED] BUG FOUND BY FV: missing panic documentation. https://github.com/asterinas/asterinas/pull/3007
     /// Jump to the virtual address.
     ///
     /// This is the same as [`Cursor::jump`].
```

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 697 @@
                 &&& final(owner).in_barrier_va()
             },
             res is Some ==> Self::find_not_unmap_subtree_ensures(*old(owner), *final(owner)),
             res is None ==> {
                 &&& final(self).va >= old(self).va + len
             },
+            final(self).barrier_va == old(self).barrier_va,
+            final(self).guard_level == old(self).guard_level,
+            final(self).va >= old(self).va,
+            final(owner)@.mappings == old(owner)@.mappings,
+            res is Some ==> final(self).va < old(self).va + len,
     )]
     pub fn find_next(&mut self, len: usize) -> Option<Vaddr> {
         #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
         self.find_next_impl(len, false, false)
     }
 
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2089 @@
             final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
             res is Some ==> {
                 &&& res->0 == final(self).0.va
                 &&& final(owner).level <= final(owner).guard_level
                 &&& final(owner).in_barrier_va()
             },
+            final(self).0.barrier_va == old(self).0.barrier_va,
+            final(self).0.guard_level == old(self).0.guard_level,
+            final(self).0.va >= old(self).0.va,
+            final(owner)@.mappings == old(owner)@.mappings,
+            res is Some ==> final(self).0.va < old(self).0.va + len,
+            res is Some ==> crate::mm::page_table::Cursor::<C, A>::find_not_unmap_subtree_ensures(*old(owner), *final(owner)),
+            res is None ==> final(self).0.va >= old(self).0.va + len,
     )]
     pub fn find_next(&mut self, len: usize) -> Option<Vaddr> {
         #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
         self.0.find_next(len)
     }
 
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__3__find_next_8<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut Cursor<'a, C, A>,
    mut len: usize,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(self_).invariants((*old(owner)), (*old(regions)), (*old(guards))),
        (old(self_).find_next_panic_condition(len) ==> vstd_extra::panic::may_panic()),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!(self_.find_next_panic_condition(len))); } // no panic
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))] self_.find_next(len));
    assert((*self_).va >= old_self_.va); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).va >= old_self_.va); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 12 failing clients in 12 groups of failures pass.

<a id="r13"></a>

### R13. Cursor::jump keeps barrier_va and guard_level (loop invariants) and returns Err before touching the cursor or owner, but ensures none of it; CursorMut::jump and VmSpace CursorMut::jump forward the same frame facts.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 783 @@
             final(self).pt_cursor.0.invariants(*final(owner), *final(regions), *final(guards)),
             final(self).pt_cursor.0.barrier_va.start <= va < final(self).pt_cursor.0.barrier_va.end ==> {
                 &&& res is Ok
                 &&& final(self).pt_cursor.0.va == va
             },
             !(final(self).pt_cursor.0.barrier_va.start <= va < final(self).pt_cursor.0.barrier_va.end) ==> res is Err,
+            final(self).pt_cursor.0.barrier_va == old(self).pt_cursor.0.barrier_va,
+            final(self).pt_cursor.0.guard_level == old(self).pt_cursor.0.guard_level,
+            res is Err ==> final(self).pt_cursor.0.va == old(self).pt_cursor.0.va,
     )]
     pub fn jump(&mut self, va: Vaddr) -> Result<()> {
         (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
         self.pt_cursor.jump(va))?;
         Ok(())
     }
```

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 1297 @@
             final(self).invariants(*final(owner), *final(regions), *final(guards)),
             final(self).barrier_va.start <= va < final(self).barrier_va.end ==> {
                 &&& res is Ok
                 &&& final(self).va == va
             },
             !(final(self).barrier_va.start <= va < final(self).barrier_va.end) ==> res is Err,
+            final(self).barrier_va == old(self).barrier_va,
+            final(self).guard_level == old(self).guard_level,
+            res is Err ==> final(self).va == old(self).va,
+            res is Err ==> *final(owner) == *old(owner),
     )]
     #[verifier::spinoff_prover]
     pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError> {
         assert_eq!(va % PAGE_SIZE, 0);
 
         if !self.barrier_va.contains(&va) {
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2129 @@
             final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
             final(self).0.barrier_va.start <= va < final(self).0.barrier_va.end ==> {
                 &&& res is Ok
                 &&& final(self).0.va == va
             },
             !(final(self).0.barrier_va.start <= va < final(self).0.barrier_va.end) ==> res is Err,
+            final(self).0.barrier_va == old(self).0.barrier_va,
+            final(self).0.guard_level == old(self).0.guard_level,
+            res is Err ==> final(self).0.va == old(self).0.va,
+            res is Err ==> *final(owner) == *old(owner),
     )]
     #[verifier::spinoff_prover]
     pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError> {
         #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
         self.0.jump(va)
     }
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__3__jump_12<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut Cursor<'a, C, A>,
    mut va: usize,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(self_).invariants((*old(owner)), (*old(regions)), (*old(guards))),
        (old(self_).jump_panic_condition(va) ==> vstd_extra::panic::may_panic()),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!(self_.jump_panic_condition(va))); } // no panic
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))] self_.jump(va));
    assert(r is Err ==> (*self_).va == old_self_.va); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r is Err ==> (*self_).va == old_self_.va); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 4 failing clients in 3 groups of failures pass.

<a id="r14"></a>

### R14. Cursor::query keeps va, barrier_va and guard_level and returns Err outside the barrier, but states only va and only 'in barrier implies Ok'; page_table CursorMut::query and the VmSpace query wrappers drop even va, so each layer now states these facts (and VmSpace CursorMut::query that flusher is untouched).

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 512 @@
                 final(self).0.query_some_condition(*final(owner)) ==>
                 final(self).0.query_some_ensures(*final(owner), state),
             r matches Ok(state) ==>
                 !final(self).0.query_some_condition(*final(owner)) ==>
                 final(self).0.query_none_ensures(*final(owner), state),
             old(owner)@.mappings == final(owner)@.mappings,
+            final(self).0.va == old(self).0.va,
+            final(self).0.barrier_va == old(self).0.barrier_va,
+            final(self).0.guard_level == old(self).0.guard_level,
     )]
     pub fn query(&mut self) -> Result<(Range<Vaddr>, Option<MappedItem>)> {
         Ok(
             #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
             self.0.query()?,
         )
@@ ostd/src/mm/vm_space.rs, from line 687 @@
                 final(self).pt_cursor.0.query_some_condition(*final(owner)) ==>
                 final(self).pt_cursor.0.query_some_ensures(*final(owner), state),
             res matches Ok(state) ==>
                 !final(self).pt_cursor.0.query_some_condition(*final(owner)) ==>
                 final(self).pt_cursor.0.query_none_ensures(*final(owner), state),
             old(owner)@.mappings == final(owner)@.mappings,
+            final(self).pt_cursor.0.va == old(self).pt_cursor.0.va,
+            final(self).pt_cursor.0.barrier_va == old(self).pt_cursor.0.barrier_va,
+            final(self).pt_cursor.0.guard_level == old(self).pt_cursor.0.guard_level,
+            final(self).flusher == old(self).flusher,
     )]
     pub fn query(&mut self) -> Result<(Range<Vaddr>, Option<MappedItem>)> {
         Ok(
             #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
             self.pt_cursor.query()?,
         )
```

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 360 @@
                 final(self).query_some_ensures(*final(owner), state),
             res matches Ok(state) ==>
                 !final(self).query_some_condition(*final(owner)) ==>
                 final(self).query_none_ensures(*final(owner), state),
             old(owner)@.mappings == final(owner)@.mappings,
             final(self).va == old(self).va,
+            final(self).barrier_va == old(self).barrier_va,
+            final(self).guard_level == old(self).guard_level,
+            !(old(self).barrier_va.start <= old(self).va && old(self).va < old(self).barrier_va.end) ==> res is Err,
     )]
     #[verifier::spinoff_prover]
     #[verifier::rlimit(200)]
     pub fn query(&mut self) -> Result<PagesState<C>, PageTableError> {
         hide(MetaSlotOwner::storage_perm);
         hide(MetaSlotOwner::vtable_ptr_perm);
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 390 @@
                 // Past the early out-of-range `Err`: the cursor stays in
                 // range for the whole descent (it never moves its VA).
                 self.va < self.barrier_va.end,
                 self.barrier_va == old(self).barrier_va,
                 old(owner)@.mappings == owner@.mappings,
                 old(owner)@.cur_va == owner@.cur_va,
+                self.guard_level == old(self).guard_level,
                 PageTableOwner(owner.cur_subtree()).query_leaf(self.va)
                     == PageTableOwner(old(owner).cur_subtree()).query_leaf(old(self).va),
                 forall|i: int|
                     #![trigger regions.slot_owners[i]]
                     old(regions).contains(i)
                         ==> regions.ref_count(i) == old(
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2186 @@
                 final(self).0.query_some_condition(*final(owner)) ==>
                 final(self).0.query_some_ensures(*final(owner), state),
             res matches Ok(state) ==>
                 !final(self).0.query_some_condition(*final(owner)) ==>
                 final(self).0.query_none_ensures(*final(owner), state),
             old(owner)@.mappings == final(owner)@.mappings,
+            final(self).0.va == old(self).0.va,
+            final(self).0.barrier_va == old(self).0.barrier_va,
+            final(self).0.guard_level == old(self).0.guard_level,
+            !(old(self).0.barrier_va.start <= old(self).0.va && old(self).0.va < old(self).0.barrier_va.end) ==> res is Err,
+            old(self).0.va >= old(self).0.barrier_va.end ==> res is Err,
     )]
     pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>) {
         #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
         self.0.query()
     }
 
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__4__query_2<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut CursorMut<'a, C, A>,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(self_).0.invariants((*old(owner)), (*old(regions)), (*old(guards))),
        (old(self_).0.query_panic_condition((*old(owner)), (*old(regions))) ==> vstd_extra::panic::may_panic()),
        !old(self_).0.query_panic_condition((*old(owner)), (*old(regions))),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!(self_.0.query_panic_condition((*owner), (*regions)))); } // no panic
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))] self_.query());
    assert((*self_).0.va == old_self_.0.va); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).0.va == old_self_.0.va); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 9 failing clients in 8 groups of failures pass.

<a id="r15"></a>

### R15. Cursor::query returns cur_va_range(), which contains the cursor va, but cur_va_range does not ensure va < end and query states the range only when a mapping is present; cur_va_range now ensures it (from align_down) and query forwards 'range contains old va' for every Ok.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 358 @@
             res matches Ok(state) ==>
                 final(self).query_some_condition(*final(owner)) ==>
                 final(self).query_some_ensures(*final(owner), state),
             res matches Ok(state) ==>
                 !final(self).query_some_condition(*final(owner)) ==>
                 final(self).query_none_ensures(*final(owner), state),
+            res matches Ok(state) ==> state.0.start <= old(self).va && old(self).va < state.0.end,
             old(owner)@.mappings == final(owner)@.mappings,
             final(self).va == old(self).va,
     )]
     #[verifier::spinoff_prover]
     #[verifier::rlimit(200)]
     pub fn query(&mut self) -> Result<PagesState<C>, PageTableError> {
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 1858 @@
             owner.in_barrier_va(),
             1 <= self.level <= owner.guard_level,
         ensures
             res.start <= self.va,
             res.end <= self.va + page_size::<PagingConsts>(self.level),
             res.start == self.va ==> res.end == self.va + page_size::<PagingConsts>(self.level),
+            self.va < res.end,
         returns
             owner.cur_va_range(),
     )]
     fn cur_va_range(&self) -> Range<Vaddr> {
         proof {
             C::lemma_paging_consts_properties();
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 1872 @@
         let page_size = page_size::<C>(self.level);
         let start = self.va.align_down(page_size);
 
         proof {
             // Bound the returned range end.
             owner.lemma_va_plus_page_size_no_overflow(self.level);
+            lemma_nat_align_down_sound(self.va as nat, page_size as nat);
         }
 
         start..start + page_size
     }
 }
 
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__3__query_4<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut Cursor<'a, C, A>,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(self_).invariants((*old(owner)), (*old(regions)), (*old(guards))),
        (old(self_).query_panic_condition((*old(owner)), (*old(regions))) ==> vstd_extra::panic::may_panic()),
        !old(self_).query_panic_condition((*old(owner)), (*old(regions))),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!(self_.query_panic_condition((*owner), (*regions)))); } // no panic
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))] self_.query());
    assert(r matches Ok(st) ==> (st.0.start <= old_self_.va && old_self_.va < st.0.end)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Ok(st) ==> (st.0.start <= old_self_.va && old_self_.va < st.0.end)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r16"></a>

### R16. Cursor::new returns Err before touching regions and ensures the owner relation, item_not_mapped and non-saturation preservation, but CursorMut::new, PageTable::cursor_mut and PageTable::cursor drop some of these and none states 'Err implies regions unchanged'; Cursor::new now states it and each wrapper forwards all of them.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/mod.rs, from line 1235 @@
                 &&& r.unwrap().0.0.invariants(*r.unwrap().1, *final(regions), *final(guards))
                 &&& r.unwrap().1.in_barrier_va()
                 &&& r.unwrap().0.0.level == r.unwrap().0.0.guard_level
                 &&& r.unwrap().0.0.va < r.unwrap().0.0.barrier_va.end
                 &&& r.unwrap().0.0.va == va.start
                 &&& r.unwrap().0.0.barrier_va == *va
+                &&& r.unwrap().1@.as_page_table_owner() == owner
+                &&& r.unwrap().1@.continuations[3].path() == owner.0.value().path
             },
             !Cursor::<C, G>::cursor_new_success_conditions(*va) ==> r is Err,
+            r is Err ==> *final(regions) == *old(regions),
+            (forall |i: int| #![trigger old(regions).slot_owners[i]]
+                old(regions).contains(i)
+                && old(regions).ref_count(i)
+                    != REF_COUNT_UNUSED
+                ==> old(regions).ref_count(i) + 1
+                    < REF_COUNT_MAX)
+            ==>
+            (forall |i: int| #![trigger final(regions).slot_owners[i]]
+                final(regions).contains(i)
+                && final(regions).ref_count(i)
+                    != REF_COUNT_UNUSED
+                ==> final(regions).ref_count(i) + 1 < REF_COUNT_MAX),
             forall |item: C::Item| #![trigger CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions))]
                 CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions)) ==>
                 CursorMut::<'rcu, C, G>::item_not_mapped(item, *final(regions)),
             // CursorMut::new inherits Cursor::new's weakened preservation:
             // PT-node allocations come from UNUSED slots, so any slot that
             // was already in use keeps its paths_in_pt.
@@ ostd/src/mm/page_table/mod.rs, from line 1299 @@
                 &&& r.unwrap().0.va == va.start
                 &&& r.unwrap().0.barrier_va == *va
                 &&& r.unwrap().1@.as_page_table_owner() == owner
                 &&& r.unwrap().1@.continuations[3].path() == owner.0.value().path
             },
             !Cursor::<C, G>::cursor_new_success_conditions(*va) ==> r is Err,
+            r is Err ==> *final(regions) == *old(regions),
+            forall |item: C::Item| #![trigger CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions))]
+                CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions)) ==>
+                CursorMut::<'rcu, C, G>::item_not_mapped(item, *final(regions)),
             forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                 old(regions).contains(idx) && old(regions).ref_count(idx)
                     != REF_COUNT_UNUSED
                 ==> final(regions).slot_owners[idx].paths_in_pt
                         == old(regions).slot_owners[idx].paths_in_pt,
             // Non-saturation preservation.
```

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 244 @@
                 &&& r.unwrap().0.va == va.start
                 &&& r.unwrap().0.barrier_va == *va
                 &&& r.unwrap().1@.as_page_table_owner() == pt_own
                 &&& r.unwrap().1@.continuations[3].path() == pt_own.0.value().path
             },
             !Self::cursor_new_success_conditions(*va) ==> r is Err,
+            r is Err ==> *final(regions) == *old(regions),
             forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                 old(regions).contains(idx) && old(regions).ref_count(idx) != REF_COUNT_UNUSED
                 ==> final(regions).slot_owners[idx].paths_in_pt
                         == old(regions).slot_owners[idx].paths_in_pt,
             forall|idx: int| #![trigger final(regions).slot_owners[idx]]
                 old(regions).contains(idx)
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2011 @@
                 &&& r.unwrap().0.0.invariants(*r.unwrap().1, *final(regions), *final(guards))
                 &&& r.unwrap().1.in_barrier_va()
                 &&& r.unwrap().0.0.level == r.unwrap().0.0.guard_level
                 &&& r.unwrap().0.0.va < r.unwrap().0.0.barrier_va.end
                 &&& r.unwrap().0.0.va == va.start
                 &&& r.unwrap().0.0.barrier_va == *va
+                &&& r.unwrap().1@.as_page_table_owner() == pt_own
+                &&& r.unwrap().1@.continuations[3].path() == pt_own.0.value().path
             },
             !Cursor::<C, A>::cursor_new_success_conditions(*va) ==> r is Err,
+            r is Err ==> *final(regions) == *old(regions),
+            (forall |i: int| #![trigger old(regions).slot_owners[i]]
+                old(regions).contains(i)
+                && old(regions).ref_count(i)
+                    != REF_COUNT_UNUSED
+                ==> old(regions).ref_count(i) + 1
+                    < REF_COUNT_MAX)
+            ==>
+            (forall |i: int| #![trigger final(regions).slot_owners[i]]
+                final(regions).contains(i)
+                && final(regions).ref_count(i)
+                    != REF_COUNT_UNUSED
+                ==> final(regions).ref_count(i) + 1 < REF_COUNT_MAX),
             forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                 Self::item_not_mapped(item, *old(regions)) ==>
                 Self::item_not_mapped(item, *final(regions)),
             forall |idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                 old(regions).contains(idx) && old(regions).ref_count(idx)
                     != REF_COUNT_UNUSED
```

**A client that fails** (module `mm.page_table`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__impl__10__cursor_mut_0<'a, C: PageTableConfig, G: InAtomicMode>(
    self_: &'a PageTable<C>,
    guard: &'a G,
    va: &'a Range<usize>,
    Tracked(owner): Tracked<PageTableOwner<C>>,
    Ghost(root_guard): Ghost<PageTableGuard<'a, C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        self_.relates_owner(owner, (*old(regions))),
        (Cursor::<C, G>::cursor_new_input_valid((*va)) ==> Cursor::<C, G>::cursor_new_success_conditions((*va))),
        owner.0.value().node().relate_guard(root_guard),
        (va.end > 0),
{
    let tracked mut owner = owner;
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    let mut r = (#[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards))] self_.cursor_mut(guard, va));
    assert(r matches Ok(r_b) ==> r_b.1@.as_page_table_owner() == owner); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Ok(r_b) ==> r_b.1@.as_page_table_owner() == owner); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 11 failing clients in 10 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r24"></a>

### R24. page_table CursorMut::map moves the cursor past the mapped slot and returns the replaced fragment at the old va (replace_cur_entry ensures it) but states neither.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2800 @@
                     frame_to_index(C::item_into_raw(item).0))
                     <= REF_COUNT_MAX,
             forall|idx: int| #![trigger final(regions).contains(idx)]
                 old(regions).contains(idx) ==> final(regions).contains(idx),
             final(self).0.guard_level == old(self).0.guard_level,
             final(self).0.barrier_va == old(self).0.barrier_va,
+            final(self).0.va > old(self).0.va,
+            res matches Err(PageTableFrag::Mapped { va, .. }) ==> va == old(self).0.va,
     )]
     #[verifier::spinoff_prover]
     #[verifier::rlimit(300)]
     pub unsafe fn map(&mut self, item: C::Item) -> (res: Result<(), PageTableFrag<C>>) {
         hide(CursorContinuation::view_mappings);
         hide(CursorOwner::view_mappings);
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__4__map_15<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut CursorMut<'a, C, A>,
    mut item: C::Item,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(entry_owner): Tracked<EntryOwner<C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        ((<C as crate::mm::page_table::PageTableConfig>::item_into_raw(item).1 > 1) ==> vstd_extra::panic::may_panic()),
        old(self_).0.invariants((*old(owner)), (*old(regions)), (*old(guards))),
        old(self_).item_wf(item, entry_owner),
        CursorMut::<C, A>::item_slot_in_regions(item, (*old(regions))),
        (old(self_).map_panic_conditions(item) ==> vstd_extra::panic::may_panic()),
{
    let tracked mut entry_owner = entry_owner;
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!((<C as crate::mm::page_table::PageTableConfig>::item_into_raw(item).1 > 1))); } // no panic
    proof { assume(!(self_.map_panic_conditions(item))); } // no panic
    let mut r = unsafe { (#[verus_spec(with Tracked(owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))] self_.map(item)) };
    assert((*self_).0.va > old_self_.0.va); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).0.va > old_self_.0.va); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

<a id="r25"></a>

### R25. page_table CursorMut::map advances the cursor to align_up(va, page_size(level)) = va + page_size(level) (va is asserted aligned) but does not state it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2762 @@
                 old(owner)@,
                 final(owner)@,
             ),
             (C::item_into_raw(item).1 <= old(self).0.level
                 && old(owner).cur_entry_owner().is_absent()) ==> res.is_ok(),
             res is Err && res.unwrap_err() is StrayPageTable ==> C::item_into_raw(item).1 > 1,
+            final(self).0.va == (old(self).0.va + page_size::<PagingConsts>(C::item_into_raw(item).1)) as usize,
             forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                 old(regions).contains(idx) &&
                 idx != frame_to_index(C::item_into_raw(item).0) &&
                 old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                 {
                     &&& old(regions).slot_owners[idx].paths_in_pt.subset_of(final(regions).slot_owners[idx].paths_in_pt)
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__4__map_30<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut CursorMut<'a, C, A>,
    mut item: C::Item,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(entry_owner): Tracked<EntryOwner<C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        ((<C as crate::mm::page_table::PageTableConfig>::item_into_raw(item).1 > 1) ==> vstd_extra::panic::may_panic()),
        old(self_).0.invariants((*old(owner)), (*old(regions)), (*old(guards))),
        old(self_).item_wf(item, entry_owner),
        CursorMut::<C, A>::item_slot_in_regions(item, (*old(regions))),
        (old(self_).map_panic_conditions(item) ==> vstd_extra::panic::may_panic()),
{
    let tracked mut entry_owner = entry_owner;
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!((<C as crate::mm::page_table::PageTableConfig>::item_into_raw(item).1 > 1))); } // no panic
    proof { assume(!(self_.map_panic_conditions(item))); } // no panic
    let mut r = unsafe { (#[verus_spec(with Tracked(owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))] self_.map(item)) };
    assert((*self_).0.va == (old_self_.0.va + crate::mm::page_size::<crate::arch::mm::PagingConsts>(C::item_into_raw(item).1)) as usize); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).0.va == (old_self_.0.va + crate::mm::page_size::<crate::arch::mm::PagingConsts>(C::item_into_raw(item).1)) as usize); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r26"></a>

### R26. CursorMut::take_next ensures barrier_va preservation but not guard_level preservation, which map's item_wf needs on the same cursor.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 3013 @@
             !old(self).0.find_next_panic_condition(len),
             final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
             final(self).0.va >= old(self).0.va,
             final(self).0.va % PAGE_SIZE == 0,
             final(self).0.barrier_va == old(self).0.barrier_va,
             res is Some ==> final(self).0.va <= old(self).0.va + len,
+            final(self).0.guard_level == old(self).0.guard_level,
             res is Some ==> final(self).0.va > old(self).0.va,
             res is Some ==> final(owner).in_barrier_va() || final(owner).at_or_past_barrier_end(),
             res is None ==> {
                 &&& final(owner)@.cur_va >= (old(owner)@.cur_va + len) as Vaddr
                 &&& final(owner)@.mappings == old(owner)@.mappings
                 &&& old(owner)@.mappings.filter(|m: Mapping|
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__4__take_next_17<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut CursorMut<'a, C, A>,
    mut len: usize,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        ((len >= crate::mm::page_size::<PagingConsts>(2)) ==> vstd_extra::panic::may_panic()),
        old(self_).0.invariants((*old(owner)), (*old(regions)), (*old(guards))),
        (old(self_).0.find_next_panic_condition(len) ==> vstd_extra::panic::may_panic()),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!((len >= crate::mm::page_size::<PagingConsts>(2)))); } // no panic
    proof { assume(!(self_.0.find_next_panic_condition(len))); } // no panic
    let mut r = unsafe { (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))] self_.take_next(len)) };
    assert((*self_).0.guard_level == old_self_.0.guard_level); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).0.guard_level == old_self_.0.guard_level); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r78"></a>

### R78. page_table CursorMut::query wraps Cursor::query, which now ensures slots and the slot_owners domain unchanged (cursor-4), but does not forward either fact.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2179 @@
             old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
             old(self).0.query_panic_condition(*old(owner), *old(regions)) ==> may_panic(),
         ensures
             final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
             !old(self).0.query_panic_condition(*old(owner), *old(regions)),
             old(owner).in_barrier_va() ==> res is Ok,
+            final(regions).slots == old(regions).slots,
+            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
             res matches Ok(state) ==>
                 final(self).0.query_some_condition(*final(owner)) ==>
                 final(self).0.query_some_ensures(*final(owner), state),
             res matches Ok(state) ==>
                 !final(self).0.query_some_condition(*final(owner)) ==>
                 final(self).0.query_none_ensures(*final(owner), state),
```

**A client that fails** (module `mm.page_table.cursor`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__cursor__impl__3__query_21<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut Cursor<'a, C, A>,
    Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(self_).invariants((*old(owner)), (*old(regions)), (*old(guards))),
        (old(self_).query_panic_condition((*old(owner)), (*old(regions))) ==> vstd_extra::panic::may_panic()),
        !old(self_).query_panic_condition((*old(owner)), (*old(regions))),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!(self_.query_panic_condition((*owner), (*regions)))); } // no panic
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))] self_.query());
    assert((*regions).slots == old_regions.slots && (*regions).slot_owners.dom() == old_regions.slot_owners.dom()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*regions).slots == old_regions.slots && (*regions).slot_owners.dom() == old_regions.slot_owners.dom()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies together with [R14](#r14), [cursor-4](#fix-cursor-4), [R15](#r15), [R61](#r61), which it builds on (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 1 group of failures pass.

<a id="r90"></a>

### R90. page_table Cursor::query ensures the returned range contains the old cursor va (kept fix cursor-5), but page_table CursorMut::query and VmSpace CursorMut::query, which return that same range, drop it; both now forward it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 677 @@
             // Out-of-range → graceful `Err`; the sole panic is cloning the
             // resolved leaf frame when *that specific slot* is saturated —
             // precisely propagated from `Cursor::query_panic_condition`.
             old(self).pt_cursor.0.query_panic_condition(*old(owner), *old(regions))
                 ==> may_panic(),
         ensures
+            res matches Ok(state) ==> state.0.start <= old(self).pt_cursor.0.va && old(self).pt_cursor.0.va < state.0.end,
             final(self).pt_cursor.0.invariants(*final(owner), *final(regions), *final(guards)),
             !old(self).pt_cursor.0.query_panic_condition(*old(owner), *old(regions)),
             old(owner).in_barrier_va() ==> res is Ok,
             res matches Ok(state) ==>
                 final(self).pt_cursor.0.query_some_condition(*final(owner)) ==>
                 final(self).pt_cursor.0.query_some_ensures(*final(owner), state),
```

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 2176 @@
              Tracked(regions): Tracked<&mut MetaRegionOwners>,
              Tracked(guards): Tracked<&mut Guards>,
         requires
             old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
             old(self).0.query_panic_condition(*old(owner), *old(regions)) ==> may_panic(),
         ensures
+            res matches Ok(state) ==> state.0.start <= old(self).0.va && old(self).0.va < state.0.end,
             final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
             !old(self).0.query_panic_condition(*old(owner), *old(regions)),
             old(owner).in_barrier_va() ==> res is Ok,
             res matches Ok(state) ==>
                 final(self).0.query_some_condition(*final(owner)) ==>
                 final(self).0.query_some_ensures(*final(owner), state),
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__2__query_8<'a, A: InAtomicMode>(
    self_: &mut CursorMut<'a, A>,
    Tracked(owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(self_).pt_cursor.0.invariants((*old(owner)), (*old(regions)), (*old(guards))),
        (old(self_).pt_cursor.0.query_panic_condition((*old(owner)), (*old(regions))) ==> vstd_extra::panic::may_panic()),
        !old(self_).pt_cursor.0.query_panic_condition((*old(owner)), (*old(regions))),
        !old(self_).pt_cursor.0.query_panic_condition(*old(owner), *old(regions)),
{
    let ghost old_self_ = (*self_);
    let ghost old_owner = (*owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof { assume(!(self_.pt_cursor.0.query_panic_condition((*owner), (*regions)))); } // no panic
    let mut r = (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))] self_.query());
    assert(r matches Ok(st) ==> (st.0.start <= old_self_.pt_cursor.0.va && old_self_.pt_cursor.0.va < st.0.end)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Ok(st) ==> (st.0.start <= old_self_.pt_cursor.0.va && old_self_.pt_cursor.0.va < st.0.end)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies together with [R14](#r14), [cursor-4](#fix-cursor-4), [R15](#r15), [R61](#r61), which it builds on (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

## `mm/page_table/mod.rs`

<a id="r27"></a>

### R27. create_user_page_table keeps the kernel page table related to kernel_owner in the new regions but does not ensure it, so VmSpace::new cannot create a second user page table.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/mod.rs, from line 902 @@
             kernel_owner.0.value().metaregion_sound(*old(regions)),
             kernel_owner.metaregion_sound(*old(regions)),
             // The kernel root is not currently locked.
             old(guards).unlocked(kernel_owner.0.value().node().slot_vaddr()),
         ensures
             final(regions).inv(),
+            self.relates_owner(*kernel_owner, *final(regions)),
+            *final(guards) == *old(guards),
+            final(regions).slots == old(regions).slots,
+            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
+            forall|i: int|
+                #![trigger final(regions).slot_owners[i]]
+                final(regions).slot_owners[i] != old(regions).slot_owners[i]
+                    ==> old(regions).ref_count(i) == REF_COUNT_UNUSED,
     )]
     pub(in crate::mm) fn create_user_page_table<'rcu, G: InAtomicMode + 'static>(
         &'static self,
     ) -> PageTable<UserPtConfig> {
         let preempt_guard: &'rcu G = disable_preempt::<G>();
 
@@ ostd/src/mm/page_table/mod.rs, from line 948 @@
         // Discharge borrow/lock preconditions for the kernel root from
         // kernel_owner.inv() + metaregion_sound + guards unlocked.
         proof {
             assert(kernel_owner.0.value().is_node());
             assert(kernel_owner.0.value().metaregion_sound(*regions));
         }
+        let ghost guards_pre_lock = *guards;
         let mut root_node = {
             let root_ref = self.root.borrow();
             #[verus_spec(with Tracked(guards), Tracked(regions.tracked_borrow_slot_owner(root_ref.start_paddr_spec()).metadata_perm.tracked_borrow()))]
             root_ref.lock(preempt_guard)
         };
+        let ghost guards_mid = *guards;
         let mut new_node: PageTableGuard<'_, UserPtConfig> = {
             let new_ref = new_root.borrow();
             #[verus_spec(with Tracked(guards), Tracked(regions.tracked_borrow_slot_owner(new_ref.start_paddr_spec()).metadata_perm.tracked_borrow()))]
             new_ref.lock(preempt_guard)
         };
+        let ghost root_inner = root_node.inner;
+        let ghost new_inner = new_node.inner;
+        proof {
+            // Both roots are now locked; nothing else in `guards` changed.
+            let a = root_inner.slot_vaddr();
+            let b = new_inner.slot_vaddr();
+            assert(guards_pre_lock.unlocked(a));
+            assert(guards_mid.lock_held(a));
+            assert(guards_mid.unlocked(b));
+            assert(guards.lock_held(a));
+            assert(guards.lock_held(b));
+            assert(guards_pre_lock.guards == old(guards).guards);
+            assert forall|x: usize|
+                #[trigger] guards.guards.remove(a).remove(b).contains(x)
+                    == old(guards).guards.contains(x) by {
+                if guards_pre_lock.lock_held(x) {
+                    assert(guards_mid.lock_held(x));
+                    assert(guards.lock_held(x));
+                } else {
+                    assert(guards_pre_lock.unlocked(x));
+                    if x != a {
+                        assert(guards_mid.unlocked(x));
+                        if x != b {
+                            assert(guards.unlocked(x));
+                        }
+                    }
+                }
+            };
+            assert(guards.guards.remove(a).remove(b) =~= old(guards).guards);
+            // Only the new root's slot, previously unused, changed in `regions`.
+            assert(regions.slot_owners.dom() =~= old(regions).slot_owners.dom());
+            assert forall|j: int|
+                #![trigger regions.slot_owners[j]]
+                regions.slot_owners[j] != old(regions).slot_owners[j] implies old(
+                    regions,
+                ).ref_count(j) == REF_COUNT_UNUSED by {
+                assert(j == new_idx_g);
+            };
+        }
         for i in KernelPtConfig::TOP_LEVEL_INDEX_RANGE()
             invariant
+                root_node.inner == root_inner,
+                new_node.inner == new_inner,
                 kernel_owner.inv(),
                 kernel_owner.0.value().is_node(),
                 regions.inv(),
                 !Self::create_user_pt_panic_condition(kernel_owner.0.value().node()),
                 // Lock postcondition for the kernel root.
                 *root_owner == kernel_owner.0.value().node(),
@@ ostd/src/mm/page_table/mod.rs, from line 1061 @@
             unsafe {
                 #[verus_spec(with Tracked(&mut new_node_owner), Tracked(&*regions))]
                 new_node.write_pte(i, pte)
             };
         }
 
+        // Release both locks in the model (same idiom as `find_next_impl`).
+        proof_decl! {
+            let tracked root_obl = vstd_extra::drop_tracking::TrackDrop::tracked_redeem(root_node, guards);
+            let tracked new_obl = vstd_extra::drop_tracking::TrackDrop::tracked_redeem(new_node, guards);
+        }
+        proof_with!(Tracked(root_obl));
+        let _ = vstd_extra::drop_tracking::ManuallyDrop::new(root_node);
+        proof_with!(Tracked(new_obl));
+        let _ = vstd_extra::drop_tracking::ManuallyDrop::new(new_node);
+        proof {
+            assert(guards.guards == old(guards).guards);
+        }
+
         PageTable::<UserPtConfig> { root: new_root }
     }/*
     /// Protect the given virtual address range in the kernel page table.
     ///
     /// This method flushes the TLB entries when doing protection.
     ///
```

**A client that fails** (module `mm.page_table`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn goal_mm__page_table__impl__9__create_user_page_table_mm__page_table__impl__9__create_user_page_table_61a1afff<G: InAtomicMode + 'static>(
    self_: &'static PageTable<KernelPtConfig>,
    Tracked(kernel_owner): Tracked<&PageTableOwner<KernelPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        kernel_owner.inv(),
        old(regions).inv(),
        kernel_owner.0.value().is_node(),
        !(PageTable::<KernelPtConfig>::create_user_pt_panic_condition(kernel_owner.0.value().node())),
        (self_.root.slot_vaddr() == kernel_owner.0.value().node().slot_vaddr()),
        self_.relates_owner((*kernel_owner), (*old(regions))),
        kernel_owner.0.value().metaregion_sound((*old(regions))),
        kernel_owner.metaregion_sound((*old(regions))),
        old(guards).unlocked(kernel_owner.0.value().node().slot_vaddr()),
{
    let mut v0 = (#[verus_spec(with Tracked(kernel_owner), Tracked(regions), Tracked(guards))] self_.create_user_page_table::<G>());
    assert(kernel_owner.inv()); // requires of mm::page_table::impl&%9::create_user_page_table
    assert(regions.inv()); // requires of mm::page_table::impl&%9::create_user_page_table
    assert(kernel_owner.0.value().is_node()); // requires of mm::page_table::impl&%9::create_user_page_table
    assert(!(PageTable::<KernelPtConfig>::create_user_pt_panic_condition(kernel_owner.0.value().node()))); // requires of mm::page_table::impl&%9::create_user_page_table
    assert((self_.root.slot_vaddr() == kernel_owner.0.value().node().slot_vaddr())); // requires of mm::page_table::impl&%9::create_user_page_table
    assert(self_.relates_owner((*kernel_owner), (*regions))); // requires of mm::page_table::impl&%9::create_user_page_table
    assert(kernel_owner.0.value().metaregion_sound((*regions))); // requires of mm::page_table::impl&%9::create_user_page_table
    assert(kernel_owner.metaregion_sound((*regions))); // requires of mm::page_table::impl&%9::create_user_page_table
    assert(guards.unlocked(kernel_owner.0.value().node().slot_vaddr())); // requires of mm::page_table::impl&%9::create_user_page_table
    let mut v1 = (#[verus_spec(with Tracked(kernel_owner), Tracked(regions), Tracked(guards))] self_.create_user_page_table::<G>());
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(self_.relates_owner((*kernel_owner), (*regions))); // requires of mm::page_table::impl&%9::create_user_page_table`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r79"></a>

### R79. PageTable::cursor_mut and cursor return a CursorOwner with as_page_table_owner() == owner and continuations[3].path() == the owner's path, but the view equality needs CursorOwner::as_page_table_owner_preserves_view_mappings, which nobody calls; both now call it and ensure the cursor view's mappings equal the owner's.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 294 @@
             owner.0.value().node().relate_guard(root_guard),
             va.end > 0,
         ensures
             crate::mm::page_table::Cursor::<UserPtConfig, G>::cursor_new_success_conditions(*va) ==> (r matches Ok(_) && cursor_owner@ matches Some(_)),
             // See `cursor` above for the derivation.
             cursor_owner@ matches Some(c) ==> c.inv(),
+            cursor_owner@ matches Some(o) ==> o@.mappings == owner@.mappings,
     )]
     pub fn cursor_mut<G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<
         CursorMut<'a, G>,
     > {
         proof_decl! {
             let tracked mut out_owner: Option<CursorOwner<'a, UserPtConfig>>;
```

```diff
@@ ostd/src/mm/page_table/mod.rs, from line 1256 @@
                 && old(regions).ref_count(idx)
                     != REF_COUNT_UNUSED
                 ==> final(regions).ref_count(idx)
                         == old(regions).ref_count(idx)
                     && final(regions).slot_owners[idx].usage
                         == old(regions).slot_owners[idx].usage,
+            r matches Ok(rb) ==> rb.1@.view().mappings == owner.view().mappings,
     )]
     pub fn cursor_mut<'rcu, G: InAtomicMode>(
         &'rcu self,
         guard: &'rcu G,
         va: &Range<Vaddr>,
     ) -> Result<(CursorMut<'rcu, C, G>, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
-        #[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
-        CursorMut::new(self, guard, va)
+        let res = #[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
+        CursorMut::new(self, guard, va);
+        proof {
+            if res is Ok {
+                res.unwrap().1@.as_page_table_owner_preserves_view_mappings();
+            }
+        }
+        res
     }
 
     /// Create a new cursor exclusively accessing the virtual address range for querying.
     ///
     /// If another cursor is already accessing the range, the new cursor may wait until the
     /// previous cursor is dropped. The modification to the mapping by the cursor may also
@@ ostd/src/mm/page_table/mod.rs, from line 1328 @@
                         == final(regions).ref_count(idx),
             forall|idx: int| #![trigger old(regions).slot_owners[idx].ref_count()]
                 old(regions).ref_count(idx)
                     >= REF_COUNT_MAX
                 ==> final(regions).ref_count(idx)
                         == old(regions).ref_count(idx),
+            r matches Ok(rb) ==> rb.1@.view().mappings == owner.view().mappings,
     )]
     pub fn cursor<'rcu, G: InAtomicMode>(&'rcu self, guard: &'rcu G, va: &Range<Vaddr>) -> Result<
         (Cursor<'rcu, C, G>, Tracked<CursorOwner<'rcu, C>>),
         PageTableError,
     > {
-        #[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
-        Cursor::new(self, guard, va)
+        let res = #[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards))]
+        Cursor::new(self, guard, va);
+        proof {
+            if res is Ok {
+                res.unwrap().1@.as_page_table_owner_preserves_view_mappings();
+            }
+        }
+        res
     }/*
     /// Create a new reference to the same page table.
     /// The caller must ensure that the kernel page table is not copied.
     /// This is only useful for IOMMU page tables. Think twice before using it in other cases.
     pub unsafe fn shallow_copy(&self) -> Self {
         PageTable {
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__0__cursor_mut_5<'a, G: InAtomicMode>(
    self_: &'a VmSpace<'a>,
    guard: &'a G,
    va: &'a Range<usize>,
    Tracked(owner): Tracked<PageTableOwner<UserPtConfig>>,
    Ghost(root_guard): Ghost<PageTableGuard<'a, UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        self_.pt.relates_owner(owner, (*old(regions))),
        owner.0.value().node().relate_guard(root_guard),
        (va.end > 0),
{
    let tracked mut owner = owner;
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards) => Tracked(gr))] self_.cursor_mut(guard, va));
    assert(gr matches Some(o) ==> o@.mappings == owner@.mappings); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr matches Some(o) ==> o@.mappings == owner@.mappings); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies together with [R16](#r16), which it builds on (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 2 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

## `mm/page_table/node/child.rs`

<a id="r61"></a>

### R61. ChildRef::from_pte returns Frame(pte.paddr(), level, pte.prop()) but ensures only res.invariants, whose ChildRef wf does not tie the frame's paddr/level/prop to the PTE and the input level; add that equivalence as an ensures.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/node/child.rs, from line 194 @@
              Tracked(entry_owner): Tracked<&EntryOwner<C>>,
         requires
             entry_owner.pte_invariants(*pte, *regions),
             level == entry_owner.parent_level,
         ensures
             res.invariants(*entry_owner, *regions),
+            res matches ChildRef::Frame(pa, lv, pr) ==> pa == pte.paddr_spec() && lv == level && pr == pte.prop_spec(),
     )]
     pub unsafe fn from_pte(pte: &C::E, level: PagingLevel) -> Self {
         if !pte.is_present() {
             return ChildRef::None;
         }
         let paddr = pte.paddr();
```

**A client that fails** (module `mm.page_table.node.child`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_table__node__child__impl__3__from_pte_6<'a, C: PageTableConfig>(
    pte: &'a C::E,
    mut level: u8,
    Tracked(regions): Tracked<&'a MetaRegionOwners>,
    Tracked(entry_owner): Tracked<&'a EntryOwner<C>>,
)
    requires
        entry_owner.pte_invariants((*pte), (*regions)),
        (level == entry_owner.parent_level),
{
    let mut r = unsafe { (#[verus_spec(with Tracked(regions), Tracked(entry_owner))] ChildRef::<C>::from_pte(pte, level)) };
    assert(r matches ChildRef::Frame(_, lv, _) ==> lv == level); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches ChildRef::Frame(_, lv, _) ==> lv == level); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

## `mm/page_table/node/entry.rs`

<a id="r59"></a>

### R59. Entry::alloc_if_none requires parent_owner.metaregion_sound_node(regions) but does not give it back after allocating, though its body re-establishes it (as split_if_mapped_huge and replace export it), so a caller allocating several entries of one node cannot continue.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/node/entry.rs, from line 493 @@
         ensures
             final(regions).slots == old(regions).slots,
             final(self).invariants(final(owner).value(), *final(regions)),
             final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
             final(self).idx == old(self).idx,
             final(parent_owner).count_consistent(),
+            res is Some ==> final(parent_owner).metaregion_sound_node(*final(regions)),
             *final(self).node == *old(self).node,
             old(owner).value().is_absent() && old(parent_owner).level() > 1 ==> {
                 &&& final(self).node_matching(final(owner).value(), *final(parent_owner), *final(self).node)
                 &&& final(owner).inv()
             },
             old(owner).value().is_absent() && old(parent_owner).level() > 1 ==> {
```

**A client that fails** (module `mm.page_table.node.entry`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn goal_mm__page_table__node__entry__impl__2__alloc_if_none_mm__page_table__node__entry__impl__2__alloc_if_none_56b7ab73<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut Entry<'a, 'a, C>,
    guard: &'a A,
    Tracked(owner): Tracked<&mut TreeNode<EntryOwner<C>, 512, 5>>,
    Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(self_).invariants(old(owner).value(), (*old(regions))),
        old(owner).inv(),
        (old(owner).value().path.len() == old(owner).level()),
        old(self_).node_matching(old(owner).value(), (*old(parent_owner)), (*old(self_).node)),
        (old(owner).level() < (crate::specs::mm::page_table::INC_LEVELS - 1)),
        ((old(owner).level() + old(parent_owner).level()) == crate::specs::mm::page_table::INC_LEVELS),
        old(parent_owner).metaregion_sound_node((*old(regions))),
{
    let mut v0 = (#[verus_spec(with Tracked(owner), Tracked(parent_owner), Tracked(regions), Tracked(guards))] self_.alloc_if_none(guard));
    if let Some(mut x0) = v0 {
        assert(self_.invariants(owner.value(), (*regions))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(owner.inv()); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert((owner.value().path.len() == owner.level())); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(self_.node_matching(owner.value(), (*parent_owner), (*self_.node))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert((owner.level() < (crate::specs::mm::page_table::INC_LEVELS - 1))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(((owner.level() + parent_owner.level()) == crate::specs::mm::page_table::INC_LEVELS)); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(parent_owner.metaregion_sound_node((*regions))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        let mut v1 = (#[verus_spec(with Tracked(owner), Tracked(parent_owner), Tracked(regions), Tracked(guards))] self_.alloc_if_none(guard));
        if let Some(mut x1) = v1 {
        } else {
        }
    } else {
    }
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(parent_owner.metaregion_sound_node((*regions))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

<a id="r60"></a>

### R60. Entry::split_if_mapped_huge makes the entry point at the new node but, unlike alloc_if_none and replace, does not ensure final(self).wf/invariants with the new owner, which its body establishes.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/page_table/node/entry.rs, from line 760 @@
             },
             final(owner).inv(),
             final(owner).value().parent_level == old(owner).value().parent_level,
             final(self).idx == old(self).idx,
             old(owner).value().is_frame() && old(parent_owner).level() > 1 ==>
                 final(self).node_matching(final(owner).value(), *final(parent_owner), *final(self).node),
+            res is Some ==> final(self).wf(final(owner).value()),
+            res is Some ==> final(self).invariants(final(owner).value(), *final(regions)),
             final(regions).inv(),
             final(parent_owner).inv(),
             final(parent_owner).level() == old(parent_owner).level(),
             final(parent_owner).tree_level == old(parent_owner).tree_level,
             *final(self).node == *old(self).node,
             *final(final(self).node) == *final(old(self).node),
```

**A client that fails** (module `mm.page_table.node.entry`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn goal_mm__page_table__node__entry__impl__2__split_if_mapped_huge_mm__page_table__node__entry__impl__2__alloc_if_none_9a993697<'a, C: PageTableConfig, A: InAtomicMode>(
    self_: &mut Entry<'a, 'a, C>,
    guard: &'a A,
    Tracked(owner): Tracked<&mut TreeNode<EntryOwner<C>, 512, 5>>,
    Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        old(regions).inv(),
        old(owner).inv(),
        (old(owner).value().path.len() == old(owner).level()),
        old(self_).wf(old(owner).value()),
        old(parent_owner).relate_guard((*old(self_).node)),
        old(parent_owner).inv(),
        (old(parent_owner).level() == old(owner).value().parent_level),
        (old(parent_owner).level() < crate::arch::mm::NR_LEVELS),
        ((old(owner).level() + old(parent_owner).level()) == crate::specs::mm::page_table::INC_LEVELS),
        old(self_).node_matching(old(owner).value(), (*old(parent_owner)), (*old(self_).node)),
        old(parent_owner).metaregion_sound_node((*old(regions))),
        ((old(owner).value().is_frame() && (old(parent_owner).level() > 1)) ==> old(owner).value().metaregion_sound((*old(regions)))),
{
    let mut v0 = (#[verus_spec(with Tracked(owner), Tracked(parent_owner), Tracked(regions), Tracked(guards))] self_.split_if_mapped_huge(guard));
    if let Some(mut x0) = v0 {
        assert(self_.invariants(owner.value(), (*regions))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(owner.inv()); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert((owner.value().path.len() == owner.level())); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(self_.node_matching(owner.value(), (*parent_owner), (*self_.node))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert((owner.level() < (crate::specs::mm::page_table::INC_LEVELS - 1))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(((owner.level() + parent_owner.level()) == crate::specs::mm::page_table::INC_LEVELS)); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        assert(parent_owner.metaregion_sound_node((*regions))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none
        let mut v1 = (#[verus_spec(with Tracked(owner), Tracked(parent_owner), Tracked(regions), Tracked(guards))] self_.alloc_if_none(guard));
        if let Some(mut x1) = v1 {
        } else {
        }
    } else {
    }
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(self_.invariants(owner.value(), (*regions))); // requires of mm::page_table::node::entry::impl&%2::alloc_if_none`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

## `mm/vm_space.rs`

<a id="r17"></a>

### R17. VmSpace::cursor and cursor_mut keep only c.inv() of the owner and drop PageTable::cursor(_mut)'s '!cond implies Err', the success-branch facts (cursor invariants with the returned owner, which include regions.inv(), va, barrier_va, level, in_barrier_va) and the regions frame condition; they now forward them.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 227 @@
         requires
             self.pt.relates_owner(owner, *old(regions)),
             owner.0.value().node().relate_guard(root_guard),
             va.end > 0,
         ensures
             crate::mm::page_table::Cursor::<UserPtConfig, G>::cursor_new_success_conditions(*va) ==> (r matches Ok(_) && cursor_owner@ matches Some(_)),
+            !crate::mm::page_table::Cursor::<UserPtConfig, G>::cursor_new_success_conditions(*va) ==> r is Err,
+            r is Ok ==> final(regions).inv(),
+            r matches Ok(c) ==> (cursor_owner@ matches Some(o) && c.0.invariants(o, *final(regions), *final(guards))),
+            r matches Ok(c) ==> c.0.va == va.start && c.0.barrier_va == *va && c.0.level == c.0.guard_level,
+            cursor_owner@ matches Some(o) ==> o.in_barrier_va(),
             // On the success branch, the returned cursor owner satisfies
             // its invariant. Follows from the underlying PT::cursor's
             // ensures: r is Ok ⇒ cursor_new_success_conditions (by
             // contrapositive of the !cond ⇒ Err clause) ⇒ invariants
             // hold ⇒ cursor_owner.inv().
             cursor_owner@ matches Some(c) ==> c.inv(),
@@ ostd/src/mm/vm_space.rs, from line 292 @@
         requires
             self.pt.relates_owner(owner, *old(regions)),
             owner.0.value().node().relate_guard(root_guard),
             va.end > 0,
         ensures
             crate::mm::page_table::Cursor::<UserPtConfig, G>::cursor_new_success_conditions(*va) ==> (r matches Ok(_) && cursor_owner@ matches Some(_)),
+            !crate::mm::page_table::Cursor::<UserPtConfig, G>::cursor_new_success_conditions(*va) ==> r is Err,
+            r is Ok ==> final(regions).inv(),
+            r matches Ok(c) ==> (cursor_owner@ matches Some(o) && c.pt_cursor.0.invariants(o, *final(regions), *final(guards))),
+            r matches Ok(c) ==> c.pt_cursor.0.va == va.start && c.pt_cursor.0.barrier_va == *va && c.pt_cursor.0.level == c.pt_cursor.0.guard_level,
+            cursor_owner@ matches Some(o) ==> o.in_barrier_va(),
+            final(regions).slots == old(regions).slots,
+            forall|idx: int| #![trigger final(regions).slot_owners[idx]]
+                old(regions).contains(idx) && old(regions).ref_count(idx) != crate::mm::frame::meta::REF_COUNT_UNUSED ==>
+                    final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
             // See `cursor` above for the derivation.
             cursor_owner@ matches Some(c) ==> c.inv(),
     )]
     pub fn cursor_mut<G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<
         CursorMut<'a, G>,
     > {
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__0__cursor_mut_4<'a, G: InAtomicMode>(
    self_: &'a VmSpace<'a>,
    guard: &'a G,
    va: &'a Range<usize>,
    Tracked(owner): Tracked<PageTableOwner<UserPtConfig>>,
    Ghost(root_guard): Ghost<PageTableGuard<'a, UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        self_.pt.relates_owner(owner, (*old(regions))),
        owner.0.value().node().relate_guard(root_guard),
        (va.end > 0),
{
    let tracked mut owner = owner;
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards) => Tracked(gr))] self_.cursor_mut(guard, va));
    assert(gr matches Some(o) ==> o.in_barrier_va()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr matches Some(o) ==> o.in_barrier_va()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 32 failing clients in 18 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r18"></a>

### R18. VmSpace::cursor drops PageTable::cursor's as_page_table_owner() == owner for the returned cursor owner, which ties the cursor view to the walked page table.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 233 @@
             // On the success branch, the returned cursor owner satisfies
             // its invariant. Follows from the underlying PT::cursor's
             // ensures: r is Ok ⇒ cursor_new_success_conditions (by
             // contrapositive of the !cond ⇒ Err clause) ⇒ invariants
             // hold ⇒ cursor_owner.inv().
             cursor_owner@ matches Some(c) ==> c.inv(),
+            cursor_owner@ matches Some(o) ==> o.as_page_table_owner() == owner,
+            final(regions).slots == old(regions).slots,
     )]
     pub fn cursor<G: InAtomicMode>(&'a self, guard: &'a G, va: &Range<Vaddr>) -> Result<
         Cursor<'a, G>,
     > {
         proof_decl! {
             let tracked mut out_owner: Option<CursorOwner<'a, UserPtConfig>>;
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__0__cursor_34<'a, G: InAtomicMode>(
    self_: &'a VmSpace<'a>,
    guard: &'a G,
    va: &'a Range<usize>,
    Tracked(owner): Tracked<PageTableOwner<UserPtConfig>>,
    Ghost(root_guard): Ghost<PageTableGuard<'a, UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        self_.pt.relates_owner(owner, (*old(regions))),
        owner.0.value().node().relate_guard(root_guard),
        (va.end > 0),
{
    let tracked mut owner = owner;
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards) => Tracked(gr))] self_.cursor(guard, va));
    assert(gr matches Some(o) ==> o.as_page_table_owner() == owner); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(gr matches Some(o) ==> o.as_page_table_owner() == owner); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r19"></a>

### R19. VmSpace::reader and writer never change the VmSpaceOwner (new_vm_io_id is a spec function) and return Some exactly with Ok, but ensure only final(owner).inv() and Some under the success condition.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 372 @@
                 -> reader_owner: Tracked<Option<VmIoOwner>>,
         requires
             old(owner).inv(),
         ensures
             final(owner).inv(),
             self.reader_success_cond(vaddr, len) ==> r is Ok && reader_owner@ is Some,
+            *final(owner) == *old(owner),
+            r is Ok ==> reader_owner@ is Some,
             r is Ok && reader_owner@ is Some ==> {
                 &&& r.unwrap().wf(reader_owner@->0)
                 &&& reader_owner@->0.mem_view is None
                 &&& reader_owner@->0.inv()
             },
             // Range bound is necessary for success: the body's `checked_add`
@@ ostd/src/mm/vm_space.rs, from line 431 @@
                 -> writer_owner: Tracked<Option<VmIoOwner>>,
         requires
             old(owner).inv(),
         ensures
             final(owner).inv(),
             self.writer_success_cond(vaddr, len) ==> r is Ok && writer_owner@ is Some,
+            *final(owner) == *old(owner),
+            r is Ok ==> writer_owner@ is Some,
             r is Ok && writer_owner@ is Some ==> {
                 &&& r.unwrap().wf(writer_owner@->0)
                 &&& writer_owner@->0.mem_view is None
                 &&& writer_owner@->0.inv()
             },
             // Range bound is necessary for success: see `reader` above.
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__0__reader_40<'a>(
    self_: &'a VmSpace<'a>,
    mut vaddr: usize,
    mut len: usize,
    Tracked(owner): Tracked<&mut VmSpaceOwner>,
)
    requires
        old(owner).inv(),
{
    let ghost old_owner = (*owner);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner) => Tracked(gr))] self_.reader(vaddr, len));
    assert((*owner) == old_owner); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*owner) == old_owner); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

<a id="r20"></a>

### R20. VmReader/VmWriter::from_user_space fix cursor and end from (vaddr, len), but VmSpace::reader/writer do not export remain()/avail() == len, nor (writer) that a current page table and an in-range request give Ok.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 381 @@
                 &&& reader_owner@->0.inv()
             },
             // Range bound is necessary for success: the body's `checked_add`
             // guard rejects any out-of-range request before constructing a
             // reader. `nat` arithmetic subsumes the overflow case.
             r is Ok ==> (vaddr as nat) + (len as nat) <= MAX_USERSPACE_VADDR as nat,
+            r matches Ok(rd) ==> rd.remain_spec() == len,
     )]
     pub fn reader(&self, vaddr: Vaddr, len: usize) -> Result<VmReader<'a, Fallible>> {
         if current_page_table_paddr() != self.pt.root_paddr() {
             proof_with!(|= Tracked(None));
             Err(Error::AccessDenied)
         } else if vaddr.checked_add(len).unwrap_or(usize::MAX) > MAX_USERSPACE_VADDR {
@@ ostd/src/mm/vm_space.rs, from line 438 @@
                 &&& r.unwrap().wf(writer_owner@->0)
                 &&& writer_owner@->0.mem_view is None
                 &&& writer_owner@->0.inv()
             },
             // Range bound is necessary for success: see `reader` above.
             r is Ok ==> (vaddr as nat) + (len as nat) <= MAX_USERSPACE_VADDR as nat,
+            crate::arch::mm::current_page_table_paddr_spec() == self.pt.root_paddr_spec() && (vaddr as nat) + (len as nat) <= MAX_USERSPACE_VADDR as nat ==> r is Ok,
+            r matches Ok(w) ==> w.avail_spec() == len,
     )]
     pub fn writer(self, vaddr: Vaddr, len: usize) -> Result<VmWriter<'a, Fallible>> {
         if current_page_table_paddr() != self.pt.root_paddr() {
             proof_with!(|= Tracked(None));
             Err(Error::AccessDenied)
         } else if vaddr.checked_add(len).unwrap_or(usize::MAX) > MAX_USERSPACE_VADDR {
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__0__writer_27<'a>(
    mut self_: VmSpace<'a>,
    mut vaddr: usize,
    mut len: usize,
    Tracked(owner): Tracked<&mut VmSpaceOwner>,
)
    requires
        old(owner).inv(),
{
    let ghost old_owner = (*owner);
    proof_decl! { let tracked mut gr; }
    let mut r = (#[verus_spec(with Tracked(owner) => Tracked(gr))] self_.writer(vaddr, len));
    assert(r matches Ok(w) ==> w.avail_spec() == len); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r matches Ok(w) ==> w.avail_spec() == len); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 3 groups of failures pass.

<a id="r22"></a>

### R22. CursorMut::flusher only returns &mut self.flusher but does not ensure pt_cursor is unchanged, so the cursor invariants are lost after flushing through it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 804 @@
 
     /// Get the dedicated TLB flusher for this cursor.
     #[verus_spec(ret =>
         ensures
             *ret == old(self).flusher,
             *final(ret) == final(self).flusher,
+            final(self).pt_cursor == old(self).pt_cursor,
     )]
     pub fn flusher(&mut self) -> &mut TlbFlusher<'a> {
         &mut self.flusher
     }
 
     /// Map a frame into the current slot.
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__2__flusher_56<'a, A: InAtomicMode>(
    self_: &mut CursorMut<'a, A>,
)
{
    let ghost old_self_ = (*self_);
    let mut r = self_.flusher();
    assert((*self_).pt_cursor == old_self_.pt_cursor); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).pt_cursor == old_self_.pt_cursor); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r23"></a>

### R23. VmSpace CursorMut::map requires tlb_model.inv() and keeps it (issue_tlb_flush_with and dispatch_tlb_flush preserve it) but does not ensure it, so a second map or an unmap cannot follow.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 853 @@
             old(self).map_item_ensures(
                 frame,
                 prop,
                 old(cursor_owner)@,
                 final(cursor_owner)@,
             ),
+            final(tlb_model).inv(),
     )]
     pub fn map(&mut self, frame: UFrame, prop: PageProperty) {
         let start_va = self.virt_addr();
         let item = MappedItem { frame: frame, prop: prop };
 
         // SAFETY: It is safe to map untyped memory into the userspace.
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__2__map_57<'a, A: InAtomicMode>(
    self_: &mut CursorMut<'a, A>,
    mut frame: Frame<MetaSlotStorage>,
    mut prop: PageProperty,
    Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
    Tracked(entry_owner): Tracked<EntryOwner<UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
    Tracked(tlb_model): Tracked<&mut TlbModel>,
)
    requires
        old(tlb_model).inv(),
        old(self_).pt_cursor.0.invariants((*old(cursor_owner)), (*old(regions)), (*old(guards))),
        old(self_).item_wf(frame, prop, entry_owner, (*old(regions))),
        ((*old(self_)).pt_cursor.map_panic_conditions(crate::mm::vm_space::MappedItem { frame: frame, prop: prop }) ==> vstd_extra::panic::may_panic()),
{
    let tracked mut entry_owner = entry_owner;
    let ghost old_self_ = (*self_);
    let ghost old_cursor_owner = (*cursor_owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    let ghost old_tlb_model = (*tlb_model);
    proof { assume(!((*self_).pt_cursor.map_panic_conditions(crate::mm::vm_space::MappedItem { frame: frame, prop: prop }))); } // no panic
    (#[verus_spec(with Tracked(cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards), Tracked(tlb_model))] self_.map(frame, prop));
    assert((*tlb_model).inv()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*tlb_model).inv()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r28"></a>

### R28. VmSpace CursorMut::unmap's ensures never constrain the returned count although the loop keeps num_unmapped == removed.len() with every removed mapping starting in the range and refining an old mapping; with no old mapping in the range nothing is removed and the count is 0.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 940 @@
             old(self).pt_cursor.0.find_next_panic_condition(len) ==> may_panic(),
         ensures
             !old(self).pt_cursor.0.find_next_panic_condition(len),
             final(self).pt_cursor.0.invariants(*final(cursor_owner), *final(regions), *final(guards)),
             old(cursor_owner)@.unmap_spec(len, final(cursor_owner)@, r),
             final(tlb_model).inv(),
+            (forall|m: Mapping| #[trigger] old(cursor_owner)@.mappings.contains(m) ==> (m.va_range.end <= old(cursor_owner)@.cur_va || m.va_range.start >= old(cursor_owner)@.cur_va + len)) ==> r == 0,
     )]
     #[verifier::spinoff_prover]
     pub fn unmap(&mut self, len: usize) -> usize {
         proof {
             cursor_owner.view_preserves_inv();
         }
@@ ostd/src/mm/vm_space.rs, from line 1471 @@
                 parent: Mapping,
             | #[trigger]
                 old_view.mappings.contains(parent) && parent.va_range.start <= m.va_range.start
                     && m.va_range.end <= parent.va_range.end && m.pa_range.start == (
                 parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                     && m.property == parent.property by {};
+
+            if (forall|m: Mapping| #[trigger] old_view.mappings.contains(m) ==> (m.va_range.end <= old_view.cur_va || m.va_range.start >= old_view.cur_va + len)) {
+                assert forall|m: Mapping| #[trigger] removed.contains(m) implies false by {
+                    assert(adjusted_base.contains(m));
+                    assert(m.inv());
+                    if !old_view.mappings.contains(m) {
+                        let parent = choose|parent: Mapping| #[trigger] old_view.mappings.contains(parent)
+                            && parent.va_range.start <= m.va_range.start && m.va_range.end <= parent.va_range.end
+                            && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
+                            && m.property == parent.property;
+                        assert(old_view.mappings.contains(parent));
+                    }
+                };
+                assert(removed =~= Set::<Mapping>::empty());
+            }
         }
 
         #[verus_spec(with Tracked(tlb_model))]
         self.flusher.dispatch_tlb_flush();
 
         num_unmapped
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__2__unmap_23<'a, A: InAtomicMode>(
    self_: &mut CursorMut<'a, A>,
    mut len: usize,
    Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
    Tracked(tlb_model): Tracked<&mut TlbModel>,
)
    requires
        ((len >= crate::mm::page_size::<PagingConsts>(2)) ==> vstd_extra::panic::may_panic()),
        old(self_).pt_cursor.0.invariants((*old(cursor_owner)), (*old(regions)), (*old(guards))),
        old(tlb_model).inv(),
        (old(self_).pt_cursor.0.find_next_panic_condition(len) ==> vstd_extra::panic::may_panic()),
        old(self_).pt_cursor.0.va + len <= usize::MAX,
{
    let ghost old_self_ = (*self_);
    let ghost old_cursor_owner = (*cursor_owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    let ghost old_tlb_model = (*tlb_model);
    proof { assume(!((len >= crate::mm::page_size::<PagingConsts>(2)))); } // no panic
    proof { assume(!(self_.pt_cursor.0.find_next_panic_condition(len))); } // no panic
    let mut r = (#[verus_spec(with Tracked(cursor_owner), Tracked(regions), Tracked(guards), Tracked(tlb_model))] self_.unmap(len));
    assert((forall|m: Mapping| #[trigger] old_cursor_owner@.mappings.contains(m) ==> (m.va_range.end <= old_cursor_owner@.cur_va || m.va_range.start >= old_cursor_owner@.cur_va + len)) ==> r == 0); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((forall|m: Mapping| #[trigger] old_cursor_owner@.mappings.contains(m) ==> (m.va_range.end <= old_cursor_owner@.cur_va || m.va_range.start >= old_cursor_owner@.cur_va + len)) ==> r == 0); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

**Note.** the changed function's proof rests on an existing `assume` at `ostd/src/mm/vm_space.rs:956` (`self.pt_cursor.0.va + len <= usize::MAX`).

<a id="r70"></a>

### R70. VmSpace::default calls VmSpace::new, which ensures final(regions).inv(), but default itself has no ensures, so neither new nor default can follow a default.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 152 @@
     #[verus_spec(r =>
         with
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
         requires
             old(regions).inv(),
+        ensures
+            final(regions).inv(),
     )]
     #[allow(private_interfaces)]
     pub fn default<'rcu>() -> Self {
         proof_with!(Tracked(regions), Tracked(guards));
         Self::new()
     }
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn goal_mm__vm_space__impl__0__cursor_mm__vm_space__impl__0__new_817998b2<'a, G: InAtomicMode>(
    self_: &'a VmSpace<'a>,
    guard: &'a G,
    va: &'a Range<usize>,
    Tracked(owner): Tracked<PageTableOwner<UserPtConfig>>,
    Ghost(root_guard): Ghost<PageTableGuard<'a, UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
)
    requires
        self_.pt.relates_owner(owner, (*old(regions))),
        owner.0.value().node().relate_guard(root_guard),
        (va.end > 0),
        old(regions).inv(),
{
    let tracked mut owner = owner;
    proof_decl! { let tracked mut o0; }
    let mut v0 = (#[verus_spec(with Tracked(owner), Ghost(root_guard), Tracked(regions), Tracked(guards) => Tracked(o0))] self_.cursor(guard, va));
    if let Ok(mut x0) = v0 {
        assert(regions.inv()); // requires of mm::vm_space::impl&%0::new
        let mut v1 = (#[verus_spec(with Tracked(regions), Tracked(guards))] VmSpace::new());
    } else {
    }
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(regions.inv()); // requires of mm::vm_space::impl&%0::new`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 6 failing clients in 2 groups of failures pass.

<a id="r80"></a>

### R80. VmSpace CursorMut::map drops page_table CursorMut::map's barrier_va preservation and its va advance by page_size(level) (cursor-16); a UFrame item has level 1 and item_wf bounds va + 4096 by barrier_va.end, so the cursor moves by exactly 4096.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/mm/vm_space.rs, from line 846 @@
             old(tlb_model).inv(),
             old(self).pt_cursor.0.invariants(*old(cursor_owner), *old(regions), *old(guards)),
             old(self).item_wf(frame, prop, entry_owner, *old(regions)),
             old(self).pt_cursor.map_panic_conditions(MappedItem { frame: frame, prop: prop }) ==> may_panic(),
         ensures
             !old(self).pt_cursor.map_panic_conditions(MappedItem { frame: frame, prop: prop }),
+            final(self).pt_cursor.0.barrier_va == old(self).pt_cursor.0.barrier_va,
+            final(self).pt_cursor.0.va == old(self).pt_cursor.0.va + 4096,
             final(self).pt_cursor.0.invariants(*final(cursor_owner), *final(regions), *final(guards)),
             old(self).map_item_ensures(
                 frame,
                 prop,
                 old(cursor_owner)@,
                 final(cursor_owner)@,
             ),
     )]
     pub fn map(&mut self, frame: UFrame, prop: PageProperty) {
         let start_va = self.virt_addr();
         let item = MappedItem { frame: frame, prop: prop };
+        proof {
+            assert(UserPtConfig::item_into_raw(item).1 == 1);
+            lemma_page_size_spec_values();
+        }
 
         // SAFETY: It is safe to map untyped memory into the userspace.
         let Err(frag) = (unsafe {
             #[verus_spec(with Tracked(cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards))]
             self.pt_cursor.map(item)
         }) else {
```

**A client that fails** (module `mm.vm_space`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__vm_space__impl__2__map_58<'a, A: InAtomicMode>(
    self_: &mut CursorMut<'a, A>,
    mut frame: Frame<MetaSlotStorage>,
    mut prop: PageProperty,
    Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
    Tracked(entry_owner): Tracked<EntryOwner<UserPtConfig>>,
    Tracked(regions): Tracked<&mut MetaRegionOwners>,
    Tracked(guards): Tracked<&mut Guards>,
    Tracked(tlb_model): Tracked<&mut TlbModel>,
)
    requires
        old(tlb_model).inv(),
        old(self_).pt_cursor.0.invariants((*old(cursor_owner)), (*old(regions)), (*old(guards))),
        old(self_).item_wf(frame, prop, entry_owner, (*old(regions))),
        ((*old(self_)).pt_cursor.map_panic_conditions(crate::mm::vm_space::MappedItem { frame: frame, prop: prop }) ==> vstd_extra::panic::may_panic()),
{
    let tracked mut entry_owner = entry_owner;
    let ghost old_self_ = (*self_);
    let ghost old_cursor_owner = (*cursor_owner);
    let ghost old_regions = (*regions);
    let ghost old_guards = (*guards);
    let ghost old_tlb_model = (*tlb_model);
    proof { assume(!((*self_).pt_cursor.map_panic_conditions(crate::mm::vm_space::MappedItem { frame: frame, prop: prop }))); } // no panic
    (#[verus_spec(with Tracked(cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards), Tracked(tlb_model))] self_.map(frame, prop));
    assert((*self_).pt_cursor.0.barrier_va == old_self_.pt_cursor.0.barrier_va && (*self_).pt_cursor.0.va == old_self_.pt_cursor.0.va + 4096); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_).pt_cursor.0.barrier_va == old_self_.pt_cursor.0.barrier_va && (*self_).pt_cursor.0.va == old_self_.pt_cursor.0.va + 4096); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies together with [R15](#r15), [R24](#r24), [R25](#r25), [R60](#r60), [R61](#r61), [pt6-2](#fix-pt6-2), which it builds on (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

## `sync/mutex.rs`

<a id="r64"></a>

### R64. Mutex::lock has no ensures although try_lock ensures ret.rel_mutex(*self) and wait_until forwards the closure's ensures; give the closure that ensures and forward it.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/mutex.rs, from line 67 @@
 #[verus_verify]
 impl<T  /* : ?Sized */ > Mutex<T> {
     /// Acquires the mutex.
     ///
     /// This method runs in a block way until the mutex can be acquired.
     #[track_caller]
+    #[verus_spec(ret =>
+        ensures
+            ret.rel_mutex(*self),
+    )]
     pub fn lock(&self) -> MutexGuard<'_, T> {
-        self.queue.wait_until(|| self.try_lock())
+        self.queue.wait_until(
+            || -> (r: Option<MutexGuard<T>>)
+                ensures
+                    r is Some ==> r->0.rel_mutex(*self),
+                { self.try_lock() },
+        )
     }
 
     /// Tries to acquire the mutex immediately.
     #[verus_spec(ret =>
         ensures
             ret is Some ==> ret->0.rel_mutex(*self),
```

**A client that fails** (module `sync.mutex`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__mutex__impl__3__lock_0<'a, T>(
    self_: &'a Mutex<T>,
)
{
    let mut r = self_.lock();
    assert(r.rel_mutex(*self_)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.rel_mutex(*self_)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

<a id="r65"></a>

### R65. MutexGuard::deref_mut does not say the guard's closed rel_mutex is unchanged, so after writing through the guard the caller loses which mutex it belongs to.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/mutex.rs, from line 255 @@
 #[verus_verify]
 impl<T/* : ?Sized */> DerefMut for MutexGuard<'_, T> {
     #[verus_spec(ret =>
         ensures
             final(self).view() == *final(ret),
             old(self).view() == *ret,
+            forall|m: Mutex<T>| #[trigger] (*final(self)).rel_mutex(m) == (*old(self)).rel_mutex(m),
     )]
     fn deref_mut(&mut self) -> &mut Self::Target
     {
         proof!{
             use_type_invariant(&*self);
         }
```

**A client that fails** (module `sync.mutex`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__mutex__impl__9__deref_mut_1<'a, T>(
    self_: &mut MutexGuard<'a, T>,
)
{
    let ghost old_self_ = (*self_);
    let mut r = self_.deref_mut();
    assert(forall|m: Mutex<T>| #[trigger] (*self_).rel_mutex(m) == old_self_.rel_mutex(m)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(forall|m: Mutex<T>| #[trigger] (*self_).rel_mutex(m) == old_self_.rel_mutex(m)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

## `sync/rcu/mod.rs`

<a id="r66"></a>

### R66. RcuOptionReadGuard::compare_exchange does not forward the inner RcuReadGuardInner::compare_exchange ensures new_ptr is Some && r is Err ==> r->Err_0 is Some.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/rcu/mod.rs, from line 898 @@
     #[inline]
     pub fn is_none(&self) -> bool {
         self.0.obj_ptr.is_null()
     }
 
     #[inline]
+    #[verus_spec(r =>
+        ensures
+            new_ptr is Some && r is Err ==> r->Err_0 is Some,
+            r matches Err(p) ==> p == new_ptr,
+    )]
     pub fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
         proof {
             use_type_invariant(&self);
         }
         self.0.compare_exchange(new_ptr)
     }
```

**A client that fails** (module `sync.rcu`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__rcu__impl__12__compare_exchange_2<'a, P: NonNullPtr + Send>(
    mut self_: RcuOptionReadGuard<'a, P>,
    mut new_ptr: Option<P>,
)
{
    let mut r = self_.compare_exchange(new_ptr);
    assert(r is Err ==> r->Err_0 == new_ptr); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r is Err ==> r->Err_0 == new_ptr); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies together with [R91](#r91), which it builds on (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

## `sync/rcu/non_null/either.rs`

<a id="r67"></a>

### R67. Either's ref_rel_perm is defined as true, so raw_as_ref/ref_as_raw lose the side and the per-side L/R::ref_rel_perm that their bodies get from L/R::raw_as_ref and L/R::ref_as_raw; define it side-wise like rel_perm.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/rcu/non_null/either.rs, from line 242 @@
             Sum::Left(left) => Sum::Left(L::ref_perm_view_permission(left)),
             Sum::Right(right) => Sum::Right(R::ref_perm_view_permission(right)),
         }
     }
 
     open spec fn ref_rel_perm(r: Self::Ref, perm: Self::RefPermission) -> bool {
-        true
+        match (r, perm) {
+            (Either::Left(left), Sum::Left(left_perm)) => L::ref_rel_perm(left, left_perm),
+            (Either::Right(right), Sum::Right(right_perm)) => R::ref_rel_perm(right, right_perm),
+            _ => false,
+        }
     }
 
     proof fn lemma_ref_perm_inv_impl_perm_inv(perm: Self::RefPermission) {
         match perm {
             Sum::Left(left) => L::lemma_ref_perm_inv_impl_perm_inv(left),
             Sum::Right(right) => R::lemma_ref_perm_inv_impl_perm_inv(right),
```

**A client that fails** (module `sync.rcu.non_null.either`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__rcu__non_null__either__impl__1__ref_as_raw_1<'a, L: NonNullPtrRef<'a>, R: NonNullPtrRef<'a>>(
    mut ptr_ref: Either<L::Ref, R::Ref>,
)
{
    let mut r = <Either<L, R> as crate::sync::rcu::non_null::NonNullPtrRef>::ref_as_raw(ptr_ref);
    assert((r.1@ is Left) == (ptr_ref is Left)); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((r.1@ is Left) == (ptr_ref is Left)); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 6 failing clients in 6 groups of failures pass.

**Note.** this changes the definition of the open spec function `Either::ref_rel_perm` (from `true`), not only an `ensures`; please check that no trusted (`external_body`) contract relies on the old definition.

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

## `sync/rcu/non_null/mod.rs`

<a id="r91"></a>

### R91. On failure RcuReadGuardInner::compare_exchange returns from_raw(into_raw(new_ptr)), but NonNullPtr only says both are rel_perm-related to the same permission, not that they are equal; a new NonNullPtr proof obligation (rel_perm determines the pointer, proved for Box, Arc and Either) lets the inner compare_exchange and RcuReadGuard::compare_exchange ensure the returned pointer is new_ptr.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/rcu/non_null/mod.rs, from line 106 @@
     /// This design is to support the tagged pointer trick used in `Either`.
     spec fn ptr_perm_match(ptr: *mut Self::Target, perm: Self::Permission) -> bool;
 
     /// A specification function that relates the original smart pointer and the permission.
     spec fn rel_perm(self, perm: Self::Permission) -> bool;
 
+    /// The permission determines the pointer it is related to.
+    proof fn lemma_rel_perm_injective(self, other: Self, perm: Self::Permission)
+        requires
+            self.rel_perm(perm),
+            other.rel_perm(perm),
+        ensures
+            self == other,
+    ;
+
     /// The ALIGN_BITS must be less than usize::BITS.
     proof fn lemma_align_bits_range()
         ensures
             Self::ALIGN_BITS < usize::BITS,
     ;
 }
@@ ostd/src/sync/rcu/non_null/mod.rs, from line 293 @@
     }
 
     open spec fn rel_perm(self, perm: Self::Permission) -> bool {
         perm.view_target() == *self
     }
 
+    proof fn lemma_rel_perm_injective(self, other: Self, perm: Self::Permission) {
+    }
+
     axiom fn lemma_align_bits_range();
 }
 
 unsafe impl<'a, T: 'static> NonNullPtrRef<'a> for Box<T> {
     type Ref = BoxRef<'a, T>;
 
@@ ostd/src/sync/rcu/non_null/mod.rs, from line 447 @@
     }
 
     open spec fn rel_perm(self, perm: Self::Permission) -> bool {
         perm.view_target() == *self
     }
 
+    proof fn lemma_rel_perm_injective(self, other: Self, perm: Self::Permission) {
+    }
+
     axiom fn lemma_align_bits_range();
 }
 
 unsafe impl<'a, T: 'static> NonNullPtrRef<'a> for Arc<T> {
     type Ref = ArcRef<'a, T>;
 
```

```diff
@@ ostd/src/sync/rcu/non_null/either.rs, from line 219 @@
             (Either::Left(left), Sum::Left(left_perm)) => left.rel_perm(left_perm),
             (Either::Right(right), Sum::Right(right_perm)) => right.rel_perm(right_perm),
             _ => false,
         }
     }
 
+    proof fn lemma_rel_perm_injective(self, other: Self, perm: Self::Permission) {
+        match (self, other, perm) {
+            (Either::Left(l1), Either::Left(l2), Sum::Left(p)) => {
+                l1.lemma_rel_perm_injective(l2, p);
+            },
+            (Either::Right(r1), Either::Right(r2), Sum::Right(p)) => {
+                r1.lemma_rel_perm_injective(r2, p);
+            },
+            _ => {},
+        }
+    }
+
     axiom fn lemma_align_bits_range()
         ensures
             Self::ALIGN_BITS == if L::ALIGN_BITS < R::ALIGN_BITS {
                 L::ALIGN_BITS - 1
             } else {
                 R::ALIGN_BITS - 1
```

```diff
@@ ostd/src/sync/rcu/mod.rs, from line 533 @@
 
     #[verus_spec(r =>
         requires
             self.rcu.is_nullable() || new_ptr is Some,
         ensures
             new_ptr is Some && r is Err ==> r->Err_0 is Some,
+            r matches Err(p) ==> p == new_ptr,
     )]
     fn compare_exchange(self, new_ptr: Option<P>) -> Result<(), Option<P>> {
+        let ghost new_ptr_g = new_ptr;
         let obj_ptr = self.obj_ptr;
         proof {
             use_type_invariant(&self);
             use_type_invariant(self.rcu);
         }
         proof_decl! {
@@ ostd/src/sync/rcu/mod.rs, from line 627 @@
                 let tracked new_perm = err_new_perm.tracked_unwrap().tracked_unwrap();
             }
             // SAFETY:
             // 1. It was previously returned by `into_raw`.
             // 2. The `compare_exchange` fails so the pointer will not
             //    be used by other threads via reading the RCU primitive.
-            Err(Some(unsafe { <P as NonNullPtr>::from_raw(new_nonnull, Tracked(new_perm)) }))
+            let ghost new_perm_g = new_perm;
+            let ret = unsafe { <P as NonNullPtr>::from_raw(new_nonnull, Tracked(new_perm)) };
+            proof {
+                ret.lemma_rel_perm_injective(new_ptr_g->0, new_perm_g);
+            }
+            Err(Some(ret))
         }
     }
 
     /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
     #[inline]
     #[verus_spec]
@@ ostd/src/sync/rcu/mod.rs, from line 862 @@
     /// to relax the CPU or yield the task on failure. Otherwise contention
     /// will occur.
     ///
     /// This API does not help to avoid
     /// [the ABA problem](https://en.wikipedia.org/wiki/ABA_problem).
     #[inline]
+    #[verus_spec(r =>
+        ensures
+            r is Err ==> r->Err_0 == new_ptr,
+    )]
     pub fn compare_exchange(self, new_ptr: P) -> Result<(), P> {
         self.0.compare_exchange(Some(new_ptr)).map_err(
-            |err|
+            |err: Option<P>| -> (ret: P)
                 requires
                     err is Some,
+                ensures
+                    ret == err->0,
                 { err.unwrap() },
         )
     }
 }
 
 /*
```

**A client that fails** (module `sync.rcu`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__rcu__impl__11__compare_exchange_1<'a, P: NonNullPtr + Send>(
    mut self_: RcuReadGuard<'a, P>,
    mut new_ptr: P,
)
{
    let mut r = self_.compare_exchange(new_ptr);
    assert(r is Err ==> r->Err_0 == new_ptr); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r is Err ==> r->Err_0 == new_ptr); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 3 failing clients in 2 groups of failures pass.

**Note.** the changed function's proof rests on an existing `assume` at `ostd/src/sync/rcu/mod.rs:603` (`false`); the changed function's proof rests on an existing `assume` at `ostd/src/sync/rcu/mod.rs:606` (`false #2`); adds a proof obligation lemma_rel_perm_injective to the NonNullPtr trait, proved by every impl (Box, Arc, Either).

**Upstream.** The code at this place changed in `main` (origin/main); this may already be addressed there (not checked).

## `sync/rwlock.rs`

<a id="r77"></a>

### R77. RwLockUpgradeableGuard::upgrade has no ensures tying the write guard's value to the upread guard's value, which try_upgrade keeps (it builds the write permission from the upread token's cell permission); the round-1 fix failed only because upgrade's loop is isolated, so the ensures' `self` (the parameter's value at entry, not the loop-reassigned `self`) is unknown in the loop: turn loop isolation off for upgrade so v0 == self.value() at entry reaches the return.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/rwlock.rs, from line 953 @@
     /// Upgrades this upread guard to a write guard atomically.
     ///
     /// After calling this method, subsequent readers will be blocked
     /// while previous readers remain unaffected. The calling thread
     /// will spin-wait until previous readers finish.
     #[verifier::exec_allows_no_decreases_clause]
+    #[verifier::loop_isolation(false)]
+    #[verus_spec(r =>
+        ensures
+            r.value() == self.value(),
+    )]
     pub fn upgrade(mut self) -> RwLockWriteGuard<'a, T, G> {
+        let ghost v0 = self.value();
         proof! {
             use_type_invariant(&self);
             use_type_invariant(&self.inner);
             lemma_consts_properties();
         }
         // self.inner.lock.fetch_or(BEING_UPGRADED, Acquire);
@@ ostd/src/sync/rwlock.rs, from line 967 @@
             self.inner.lock => fetch_or(BEING_UPGRADED);
             update prev -> next;
             ghost g => {
                 lemma_consts_properties_prev_next(prev, next);
             }
         );
-        loop {
+        loop
+            invariant
+                self.value() == v0,
+        {
             self =
             match self.try_upgrade() {
                 Ok(guard) => return guard,
                 Err(e) => e,
             };
         }
@@ ostd/src/sync/rwlock.rs, from line 983 @@
     /// Attempts to upgrade this upread guard to a write guard atomically.
     ///
     /// This function will never spin-wait and will return immediately.
     ///
     /// This function is not exposed publicly because the `BEING_UPGRADED` bit
     /// is set only in [`Self::upgrade`].
+    #[verus_spec(r =>
+        ensures
+            r is Ok ==> r->Ok_0.value() == self.value(),
+            r is Err ==> r->Err_0.value() == self.value(),
+    )]
     fn try_upgrade(mut self) -> Result<RwLockWriteGuard<'a, T, G>, Self> {
         proof! {
             use_type_invariant(&self);
             use_type_invariant(self.inner);
             lemma_consts_properties();
         }
```

**A client that fails** (module `sync.rwlock`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__rwlock__impl__21__upgrade_0<'a, T, G: SpinGuardian>(
    mut self_: RwLockUpgradeableGuard<'a, T, G>,
)
{
    let mut r = self_.upgrade();
    assert(r.value() == self_.value()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.value() == self_.value()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

**Note.** the change adds `#[verifier::loop_isolation(false)]`, which is not a specification; adds #[verifier::loop_isolation(false)] to upgrade: a proof setting, not a specification.

## `sync/spin.rs`

<a id="r68"></a>

### R68. SpinLock::wf is the public well-formedness predicate for wrappers, but SpinLock::new does not ensure it (res.wf() verifies).

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/spin.rs, from line 168 @@
         Tracked(resource): Tracked<I::Resource>,
     ) -> (res: Self)
         requires
             I::inv(resource_constant, val, resource),
         ensures
             res.constant() == resource_constant,
+            res.wf(),
     {
         let (val, Tracked(perm)) = PCell::new(val);
         let tracked resource = SpinLockResource { perm, resource: resource };
         let lock_inner = SpinLockInner {
             lock: AtomicBool::new(
                 Ghost((val, Ghost(resource_constant))),
```

**A client that fails** (module `sync.spin`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__spin__impl__3__new_0<T, G, I: ResourceInvariant<T>>(
    mut val: T,
    Ghost(resource_constant): Ghost<I::Constant>,
    Tracked(resource): Tracked<I::Resource>,
)
    requires
        <I as vstd_extra::resource_invariant::ResourceInvariant<T>>::inv(resource_constant, val, resource),
{
    let tracked mut resource = resource;
    let mut r = SpinLock::<T, G, I>::new(val, Ghost(resource_constant), Tracked(resource));
    assert(r.wf()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(r.wf()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 1 failing client in 1 group of failures passes.

<a id="r69"></a>

### R69. SpinLock::wf equals its closed type invariant, and lock/try_lock (which hold &self) never export it, so a wrapper cannot re-establish wf for an existing lock; ensure self.wf() via use_type_invariant.

**How to fix** (the specification change, verified: see below):

```diff
@@ ostd/src/sync/spin.rs, from line 265 @@
     ///}.is_ok()
     /// ```
     #[verus_spec(ret =>
         ensures
             ret.constant() == self.constant(),
             I::inv(ret.constant(), ret.value(), ret.resource()),
+            self.wf(),
     )]
     pub fn lock(&self) -> SpinLockGuard<'_, T, G, I> {
         // Notice the guard must be created before acquiring the lock.
         proof!{ use_type_invariant(self);}
         proof_decl!{
             let tracked resource: SpinLockResource<T, I>;
@@ ostd/src/sync/spin.rs, from line 303 @@
     #[verus_spec(ret =>
         ensures
             ret is Some ==> {
                 &&& ret->0.constant() == self.constant()
                 &&& I::inv(ret->0.constant(), ret->0.value(), ret->0.resource())
             },
+            self.wf(),
     )]
     pub fn try_lock(&self) -> Option<SpinLockGuard<'_, T, G, I>> {
+        proof!{ use_type_invariant(self); }
         let inner_guard = G::guard();
         proof_decl!{
             let tracked mut resource: Option<SpinLockResource<T, I>> = None;
         }
         if #[verus_spec(with => Tracked(resource))] self.try_acquire_lock() {
             proof_decl! {
```

**A client that fails** (module `sync.spin`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_sync__spin__impl__5__lock_1<'a, T, G: SpinGuardian, I: ResourceInvariant<T>>(
    self_: &'a SpinLock<T, G, I>,
)
{
    let mut r = self_.lock();
    assert(self_.wf()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert(self_.wf()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 2 failing clients in 2 groups of failures pass.

## `verified_libs/bitflags/src/lib.rs`

<a id="r63"></a>

### R63. The bitflags macro's insert/set/toggle/clear/sub ensure only bits-level facts while union_spec/difference_spec/symmetric_difference_spec/empty_spec are closed, so callers outside the module cannot equate the result with the spec operation; ensure the value-level equalities (and the contains/!intersects bit facts, proved by bit_vector).

**How to fix** (the specification change, verified: see below):

```diff
@@ verified_libs/bitflags/src/lib.rs, from line 572 @@
                     Self::from_bits_unchecked_spec(self.bits() & !other.bits())
                 }
 
                 $vis fn insert(&mut self, other: Self)
                     ensures
                         final(self).bits() == (old(self).bits() | other.bits()),
+                        *final(self) == old(self).union(other),
+                        final(self).contains(other),
                         final(self).flags_spec() == Self::flags_from_bits(
                             old(self).bits() | other.bits(),
                         ),
                 {
                     *self = Self::from_bits_retain(self.bits()).union(other);
+                    proof {
+                        let a = old(self).bits();
+                        let b = other.bits();
+                        assert(((a | b) & b) == b) by (bit_vector);
+                    }
                 }
 
                 $vis fn remove(&mut self, other: Self)
                     ensures
                         *final(self) == old(self).remove_spec(other),
                         final(self).bits() == (old(self).bits() & !other.bits()),
@@ verified_libs/bitflags/src/lib.rs, from line 594 @@
                 }
 
                 /// The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
                 $vis fn toggle(&mut self, other: Self)
                     ensures
                         final(self).bits() == (old(self).bits() ^ other.bits()),
+                        *final(self) == old(self).symmetric_difference(other),
                         final(self).flags_spec() == Self::flags_from_bits(
                             old(self).bits() ^ other.bits(),
                         ),
                 {
                     *self = Self::from_bits_retain(self.bits()).symmetric_difference(other);
                 }
 
                 /// Call `insert` when `value` is `true` or `remove` when `value` is `false`.
                 $vis fn set(&mut self, other: Self, value: bool)
                     ensures
                         value ==> final(self).bits() == (old(self).bits() | other.bits()),
                         !value ==> final(self).bits() == (old(self).bits() & !other.bits()),
+                        value ==> *final(self) == old(self).union(other),
+                        !value ==> *final(self) == old(self).difference(other),
                 {
                     if value {
                         self.insert(other);
                     } else {
                         self.remove(other);
                     }
@@ verified_libs/bitflags/src/lib.rs, from line 629 @@
                 }
 
                 /// Unsets all bits in the flags.
                 $vis fn clear(&mut self)
                     ensures
                         final(self).bits() == 0,
+                        *final(self) == Self::empty(),
                         final(self).flags_spec() == Self::flags_from_bits(0),
                 {
                     *self = Self::empty();
                 }
 
                 $vis closed spec fn union_spec(self, other: Self) -> Self {
@@ verified_libs/bitflags/src/lib.rs, from line 794 @@
 
             impl core::ops::Sub for $name {
                 type Output = Self;
                 fn sub(self, other: Self) -> (r: Self)
                     ensures
                         r.bits() == (self.bits() & !other.bits()),
+                        r == self.difference(other),
+                        !r.intersects(other),
                 {
+                    proof {
+                        let a = self.bits();
+                        let b = other.bits();
+                        assert(((a & !b) & b) == (0 as $T)) by (bit_vector);
+                    }
                     self.difference(other)
                 }
             }
 
             impl vstd::std_specs::ops::NotSpecImpl for $name {
                 open spec fn obeys_not_spec() -> bool { true }
```

**A client that fails** (module `mm.page_prop`, generated by the tool; it calls the public API as a caller would, under the API's own requires):

```rust
fn claim_mm__page_prop__impl__26__clear_16(
    self_: &mut PageFlags,
)
{
    let ghost old_self_ = (*self_);
    self_.clear();
    assert((*self_) == crate::mm::page_prop::PageFlags::empty() && (*self_).is_empty()); // claim
}
```

**What goes wrong** (Verus at 8e4b202d6):

- `assertion failed`: `assert((*self_) == crate::mm::page_prop::PageFlags::empty() && (*self_).is_empty()); // claim`

With the change (and the other changes in this document), this client verifies.

**Evidence.** The change verifies on its own (the whole `ostd` crate, 0 errors); with it, 5 failing clients in 5 groups of failures pass.

## Appendix: changes that entries above build on

These changes are needed by the entries that name them; on their own they did not clear a group of failures.

<a id="fix-list-4"></a>

### list-4

LinkedList::new has no ensures, so the fields of the empty list it builds (size 0, no front/back, list_id 0) are unknown to callers; ensure them.

```diff
@@ ostd/src/mm/frame/linked_list.rs, from line 177 @@
         }
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
     /// Creates a new linked list.
-    pub const fn new() -> Self {
+    pub const fn new() -> (r: Self)
+        ensures
+            r.size == 0,
+            r.front is None,
+            r.back is None,
+            r.list_id == 0,
+    {
         Self { front: None, back: None, size: 0, list_id: 0 }
     }
 }
 
 impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Default for LinkedList<M> {
     fn default() -> Self {
```


<a id="fix-cursor-4"></a>

### cursor-4

Cursor::query changes regions only through clone_item, which keeps slots and the slot_owners domain, but ensures neither; a loop invariant keeps slots equal across the descent (push_level and cur_entry take regions shared).

```diff
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 352 @@
             old(self).invariants(*old(owner), *old(regions), *old(guards)),
             old(self).query_panic_condition(*old(owner), *old(regions)) ==> may_panic(),
         ensures
             final(self).invariants(*final(owner), *final(regions), *final(guards)),
             !old(self).query_panic_condition(*old(owner), *old(regions)),
             old(owner).in_barrier_va() ==> res is Ok,
+            final(regions).slots == old(regions).slots,
+            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
             res matches Ok(state) ==>
                 final(self).query_some_condition(*final(owner)) ==>
                 final(self).query_some_ensures(*final(owner), state),
             res matches Ok(state) ==>
                 !final(self).query_some_condition(*final(owner)) ==>
                 final(self).query_none_ensures(*final(owner), state),
@@ ostd/src/mm/page_table/cursor/mod.rs, from line 425 @@
                     },
                 forall|k: int|
                     old(regions).slots.contains_key(k) ==> #[trigger] regions.slots.contains_key(k),
                 forall|k: int|
                     old(regions).slots.contains_key(k) ==> old(regions).slots[k]
                         == #[trigger] regions.slots[k],
+                regions.slots == old(regions).slots,
             decreases self.level,
         )]
         loop {
             let cur_va = self.va;
             let level = self.level;
 
```


<a id="fix-pt6-2"></a>

### pt6-2

Entry::split_if_mapped_huge returns None at once when the entry is not a huge frame, without touching anything, but the spec keeps only owner, node and idx; it never says the PTE or parent_owner (children_perm) are unchanged, so self.wf(owner) and node_matching are lost after None. It now ensures res is None ==> PTE, owner, parent_owner, regions and guards unchanged.

```diff
@@ ostd/src/mm/page_table/node/entry.rs, from line 755 @@
                     PageTableOwner::<C>::metaregion_sound_pred(*final(regions)))
             },
             !old(owner).value().is_frame() || old(parent_owner).level() <= 1 ==> {
                 &&& res is None
                 &&& *final(owner) == *old(owner)
             },
+            res is None ==> {
+                &&& final(self).pte == old(self).pte
+                &&& *final(parent_owner) == *old(parent_owner)
+                &&& *final(regions) == *old(regions)
+                &&& *final(guards) == *old(guards)
+            },
             final(owner).inv(),
             final(owner).value().parent_level == old(owner).value().parent_level,
             final(self).idx == old(self).idx,
             old(owner).value().is_frame() && old(parent_owner).level() > 1 ==>
                 final(self).node_matching(final(owner).value(), *final(parent_owner), *final(self).node),
             final(regions).inv(),
```

