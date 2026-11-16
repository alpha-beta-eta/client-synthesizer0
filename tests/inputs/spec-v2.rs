impl<M: AnyFrameMeta> Frame<M> {
    /// Returns the frame's physical address.
    pub fn start_paddr(&self) -> Paddr {
        self.paddr
    }

    /// Gets the reference count of the frame.
    ///
    /// The count can change at any time.
    #[verus_spec(
        with
            Tracked(slot_own): Tracked<&MetaSlotOwner>,
        requires
            self.ptr_inv(),
            forall|i: int|
                #[trigger] slot_own.paths(i) ==> i >= 0,
        returns
            slot_own.ref_count(),
    )]
    pub fn reference_count(&self) -> u64 {
        let refcnt = self.slot().ref_count.load();
        refcnt
    }

    pub fn size(&self) -> usize
        ensures
            res == PAGE_SIZE,
    {
        PAGE_SIZE
    }
}
