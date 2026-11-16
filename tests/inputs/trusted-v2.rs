// Version 2 of trusted-v1.rs: max_paddr's ensures changed, a blank line and
// a comment added (no change), the trait renamed (NonNullPtr -> RawPtr: the
// same texts under new names), the Send impl verified (gone), and a new
// external_body (unjudged).
verus! {

/* a block comment with admit() and /* a nested one */ still in it */
pub struct Frame<M> {
    ptr: usize,
}

impl<M: AnyFrameMeta + ?Sized> Frame<M> {
    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            self.inv(),
        ensures
            r == match self.ptr { 0 => 0usize, _ => 2usize },
    )]
    pub fn max_paddr(&self) -> usize {
        let s = "assume(x) { unbalanced";
        let c = '{';
        0
    }

    fn eq(&self, other: &Self) -> bool {
        proof {
            // a new comment does not change the fingerprint
            assume(self.ptr_inv());

            assume(
                other.ptr_inv()
            );
        }
        self.ptr == other.ptr
    }

    #[verifier::external_body]
    fn acquire_fence() {}
}

unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static> RawPtr for Frame<M> {
    #[verifier::external_body]
    const ALIGN_BITS: u32 = core::mem::align_of::<MetaSlot>().trailing_zeros();

    fn into_raw(self) -> usize {
        assume(self.inv());
        self.ptr
    }
}

pub broadcast axiom fn axiom_insert(used: Set<u64>)
    ensures
        used.len() > 0,
;

pub assume_specification<A: Array, I: SliceIndex<[A::Item]>>[ SmallVec::<A>::index ](
    v: &SmallVec<A>,
    index: I,
) -> &<I as SliceIndex<[A::Item]>>::Output;

fn wait(cond: &F) {
    if cond() {
        admit();
    } else {
        admit();
    }
}

} // verus!
