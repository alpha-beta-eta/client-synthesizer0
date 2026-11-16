// Every kind of trusted site, and what the lexer must not be fooled by:
// assume(false) in a comment, "assume(x)" and "{" in strings, '{' as a char.
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
            r == match self.ptr { 0 => 0usize, _ => 1usize },
    )]
    pub fn max_paddr(&self) -> usize {
        let s = "assume(x) { unbalanced";
        let c = '{';
        0
    }

    fn eq(&self, other: &Self) -> bool {
        proof {
            assume(self.ptr_inv());
            assume(
                other.ptr_inv()
            );
        }
        self.ptr == other.ptr
    }
}

unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static> NonNullPtr for Frame<M> {
    #[verifier::external_body]
    const ALIGN_BITS: u32 = core::mem::align_of::<MetaSlot>().trailing_zeros();

    fn into_raw(self) -> usize {
        assume(self.inv());
        self.ptr
    }
}

#[verifier::external]
unsafe impl<M: AnyFrameMeta + ?Sized> Send for Frame<M> {}

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
