use vstd::prelude::*;
use crate::x86_64::mm::PAGE_SIZE_SPEC;

verus! {

pub open spec fn va_base(va: int) -> int {
    (va / PAGE_SIZE_SPEC() as int) * PAGE_SIZE_SPEC() as int
}

pub proof fn lemma_va_base_min(va: int)
    requires
        va == va_base(va),
    ensures
        forall|_va: int| #![auto] (va_base(_va) == va) ==> (va <= _va),
{
}

pub open spec fn va_is_aligned(va: int) -> bool {
    va == va_base(va)
}

pub proof fn lemma_va_base_is_aligned(va: int)
    ensures
        va_is_aligned(va_base(va)),
{
}

pub open spec fn va_belong_to_same_page(va_1: int, va_2: int) -> bool {
    va_base(va_1) == va_base(va_2)
}

pub proof fn lemma_reflexivity_va_belong_to_same_page(va_1: int, va_2: int)
    requires
        va_1 == va_2,
    ensures
        va_belong_to_same_page(va_1, va_2),
{
}

pub proof fn lemma_exchangeable_va_belong_to_same_page(va_1: int, va_2: int)
    requires
        va_belong_to_same_page(va_1, va_2),
    ensures
        va_belong_to_same_page(va_2, va_1),
{
}

pub open spec fn va_set_has_prefix(va_set: Set<int>, va: int) -> bool
    recommends
        va_set.finite(),
{
    va != va_set.to_seq().min() && va_set.contains(va)
}

pub open spec fn va_set_is_compact(va_set: Set<int>) -> bool
    recommends
        va_set.finite(),
{
    forall|va: int| #![auto] va_set_has_prefix(va_set, va) ==> { va_set.contains(va - 1) }
}

pub open spec fn va_set_is_valid(va_set: Set<int>) -> bool
    recommends
        va_set.finite(),
{
    forall|va: int| #![auto] va_set.contains(va) ==> va_set.contains(va_base(va))
}

pub open spec fn va_set_is_aligned(va_set: Set<int>) -> bool
    recommends
        va_set.finite(),
{
    &&& va_is_aligned(va_set.to_seq().min())
    &&& va_set_is_valid(va_set)
    &&& va_set_is_compact(va_set)
}

pub open spec fn va_expansion(va: int) -> Set<int> {
    Set::new(|_va: int| va_belong_to_same_page(_va, va))
}

#[verifier::external_body]
pub proof fn lemma_va_expansion_is_aligned(va: int)
    ensures
        va_set_is_aligned(va_expansion(va)),
{
}

#[verifier::external_body]
pub proof fn lemma_va_expansion_size(va: int)
    ensures
        va_expansion(va).len() == PAGE_SIZE_SPEC() as int,
{
    assert(forall|_va: int|
        #![auto]
        va_belong_to_same_page(_va, va) <==> { va_base(_va) == va_base(va) });
}

pub open spec fn va_set_expansion(va_set: Set<int>) -> Set<int>
    recommends
        va_set.finite(),
        va_set.len() > 0,
        va_set_is_compact(va_set),
{
    Set::new(|_va: int| va_set.contains(va_base(_va)))
}

pub proof fn lemma_va_set_expansion_subset(va_set: Set<int>)
    requires
        va_set.finite(),
        va_set.len() > 0,
        va_set_is_aligned(va_set),
    ensures
        va_set.subset_of(va_set_expansion(va_set)),
{
}

#[verifier::external_body]
pub proof fn lemma_va_set_expansion_size(va_set: Set<int>)
    requires
        va_set.finite(),
        va_set.len() > 0,
        va_set_is_compact(va_set),
    ensures
        va_set_expansion(va_set).len() == {
            (va_base(va_set.to_seq().max()) - va_base(va_set.to_seq().min()) + 1)
                * PAGE_SIZE_SPEC() as int
        },
{
}

} // verus!
