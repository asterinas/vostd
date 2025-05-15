use vstd::prelude::*;

verus! {

pub proof fn lemma_filter_false<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        forall|x: T| s.contains(x) ==> !#[trigger] f(x),
    ensures
        s.filter(f).is_empty(),
{
}

} // verus!
