use vstd::prelude::*;

verus! {

pub proof fn lemma_filter_false<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        forall|x: T| s.contains(x) ==> !#[trigger] f(x),
    ensures
        s.filter(f).is_empty(),
{
}

pub proof fn lemma_insert_filter_true<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        !s.contains(x),
        f(x),
    ensures
        s.insert(x).filter(f) =~= s.filter(f).insert(x),
{
}

pub proof fn lemma_insert_filter_false<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        !s.contains(x),
        !f(x),
    ensures
        s.insert(x).filter(f) =~= s.filter(f),
{
}

pub proof fn lemma_remove_filter_true<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        s.contains(x),
        f(x),
    ensures
        s.remove(x).filter(f) =~= s.filter(f).remove(x),
{
}

pub proof fn lemma_nat_range_finite(l: nat, r: nat)
    requires
        l <= r,
    ensures
        Set::new(|p: nat| l <= p < r).finite(),
        Set::new(|p: nat| l <= p < r).len() == (r - l) as nat,
    decreases r - l,
{
    if l == r {
        assert(Set::new(|p: nat| l <= p < r) =~= Set::empty());
    } else {
        lemma_nat_range_finite(l, (r - 1) as nat);
        assert(Set::new(|p| l <= p < r - 1).insert((r - 1) as nat) =~= Set::new(|p| l <= p < r));
    }
}

} // verus!
