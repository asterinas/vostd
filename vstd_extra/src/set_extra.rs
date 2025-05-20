use vstd::prelude::*;

verus! {

/// If all elements in set `s` does not satisfy the predicate `f`, then the filtered set
/// is empty.
pub proof fn lemma_filter_all_false<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        forall|x: T| s.contains(x) ==> !#[trigger] f(x),
    ensures
        s.filter(f).is_empty(),
{
}

/// If 'x' satisfies the predicate 'f' and set `s` does not contain 'x', then first inserting 'x' into
/// the set `s` and then applying the filter is equivalent to applying the filter first and then
/// inserting 'x' into the result.
pub proof fn lemma_insert_filter_true<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        !s.contains(x),
        f(x),
    ensures
        s.insert(x).filter(f) =~= s.filter(f).insert(x),
{
}

/// If 'x' does not satisfy the predicate 'f' and set `s` does not contain 'x', then first inserting 'x' into
/// the set `s` and then applying the filter is equivalent to directly applying the filter to the original set `s`.
pub proof fn lemma_insert_filter_false<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        !s.contains(x),
        !f(x),
    ensures
        s.insert(x).filter(f) =~= s.filter(f),
{
}

/// If 'x' satisfies the predicate 'f' and set `s` contains 'x', then first removing 'x' from
/// the set `s` and then applying the filter is equivalent to applying the filter first and then
/// removing 'x' from the result.
pub proof fn lemma_remove_filter_true<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        s.contains(x),
        f(x),
    ensures
        s.remove(x).filter(f) =~= s.filter(f).remove(x),
{
}

/// If all elements of set 's' are natural numbers between 'l' and 'r', then the set is finite.
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
