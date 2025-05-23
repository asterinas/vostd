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

/// A finite set can be separated by a predicate.
pub proof fn lemma_set_separation<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        s.finite(),
    ensures
        #![trigger s.filter(f)]
        s.filter(f).disjoint(s.filter(|x| !f(x))),
        s =~= s.filter(f) + s.filter(|x| !f(x)),
        s.filter(f).len() + s.filter(|x| !f(x)).len() == s.len(),
    decreases s.len(),
{
    if s.is_empty() {
        assert(s.filter(f) =~= Set::empty());
        assert(s.filter(|x| !f(x)) =~= Set::empty());
    } else {
        let x = s.choose();
        lemma_set_separation(s.remove(x), f);
        if f(x) {
            assert(s.filter(f) =~= s.remove(x).filter(f).insert(x));
            assert(s.filter(|x| !f(x)) =~= s.remove(x).filter(|x| !f(x)));
        } else {
            assert(s.filter(f) =~= s.remove(x).filter(f));
            assert(s.filter(|x| !f(x)) =~= s.remove(x).filter(|x| !f(x)).insert(x));
        }
    }
}

/// If no element in set `Set::new(|x: T| p(x))` satisfies the predicate `q`, then all elements
/// satisfying `p` also satisfy `q`.
pub proof fn lemma_empty_bad_set_implies_forall<T>(p: spec_fn(T) -> bool, q: spec_fn(T) -> bool)
    requires
        Set::new(|x: T| p(x)).filter(|x| !q(x)).is_empty(),
    ensures
        forall|x: T| #[trigger] p(x) ==> q(x),
{
    assert forall|x: T| #[trigger] p(x) implies q(x) by {
        if (!q(x)) {
            assert(Set::new(|x: T| p(x)).filter(|x| !q(x)).contains(x));
        };
    }
}

/// If all elements in the finite set `Set::new(|x: T| p(x))` satisfy the predicate `q`, then all elements
/// satisfying `p` also satisfy `q`.
pub proof fn lemma_full_good_set_implies_forall<T>(p: spec_fn(T) -> bool, q: spec_fn(T) -> bool)
    requires
        Set::new(|x: T| p(x)).finite(),
        Set::new(|x: T| p(x)) == Set::new(|x: T| p(x)).filter(q),
    ensures
        forall|x: T| #[trigger] p(x) ==> q(x),
{
    lemma_set_separation(Set::new(|x: T| p(x)), q);
    assert forall|x: T| #[trigger] p(x) implies q(x) by {
        if (!q(x)) {
            assert(Set::new(|x: T| p(x)).filter(|x| !q(x)).contains(x));
        };
    }
}

} // verus!
