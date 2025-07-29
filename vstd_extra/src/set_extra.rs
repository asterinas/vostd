use vstd::{prelude::*, set::fold::*, set_lib::*};

verus! {

/// If all elements in set `s` does not satisfy the predicate `f`, then the filtered set
/// is empty.
pub proof fn lemma_filter_all_false<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        s.all(|x: T| !f(x)),
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

/// A finite set can be separated by a predicate into two disjoiint sets.
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

/// If the length of the filtered set is equal to the length of the original set,
/// then the filtered set is equal to the original set.
pub proof fn lemma_filter_len_unchanged_implies_equal<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        s.finite(),
        s.filter(f).len() == s.len(),
    ensures
        s.filter(f) =~= s,
{
    lemma_set_separation(s, f)
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
        Set::new(|x: T| p(x)).len() == Set::new(|x: T| p(x)).filter(q).len(),
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

/// A set of sets is pairwise disjoint if all distinct sets are disjoint.
pub open spec fn pairwise_disjoint<A>(sets: Set<Set<A>>) -> bool {
    forall|s1: Set<A>, s2: Set<A>|
        #![trigger sets.contains(s1), sets.contains(s2)]
        sets.contains(s1) && sets.contains(s2) && s1 != s2 ==> s1.disjoint(s2)
}

pub open spec fn is_partition<A>(s: Set<A>, parts: Set<Set<A>>) -> bool {
    // Each part is non-empty and subset of s
    forall|part: Set<A>| #[trigger]
        parts.contains(part) ==> !part.is_empty() && part <= s
            &&
        // Parts are pairwise disjoint
        pairwise_disjoint(parts) &&
        // Union of parts is s
        s =~= parts.flatten()
}

/// If `parts` is a finite set of finite, pairwise-disjoint sets,
/// then the cardinality of the union is the sum of cardinalities.
pub proof fn lemma_flatten_cardinality_under_disjointness<A>(parts: Set<Set<A>>)
    requires
        parts.finite(),
        pairwise_disjoint(parts),
        forall|p: Set<A>| #[trigger] parts.contains(p) ==> p.finite(),
    ensures
        parts.flatten().len() == parts.fold(0nat, |acc: nat, p: Set<A>| acc + p.len()),
        parts.flatten().finite(),
    decreases parts.len(),
{
    if parts.is_empty() {
        assert(parts.flatten() =~= Set::empty());
        lemma_fold_empty(0nat, |acc: nat, p: Set<A>| acc + p.len());
    } else {
        let p = parts.choose();
        let rest = parts.remove(p);
        assert(parts =~= rest.insert(p));
        lemma_flatten_cardinality_under_disjointness(rest);
        assert(rest.flatten().len() == rest.fold(0nat, |acc: nat, p: Set<A>| acc + p.len()));
        assert(parts.flatten() =~= rest.flatten().union(p));
        assert(parts.flatten().len() == rest.flatten().len() + p.len()) by {
            lemma_set_disjoint_lens(rest.flatten(), p);
        }

        assert(parts.fold(0nat, |acc: nat, p: Set<A>| acc + p.len()) == rest.fold(
            0nat,
            |acc: nat, p: Set<A>| acc + p.len(),
        ) + p.len()) by {
            lemma_fold_insert(rest, 0nat, |acc: nat, p: Set<A>| acc + p.len(), p);
        }
    }
}

/// If `parts` is a finite set of finite, pairwise-disjoint sets, and each set has the same length `c`,
/// then the cardinality of the union is the product of the number of sets and `c`.
pub proof fn lemma_flatten_cardinality_under_disjointness_same_length<A>(parts: Set<Set<A>>, c: nat)
    requires
        parts.finite(),
        pairwise_disjoint(parts),
        parts.all(|p: Set<A>| p.finite() && p.len() == c),
    ensures
        parts.flatten().len() == parts.len() * c,
        parts.flatten().finite(),
    decreases parts.len(),
{
    if parts.is_empty() {
        assert(parts.flatten() =~= Set::empty());
    } else {
        let p = parts.choose();
        let rest = parts.remove(p);
        assert(parts =~= rest.insert(p));
        lemma_flatten_cardinality_under_disjointness_same_length(rest, c);
        assert(parts.flatten() =~= rest.flatten().union(p));
        assert(parts.flatten().len() == rest.flatten().len() + p.len()) by {
            lemma_set_disjoint_lens(rest.flatten(), p);
        }
        assert(parts.flatten().len() == (rest.len() + 1) * c) by (nonlinear_arith)
            requires
                parts.flatten().len() == rest.len() * c + c,
        ;
    }
}

} // verus!
