//! Extra properties of [`vstd::set::Set`](https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html).
use vstd::{iset::fold::*, prelude::*, set::fold::*, set_lib::*};

verus! {

/// A finite `Set<int>` cannot contain every integer: there always exists
/// an `int` outside the set. Used to prove the freshness axioms.
pub proof fn lemma_finite_int_set_has_unused(s: Set<int>)
    ensures
        exists|id: int| !s.contains(id),
{
    let n = s.len() as int;
    vstd::set_lib::lemma_int_range(0, n + 1);
    if forall|i: int| 0 <= i < n + 1 ==> s.contains(i) {
        assert(Set::range(0, n + 1).subset_of(s)) by {
            assert forall|i: int| Set::<int>::range(0, n + 1).contains(i) implies s.contains(
                i,
            ) by {}
        }
        vstd::set_lib::lemma_len_subset(Set::range(0, n + 1), s);
        assert(false);
    }
}

/// If all elements in set `s` does not satisfy the predicate `f`, then the filtered set
/// is empty.
pub proof fn lemma_filter_all_false<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        s.all(|x: T| !f(x)),
    ensures
        s.filter(f).is_empty(),
{
}

/// If `x` satisfies the predicate `f` and set `s` does not contain `x`, then first inserting `x` into
/// the set `s` and then applying the filter is equivalent to applying the filter first and then
/// inserting `x` into the result.
pub proof fn lemma_insert_filter_true<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        !s.contains(x),
        f(x),
    ensures
        s.insert(x).filter(f) == s.filter(f).insert(x),
{
}

/// If `x` does not satisfy the predicate `f` and set `s` does not contain `x`, then first inserting `x` into
/// the set `s` and then applying the filter is equivalent to directly applying the filter to the original set `s`.
pub proof fn lemma_insert_filter_false<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        !s.contains(x),
        !f(x),
    ensures
        s.insert(x).filter(f) == s.filter(f),
{
}

/// If `x` satisfies the predicate `f` and set `s` contains `x`, then first removing `x` from
/// the set `s` and then applying the filter is equivalent to applying the filter first and then
/// removing `x` from the result.
pub proof fn lemma_remove_filter_true<T>(s: Set<T>, f: spec_fn(T) -> bool, x: T)
    requires
        s.contains(x),
        f(x),
    ensures
        s.remove(x).filter(f) == s.filter(f).remove(x),
{
}

/// The length of a set of natural numbers between `l` and `r` equals `r - l`.
pub proof fn lemma_nat_range_finite(l: nat, r: nat)
    requires
        l <= r,
    ensures
        Set::<nat>::range(l, r).len() == (r - l) as nat,
{
    broadcast use vstd::set_lib::range_set_properties;

}

/// A finite set can be separated by a predicate into two disjoint sets.
pub proof fn lemma_set_separation<T>(s: Set<T>, f: spec_fn(T) -> bool)
    ensures
        #![trigger s.filter(f)]
        s.filter(f).disjoint(s.filter(|x| !f(x))),
        s == s.filter(f) + s.filter(|x| !f(x)),
        s.filter(f).len() + s.filter(|x| !f(x)).len() == s.len(),
    decreases s.len(),
{
    if s.is_empty() {
        assert(s.filter(f) == Set::<T>::empty());
        assert(s.filter(|x| !f(x)) == Set::<T>::empty());
    } else {
        let x = s.choose();
        lemma_set_separation(s.remove(x), f);
        if f(x) {
            assert(s.filter(f) == s.remove(x).filter(f).insert(x));
            assert(s.filter(|x| !f(x)) == s.remove(x).filter(|x| !f(x)));
        } else {
            assert(s.filter(f) == s.remove(x).filter(f));
            assert(s.filter(|x| !f(x)) == s.remove(x).filter(|x| !f(x)).insert(x));
        }
    }
}

/// If the length of the filtered set is equal to the length of the original set,
/// then the filtered set is equal to the original set.
pub proof fn lemma_filter_len_unchanged_implies_equal<T>(s: Set<T>, f: spec_fn(T) -> bool)
    requires
        s.filter(f).len() == s.len(),
    ensures
        s.filter(f) == s,
{
    lemma_set_separation(s, f)
}

/// If no element in set `s` fails the predicate `q`, then all elements in `s` satisfy `q`.
pub proof fn lemma_empty_bad_set_implies_forall<T>(s: Set<T>, q: spec_fn(T) -> bool)
    requires
        s.filter(|x| !q(x)).is_empty(),
    ensures
        forall|x: T| #[trigger] s.contains(x) ==> q(x),
{
    assert forall|x: T| #[trigger] s.contains(x) implies q(x) by {
        if !q(x) {
            assert(s.filter(|x| !q(x)).contains(x));
        };
    }
}

/// If all elements in the set `s` satisfy predicate `q` (i.e., the filtered set has the same length),
/// then every element of `s` satisfies `q`.
pub proof fn lemma_full_good_set_implies_forall<T>(s: Set<T>, q: spec_fn(T) -> bool)
    requires
        s.len() == s.filter(q).len(),
    ensures
        forall|x: T| #[trigger] s.contains(x) ==> q(x),
{
    lemma_set_separation(s, q);
    assert forall|x: T| #[trigger] s.contains(x) implies q(x) by {
        if !q(x) {
            assert(s.filter(|x| !q(x)).contains(x));
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
        s == parts.flatten()
}

/// If `parts` is a finite set of finite, pairwise-disjoint sets,
/// then the cardinality of the union is the sum of cardinalities.
pub proof fn lemma_flatten_cardinality_under_disjointness<A>(parts: Set<Set<A>>)
    requires
        pairwise_disjoint(parts),
    ensures
        parts.flatten().len() == parts.fold(0nat, |acc: nat, p: Set<A>| acc + p.len()),
    decreases parts.len(),
{
    if parts.is_empty() {
        assert(parts.flatten() == Set::<A>::empty());
        assert(parts.to_iset() == ISet::empty());
        lemma_fold_empty(0nat, |acc: nat, p: Set<A>| acc + p.len());
    } else {
        let p = parts.choose();
        let rest = parts.remove(p);
        assert(parts == rest.insert(p));
        lemma_flatten_cardinality_under_disjointness(rest);
        assert(rest.flatten().len() == rest.fold(0nat, |acc: nat, p: Set<A>| acc + p.len()));
        assert(parts.flatten() == rest.flatten().union(p));
        assert(parts.flatten().len() == rest.flatten().len() + p.len()) by {
            lemma_set_disjoint_lens(rest.flatten(), p);
        }
        assert(parts.to_iset() == rest.to_iset().insert(p));
        lemma_fold_insert(rest.to_iset(), 0nat, |acc: nat, p: Set<A>| acc + p.len(), p);
    }
}

/// If `parts` is a finite set of finite, pairwise-disjoint sets, and each set has the same length `c`,
/// then the cardinality of the union is the product of the number of sets and `c`.
pub proof fn lemma_flatten_cardinality_under_disjointness_same_length<A>(parts: Set<Set<A>>, c: nat)
    requires
        pairwise_disjoint(parts),
        parts.all(|p: Set<A>| p.len() == c),
    ensures
        parts.flatten().len() == parts.len() * c,
    decreases parts.len(),
{
    if parts.is_empty() {
        assert(parts.flatten() == Set::<A>::empty());
    } else {
        let p = parts.choose();
        let rest = parts.remove(p);
        assert(parts == rest.insert(p));
        lemma_flatten_cardinality_under_disjointness_same_length(rest, c);
        assert(parts.flatten() == rest.flatten().union(p));
        assert(parts.flatten().len() == rest.flatten().len() + p.len()) by {
            lemma_set_disjoint_lens(rest.flatten(), p);
        }
        assert(parts.flatten().len() == (rest.len() + 1) * c) by (nonlinear_arith)
            requires
                parts.flatten().len() == rest.len() * c + c,
        ;
    }
}

pub open spec fn set_prop_mutual_exclusion<A>(s: Set<A>, f: spec_fn(A) -> bool) -> bool {
    forall|x: A, y: A| #[trigger]
        s.contains(x) && #[trigger] s.contains(y) && x != y ==> !(f(x) && f(y))
}

proof fn lemma_set_prop_mutual_exclusion_internal<A>(s: Set<A>, f: spec_fn(A) -> bool)
    requires
        set_prop_mutual_exclusion(s, f),
    ensures
        s.filter(f).len() <= 1,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.filter(f).is_empty());
    } else {
        let x = s.choose();
        lemma_set_prop_mutual_exclusion_internal(s.remove(x), f);
        if s.remove(x).filter(f).len() == 0 {
            if f(x) {
                assert(s.filter(f) == s.remove(x).filter(f).insert(x));
            } else {
                assert(s.filter(f) == s.remove(x).filter(f));
            }
        } else {
            let a = s.remove(x).filter(f).choose();
            assert(s.remove(x).filter(f).contains(a));
            assert(s.filter(f) == s.remove(x).filter(f));
        }
    }
}

pub proof fn lemma_set_prop_mutual_exclusion<A>(s: Set<A>, f: spec_fn(A) -> bool)
    ensures
        set_prop_mutual_exclusion(s, f) <==> s.filter(f).len() <= 1,
{
    if set_prop_mutual_exclusion(s, f) {
        lemma_set_prop_mutual_exclusion_internal(s, f);
    }
    if s.filter(f).len() <= 1 {
        assert forall|x: A, y: A| #[trigger]
            s.contains(x) && #[trigger] s.contains(y) && x != y implies !(f(x) && f(y)) by {
            if f(x) && f(y) {
                assert(s.filter(f).contains(x));
                assert(s.filter(f).contains(y));
                if s.filter(f).len() == 1 {
                    Set::lemma_is_singleton(s.filter(f));
                }
            }
        };
    }
}

} // verus!
