use vstd::prelude::*;
use vstd::seq::*;

verus! {

#[verifier::external_body]
pub proof fn seq_tracked_new<T>(len: nat, f: impl Fn(int) -> T) -> (tracked res: Seq<T>)
    ensures
        res == Seq::<T>::new(len, f),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn seq_tracked_update<T>(s: Seq<T>, idx: int, x: T) -> (tracked res: Seq<T>)
    requires
        0 <= idx < s.len(),
    ensures
        res == s.update(idx, x),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn seq_tracked_add<T>(s1: Seq<T>, s2: Seq<T>) -> (tracked res: Seq<T>)
    ensures
        res == s1.add(s2),
{
    unimplemented!();
}

pub proof fn lemma_seq_add_head_back<T>(s: Seq<T>)
    requires
        s.len() > 0,
    ensures
        s =~= seq![s[0]].add(s.drop_first()),
{
}

pub proof fn lemma_seq_push_head<T>(s: Seq<T>, hd: T)
    ensures
        seq![hd].add(s) =~= s.reverse().push(hd).reverse(),
{
}

pub proof fn lemma_seq_drop_pushed_head<T>(s: Seq<T>, hd: T)
    ensures
        seq![hd].add(s).drop_first() =~= s,
{
}

pub proof fn lemma_seq_push_head_take_head<T>(s: Seq<T>, hd: T)
    ensures
        seq![hd].add(s)[0] == hd,
{
}

} // verus!
verus! {

/// The result of pushing elemrnt 'needle' into the sequence 's' contains 'needle'.
pub proof fn lemma_push_contains_same<T>(s: Seq<T>, needle: T)
    ensures
        #[trigger] s.push(needle).contains(needle),
{
    assert(s.push(needle).last() == needle);
}

/// If element 'needle' is different from 'new_elem', then whether the sequence 's' contains 'needle'
/// after pushing 'new_elem' depends on whether 's' contains 'needle' before the push.
pub proof fn lemma_push_contains_different<T>(s: Seq<T>, new_elem: T, needle: T)
    requires
        new_elem != needle,
    ensures
        #[trigger] s.push(new_elem).contains(needle) == s.contains(needle),
{
    if (s.contains(needle)) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == needle;
        axiom_seq_push_index_different(s, needle, i);
        assert(0 <= i < s.push(new_elem).len() && s.push(new_elem)[i] == needle);
    }
}

/// If the last element of the sequence 's' is different from 'needle', then whether the sequence
/// 's' contains 'needle' after dropping the last element depends on whether 's' contains 'needle'
/// before the drop.
pub proof fn lemma_drop_last_contains_different<T>(s: Seq<T>, needle: T)
    requires
        s.len() > 0,
        s.last() != needle,
    ensures
        #[trigger] s.drop_last().contains(needle) == s.contains(needle),
{
    if (s.contains(needle)) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == needle;
        assert(0 <= i < s.drop_last().len() && s.drop_last()[i] == needle);
    }
}

} // verus!
verus! {

/// Returns true if predicate `f(i,seq[i])` holds for all indices 'i'.
pub open spec fn forall_seq<T>(seq: Seq<T>, f: spec_fn(int, T) -> bool) -> bool {
    forall|i| #![trigger seq[i]] 0 <= i < seq.len() ==> f(i, seq[i])
}

pub broadcast group group_forall_seq_lemmas {
    lemma_forall_seq_push,
    lemma_seq_all_push,
    lemma_forall_seq_drop_last,
    lemma_seq_all_drop_last,
    lemma_seq_all_add,
    lemma_seq_all_index,
}

/// Index `i` of the sequence `s` satisfies `f(i,s[i])` if `forall_seq(s,f)` holds.
pub proof fn lemma_forall_seq_index<T>(s: Seq<T>, f: spec_fn(int, T) -> bool, i: int)
    requires
        forall_seq(s, f),
        0 <= i < s.len(),
    ensures
        f(i, s[i]),
{
}

/// Index `i` of the sequence `s` satisfies `f(s[i])` if `s.all(f)` holds.
/// This proof is required due to the change of trigger by replacing the original `forall_seq_values` with `Seq::all`.
pub broadcast proof fn lemma_seq_all_index<T>(s: Seq<T>, f: spec_fn(T) -> bool, i: int)
    requires
        0 <= i < s.len(),
        #[trigger] s.all(f),
    ensures
        f(#[trigger] (s[i])),
{
}

/// `forall_seq(s.push(v),f)` is equivalent to `forall_seq(s,f)` and `f(s.len(),v)`.
pub broadcast proof fn lemma_forall_seq_push<T>(s: Seq<T>, f: spec_fn(int, T) -> bool, v: T)
    ensures
        forall_seq(s, f) && f(s.len() as int, v) <==> #[trigger] forall_seq(s.push(v), f),
{
    if (forall_seq(s.push(v), f)) {
        assert forall|i| 0 <= i < s.len() implies f(i, s[i]) by {
            assert(s[i] === s.push(v)[i]);
        }
        assert(s.push(v)[s.len() as int] == v);
    }
}

/// s.push(v).all(f)` is equivalent to `s.all(f)` and `f(v)`.
pub broadcast proof fn lemma_seq_all_push<T>(s: Seq<T>, f: spec_fn(T) -> bool, v: T)
    ensures
        #[trigger] s.push(v).all(f) <==> s.all(f) && f(v),
{
    if (s.push(v).all(f)) {
        assert forall|i| 0 <= i < s.len() implies f(s[i]) by {
            assert(s[i] === s.push(v)[i]);
        }
        assert(s.push(v)[s.len() as int] == v);
    }
}

/// `forall_seq(s,f)` is equivalent to `forall_seq(s.drop_last(),f)` and `f(s.len() as int - 1, s.last())`.
pub broadcast proof fn lemma_forall_seq_drop_last<T>(s: Seq<T>, f: spec_fn(int, T) -> bool)
    requires
        s.len() > 0,
    ensures
        forall_seq(s, f) <==> #[trigger] forall_seq(s.drop_last(), f) && f(
            s.len() as int - 1,
            s.last(),
        ),
{
    assert(s == s.drop_last().push(s.last()));
}

/// `s.all(f)` is equivalent to `s.drop_last().all(f)` and `f(s.last())`.
pub broadcast proof fn lemma_seq_all_drop_last<T>(s: Seq<T>, f: spec_fn(T) -> bool)
    requires
        s.len() > 0,
    ensures
        s.all(f) <==> #[trigger] s.drop_last().all(f) && f(s.last()),
{
    assert(s == s.drop_last().push(s.last()));
}

pub broadcast proof fn lemma_seq_all_add<T>(s1: Seq<T>, s2: Seq<T>, f: spec_fn(T) -> bool)
    ensures
        s1.all(f) && s2.all(f) <==> #[trigger] (s1 + s2).all(f),
    decreases s2.len(),
// Induction proof on the length of s2

{
    if s2.len() == 0 {
        assert(s1 + s2 == s1);
    } else {
        // Induction step: assume the lemma holds for s2.drop_last() and show that s2==s2.drop_last().push(s2.last()).
        lemma_seq_all_add(s1, s2.drop_last(), f);
        if s1.all(f) && s2.all(f) {
            assert((s1 + s2).all(f));
        }
        if (s1 + s2).all(f) {
            assert((s1 + s2).drop_last() == s1 + s2.drop_last());
            assert(s2 == s2.drop_last().push(s2.last()));
            assert((s1 + s2).last() == s2.last());
        }
    }
}

/// If `source1` and `source2` are prefixes of `child`, then either `source1` is equal to `source2` or
/// one of them is a prefix of the other.
pub proof fn lemma_prefix_of_common_sequence(source1: Seq<nat>, source2: Seq<nat>, child: Seq<nat>)
    requires
        source1.is_prefix_of(child),
        source2.is_prefix_of(child),
    ensures
        source1 == source2 || source1.len() < source2.len() && source1.is_prefix_of(source2)
            || source2.len() < source1.len() && source2.is_prefix_of(source1),
{
}

} // verus!
