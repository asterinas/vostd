use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

broadcast use {group_seq_axioms, group_seq_lib_default};

#[verifier::external_body]
pub proof fn seq_tracked_empty<T>() -> (tracked res: Seq<T>)
    ensures
        res == Seq::<T>::empty(),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn seq_tracked_new<T>(len: nat, f: impl Fn(int) -> T) -> (tracked res: Seq<T>)
    ensures
        res == Seq::<T>::new(len, f),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn seq_tracked_push<T>(s: Seq<T>, x: T) -> (tracked res: Seq<T>)
    ensures
        res == s.push(x),
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

pub broadcast proof fn lemma_seq_add_head_back<T>(s: Seq<T>)
    requires
        s.len() > 0,
    ensures
        s =~= #[trigger] seq![s[0]].add(s.drop_first()),
{
}

pub broadcast proof fn lemma_seq_push_head<T>(s: Seq<T>, hd: T)
    ensures
        #[trigger] seq![hd].add(s) =~= #[trigger] s.reverse().push(hd).reverse(),
{
}

pub broadcast proof fn lemma_seq_drop_pushed_head<T>(s: Seq<T>, hd: T)
    ensures
        #[trigger] seq![hd].add(s).drop_first() =~= s,
{
}

pub broadcast proof fn lemma_seq_push_head_take_head<T>(s: Seq<T>, hd: T)
    ensures
        #[trigger] seq![hd].add(s)[0] == hd,
{
}

pub broadcast group group_seq_extra_lemmas {
    lemma_seq_add_head_back,
    lemma_seq_push_head,
    lemma_seq_drop_pushed_head,
    lemma_seq_push_head_take_head,
}

} // verus!
verus! {

pub proof fn lemma_push_contains_same<T>(s: Seq<T>, needle: T)
    ensures
        #[trigger] s.push(needle).contains(needle),
{
    assert(s.push(needle).last() == needle);
}

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

} // verus!
