use std::collections::HashMap;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
verus! {

#[verifier::loop_isolation(false)]
fn test() {
    broadcast use vstd::std_specs::hash::group_hash_axioms;

    let mut m = HashMap::<u32, i8>::new();
    assert(m@ == Map::<u32, i8>::empty());

    m.insert(3, 4);
    m.insert(6, -8);
    let m_keys = m.keys();
    assert(m_keys@.0 == 0);
    assert(m_keys@.1.to_set() =~= set![3u32, 6u32]);
    let ghost g_keys = m_keys@.1;

    let mut items = Vec::<u32>::new();
    assert(items@ =~= g_keys.take(0));

    for k in iter: m_keys
        invariant
            iter.keys == g_keys,
            g_keys.to_set() =~= set![3u32, 6u32],
            items@ == iter@,
    // iter.pos == m_keys@.0, // this also fails
    {
        assert(iter.keys.take(iter.pos).push(*k) =~= iter.keys.take(iter.pos + 1));
        items.push(*k);
    }
    assert(items@.to_set() =~= set![3u32, 6u32]) by {
        assert(g_keys.take(g_keys.len() as int) =~= g_keys);
    }
    assert(g_keys.len() == m_keys@.1.len());
    // assert(m_keys@.0 == m_keys@.1.len()); // this fails
    assert(items@.no_duplicates());
}

} // verus!
