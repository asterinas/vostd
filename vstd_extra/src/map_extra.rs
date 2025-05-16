use vstd::prelude::*;

verus! {

pub open spec fn value_filter<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool) -> Map<K, V> {
    m.restrict(m.dom().filter(|s| f(m[s])))
}

pub proof fn lemma_value_filter_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        forall|k: K| m.contains_key(k) ==> !#[trigger] f(m[k]),
    ensures
        value_filter(m, f).is_empty(),
{
}

pub proof fn lemma_remove_value_filter_true<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        m.contains_key(k),
        f(m[k]),
    ensures
        value_filter(m.remove(k), f) =~= value_filter(m, f).remove(k),
{
}

pub proof fn lemma_remove_value_filter_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        m.contains_key(k),
        !f(m[k]),
    ensures
        value_filter(m.remove(k), f) =~= value_filter(m, f),
{
}

pub proof fn lemma_insert_value_filter_true<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K, v: V)
    requires
        !m.contains_key(k),
        f(v),
    ensures
        value_filter(m.insert(k, v), f) =~= value_filter(m, f).insert(k, v),
{
}

pub proof fn lemma_insert_value_filter_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K, v: V)
    requires
        !m.contains_key(k),
        !f(v),
    ensures
        value_filter(m.insert(k, v), f) =~= value_filter(m, f),
{
}

} // verus!
