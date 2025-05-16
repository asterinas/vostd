use vstd::prelude::*;
use vstd::map::*;

verus! {

pub proof fn lemma_map_insert_len<K, V>(m: Map<K, V>, k: K, v: V)
    requires
        m.dom().finite(),
    ensures
        #[trigger] m.insert(k, v).len() == m.len() + (if m.contains_key(k) {
            0int
        } else {
            1
        }),
{
    axiom_map_insert_domain(m, k, v)
}

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
        f(m[k]),
    ensures
        value_filter(m.remove(k), f) =~= value_filter(m, f).remove(k),
{
}

pub proof fn lemma_remove_value_filter_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        !f(m[k]),
    ensures
        value_filter(m.remove(k), f) =~= value_filter(m, f),
{
}

pub proof fn lemma_insert_value_filter_true<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K, v: V)
    requires
        f(v),
    ensures
        value_filter(m.insert(k, v), f) =~= value_filter(m, f).insert(k, v),
{
}

pub proof fn lemma_insert_value_filter_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K, v: V)
    requires
        !m.contains_key(k) || !f(m[k]),
        !f(v),
    ensures
        value_filter(m.insert(k, v), f) =~= value_filter(m, f),
{
}

pub proof fn lemma_insert_value_filter_same_len<K, V>(
    m: Map<K, V>,
    f: spec_fn(V) -> bool,
    k: K,
    v: V,
)
    requires
        m.dom().finite(),
        m.contains_key(k),
        f(m[k]) == f(v),
    ensures
        value_filter(m.insert(k, v), f).len() == value_filter(m, f).len(),
{
    if f(v) {
        lemma_map_insert_len(m, k, v);
    } else {
        lemma_insert_value_filter_false(m, f, k, v)
    }
}

} // verus!
