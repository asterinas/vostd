use vstd::prelude::*;
use vstd::{map::*};

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

pub proof fn lemma_map_remove_len<K, V>(m: Map<K, V>, k: K)
    requires
        m.dom().finite(),
    ensures
        m.len() == #[trigger] m.remove(k).len() + (if m.contains_key(k) {
            1
        } else {
            0int
        }),
{
    axiom_map_remove_domain(m, k)
}

pub open spec fn value_filter<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool) -> Map<K, V> {
    m.restrict(m.dom().filter(|s| f(m[s])))
}

pub proof fn lemma_value_filter_finite<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        m.dom().finite(),
    ensures
        value_filter(m, f).dom().finite(),
{
    assert(value_filter(m, f).dom() =~= m.dom().filter(|s| f(m[s])));
    m.dom().lemma_len_filter(|s| f(m[s]));
}

pub proof fn lemma_value_filter_contains<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        m.contains_key(k),
    ensures
        if f(m[k]) {
            value_filter(m, f).contains_key(k)
        } else {
            !value_filter(m, f).contains_key(k)
        },
{
}

pub proof fn lemma_value_filter_all_true<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        forall|k: K| m.contains_key(k) ==> #[trigger] f(m[k]),
    ensures
        value_filter(m, f) =~= m,
{
}

pub proof fn lemma_value_filter_all_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
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
        !f(v),
    ensures
        value_filter(m.insert(k, v), f) =~= if m.contains_key(k) {
            value_filter(m, f).remove(k)
        } else {
            value_filter(m, f)
        },
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
    lemma_value_filter_finite(m, f);
    if f(v) {
        lemma_insert_value_filter_true(m, f, k, v);
        lemma_map_insert_len(value_filter(m, f), k, v);
    } else {
        lemma_insert_value_filter_false(m, f, k, v);
        lemma_map_remove_len(value_filter(m, f), k);
    }
}

pub proof fn lemma_insert_value_filter_different_len<K, V>(
    m: Map<K, V>,
    f: spec_fn(V) -> bool,
    k: K,
    v: V,
)
    requires
        m.dom().finite(),
        m.contains_key(k),
        f(m[k]) != f(v),
    ensures
        value_filter(m.insert(k, v), f).len() == value_filter(m, f).len() + if f(v) {
            1
        } else {
            -1
        },
{
    lemma_value_filter_finite(m, f);
    if (f(v)) {
        lemma_insert_value_filter_true(m, f, k, v);
        lemma_map_insert_len(m, k, v);
    } else {
        lemma_insert_value_filter_false(m, f, k, v);
        assert(value_filter(m.insert(k, v), f).len() == value_filter(m, f).remove(k).len());
        lemma_map_remove_len(value_filter(m, f), k);
    }
}

} // verus!
