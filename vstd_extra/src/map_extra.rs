use vstd::prelude::*;
use vstd::{map::*};

verus! {

/// The length of inserting a key-value pair `(k,v)` into a map `m` depends on whether
/// the key `k` already exists in the map. If it does, the length remains the same;
/// if it doesn't, the length increases by 1.
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

/// The length of removing a key-value pair `(k,v)` from a map `m` depends on whether
/// the key `k` exists in the map. If it does, the length decreases by 1; if it doesn't,
/// the length remains the same.
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

/// Filters a map based on a predicate function applied to its values.
pub open spec fn value_filter<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool) -> Map<K, V> {
    m.restrict(m.dom().filter(|s| f(m[s])))
}

/// The result of value-filtering a finite map is also finite.
pub proof fn lemma_value_filter_finite<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        m.dom().finite(),
    ensures
        value_filter(m, f).dom().finite(),
{
    assert(value_filter(m, f).dom() =~= m.dom().filter(|s| f(m[s])));
    m.dom().lemma_len_filter(|s| f(m[s]));
}

/// If a key `k` exists in the map `m`, then whether the value-filtered map
/// contains the key depends on whether the predicate function `f` is true for
/// its value.
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

/// If the predicate function `f` is true for all values in the map `m`, then
/// the value-filtered map is equal to the original map.
pub proof fn lemma_value_filter_all_true<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        forall|k: K| m.contains_key(k) ==> #[trigger] f(m[k]),
    ensures
        value_filter(m, f) =~= m,
{
}

/// If the predicate function `f` is false for all values in the map `m`, then
/// the value-filtered map is empty.
pub proof fn lemma_value_filter_all_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        forall|k: K| m.contains_key(k) ==> !#[trigger] f(m[k]),
    ensures
        value_filter(m, f).is_empty(),
{
}

/// If the predicate function `f` is true for `m[k]`, then fist removing `k`
/// from the map `m` and then applying the value filter is equivalent to
/// applying the value filter first and then removing `k` from the result.
pub proof fn lemma_remove_value_filter_true<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        f(m[k]),
    ensures
        value_filter(m.remove(k), f) =~= value_filter(m, f).remove(k),
{
}

/// If the predicate function `f` is false for `m[k]`, then first removing `k`
/// from the map `m` and then applying the value filter is equivalent to
/// directly applying the value filter to the original map `m`.
pub proof fn lemma_remove_value_filter_false<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        !f(m[k]),
    ensures
        value_filter(m.remove(k), f) =~= value_filter(m, f),
{
}

/// If the predicate function `f` is true for the newly inserted value `v`,
/// then inserting `(k,v)` into the map `m` and then applying the value filter
/// is equivalent to applying the value filter to the original map `m` and
/// then inserting `(k,v)` into the result.
pub proof fn lemma_insert_value_filter_true<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K, v: V)
    requires
        f(v),
    ensures
        value_filter(m.insert(k, v), f) =~= value_filter(m, f).insert(k, v),
{
}

/// If the predicate function `f` is false for the newly inserted value `v`,
/// then inserting `(k,v)` into the map `m` and then applying the value filter
/// is equivalent to applying the value filter to the original map `m` and
/// then removing `k` from the result (if 'k' exists in 'm') or leaving it unchanged
/// (if it doesn't).
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

/// The length of the value-filtered map after inserting `(k,v)` into `m`
/// is equal to the length of the value-filtered map for the original map `m`
/// if `k` exists in `m`, and `m[k]` and `v` both satisfy/un-satisfy the predicate
/// function `f`.
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

/// The length of the value-filtered map after inserting `(k,v)` into `m`
/// is equal to the length of the value-filtered map for the original map `m`
/// plus one if `m[k]` does not satisfy `f` but `v` does, and minus one if
/// `m[k]` satisfies `f` but `v` does not.
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
