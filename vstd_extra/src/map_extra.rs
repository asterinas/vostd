use vstd::prelude::*;
use vstd::{set::*, map::*};

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

pub open spec fn value_filter_choose<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool) -> K {
    choose|k: K| value_filter(m, f).contains_key(k)
}

pub broadcast group group_value_filter_lemmas {
    lemma_value_filter_finite,
    lemma_value_filter_choose,
    lemma_insert_value_filter_same_len,
    lemma_insert_value_filter_different_len,
}

/// The result of value-filtering a finite map is also finite.
pub broadcast proof fn lemma_value_filter_finite<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        m.dom().finite(),
    ensures
        #[trigger] value_filter(m, f).dom().finite(),
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
pub broadcast proof fn lemma_insert_value_filter_same_len<K, V>(
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
        #[trigger] value_filter(m.insert(k, v), f).len() == value_filter(m, f).len(),
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
pub broadcast proof fn lemma_insert_value_filter_different_len<K, V>(
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
        #[trigger] value_filter(m.insert(k, v), f).len() == value_filter(m, f).len() + if f(v) {
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

pub proof fn lemma_value_filter_contains_key<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        value_filter(m, f).contains_key(k),
    ensures
        m.contains_key(k),
{
}

pub broadcast proof fn lemma_value_filter_choose<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool)
    requires
        value_filter(m, f).len() != 0,
    ensures
        value_filter(m, f).contains_key(#[trigger] value_filter_choose(m, f)),
        f(m[value_filter_choose(m, f)]),
{
    if value_filter(m, f).dom().finite() {
        axiom_set_choose_len(value_filter(m, f).dom());
    } else {
        axiom_set_choose_finite(value_filter(m, f).dom());
    }
}

} // verus!
verus! {

/// Returns true if predicate `f(k,v)` holds for all `(k,v)` in `map`.
pub open spec fn forall_map<K, V>(map: Map<K, V>, f: spec_fn(K, V) -> bool) -> bool {
    forall|k| #[trigger] map.contains_key(k) ==> f(k, map[k])
}

/// Returns true if predicate `f(v)` holds for all values in `map`.
pub open spec fn forall_map_values<K, V>(map: Map<K, V>, f: spec_fn(V) -> bool) -> bool {
    forall|k| #[trigger] map.contains_key(k) ==> f(map[k])
}

pub broadcast group group_forall_map_lemmas {
    lemma_forall_map_insert,
    lemma_forall_map_values_insert,
    lemma_forall_map_remove,
    lemma_forall_map_values_remove,
}

/// For any key in the map, `f(k, map[k])` holds if `forall_map(map, f)` holds.
pub proof fn lemma_forall_map_entry<K, V>(m: Map<K, V>, f: spec_fn(K, V) -> bool, k: K)
    requires
        forall_map(m, f),
        m.contains_key(k),
    ensures
        f(k, m[k]),
{
}

/// For any key in the map, `f(map[k])` holds if `forall_map_values(map, f)` holds.
pub proof fn lemma_forall_map_values_entry<K, V>(m: Map<K, V>, f: spec_fn(V) -> bool, k: K)
    requires
        forall_map_values(m, f),
        m.contains_key(k),
    ensures
        f(m[k]),
{
}

/// `forall_map(m.insert(k, v), f)` holds if `f(k, v)` holds and
/// `forall_map(m.remove(k),f)` (if `m` contains `k`) or `forall_map(m, f)` (if `m` does not contain `k`).
pub broadcast proof fn lemma_forall_map_insert<K, V>(
    m: Map<K, V>,
    f: spec_fn(K, V) -> bool,
    k: K,
    v: V,
)
    ensures
        #[trigger] forall_map(m.insert(k, v), f) ==> f(k, v) && if m.contains_key(k) {
            forall_map(m.remove(k), f)
        } else {
            forall_map(m, f)
        },
{
    assert(m.insert(k, v).contains_key(k));
    if m.contains_key(k) {
        assert(m.insert(k, v) =~= m.remove(k).insert(k, v));
    } else {
        assert(m.insert(k, v) =~= m.insert(k, v));
    }
    if forall_map(m.insert(k, v), f) {
        if m.contains_key(k) {
        } else {
            assert(forall|k0| #[trigger] m.contains_key(k0) ==> m.insert(k, v).contains_key(k0));
        }
    }
}

/// `forall_map_values(m.insert(k, v), f)` holds if `f(v)` holds and
/// `forall_map_values(m.remove(k),f)` (if `m` contains `k`) or `forall_map_values(m, f)` (if `m` does not contain `k`).
pub broadcast proof fn lemma_forall_map_values_insert<K, V>(
    m: Map<K, V>,
    f: spec_fn(V) -> bool,
    k: K,
    v: V,
)
    ensures
        #[trigger] forall_map_values(m.insert(k, v), f) ==> f(v) && if m.contains_key(k) {
            forall_map_values(m.remove(k), f)
        } else {
            forall_map_values(m, f)
        },
{
    assert(m.insert(k, v).contains_key(k));
    if m.contains_key(k) {
        assert(m.insert(k, v) =~= m.remove(k).insert(k, v));
    } else {
        assert(m.insert(k, v) =~= m.insert(k, v));
    }
    if forall_map_values(m.insert(k, v), f) {
        if m.contains_key(k) {
        } else {
            assert(forall|k0| #[trigger] m.contains_key(k0) ==> m.insert(k, v).contains_key(k0));
        }
    }
}

/// `forall_map(m,f)` holds if `forall_map(m.remove(k), f)` holds and
/// `f(k, m[k])` holds (if `m` contains `k`).
pub broadcast proof fn lemma_forall_map_remove<K, V>(m: Map<K, V>, f: spec_fn(K, V) -> bool, k: K)
    ensures
        forall_map(m, f) <==> #[trigger] forall_map(m.remove(k), f) && (m.contains_key(k) ==> f(
            k,
            m[k],
        )),
{
    if m.contains_key(k) {
        assert(m =~= m.remove(k).insert(k, m[k]));
    } else {
        assert(m =~= m.remove(k));
    }
}

/// `forall_map_values(m,f)` holds if `forall_map_values(m.remove(k), f)` holds and
/// `f(m[k])` holds (if `m` contains `k`).
pub broadcast proof fn lemma_forall_map_values_remove<K, V>(
    m: Map<K, V>,
    f: spec_fn(V) -> bool,
    k: K,
)
    ensures
        forall_map_values(m, f) <==> #[trigger] forall_map_values(m.remove(k), f) && (
        m.contains_key(k) ==> f(m[k])),
{
    if m.contains_key(k) {
        assert(m =~= m.remove(k).insert(k, m[k]));
    } else {
        assert(m =~= m.remove(k));
    }

}

/// Returns a new map that projects the first key of a pair `(K1, K2)`,
/// keeping the values associated with the second key `K2`.
pub open spec fn project_first_key<K1, K2, V>(m: Map<(K1, K2), V>, k1: K1) -> Map<K2, V> {
    Map::new(|k2: K2| m.contains_key((k1, k2)), |k2: K2| m[(k1, k2)])
}

/// Returns a new map that projects the second key of a pair `(K1, K2)`,
/// keeping the values associated with the first key `K1`.
pub open spec fn project_second_key<K1, K2, V>(m: Map<(K1, K2), V>, k2: K2) -> Map<K1, V> {
    Map::new(|k1: K1| m.contains_key((k1, k2)), |k1: K1| m[(k1, k2)])
}

/// A lemma showing that `project_first_key`` is sound.
/// There is no need to actually use this lemma in practice at most of the time because Verus can automatically prove it.
pub proof fn lemma_project_first_key_sound<K1, K2, V>(m: Map<(K1, K2), V>, k1: K1)
    ensures
        forall|k2: K2|
            {
                &&& #[trigger] project_first_key(m, k1).contains_key(k2) <==> m.contains_key(
                    (k1, k2),
                )
                &&& project_first_key(m, k1).contains_key(k2) ==> project_first_key(m, k1)[k2]
                    == m[(k1, k2)]
            },
{
}

/// If the value filter of the projected map is non-empty, then there exists a key `k2`
/// such that the original map contains the pair `(k1, k2)` and `m[(k1, k2)]` satisfies the predicate `f`.
pub proof fn lemma_project_first_key_value_filter_non_empty<K1, K2, V>(
    m: Map<(K1, K2), V>,
    k1: K1,
    f: spec_fn(V) -> bool,
)
    requires
        value_filter(project_first_key(m, k1), f).len() != 0,
    ensures
        exists|k2: K2| #[trigger]
            project_first_key(m, k1).contains_key(k2) && f(project_first_key(m, k1)[k2]),
{
    lemma_value_filter_choose(project_first_key(m, k1), f);
    let k2 = value_filter_choose(project_first_key(m, k1), f);
    assert(project_first_key(m, k1).contains_key(k2) && f(m[(k1, k2)]));
}

} // verus!
