//! Additional specifications for mutable [`BTreeMap`] operations not covered by vstd.
use alloc::{
    alloc::Allocator,
    collections::{BTreeMap, btree_map::CursorMut},
};
use core::{borrow::Borrow, ops::Bound};
use vstd::{laws_cmp::obeys_cmp, prelude::*, std_specs::btree::contains_borrowed_key};

verus! {

/// Verus declaration for Rust's mutable B-tree cursor type.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
pub struct ExCursorMut<'a, K: 'a, V: 'a, A>(CursorMut<'a, K, V, A>);

/// Additional ghost state used to remember an excluded lower bound.
pub trait CursorMutAdditionalSpecFns<Key> {
    spec fn lower_excluded_bound(&self) -> Option<Key>;
}

impl<'a, Key, Value, A> CursorMutAdditionalSpecFns<Key> for CursorMut<'a, Key, Value, A> {
    uninterp spec fn lower_excluded_bound(&self) -> Option<Key>;
}

/// Converts a borrowed lookup key back to the stored key type when the borrow model permits it.
pub uninterp spec fn borrowed_key_as_stored<Key, Q: ?Sized>(key: &Q) -> Option<Key>;

/// Interpretation of [`borrowed_key_as_stored`] when both key types are equal.
pub broadcast axiom fn axiom_deref_key_as_stored<Key>(key: &Key)
    ensures
        #[trigger] borrowed_key_as_stored::<Key, Key>(key) == Some(*key),
;

/// Relates a map before and after mutating the value selected by a borrowed key.
pub uninterp spec fn borrowed_key_mutated<Key, Value, Q: ?Sized>(
    old_map: Map<Key, Value>,
    new_map: Map<Key, Value>,
    key: &Q,
    old_value: Value,
    new_value: Value,
) -> bool;

/// Interpretation of [`borrowed_key_mutated`] when the borrowed and stored key types are equal.
pub broadcast axiom fn axiom_deref_key_mutated<Key, Value>(
    old_map: Map<Key, Value>,
    new_map: Map<Key, Value>,
    key: &Key,
    old_value: Value,
    new_value: Value,
)
    ensures
        #[trigger] borrowed_key_mutated::<Key, Value, Key>(
            old_map,
            new_map,
            key,
            old_value,
            new_value,
        ) <==> {
            &&& old_map.contains_key(*key)
            &&& old_map[*key] == old_value
            &&& new_map == old_map.insert(*key, new_value)
        },
;

/// Specification for [`BTreeMap::get_mut`].
pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::get_mut::<Q> ](
    map: &'a mut BTreeMap<Key, Value, A>,
    key: &Q,
) -> (result: Option<&'a mut Value>)
    ensures
        obeys_cmp::<Key>() ==> match result {
            Some(value) => borrowed_key_mutated(old(map)@, final(map)@, key, *value, *final(value)),
            None => !contains_borrowed_key(old(map)@, key) && final(map)@ == old(map)@,
        },
;

/// Specification for [`BTreeMap::lower_bound_mut`].
///
/// This deliberately over-approximates the cursor position until vstd exposes a reusable ordered
/// cursor model. It still provides a sound verified boundary for callers that do not rely on the
/// selected key in their postconditions.
pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::lower_bound_mut::<Q> ](
    map: &'a mut BTreeMap<Key, Value, A>,
    bound: Bound<&Q>,
) -> (cursor: CursorMut<'a, Key, Value, A>)
    ensures
        final(map)@.dom() == old(map)@.dom(),
        cursor.lower_excluded_bound() == match bound {
            Bound::Excluded(key) => borrowed_key_as_stored(key),
            _ => None,
        },
;

/// Specification for [`BTreeMap::upper_bound_mut`]. See [`BTreeMap::lower_bound_mut`].
pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::upper_bound_mut::<Q> ](
    map: &'a mut BTreeMap<Key, Value, A>,
    bound: Bound<&Q>,
) -> (cursor: CursorMut<'a, Key, Value, A>)
    ensures
        final(map)@.dom() == old(map)@.dom(),
        cursor.lower_excluded_bound() is None,
;

/// Specification for [`CursorMut::peek_prev`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_prev ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    ensures
        final(cursor).lower_excluded_bound() == old(cursor).lower_excluded_bound(),
;

/// Specification for [`CursorMut::peek_next`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_next ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    ensures
        final(cursor).lower_excluded_bound() == old(cursor).lower_excluded_bound(),
        match result {
            Some((key, _)) => match old(cursor).lower_excluded_bound() {
                Some(bound) => *key != bound,
                None => true,
            },
            None => true,
        },
;

} // verus!
