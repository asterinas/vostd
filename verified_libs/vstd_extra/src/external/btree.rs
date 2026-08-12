//! Additional specifications for mutable [`BTreeMap`] operations not covered by vstd.
use alloc::{
    alloc::Allocator,
    collections::{BTreeMap, btree_map::CursorMut},
};
use core::{borrow::Borrow, ops::Bound};
use vstd::{
    laws_cmp::obeys_cmp,
    prelude::*,
    std_specs::btree::{borrowed_key_removed, contains_borrowed_key, maps_borrowed_key_to_value},
};

verus! {

/// Verus declaration for Rust's mutable B-tree cursor type.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
pub struct ExCursorMut<'a, K: 'a, V: 'a, A>(CursorMut<'a, K, V, A>);

/// Additional ghost state used to remember the keys matching an excluded lower bound.
pub trait CursorMutAdditionalSpecFns<Key> {
    spec fn excluded_keys(&self) -> ISet<Key>;
}

impl<'a, Key, Value, A> CursorMutAdditionalSpecFns<Key> for CursorMut<'a, Key, Value, A> {
    uninterp spec fn excluded_keys(&self) -> ISet<Key>;
}

/// Whether a borrowed lookup key's ordering agrees with the ordering of stored keys.
///
/// This is the semantic requirement imposed on `Key: Borrow<Q>` by the standard library's
/// borrowed-key `BTreeMap` operations.
pub uninterp spec fn borrowed_key_ordering_matches<Key, Q: ?Sized>(key: &Q) -> bool;

/// A key type has the same ordering as itself.
pub broadcast axiom fn axiom_deref_key_ordering_matches<Key>(key: &Key)
    ensures
        #[trigger] borrowed_key_ordering_matches::<Key, Key>(key),
;

/// Relates a map before and after mutating the value selected by a borrowed key.
pub open spec fn borrowed_key_mutated<Key, Value, Q: ?Sized>(
    old_map: Map<Key, Value>,
    new_map: Map<Key, Value>,
    key: &Q,
    old_value: Value,
    new_value: Value,
) -> bool {
    &&& contains_borrowed_key(old_map, key)
    &&& contains_borrowed_key(new_map, key)
    &&& maps_borrowed_key_to_value(old_map, key, old_value)
    &&& maps_borrowed_key_to_value(new_map, key, new_value)
    &&& exists|remainder: Map<Key, Value>|
        {
            &&& borrowed_key_removed(old_map, remainder, key)
            &&& borrowed_key_removed(new_map, remainder, key)
        }
}

/// Additional axioms for mutable B-tree operations.
pub broadcast group group_btree_extra_axioms {
    axiom_deref_key_ordering_matches,
}

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
    requires
        borrowed_key_ordering_matches::<Key, Q>(key),
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
    requires
        match bound {
            Bound::Included(key) | Bound::Excluded(key) => {
                borrowed_key_ordering_matches::<Key, Q>(key)
            },
            Bound::Unbounded => true,
        },
    ensures
        final(map)@.dom() == old(map)@.dom(),
        cursor.excluded_keys() == match bound {
            Bound::Excluded(key) => ISet::new(
                |stored_key: Key|
                    contains_borrowed_key(Map::<Key, ()>::empty().insert(stored_key, ()), key),
            ),
            _ => ISet::empty(),
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
    requires
        match bound {
            Bound::Included(key) | Bound::Excluded(key) => {
                borrowed_key_ordering_matches::<Key, Q>(key)
            },
            Bound::Unbounded => true,
        },
    ensures
        final(map)@.dom() == old(map)@.dom(),
        cursor.excluded_keys() == ISet::empty(),
;

/// Specification for [`CursorMut::peek_prev`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_prev ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    ensures
        final(cursor).excluded_keys() == old(cursor).excluded_keys(),
;

/// Specification for [`CursorMut::peek_next`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_next ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    ensures
        final(cursor).excluded_keys() == old(cursor).excluded_keys(),
        match result {
            Some((key, _)) => !old(cursor).excluded_keys().contains(*key),
            None => true,
        },
;

} // verus!
