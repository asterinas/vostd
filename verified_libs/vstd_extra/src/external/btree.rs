//! Additional specifications for mutable [`BTreeMap`] operations not covered by vstd.
use alloc::{
    alloc::Allocator,
    collections::{BTreeMap, btree_map::CursorMut},
};
use core::{borrow::Borrow, cmp::Ordering, ops::Bound};
use vstd::{
    assert_maps_equal,
    laws_cmp::obeys_cmp,
    prelude::*,
    std_specs::{
        btree::{
            borrowed_key_removed, contains_borrowed_key, increasing_seq, maps_borrowed_key_to_value,
        },
        cmp::OrdSpec,
    },
};

verus! {

/// Verus declaration for Rust's mutable B-tree cursor type.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
pub struct ExCursorMut<'a, K: 'a, V: 'a, A>(CursorMut<'a, K, V, A>);

/// The abstract state of a mutable B-tree cursor.
///
/// A cursor points at the gap immediately before `keys[position]`. Therefore `peek_next`
/// accesses `keys[position]`, while `peek_prev` accesses `keys[position - 1]`.
pub ghost struct CursorMutModel<Key, Value> {
    /// All keys in the underlying map, in strictly increasing order.
    pub keys: Seq<Key>,
    /// The index of the element immediately after the cursor.
    pub position: int,
    /// The current contents of the complete map borrowed by the cursor.
    pub map: Map<Key, Value>,
}

impl<Key, Value> CursorMutModel<Key, Value> {
    /// Whether this model consistently represents an ordered map and a gap in that map.
    pub open spec fn wf(self) -> bool {
        &&& 0 <= self.position <= self.keys.len()
        &&& self.keys.no_duplicates()
        &&& self.keys.to_set() == self.map.dom()
        &&& increasing_seq(self.keys)
    }
}

/// Additional abstract and prophetic state for mutable B-tree cursors.
pub trait CursorMutAdditionalSpecFns<Key, Value>: Sized {
    spec fn view(&self) -> CursorMutModel<Key, Value>;

    /// The contents of the borrowed map when this cursor's borrow is resolved.
    #[verifier::prophetic]
    spec fn final_map(self) -> Map<Key, Value>;
}

impl<'a, Key, Value, A> CursorMutAdditionalSpecFns<Key, Value> for CursorMut<'a, Key, Value, A> {
    uninterp spec fn view(&self) -> CursorMutModel<Key, Value>;

    #[verifier::prophetic]
    uninterp spec fn final_map(self) -> Map<Key, Value>;
}

/// Whether a borrowed key type's ordering agrees with the ordering of stored keys.
///
/// This is the semantic requirement imposed on `Key: Borrow<Q>` by the standard library's
/// borrowed-key `BTreeMap` operations.
pub uninterp spec fn borrowed_key_ordering_matches<Key: Borrow<Q> + Ord, Q: Ord + ?Sized>() -> bool;

/// The ordering of a stored key relative to a borrowed lookup key.
pub uninterp spec fn borrowed_key_cmp<Key, Q: ?Sized>(stored_key: Key, key: &Q) -> Ordering;

/// A key type has the same ordering as itself.
pub broadcast axiom fn axiom_deref_key_ordering_matches<Key: Ord>()
    ensures
        #[trigger] borrowed_key_ordering_matches::<Key, Key>(),
;

/// Comparing a stored key against a borrowed key of the same type agrees with `Ord`'s model.
pub broadcast axiom fn axiom_deref_key_cmp<Key: Ord>(stored_key: Key, key: &Key)
    ensures
        #[trigger] borrowed_key_cmp::<Key, Key>(stored_key, key) == stored_key.cmp_spec(key),
;

/// Whether a key occurs before the gap returned by `lower_bound_mut`.
pub open spec fn before_lower_bound<Key, Q: ?Sized>(key: Key, bound: Bound<&Q>) -> bool {
    match bound {
        Bound::Included(bound_key) => borrowed_key_cmp(key, bound_key) is Less,
        Bound::Excluded(bound_key) => !(borrowed_key_cmp(key, bound_key) is Greater),
        Bound::Unbounded => false,
    }
}

/// Whether a key occurs before the gap returned by `upper_bound_mut`.
pub open spec fn before_upper_bound<Key, Q: ?Sized>(key: Key, bound: Bound<&Q>) -> bool {
    match bound {
        Bound::Included(bound_key) => !(borrowed_key_cmp(key, bound_key) is Greater),
        Bound::Excluded(bound_key) => borrowed_key_cmp(key, bound_key) is Less,
        Bound::Unbounded => true,
    }
}

/// Whether a cursor is at the gap selected by `lower_bound_mut`.
pub open spec fn positioned_at_lower_bound<Key, Value, Q: ?Sized>(
    model: CursorMutModel<Key, Value>,
    bound: Bound<&Q>,
) -> bool {
    &&& forall|i: int|
        #![trigger before_lower_bound(model.keys[i], bound)]
        0 <= i < model.position ==> before_lower_bound(model.keys[i], bound)
    &&& forall|i: int|
        #![trigger before_lower_bound(model.keys[i], bound)]
        model.position <= i < model.keys.len() ==> !before_lower_bound(model.keys[i], bound)
}

/// Whether a cursor is at the gap selected by `upper_bound_mut`.
pub open spec fn positioned_at_upper_bound<Key, Value, Q: ?Sized>(
    model: CursorMutModel<Key, Value>,
    bound: Bound<&Q>,
) -> bool {
    &&& forall|i: int|
        #![trigger before_upper_bound(model.keys[i], bound)]
        0 <= i < model.position ==> before_upper_bound(model.keys[i], bound)
    &&& forall|i: int|
        #![trigger before_upper_bound(model.keys[i], bound)]
        model.position <= i < model.keys.len() ==> !before_upper_bound(model.keys[i], bound)
}

/// Once the cursor has been dropped, its prophesied map is its current map.
pub broadcast axiom fn axiom_has_resolved_cursor<Key, Value, A>(cursor: CursorMut<Key, Value, A>)
    ensures
        #[trigger] has_resolved(cursor) ==> cursor.final_map() == cursor@.map,
;

/// Relates a map before and after mutating the value selected by a borrowed key.
pub open spec fn borrowed_key_mutated<Key, Value, Q: ?Sized>(
    old_map: Map<Key, Value>,
    new_map: Map<Key, Value>,
    key: &Q,
    old_value: Value,
    new_value: Value,
) -> bool {
    &&& maps_borrowed_key_to_value(old_map, key, old_value)
    &&& maps_borrowed_key_to_value(new_map, key, new_value)
    &&& exists|remainder: Map<Key, Value>|
        {
            &&& borrowed_key_removed(old_map, remainder, key)
            &&& borrowed_key_removed(new_map, remainder, key)
        }
}

/// Simplifies [`borrowed_key_mutated`] when the borrowed key has the map's key type.
pub broadcast proof fn lemma_borrowed_key_mutated_deref<Key, Value>(
    old_map: Map<Key, Value>,
    new_map: Map<Key, Value>,
    key: &Key,
    old_value: Value,
    new_value: Value,
)
    ensures
        #[trigger] borrowed_key_mutated(old_map, new_map, key, old_value, new_value) <==> {
            &&& old_map.contains_key(*key)
            &&& old_map[*key] == old_value
            &&& new_map == old_map.insert(*key, new_value)
        },
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;

    if borrowed_key_mutated(old_map, new_map, key, old_value, new_value) {
        let remainder = choose|remainder: Map<Key, Value>|
            {
                &&& borrowed_key_removed(old_map, remainder, key)
                &&& borrowed_key_removed(new_map, remainder, key)
            };
        assert(remainder == new_map.remove(*key));
        assert_maps_equal!(new_map, old_map.insert(*key, new_value), candidate => {
            if candidate != *key {
                assert(old_map.remove(*key)[candidate] == old_map[candidate]);
            }
        });
    } else if old_map.contains_key(*key) && old_map[*key] == old_value && new_map == old_map.insert(
        *key,
        new_value,
    ) {
        let remainder = old_map.remove(*key);
        assert_maps_equal!(new_map.remove(*key), remainder, candidate => {});
        assert(borrowed_key_removed(new_map, remainder, key));
    }
}

/// Additional axioms for mutable B-tree operations.
pub broadcast group group_btree_extra_axioms {
    axiom_deref_key_ordering_matches,
    axiom_deref_key_cmp,
    axiom_has_resolved_cursor,
    lemma_borrowed_key_mutated_deref,
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
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        obeys_cmp::<Key>() ==> match result {
            Some(value) => borrowed_key_mutated(old(map)@, final(map)@, key, *value, *final(value)),
            None => !contains_borrowed_key(old(map)@, key) && final(map)@ == old(map)@,
        },
;

/// Specification for [`BTreeMap::lower_bound_mut`].
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
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        obeys_cmp::<Key>() ==> {
            &&& cursor@.wf()
            &&& cursor@.map == old(map)@
            &&& final(map)@ == cursor.final_map()
            &&& positioned_at_lower_bound(cursor@, bound)
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
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        obeys_cmp::<Key>() ==> {
            &&& cursor@.wf()
            &&& cursor@.map == old(map)@
            &&& final(map)@ == cursor.final_map()
            &&& positioned_at_upper_bound(cursor@, bound)
        },
;

/// Specification for [`CursorMut::peek_prev`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_prev ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        final(cursor)@.wf(),
        match result {
            Some((key, value)) => {
                let old_model = old(cursor)@;
                let new_model = final(cursor)@;
                &&& old_model.position > 0
                &&& *key == old_model.keys[old_model.position - 1]
                &&& *value == old_model.map[*key]
                &&& new_model.keys == old_model.keys
                &&& new_model.position == old_model.position
                &&& new_model.map == old_model.map.insert(*key, *final(value))
            },
            None => {
                &&& old(cursor)@.position == 0
                &&& final(cursor)@ == old(cursor)@
            },
        },
;

/// Specification for [`CursorMut::peek_next`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_next ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        final(cursor)@.wf(),
        match result {
            Some((key, value)) => {
                let old_model = old(cursor)@;
                let new_model = final(cursor)@;
                &&& old_model.position < old_model.keys.len()
                &&& *key == old_model.keys[old_model.position]
                &&& *value == old_model.map[*key]
                &&& new_model.keys == old_model.keys
                &&& new_model.position == old_model.position
                &&& new_model.map == old_model.map.insert(*key, *final(value))
            },
            None => {
                &&& old(cursor)@.position == old(cursor)@.keys.len()
                &&& final(cursor)@ == old(cursor)@
            },
        },
;

} // verus!
