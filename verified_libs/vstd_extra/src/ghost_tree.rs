use vstd::prelude::*;

use vstd::seq::*;
use vstd::seq_lib::*;

use super::ownership::*;
use super::seq_extra::*;

verus! {

/// A sequence of child indices describing a path from a starting node to a target node.
///
/// Each element selects one child at the corresponding tree level.
/// `N` is the maximum number of children of each node, so every index is less than `N`.
#[verifier::ext_equal]
pub tracked struct TreePath<const N: usize>(pub Seq<usize>);

impl<const N: usize> TreePath<N> {
    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    pub open spec fn index(self, i: int) -> usize
        recommends
            0 <= i < self.len(),
    {
        self.0[i]
    }

    pub open spec fn spec_index(self, i:int) -> usize {
        self.index(i)
    }

    pub open spec fn elem_inv(e: usize) -> bool {
        0 <= e < N
    }

    pub open spec fn inv(self) -> bool {
        &&& N > 0
        &&& forall |i: int| 0 <= i < self.len() ==> Self::elem_inv(#[trigger] self.index(i))
    }

    pub broadcast proof fn lemma_index_satisfies_elem_inv(self, i: int)
        requires
            self.inv(),
            0 <= i < self.len(),
        ensures
            #[trigger] Self::elem_inv(self.index(i)),
    {
    }

    pub open spec fn is_empty(self) -> bool {
        self.len() == 0
    }

    pub proof fn lemma_empty_satisfies_inv(self)
        requires
            N > 0,
            #[trigger] self.is_empty(),
        ensures
            #[trigger] self.inv(),
    {
    }

    pub open spec fn append(self, path: Self) -> Self {
        Self(self.0.add(path.0))
    }

    pub open spec fn pop_head(self) -> (usize, TreePath<N>)
        recommends
            !self.is_empty(),
    {
        (self.index(0), TreePath(self.0.drop_first()))
    }

    pub broadcast proof fn lemma_pop_head_preserves_inv(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            Self::elem_inv(self.pop_head().0),
            (#[trigger] self.pop_head()).1.inv(),
    {
        let (_, s1) = self.pop_head();
        assert(forall|i: int| 0 <= i < s1.len() ==> s1.index(i) == self.index(i + 1));
    }

    pub broadcast proof fn lemma_pop_head_index(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            (#[trigger] self.pop_head()).0 == self.index(0),
    {
    }

    pub open spec fn pop_tail(self) -> (usize, TreePath<N>)
        recommends
            !self.is_empty(),
    {
        (self.index(self.len() as int - 1), TreePath(self.0.drop_last()))
    }

    pub broadcast proof fn lemma_pop_tail_preserves_inv(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            Self::elem_inv(self.pop_tail().0),
            (#[trigger] self.pop_tail()).1.inv(),
    {
        let (_, s1) = self.pop_tail();
        if s1.len() > 0 {
            assert(forall|i: int| 0 <= i < s1.len() ==> s1.index(i) == self.index(i));
        }
    }

    pub broadcast proof fn lemma_pop_tail_index(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            (#[trigger] self.pop_tail()).0 == self.index(self.len() as int - 1),
    {
    }

    pub open spec fn push_head(self, hd: usize) -> TreePath<N>
        recommends
            0 <= hd < N,
    {
        TreePath(seq![hd].add(self.0))
    }

    pub proof fn lemma_push_head_index(self, hd: usize)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            self.push_head(hd).index(0) == hd,
            forall|i: int| 0 <= i < self.len() ==> self.push_head(hd).index(i + 1) == self.index(i),
    {
    }

    pub broadcast proof fn lemma_push_head_preserves_inv(self, hd: usize)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            (#[trigger] self.push_head(hd)).inv(),
    {
        let s1 = self.push_head(hd);
        assert forall|i: int| 0 <= i < s1.len() implies Self::elem_inv(#[trigger] s1.index(i)) by {
            if i == 0 {
            } else {
                assert(Self::elem_inv(self.index(i - 1)));
            }
        }
    }

    pub open spec fn push_tail(self, val: usize) -> TreePath<N>
        recommends
            0 <= val < N,
    {
        TreePath(self.0.push(val))
    }

    pub broadcast proof fn lemma_push_tail_len(self, val: usize)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            (#[trigger] self.push_tail(val)).len() == self.len() + 1,
    {
    }

    pub proof fn lemma_push_tail_index(self, val: usize)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            self.push_tail(val).index(self.len() as int) == val,
            forall|i: int|
                0 <= i < self.len() ==> #[trigger] self.push_tail(val).index(i) == self.index(i),
    {
    }

    pub broadcast proof fn lemma_push_tail_preserves_inv(self, val: usize)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            (#[trigger]self.push_tail(val)).inv(),
    {
        let s1 = self.push_tail(val);
        assert forall|i: int| 0 <= i < s1.len() implies Self::elem_inv(#[trigger] s1.index(i)) by {
            if i == self.len() {
            } else {
                assert(Self::elem_inv(self.index(i)));
            }
        }
    }

    pub open spec fn new(path: Seq<usize>) -> TreePath<N>
        recommends
            forall|i: int| 0 <= i < path.len() ==> Self::elem_inv(#[trigger] path[i]),
    {
        TreePath(path)
    }

    pub broadcast proof fn lemma_new_preserves_inv(path: Seq<usize>)
        requires
            N > 0,
            forall|i: int| 0 <= i < path.len() ==> Self::elem_inv(#[trigger] path[i]),
        ensures
            #[trigger] Self::new(path).inv(),
    {
    }

}

} // verus!
verus! {

pub trait TreeNodeValue<const L: usize>: Sized + Inv {
    spec fn default(lv: nat) -> Self;

    proof fn lemma_default_preserves_inv()
        ensures
            forall|lv: nat| #[trigger] Self::default(lv).inv(),
    ;

    spec fn la_inv(self, lv: nat) -> bool;

    proof fn lemma_default_preserves_la_inv()
        ensures
            forall|lv: nat| #[trigger] Self::default(lv).la_inv(lv),
    ;

    spec fn rel_children(self, index: int, child: Option<Self>) -> bool;

    proof fn lemma_default_preserves_rel_children(self, lv: nat)
        requires
            self.inv(),
            self.la_inv(lv),
        ensures
            forall|i: int| #[trigger] self.rel_children(i, Some(Self::default(lv + 1))),
    ;
}

/// A ghost tree node with maximum `N` children,
/// the maximum depth of the tree is `L`
/// Each tree node has a value of type `T` and a sequence of children
pub tracked struct TreeNode<T: TreeNodeValue<L>, const N: usize, const L: usize> {
    tracked value: T,
    ghost level: nat,
    // FIXME: This should use tracked indirection, but that is blocked by
    // https://github.com/verus-lang/verus/issues/2627.
    tracked children: Ghost<Seq<Option<TreeNode<T, N, L>>>>,
}

impl<T: TreeNodeValue<L>, const N: usize, const L: usize> TreeNode<T, N, L> {
    /// Returns the value stored in this node.
    pub closed spec fn value(self) -> T {
        self.value
    }

    /// Returns the level of this node.
    pub closed spec fn level(self) -> nat {
        self.level
    }

    /// Returns the sequence of children.
    pub closed spec fn children(self) -> Seq<Option<Self>> {
        self.children@
    }

    #[verifier::inline]
    pub open spec fn size() -> nat {
        N as nat
    }

    #[verifier::inline]
    pub open spec fn max_depth() -> nat {
        L as nat
    }

    /// Constructs a node from its fields.
    pub closed spec fn new(value: T, level: nat, children: Seq<Option<Self>>) -> Self {
        TreeNode { value, level, children: Ghost::new(children) }
    }

    pub open spec fn new_default(lv: nat) -> Self {
        Self::new(T::default(lv), lv, Seq::new(N as nat, |i| None))
    }

    pub open spec fn new_val(val: T, lv: nat) -> Self
        recommends
            lv < L,
    {
        Self::new(val, lv, Seq::new(N as nat, |i| None))
    }

    /// Exposes the observable shape of a node returned by `tracked_new_val`.
    pub proof fn lemma_new_val_properties(self, val: T, lv: nat)
        requires
            self == Self::new_val(val, lv),
        ensures
            self.value() == val,
            self.level() == lv,
            self.children() == Seq::new(N as nat, |i| None),
            self == Self::new_val(self.value(), self.level()),
    {
        Self::lemma_new_properties(val, lv, Seq::new(N as nat, |i| None));
    }

    pub open spec fn inv_node(self) -> bool {
        &&& self.value().inv()
        &&& self.value().la_inv(self.level())
        &&& self.level() < L
        &&& self.children().len() == Self::size()
    }

    pub open spec fn inv_children(self) -> bool {
        if self.level() == L - 1 {
            forall|i: int| 0 <= i < Self::size() ==> #[trigger] self.children()[i] is None
        } else {
            forall|i: int|
                0 <= i < Self::size() ==> match #[trigger] self.children()[i] {
                    Some(child) => {
                        &&& child.level() == self.level() + 1
                        &&& self.value().rel_children(i, Some(child.value()))
                    },
                    None => self.value().rel_children(i, None),
                }
        }
    }

    pub open spec fn inv(self) -> bool
        decreases (L - self.level()),
    {
        &&& L > 0
        &&& N > 0
        &&& self.inv_node()
        &&& self.inv_children()
        &&& if L - self.level() == 1 {
            // leaf nodes
            true
        } else {
            // pass invariants to children
            forall|i: int|
                0 <= i < Self::size() ==> match #[trigger] self.children()[i] {
                    Some(child) => child.inv(),
                    None => true,
                }
        }
    }

    pub broadcast proof fn lemma_new_properties(
        value: T,
        level: nat,
        children: Seq<Option<Self>>,
    )
        ensures
            #[trigger] Self::new(value, level, children).value() == value,
            Self::new(value, level, children).level() == level,
            Self::new(value, level, children).children() == children,
    {
    }

    /// Two nodes are equal when all of their observable fields are equal.
    pub proof fn lemma_ext_equal(self, other: Self)
        requires
            self.value() == other.value(),
            self.level() == other.level(),
            self.children() == other.children(),
        ensures
            self == other,
    {
    }

    /// Removes a child from the underlying sequence.
    pub axiom fn tracked_remove_child(tracked &mut self, i: int) -> (tracked ret: Option<Self>)
        requires
            0 <= i < old(self).children().len(),
        ensures
            ret == old(self).children()[i],
            final(self).children().len() == old(self).children().len() - 1,
            final(self).children() == old(self).children().remove(i),
            final(self).value() == old(self).value(),
            final(self).level() == old(self).level(),
    ;

    /// Inserts a child into the underlying sequence.
    pub axiom fn tracked_insert_child(
        tracked &mut self,
        i: int,
        tracked child: Option<Self>,
    )
        requires
            0 <= i <= old(self).children().len(),
        ensures
            final(self).children().len() == old(self).children().len() + 1,
            final(self).children() == old(self).children().insert(i, child),
            final(self).value() == old(self).value(),
            final(self).level() == old(self).level(),
    ;

    /// Borrows a child from the underlying sequence.
    pub axiom fn tracked_borrow_child(tracked &self, i: int) -> (tracked ret: &Self)
        requires
            0 <= i < self.children().len(),
            self.children()[i] is Some,
        ensures
            *ret == self.children()[i] -> 0,
    ;

    pub axiom fn tracked_borrow_mut_child(tracked &mut self, i: int) -> (tracked ret: &mut Self)
        requires
            0 <= i < self.children().len(),
            self.children()[i] is Some,
        ensures
            *ret == old(self).children()[i]->0,
            final(self).value() == old(self).value(),
            final(self).level() == old(self).level(),
            final(self).children() == old(self).children().update(i, Some(*final(ret))),
            ;

    pub proof fn tracked_borrow_value(tracked &self) -> (tracked res: &T)
        ensures
            *res == self.value(),
    {
        &self.value
    }

    pub proof fn tracked_borrow_mut_value(tracked &mut self) -> (tracked res: &mut T)
        ensures
            *res == old(self).value(),
            final(self).value() == *final(res),
            final(self).level() == old(self).level(),
            final(self).children() == old(self).children(),
    {
        &mut self.value
    }

    /// Requires `f` to hold for this node and every present descendant.
    ///
    /// `path` identifies the current node. When descending through child index `i`, the
    /// corresponding child path is `path.push_tail(i)`.
    pub open spec fn subtree_satisfies(
        self,
        path: TreePath<N>,
        f: spec_fn(T, TreePath<N>) -> bool,
    ) -> bool
        decreases L - self.level(),
        when self.inv()
    {
        if self.level() < L - 1 {
            &&& f(self.value(), path)
            &&& forall|i: int|
                0 <= i < self.children().len() ==> (#[trigger] self.children()[i]) is Some
                    ==> self.children()[i]->0.subtree_satisfies(path.push_tail(i as usize), f)
        } else {
            &&& f(self.value(), path)
        }
    }

    pub proof fn lemma_map_unroll_once(
        self,
        path: TreePath<N>,
        f: spec_fn(T, TreePath<N>) -> bool,
        i: int,
    )
        requires
            self.inv(),
            self.level() < L - 1,
            0 <= i < self.children().len(),
            self.children()[i] is Some,
            self.subtree_satisfies(path, f),
        ensures
            self.children()[i]->0.subtree_satisfies(path.push_tail(i as usize), f),
    {
    }

    pub open spec fn implies(
        f: spec_fn(T, TreePath<N>) -> bool,
        g: spec_fn(T, TreePath<N>) -> bool,
    ) -> bool {
        forall |value: T, path: TreePath<N>|
            value.inv() ==> f(value, path) ==> #[trigger] g(value, path)
    }

    pub proof fn lemma_map_implies(
        self,
        path: TreePath<N>,
        f: spec_fn(T, TreePath<N>) -> bool,
        g: spec_fn(T, TreePath<N>) -> bool,
    )
        requires
            self.inv(),
            Self::implies(f, g),
            Self::subtree_satisfies(self, path, f),
        ensures
            Self::subtree_satisfies(self, path, g),
        decreases L - self.level(),
    {
        if self.level() < L - 1 {
            assert forall|i: int|
                #![trigger self.children()[i]->0]
                0 <= i < self.children().len()
                    && self.children()[i] is Some implies self.children()[i]->0.subtree_satisfies(
                path.push_tail(i as usize),
                g,
            ) by {
                self.children()[i]->0.lemma_map_implies(path.push_tail(i as usize), f, g);
            }
        }
    }

    /// `TreeNode::new_default(lv)` has all-None children, so `subtree_satisfies` reduces to `f(default(lv), path)`.
    pub proof fn lemma_new_subtree_satisfies(
        lv: nat,
        path: TreePath<N>,
        f: spec_fn(T, TreePath<N>) -> bool,
    )
        requires
            lv < L,
            Self::new_default(lv).inv(),
            f(T::default(lv), path),
        ensures
            Self::new_default(lv).subtree_satisfies(path, f),
    {
        // Self::new_default(lv).children()[i] = None for all i, so the forall in subtree_satisfies is vacuous.
    }

    /// `TreeNode::new_val(val, lv)` has all-None children.
    /// `subtree_satisfies` holds trivially: `f(val, path)` at the root,
    /// no children to recurse into.
    pub proof fn lemma_new_val_subtree_satisfies(
        self,
        path: TreePath<N>,
        f: spec_fn(T, TreePath<N>) -> bool,
    )
        requires
            self.inv(),
            self == Self::new_val(self.value(), self.level()),
            f(self.value(), path),
        ensures
            self.subtree_satisfies(path, f),
    {
        // All children are None, so the forall in subtree_satisfies is vacuous.
    }

    /// Proves `subtree_satisfies(self, path, g)` from two source predicates `f1`, `f2`,
    /// and the implication `forall |v, p| v.inv() && f1(v, p) && f2(v, p) ==> g(v, p)`.
    pub proof fn lemma_map_implies_and(
        self,
        path: TreePath<N>,
        f1: spec_fn(T, TreePath<N>) -> bool,
        f2: spec_fn(T, TreePath<N>) -> bool,
        g: spec_fn(T, TreePath<N>) -> bool,
    )
        requires
            self.inv(),
            Self::implies(|v: T, p: TreePath<N>| f1(v, p) && f2(v, p), g),
            Self::subtree_satisfies(self, path, f1),
            Self::subtree_satisfies(self, path, f2),
        ensures
            Self::subtree_satisfies(self, path, g),
        decreases L - self.level(),
    {
        if self.level() < L - 1 {
            assert forall|i: int|
                #![trigger self.children()[i]->0]
                0 <= i < self.children().len()
                    && self.children()[i] is Some implies self.children()[i]->0.subtree_satisfies(
                path.push_tail(i as usize),
                g,
            ) by {
                self.children()[i]->0.lemma_map_implies_and(path.push_tail(i as usize), f1, f2, g);
            }
        }
    }

    pub axiom fn tracked_new_val(tracked val: T, lv: nat) -> (tracked res: Self)
        requires
            0 <= lv < L,
            N > 0,
            val.inv(),
        ensures
            res.inv(),
        returns
            Self::new_val(val, lv),
    ;

    pub broadcast proof fn lemma_new_default_preserves_inv(lv: nat)
        requires
            0 <= lv < L,
            N > 0,
            forall|i: int| 0 <= i < N ==> #[trigger] T::default(lv).rel_children(i, None),
        ensures
            (#[trigger] Self::new_default(lv)).inv(),
    {
        T::lemma_default_preserves_inv();
        T::lemma_default_preserves_la_inv();
    }

    pub open spec fn insert(self, key: usize, node: Self) -> Self
        recommends
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level() < L - 1,
            node.level() == self.level() + 1,
    {
        Self::new(
            self.value(),
            self.level(),
            self.children().update(key as int, Some(node)),
        )
    }

    pub broadcast proof fn lemma_insert_preserves_inv(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level() < L - 1,
            node.level() == self.level() + 1,
            self.value().rel_children(key as int, Some(node.value())),
        ensures
            #[trigger] self.insert(key, node).inv(),
    {
    }

    pub broadcast proof fn lemma_insert_property(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level() < L - 1,
            node.level() == self.level() + 1,
        ensures
            #[trigger] self.insert(key, node).value() == self.value(),
            self.insert(key, node).children()[key as int] == Some(node),
            forall|i: int|
                0 <= i < Self::size() && i != key ==> #[trigger] self.insert(key, node).children()[i]
                    == self.children()[i],
    {
    }

    pub broadcast proof fn lemma_insert_same_child_identical(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.child(key) == Some(node),
        ensures
            #[trigger] self.insert(key, node) == self,
    {
        self.lemma_child_some_properties(key);
        self.lemma_insert_property(key, node);
        assert(self.insert(key, node).children() == self.children());
    }

    pub open spec fn remove(self, key: usize) -> Self
        recommends
            0 <= key < Self::size(),
            self.inv(),
    {
        Self::new(self.value(), self.level(), self.children().update(key as int, None))
    }

    pub broadcast proof fn lemma_remove_preserves_inv(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.children()[key as int] is None || self.value().rel_children(key as int, None),
        ensures
            #[trigger] self.remove(key).inv(),
    {
    }

    pub broadcast proof fn lemma_remove_property(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #[trigger] self.remove(key).value() == self.value(),
            self.remove(key).children()[key as int] is None,
            forall|i: int|
                0 <= i < Self::size() && i != key ==> #[trigger] self.remove(key).children()[i]
                    == self.children()[i],
    {
    }

    pub open spec fn child(self, key: usize) -> Option<Self>
        recommends
            0 <= key < Self::size(),
            self.inv(),
    {
        self.children()[key as int]
    }

    pub broadcast proof fn lemma_child_property(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #[trigger] self.child(key) == self.children()[key as int],
    {
    }

    pub broadcast proof fn lemma_child_property_cases(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            self.level() == L - 1 ==> #[trigger] self.child(key) is None,
            self.level() < L - 1 && self.children()[key as int] is None ==> #[trigger] self.child(
                key,
            ) is None,
            self.level() < L - 1 && self.children()[key as int] is Some ==> #[trigger] self.child(
                key,
            ) is Some && self.child(key)->0.level() == self.level() + 1 && self.child(key)->0.inv(),
    {
    }

    pub proof fn lemma_child_some_properties(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.child(key) is Some,
        ensures
            self.level() < L - 1,
            self.child(key)->0.level() == self.level() + 1,
            self.child(key)->0.inv(),
    {
        self.lemma_child_property(key);
        self.lemma_child_property_cases(key);
    }

    pub broadcast proof fn lemma_insert_child_is_child(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level() < L - 1,
            node.level() == self.level() + 1,
        ensures
            #[trigger] self.insert(key, node).child(key) == Some(node),
    {
        self.lemma_insert_property(key, node);
        self.lemma_child_property(key);
    }

    pub broadcast proof fn lemma_remove_child_is_none(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #[trigger] self.remove(key).child(key) is None,
    {
        self.lemma_remove_property(key);
        self.lemma_child_property(key);
    }

    pub open spec fn get_value(self) -> T {
        self.value()
    }

    pub broadcast proof fn lemma_get_value_property(self)
        requires
            self.inv(),
        ensures
            #[trigger] self.get_value() == self.value(),
            self.get_value().inv(),
    {
    }

    pub open spec fn set_value(self, value: T) -> Self
        recommends
            self.inv(),
            value.inv(),
    {
        Self::new(value, self.level(), self.children())
    }

    /// Exposes the observable fields changed and preserved by `set_value`.
    pub proof fn lemma_set_value_observable_fields(self, value: T)
        ensures
            self.set_value(value).value() == value,
            self.set_value(value).level() == self.level(),
            self.set_value(value).children() == self.children(),
    {
        Self::lemma_new_properties(value, self.level(), self.children());
    }

    /// Replacing the value of a childless node preserves its `new_val` shape.
    pub proof fn lemma_set_value_preserves_new_val_shape(self, value: T)
        requires
            self == Self::new_val(self.value(), self.level()),
        ensures
            self.set_value(value) == Self::new_val(value, self.level()),
    {
        self.lemma_set_value_observable_fields(value);
        Self::lemma_new_properties(value, self.level(), Seq::new(N as nat, |i| None));
        Self::lemma_ext_equal(self.set_value(value), Self::new_val(value, self.level()));
    }

    pub broadcast proof fn lemma_set_value_property(self, value: T)
        requires
            self.inv(),
            value.inv(),
            value.la_inv(self.level()),
            forall|i: int|
                0 <= i < N ==> #[trigger] self.children()[i] is Some ==> value.rel_children(
                    i,
                    Some(self.children()[i]->0.value()),
                ),
            forall|i: int|
                0 <= i < N ==> #[trigger] self.children()[i] is None ==> value.rel_children(i, None),
        ensures
            #[trigger] self.set_value(value).value() == value,
            self.set_value(value).children() == self.children(),
            self.set_value(value).inv(),
    {
        if self.level() == L - 1 {
        } else {
            assert forall|i: int| 0 <= i < Self::size() implies match #[trigger] self.set_value(
                value,
            ).children()[i] {
                Some(child) => {
                    &&& child.level() == self.set_value(value).level() + 1
                    &&& self.set_value(value).value().rel_children(i, Some(child.value()))
                },
                None => self.set_value(value).value().rel_children(i, None),
            } by {}
        }
    }

    pub open spec fn is_leaf(self) -> bool {
        forall|i: int| 0 <= i < Self::size() ==> self.children()[i] is None
    }

    pub broadcast proof fn lemma_is_leaf_bounded(self)
        requires
            self.inv(),
            self.level() == L - 1,
        ensures
            #[trigger] self.is_leaf(),
    {
    }

    pub open spec fn recursive_insert(self, path: TreePath<N>, node: Self) -> Self
        recommends
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
        decreases path.len(),
    {
        if path.is_empty() {
            self
        } else if path.len() == 1 {
            self.insert(path.index(0), node)
        } else {
            let (hd, tl) = path.pop_head();
            let child = match self.child(hd) {
                Some(child) => child,
                None => TreeNode::new_default(self.level() + 1),
            };
            let updated_child = child.recursive_insert(tl, node);
            self.insert(hd, updated_child)
        }
    }

    pub broadcast proof fn lemma_recursive_insert_path_empty_identical(
        self,
        path: TreePath<N>,
        node: Self,
    )
        requires
            self.inv(),
            node.inv(),
            path.inv(),
            path.is_empty(),
        ensures
            #[trigger] self.recursive_insert(path, node) == self,
    {
    }

    pub broadcast proof fn lemma_recursive_insert_path_len_1(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            node.inv(),
            path.inv(),
            path.len() == 1,
            1 < L - self.level(),
            node.level() == self.level() + 1,
        ensures
            #[trigger] self.recursive_insert(path, node) == self.insert(path.index(0), node),
    {
    }

    pub broadcast proof fn lemma_recursive_insert_path_len_step(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
            path.len() > 1,
        ensures
            self.child(path.index(0)) is Some ==> #[trigger] self.recursive_insert(path, node)
                == self.insert(
                path.index(0),
                self.child(path.index(0))->0.recursive_insert(path.pop_head().1, node),
            ),
            self.child(path.index(0)) is None ==> #[trigger] self.recursive_insert(path, node)
                == self.insert(
                path.index(0),
                TreeNode::new_default(self.level() + 1).recursive_insert(path.pop_head().1, node),
            ),
    {
    }

    pub broadcast proof fn lemma_recursive_insert_preserves_level(
        self,
        path: TreePath<N>,
        node: Self,
    )
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
            forall|lv: nat|
                lv < L ==> #[trigger] T::default(lv).rel_children(path.pop_tail().0 as int, None),
        ensures
            #[trigger] self.recursive_insert(path, node).level() == self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
            self.lemma_recursive_insert_path_empty_identical(path, node);
        } else if path.len() == 1 {
            path.lemma_index_satisfies_elem_inv(0);
            self.lemma_recursive_insert_path_len_1(path, node);
            assert(self.insert(path.index(0), node).level() == self.level());
        } else {
            self.lemma_recursive_insert_path_len_step(path, node);
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                self.lemma_child_some_properties(hd);
                assert(self.insert(hd, c.recursive_insert(tl, node)).level() == self.level());
            } else {
                let c = TreeNode::new_default(self.level() + 1);
                assert(self.insert(hd, c.recursive_insert(tl, node)).level() == self.level());
            }
        }
    }

    pub broadcast proof fn lemma_recursive_insert_preserves_value(
        self,
        path: TreePath<N>,
        node: Self,
    )
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
            forall|lv: nat, i: int|
                lv < L && 0 <= i < N ==> #[trigger] T::default(lv).rel_children(i, None),
        ensures
            #[trigger] self.recursive_insert(path, node).value() == self.value(),
        decreases path.len(),
    {
        if path.is_empty() {
            self.lemma_recursive_insert_path_empty_identical(path, node);
        } else if path.len() == 1 {
            path.lemma_index_satisfies_elem_inv(0);
            self.lemma_recursive_insert_path_len_1(path, node);
        } else {
            self.lemma_recursive_insert_path_len_step(path, node);
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                self.lemma_child_some_properties(hd);
                c.lemma_recursive_insert_preserves_value(tl, node);
            } else {
                let c = TreeNode::new_default(self.level() + 1);
                Self::lemma_new_default_preserves_inv(self.level() + 1);
                c.lemma_recursive_insert_preserves_value(tl, node);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_insert_preserves_inv(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
            self.recursive_seek(path.pop_tail().1) is Some ==> self.recursive_seek(
                path.pop_tail().1,
            )->0.value().rel_children(path.pop_tail().0 as int, Some(node.value())),
            self.recursive_seek(path.pop_tail().1) is None ==> T::default(
                (node.level() - 1) as nat,
            ).rel_children(path.pop_tail().0 as int, Some(node.value())),
            forall|lv: nat, i: int|
                lv < L ==> 0 <= i < N ==> #[trigger] T::default(lv).rel_children(i, None),
        ensures
            #[trigger] self.recursive_insert(path, node).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
            self.lemma_recursive_insert_path_empty_identical(path, node);
        } else if path.len() == 1 {
            path.lemma_index_satisfies_elem_inv(0);
            self.lemma_recursive_insert_path_len_1(path, node);
            self.lemma_insert_preserves_inv(path.index(0), node);
        } else {
            self.lemma_recursive_insert_path_len_step(path, node);
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                self.lemma_child_some_properties(hd);
                assert(path.pop_tail().1.pop_head().1 == path.pop_head().1.pop_tail().1);
                c.lemma_recursive_insert_preserves_inv(tl, node);
                c.lemma_recursive_insert_preserves_level(tl, node);
                c.lemma_recursive_insert_preserves_value(tl, node);
                let updated_child = c.recursive_insert(tl, node);
                self.lemma_insert_preserves_inv(hd, updated_child);
            } else {
                let c = TreeNode::new_default(self.level() + 1);
                Self::lemma_new_default_preserves_inv(self.level() + 1);
                self.value().lemma_default_preserves_rel_children(self.level());
                c.lemma_recursive_insert_preserves_inv(tl, node);
                c.lemma_recursive_insert_preserves_level(tl, node);
                c.lemma_recursive_insert_preserves_value(tl, node);
                let updated_child = c.recursive_insert(tl, node);
                self.lemma_insert_preserves_inv(hd, updated_child);
            }
        }
    }

    /// Visit the tree node recursively based on the path
    /// Returns a sequence of visited node values, including the initial one
    /// If the path does not correspond to a node, stop the traverse, and return the
    /// previously visited nodes.
    pub open spec fn recursive_trace(self, path: TreePath<N>) -> Seq<T>
        recommends
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
            seq![self.value()]
        } else {
            let (hd, tl) = path.pop_head();
            match self.child(hd) {
                Some(child) => seq![self.value()].add(child.recursive_trace(tl)),
                None => seq![self.value()],
            }
        }
    }

    pub proof fn lemma_recursive_trace_length(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
        ensures
            #[trigger] self.recursive_trace(path).len() <= path.len() + 1,
        decreases path.len(),
    {
        if path.len() == 0 {
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            match self.child(hd) {
                None => {},
                Some(child) => {
                    child.lemma_recursive_trace_length(tl);
                },
            }
        }
    }

    pub proof fn lemma_recursive_trace_up_to(self, path1: TreePath<N>, path2: TreePath<N>, n: int)
        requires
            self.inv(),
            path1.inv(),
            path2.inv(),
            n <= path1.len(),
            n <= path2.len(),
            forall|i: int| 0 <= i < n ==> path1.0[i] == path2.0[i],
            self.recursive_trace(path1).len() > n,
        ensures
            self.recursive_trace(path2).len() > n,
            forall|i: int|
                0 <= i <= n ==> self.recursive_trace(path1)[i] == self.recursive_trace(path2)[i],
        decreases n,
    {
        if n <= 0 {
        } else {
            let (hd1, tl1) = path1.pop_head();
            let (hd2, tl2) = path2.pop_head();
            match self.child(hd1) {
                None => {},
                Some(child) => {
                    path1.lemma_pop_head_preserves_inv();
                    path2.lemma_pop_head_preserves_inv();
                    child.lemma_recursive_trace_up_to(tl1, tl2, n - 1);
                },
            }
        }
    }

    /// Walk to the end of a path and return the subtree at the end
    /// Returns a single node (with its children)
    /// If the path does not correspond to a node, return None
    pub open spec fn recursive_seek(self, path: TreePath<N>) -> Option<Self>
        recommends
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
            Some(self)
        } else {
            let (hd, tl) = path.pop_head();
            match self.child(hd) {
                Some(child) => child.recursive_seek(tl),
                None => None,
            }
        }
    }

    pub proof fn lemma_recursive_seek_trace_length(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            self.recursive_seek(path) is Some,
        ensures
            self.recursive_trace(path).len() == path.len() + 1,
        decreases path.len(),
    {
        if path.len() == 0 {
        } else {
            let (hd, tl) = path.pop_head();
            match self.child(hd) {
                None => {},
                Some(child) => {
                    path.lemma_pop_head_preserves_inv();
                    child.lemma_recursive_seek_trace_length(tl)
                },
            }
        }
    }

    pub proof fn lemma_recursive_seek_trace_next(self, path: TreePath<N>, idx: usize)
        requires
            self.recursive_seek(path) is Some,
            self.recursive_seek(path)->0.children()[idx as int] is Some,
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            0 <= idx < N,
        ensures
            self.recursive_trace(path.push_tail(idx)).len() == path.len() + 2,
            self.recursive_seek(path)->0.children()[idx as int]->0.value() == self.recursive_trace(
                path.push_tail(idx),
            )[path.len() as int + 1],
        decreases path.len(),
    {
        let path2 = path.push_tail(idx);

        if path.len() == 0 {
            assert(self.recursive_trace(path2) == seq![
                self.value(),
                self.children()[idx as int]->0.value(),
            ]) by { reveal_with_fuel(TreeNode::recursive_trace, 2) }
        } else {
            let (_, tl1) = path.pop_head();
            let (hd2, tl2) = path2.pop_head();
            assert(tl2 == tl1.push_tail(idx)) by {}
            assert(tl1.inv()) by { path.lemma_pop_head_preserves_inv() }
            match self.child(hd2) {
                None => {},
                Some(child) => {
                    child.lemma_recursive_seek_trace_next(tl1, idx);
                },
            }
        }
    }

    /// Visit the tree node recursively based on the path
    /// Returns a sequence of visited nodes, exclude the given one
    /// If the path is empty, return an empty sequence
    /// If the tree node is absent, stop the traverse, and return the
    /// previously visited nodes.
    pub open spec fn recursive_visit(self, path: TreePath<N>) -> Seq<Self>
        recommends
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
            Seq::empty()
        } else if path.len() == 1 {
            match self.child(path.index(0)) {
                Some(child) => seq![child],
                None => Seq::empty(),
            }
        } else {
            let (hd, tl) = path.pop_head();
            match self.child(hd) {
                Some(child) => seq![child].add(child.recursive_visit(tl)),
                None => Seq::empty(),
            }
        }
    }

    pub broadcast proof fn lemma_recursive_visited_node_inv(self, path: TreePath<N>)
        requires
            #[trigger] self.inv(),
            #[trigger] path.inv(),
            path.len() < L - self.level(),
        ensures
            forall|i: int|
                0 <= i < self.recursive_visit(path).len() ==> #[trigger] self.recursive_visit(
                    path,
                ).index(i).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
            if self.child(path.index(0)) is Some {
            }
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                assert(self.recursive_visit(path) == seq![c].add(c.recursive_visit(tl)));
                c.lemma_recursive_visited_node_inv(tl);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_visited_node_levels(self, path: TreePath<N>)
        requires
            #[trigger] self.inv(),
            #[trigger] path.inv(),
            path.len() < L - self.level(),
        ensures
            forall|i: int|
                0 <= i < self.recursive_visit(path).len() ==> #[trigger] self.recursive_visit(
                    path,
                ).index(i).level() == self.level() + i + 1,
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
            if self.child(path.index(0)) is Some {
            }
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                assert(self.recursive_visit(path) == seq![c].add(c.recursive_visit(tl)));
                c.lemma_recursive_visited_node_levels(tl);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_visit_head(self, path: TreePath<N>)
        requires
            #[trigger] self.inv(),
            #[trigger] path.inv(),
            path.len() < L - self.level(),
            !path.is_empty(),
            self.recursive_visit(path).len() > 0,
        ensures
            self.recursive_visit(path).index(0) == self.child(path.index(0))->0,
    {
    }

    pub broadcast proof fn lemma_recursive_visit_induction(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            !path.is_empty(),
            self.recursive_visit(path).len() > 0,
        ensures
            #[trigger] self.recursive_visit(path) == seq![self.child(path.pop_head().0)->0].add(
                self.child(path.pop_head().0)->0.recursive_visit(path.pop_head().1),
            ),
    {
        if path.len() == 1 {
            path.lemma_pop_head_preserves_inv();
        } else {
            let (hd, _) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                self.lemma_recursive_visit_head(path);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_visit_one_is_child(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            path.len() == 1,
        ensures
            self.child(path.index(0)) is Some ==> #[trigger] self.recursive_visit(path) == seq![
                self.child(path.index(0))->0,
            ],
            self.child(path.index(0)) is None ==> #[trigger] self.recursive_visit(path) == seq![],
    {
    }

    pub open spec fn on_subtree(self, node: Self) -> bool
        recommends
            self.inv(),
            node.inv(),
            node.level() >= self.level(),
            node.level() < L,
    {
        node == self || exists|path: TreePath<N>| #[trigger]
            path.inv() && path.len() > 0 && path.len() == node.level() - self.level()
                && self.recursive_visit(path).last() == node
    }

    pub broadcast proof fn lemma_on_subtree_property(self, node: Self)
        requires
            self.inv(),
            node.inv(),
            node.level() >= self.level(),
            node.level() < L,
            #[trigger] self.on_subtree(node),
        ensures
            node.level() == self.level() ==> self == node,
            node.level() > self.level() ==> exists|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level() - self.level() && self.recursive_visit(
                    path,
                ).last() == node,
    {
    }

    pub broadcast proof fn lemma_not_on_subtree_property(self, node: Self)
        requires
            self.inv(),
            node.inv(),
            node.level() < L,
            !#[trigger] self.on_subtree(node),
        ensures
            self != node,
            node.level() > self.level() ==> forall|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level() - self.level() ==> self.recursive_visit(
                    path,
                ).last() != node,
    {
    }

    pub broadcast proof fn lemma_on_subtree_reflexive(self)
        requires
            self.inv(),
        ensures
            #[trigger] self.on_subtree(self),
    {
    }

    pub broadcast proof fn lemma_child_on_subtree(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.child(key) is Some,
        ensures
            #[trigger] self.on_subtree(self.child(key)->0),
    {
        assert(TreePath::<N>::new(seq![key]).inv());
    }

    pub broadcast proof fn lemma_insert_on_subtree(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level() < L - 1,
            node.level() == self.level() + 1,
            self.value().rel_children(key as int, Some(node.value())),
        ensures
            #[trigger] self.insert(key, node).on_subtree(node),
    {
        self.lemma_insert_child_is_child(key, node);
        self.insert(key, node).lemma_child_on_subtree(key);
    }

    /// Remove the tree node at the end of the path
    /// If the path is empty or any node in the path is absent,
    /// return the original tree node (no change)
    /// Otherwise, remove the node at the end of the path, and
    /// update the node recursively
    pub open spec fn recursive_remove(self, path: TreePath<N>) -> Self
        recommends
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
            self
        } else if path.len() == 1 {
            self.remove(path.index(0))
        } else {
            let (hd, tl) = path.pop_head();
            if self.child(hd) is None {
                self
            } else {
                let child = self.child(hd)->0;
                let updated_child = child.recursive_remove(tl);
                self.insert(hd, updated_child)
            }
        }
    }

    pub broadcast proof fn lemma_recursive_remove_preserves_level(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        ensures
            #[trigger] self.recursive_remove(path).level() == self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                self.lemma_child_some_properties(hd);
                c.lemma_recursive_remove_preserves_level(tl);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_remove_preserves_value(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        ensures
            #[trigger] self.recursive_remove(path).value() == self.value(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                self.lemma_child_some_properties(hd);
                c.lemma_recursive_remove_preserves_value(tl);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_remove_preserves_inv(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            path.len() > 0 ==> self.recursive_seek(path.pop_tail().1) is Some
                ==> self.recursive_seek(
                path.pop_tail().1,
            )->0.children()[path.pop_tail().0 as int] is None || self.recursive_seek(
                path.pop_tail().1,
            )->0.value().rel_children(path.pop_tail().0 as int, None),
        ensures
            #[trigger] self.recursive_remove(path).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
            self.lemma_remove_preserves_inv(path.index(0));
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.child(hd) is Some {
                let c = self.child(hd)->0;
                self.lemma_child_some_properties(hd);
                assert(path.pop_tail().1.pop_head().1 == path.pop_head().1.pop_tail().1);
                c.lemma_recursive_remove_preserves_inv(tl);
                c.lemma_recursive_remove_preserves_level(tl);
                c.lemma_recursive_remove_preserves_value(tl);
                let updated_child = c.recursive_remove(tl);
                self.lemma_insert_preserves_inv(hd, updated_child);
            }
        }
    }
}

} // verus!
verus! {

pub closed spec fn path_between<T: TreeNodeValue<L>, const N: usize, const L: usize>(
    src: TreeNode<T, N, L>,
    dst: TreeNode<T, N, L>,
) -> TreePath<N>
    recommends
        src.inv(),
        dst.inv(),
        src.level() <= dst.level(),
        src.on_subtree(dst),
{
    if src.inv() && dst.inv() && dst.level() >= src.level() && dst.level() < L && src.on_subtree(dst) {
        if src == dst {
            TreePath::new(seq![])
        } else {
            choose|path: TreePath<N>| #[trigger]
                path.inv() && path.len() > 0 && path.len() == dst.level() - src.level()
                    && src.recursive_visit(path).last() == dst
        }
    } else {
        vstd::pervasive::arbitrary()
    }
}

pub broadcast proof fn lemma_path_between_properties<T: TreeNodeValue<L>, const N: usize, const L: usize>(
    src: TreeNode<T, N, L>,
    dst: TreeNode<T, N, L>,
)
    requires
        src.inv(),
        dst.inv(),
        src.level() <= dst.level(),
        #[trigger] src.on_subtree(dst),
    ensures
        path_between(src, dst).inv(),
        path_between(src, dst).len() == dst.level() - src.level(),
        dst.level() == src.level() ==> path_between(src, dst).is_empty() && src == dst,
        dst.level() > src.level() ==> src.recursive_visit(path_between(src, dst)).last() == dst,
{
}

} // verus!
verus! {

pub tracked struct Tree<T: TreeNodeValue<L>, const N: usize, const L: usize> {
    pub tracked root: TreeNode<T, N, L>,
}

impl<T: TreeNodeValue<L>, const N: usize, const L: usize> Tree<T, N, L> {
    pub open spec fn inv(self) -> bool {
        &&& L > 0
        &&& N > 0
        &&& self.root.inv()
        &&& self.root.level() == 0
    }

    pub open spec fn new() -> Self {
        Tree { root: TreeNode::new_default(0) }
    }

    pub broadcast proof fn lemma_new_preserves_inv()
        requires
            N > 0,
            L > 0,
            forall|i: int| 0 <= i < N ==> #[trigger] T::default(0).rel_children(i, None),
        ensures
            #[trigger] Self::new().inv(),
    {
        TreeNode::<T, N, L>::lemma_new_default_preserves_inv(0);
    }

    pub open spec fn insert(self, path: TreePath<N>, node: TreeNode<T, N, L>) -> Self
        recommends
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L,
            node.level() == path.len() as nat,
        decreases path.len(),
    {
        Tree { root: self.root.recursive_insert(path, node), ..self }
    }

    pub open spec fn remove(self, path: TreePath<N>) -> Self
        recommends
            self.inv(),
            path.inv(),
            path.len() < L,
        decreases path.len(),
    {
        Tree { root: self.root.recursive_remove(path), ..self }
    }

    pub open spec fn visit(self, path: TreePath<N>) -> Seq<TreeNode<T, N, L>>
        recommends
            self.inv(),
            path.inv(),
            path.len() < L,
        decreases path.len(),
    {
        self.root.recursive_visit(path)
    }

    pub broadcast proof fn lemma_visit_is_recursive_visit(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L,
        ensures
            #[trigger] self.visit(path) == self.root.recursive_visit(path),
    {
    }

    pub open spec fn trace(self, path: TreePath<N>) -> Seq<T>
        recommends
            self.inv(),
            path.inv(),
            path.len() < L,
        decreases path.len(),
    {
        self.root.recursive_trace(path)
    }

    pub broadcast proof fn lemma_trace_empty_is_head(self, path: TreePath<N>)
        requires
            path.len() == 0,
        ensures
            #[trigger] self.trace(path) == seq![self.root.value()],
    {
    }

    pub proof fn lemma_trace_up_to(self, path1: TreePath<N>, path2: TreePath<N>, n: int)
        requires
            self.inv(),
            path1.inv(),
            path2.inv(),
            n <= path1.len(),
            n <= path2.len(),
            forall|i: int| 0 <= i < n ==> path1.0[i] == path2.0[i],
            self.trace(path1).len() > n,
        ensures
            self.trace(path2).len() > n,
            forall|i: int| 0 <= i <= n ==> self.trace(path1)[i] == self.trace(path2)[i],
    {
        self.root.lemma_recursive_trace_up_to(path1, path2, n)
    }

    pub broadcast proof fn lemma_trace_length(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
        ensures
            #[trigger] self.trace(path).len() <= path.len() + 1,
    {
        self.root.lemma_recursive_trace_length(path);
    }

    pub open spec fn seek(self, path: TreePath<N>) -> Option<TreeNode<T, N, L>> {
        self.root.recursive_seek(path)
    }

    pub proof fn lemma_seek_trace_length(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L,
            self.seek(path) is Some,
        ensures
            self.trace(path).len() == path.len() + 1,
    {
        self.root.lemma_recursive_seek_trace_length(path)
    }

    pub proof fn lemma_seek_trace_next(self, path: TreePath<N>, idx: usize)
        requires
            self.seek(path) is Some,
            self.seek(path)->0.children()[idx as int] is Some,
            self.inv(),
            path.inv(),
            path.len() < L,
            0 <= idx < N,
        ensures
            self.trace(path.push_tail(idx)).len() == path.len() + 2,
            self.seek(path)->0.children()[idx as int]->0.value() == self.trace(
                path.push_tail(idx),
            )[path.len() as int + 1],
    {
        self.root.lemma_recursive_seek_trace_next(path, idx)
    }

    pub broadcast proof fn lemma_insert_preserves_inv(self, path: TreePath<N>, node: TreeNode<T, N, L>)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L,
            node.level() == path.len() as nat,
            self.seek(path.pop_tail().1) is Some ==> self.seek(
                path.pop_tail().1,
            )->0.value().rel_children(path.index(path.len() - 1) as int, Some(node.value())),
            self.seek(path.pop_tail().1) is None ==> T::default(
                (path.len() - 1) as nat,
            ).rel_children(path.index(path.len() - 1) as int, Some(node.value())),
            forall|lv: nat, i: int|
                lv < L ==> 0 <= i < N ==> #[trigger] T::default(lv).rel_children(i, None),
        ensures
            #[trigger] self.insert(path, node).inv(),
    {
        self.root.lemma_recursive_insert_preserves_inv(path, node);
    }

    pub broadcast proof fn lemma_remove_preserves_inv(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L,
            path.len() > 0 ==> self.seek(path.pop_tail().1) is Some ==> self.seek(
                path.pop_tail().1,
            )->0.children()[path.pop_tail().0 as int] is None || self.seek(
                path.pop_tail().1,
            )->0.value().rel_children(path.index(path.len() - 1) as int, None),
        ensures
            #[trigger] self.remove(path).inv(),
    {
        self.root.lemma_recursive_remove_preserves_inv(path);
    }

    pub broadcast proof fn lemma_visited_nodes_inv(self, path: TreePath<N>)
        requires
            #[trigger] self.inv(),
            #[trigger] path.inv(),
            path.len() < L,
        ensures
            forall|i: int|
                0 <= i < self.visit(path).len() ==> #[trigger] self.visit(path).index(i).inv(),
    {
        self.root.lemma_recursive_visited_node_inv(path);
    }

    #[verifier::inline]
    pub open spec fn on_tree(self, node: TreeNode<T, N, L>) -> bool
        recommends
            self.inv(),
            node.inv(),
    {
        self.root.on_subtree(node)
    }

    pub broadcast proof fn lemma_on_tree_property(self, node: TreeNode<T, N, L>)
        requires
            self.inv(),
            node.inv(),
            #[trigger] self.on_tree(node),
        ensures
            node.level() == 0 ==> self.root == node,
            node.level() > 0 ==> exists|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level() && self.visit(path).last() == node,
    {
    }

    pub broadcast proof fn lemma_not_on_tree_property(self, node: TreeNode<T, N, L>)
        requires
            self.inv(),
            node.inv(),
            !#[trigger] self.on_tree(node),
        ensures
            node != self.root,
            node.level() > 0 ==> forall|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level() ==> self.visit(path).last() != node,
    {
    }

    #[verifier::inline]
    pub open spec fn get_path(self, node: TreeNode<T, N, L>) -> TreePath<N>
        recommends
            self.inv(),
            node.inv(),
            self.on_tree(node),
    {
        path_between::<T, N, L>(self.root, node)
    }

    pub broadcast proof fn lemma_get_path_properties(self, node: TreeNode<T, N, L>)
        requires
            self.inv(),
            node.inv(),
            self.on_tree(node),
        ensures
            #[trigger] self.get_path(node).inv(),
            #[trigger] self.get_path(node).len() == node.level(),
            node.level() == 0 ==> #[trigger] self.get_path(node).is_empty(),
            node.level() > 0 ==> #[trigger] self.visit(self.get_path(node)).last() == node,
    {
        lemma_path_between_properties(self.root, node);
    }
}

} // verus!
verus! {

pub broadcast group group_ghost_tree {
    TreePath::lemma_index_satisfies_elem_inv,
    TreePath::lemma_pop_head_preserves_inv,
    TreePath::lemma_pop_head_index,
    TreePath::lemma_pop_tail_preserves_inv,
    TreePath::lemma_pop_tail_index,
    TreePath::lemma_push_tail_preserves_inv,
    TreePath::lemma_push_tail_len,
    TreePath::lemma_push_head_preserves_inv,
    TreePath::lemma_new_preserves_inv,
    TreeNode::lemma_new_properties,
    TreeNode::lemma_insert_preserves_inv,
    TreeNode::lemma_insert_property,
    TreeNode::lemma_insert_same_child_identical,
    TreeNode::lemma_remove_preserves_inv,
    TreeNode::lemma_remove_property,
    TreeNode::lemma_child_property,
    TreeNode::lemma_child_property_cases,
    TreeNode::lemma_insert_child_is_child,
    TreeNode::lemma_remove_child_is_none,
    TreeNode::lemma_get_value_property,
    TreeNode::lemma_set_value_property,
    TreeNode::lemma_is_leaf_bounded,
    TreeNode::lemma_recursive_visited_node_inv,
    TreeNode::lemma_recursive_visited_node_levels,
    TreeNode::lemma_recursive_visit_head,
    TreeNode::lemma_recursive_visit_induction,
    TreeNode::lemma_recursive_visit_one_is_child,
    TreeNode::lemma_on_subtree_property,
    TreeNode::lemma_not_on_subtree_property,
    TreeNode::lemma_on_subtree_reflexive,
    TreeNode::lemma_child_on_subtree,
    TreeNode::lemma_insert_on_subtree,
    TreeNode::lemma_recursive_remove_preserves_inv,
    lemma_path_between_properties,
    Tree::lemma_new_preserves_inv,
    Tree::lemma_visit_is_recursive_visit,
    Tree::lemma_insert_preserves_inv,
    Tree::lemma_remove_preserves_inv,
    Tree::lemma_visited_nodes_inv,
    Tree::lemma_on_tree_property,
    Tree::lemma_not_on_tree_property,
}

} // verus!
