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
pub ghost struct TreePath<const N: usize>(pub Seq<int>);

impl<const N: usize> TreePath<N> {
    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    pub open spec fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[verifier::inline]
    pub open spec fn index(self, i: int) -> int
        recommends
            0 <= i < self.len(),
    {
        self.0[i]
    }

    // Do NOT inline, it is used as trigger.
    pub open spec fn spec_index(self, i: int) -> int {
        self.index(i)
    }

    #[verifier::inline]
    pub open spec fn elem_inv(e: int) -> bool {
        0 <= e < N
    }

    pub open spec fn inv(self) -> bool {
        &&& N > 0
        &&& forall|i: int| 0 <= i < self.len() ==> Self::elem_inv(#[trigger] self[i])
    }

    pub broadcast proof fn lemma_index_satisfies_elem_inv(self, i: int)
        requires
            self.inv(),
            0 <= i < self.len(),
        ensures
            #![trigger self[i]]
            Self::elem_inv(self[i]),
    {
    }

    pub broadcast proof fn lemma_empty_satisfies_inv(self)
        requires
            N > 0,
            #[trigger] self.is_empty(),
        ensures
            self.inv(),
    {
    }

    pub open spec fn append(self, path: Self) -> Self {
        Self(self.0.add(path.0))
    }

    pub open spec fn pop_head(self) -> (int, TreePath<N>)
        recommends
            !self.is_empty(),
    {
        (self[0], TreePath(self.0.drop_first()))
    }

    pub broadcast proof fn lemma_pop_head_preserves_inv(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #![trigger self.pop_head()]
            self.pop_head().1.inv(),
    {
        let (_, s1) = self.pop_head();
        assert(forall|i: int| 0 <= i < s1.len() ==> s1[i] == self[i + 1]);
    }

    pub broadcast proof fn lemma_pop_head_index(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #![trigger self.pop_head()]
            self.pop_head().0 == self[0],
    {
    }

    pub open spec fn pop_tail(self) -> (int, TreePath<N>)
        recommends
            !self.is_empty(),
    {
        (self[self.len() - 1], TreePath(self.0.drop_last()))
    }

    pub broadcast proof fn lemma_pop_tail_preserves_inv(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #![trigger self.pop_tail()]
            self.pop_tail().1.inv(),
    {
        let (_, s1) = self.pop_tail();
        if s1.len() > 0 {
            assert(forall|i: int| 0 <= i < s1.len() ==> s1[i] == self[i]);
        }
    }

    pub broadcast proof fn lemma_pop_tail_index(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            (#[trigger] self.pop_tail()).0 == self[self.len() - 1],
    {
    }

    pub open spec fn push_head(self, hd: int) -> TreePath<N>
        recommends
            0 <= hd < N,
    {
        TreePath(seq![hd].add(self.0))
    }

    pub broadcast proof fn lemma_push_head_index(self, hd: int)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            #![trigger self.push_head(hd)]
            self.push_head(hd)[0] == hd,
            forall|i: int| 0 <= i < self.len() ==> #[trigger] self.push_head(hd)[i + 1] == self[i],
    {
    }

    pub broadcast proof fn lemma_push_head_preserves_inv(self, hd: int)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            #![trigger self.push_head(hd)]
            self.push_head(hd).inv(),
    {
        let s1 = self.push_head(hd);
        assert forall|i: int| 0 <= i < s1.len() implies Self::elem_inv(#[trigger] s1[i]) by {
            if i == 0 {
            } else {
                assert(Self::elem_inv(self[i - 1]));
            }
        }
    }

    pub open spec fn push_tail(self, val: int) -> TreePath<N>
        recommends
            0 <= val < N,
    {
        TreePath(self.0.push(val))
    }

    pub broadcast proof fn lemma_push_tail_len(self, val: int)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            #![trigger self.push_tail(val)]
            self.push_tail(val).len() == self.len() + 1,
    {
    }

    pub broadcast proof fn lemma_push_tail_index(self, val: int)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            #![trigger self.push_tail(val)]
            self.push_tail(val)[self.len() as int] == val,
            forall|i: int| 0 <= i < self.len() ==> #[trigger] self.push_tail(val)[i] == self[i],
    {
    }

    pub broadcast proof fn lemma_push_tail_preserves_inv(self, val: int)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            #![trigger self.push_tail(val)]
            self.push_tail(val).inv(),
    {
        let s1 = self.push_tail(val);
        assert forall|i: int| 0 <= i < s1.len() implies Self::elem_inv(#[trigger] s1[i]) by {
            if i == self.len() {
            } else {
                assert(Self::elem_inv(self[i]));
            }
        }
    }

    pub open spec fn new(path: Seq<int>) -> TreePath<N> {
        TreePath(path)
    }

    pub broadcast proof fn lemma_new_preserves_inv(path: Seq<int>)
        requires
            N > 0,
            forall|i: int| 0 <= i < path.len() ==> Self::elem_inv(#[trigger] path[i]),
        ensures
            (#[trigger] Self::new(path)).inv(),
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

/// A ghost tree node with depth `L` and `N` children.
///
/// Each tree node has a value of type `T` and a sequence of children, forming a subtree.
/// The length of the child seuquence is fixed at `N`, while the absence of a child is represeneted with `Option::None`.
/// The maximum depth of the tree is `L`.
pub tracked struct TreeNode<T: TreeNodeValue<L>, const N: usize, const L: usize> {
    tracked value: T,
    ghost level: nat,
    // See https://github.com/verus-lang/verus/issues/2627.
    tracked children: Tracked<Seq<Option<TreeNode<T, N, L>>>>,
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

    /// Returns whether the `i`-th child exists.
    pub open spec fn has_child(self, i: int) -> bool {
        self.children()[i] is Some
    }

    /// Returns the `i`-th child. Only valid when it exists.
    pub open spec fn child(self, i: int) -> Self {
        self.children()[i]->0
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
        TreeNode { value, level, children: Tracked(children) }
    }

    /// Constructs a tracked node from its tracked fields.
    pub proof fn tracked_new(
        tracked value: T,
        level: nat,
        tracked children: Seq<Option<Self>>,
    ) -> tracked Self
        returns
            Self::new(value, level, children),
    {
        TreeNode { value, level, children: Tracked(children) }
    }

    /// Constructs a node at the given level with default value and no children.
    pub open spec fn new_default(lv: nat) -> Self {
        Self::new(T::default(lv), lv, Seq::new(N as nat, |i| None))
    }

    /// Constructs a node with a given value and level, without childrens.
    pub open spec fn new_val(val: T, lv: nat) -> Self
        recommends
            lv < L,
    {
        Self::new(val, lv, Seq::new(N as nat, |i| None))
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

    pub broadcast proof fn lemma_new_properties(value: T, level: nat, children: Seq<Option<Self>>)
        ensures
            #![trigger Self::new(value, level, children)]
            Self::new(value, level, children).value() == value,
            Self::new(value, level, children).level() == level,
            Self::new(value, level, children).children() == children,
    {
    }

    pub broadcast proof fn lemma_new_val_properties(val: T, lv: nat)
        ensures
            #![trigger Self::new_val(val,lv)]
            Self::new_val(val, lv).value() == val,
            Self::new_val(val, lv).level() == lv,
            Self::new_val(val, lv).children() == Seq::new(N as nat, |i| None),
    {
        Self::lemma_new_properties(val, lv, Seq::new(N as nat, |i| None));
    }

    /// Two nodes are equal when all of their observable fields are equal.
    pub broadcast proof fn lemma_ext_equal(self, other: Self)
        requires
            self.value() == other.value(),
            self.level() == other.level(),
            self.children() =~= other.children(),
        ensures
            #![trigger self.children(), other.children()]
            self == other,
    {
    }

    /// Borrows a child from the underlying sequence.
    pub proof fn tracked_borrow_child(tracked &self, i: int) -> (tracked ret: &Self)
        requires
            0 <= i < self.children().len(),
            self.children()[i] is Some,
        ensures
            *ret == self.children()[i]->0,
    {
        self.children.tracked_borrow(i).tracked_borrow()
    }

    /// Mutably borrows a child from the underlying sequence.
    // FIXME: There is currenly no `tracked_borrow_mut` method for `Seq`.
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

    /// Consumes this node and returns its tracked value and children.
    pub proof fn tracked_into_parts(tracked self) -> (tracked (value, children): (
        T,
        Seq<Option<Self>>,
    ))
        ensures
            value == self.value(),
            children == self.children(),
    {
        let tracked Tracked(children) = self.children;
        (self.value, children)
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
                0 <= i < self.children().len() ==> (#[trigger] self.has_child(i)) ==> self.child(
                    i,
                ).subtree_satisfies(path.push_tail(i), f)
        } else {
            &&& f(self.value(), path)
        }
    }

    pub proof fn lemma_subtree_satisfies_unroll_once(
        self,
        path: TreePath<N>,
        f: spec_fn(T, TreePath<N>) -> bool,
        i: int,
    )
        requires
            self.inv(),
            self.level() < L - 1,
            0 <= i < self.children().len(),
            self.has_child(i),
            self.subtree_satisfies(path, f),
        ensures
            self.child(i).subtree_satisfies(path.push_tail(i), f),
    {
    }

    pub open spec fn implies(
        f: spec_fn(T, TreePath<N>) -> bool,
        g: spec_fn(T, TreePath<N>) -> bool,
    ) -> bool {
        forall|value: T, path: TreePath<N>|
            value.inv() ==> f(value, path) ==> #[trigger] g(value, path)
    }

    pub proof fn lemma_subtree_satisfies_implies(
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
                #![trigger self.has_child(i)]
                0 <= i < self.children().len() && self.has_child(i) implies self.child(
                i,
            ).subtree_satisfies(path.push_tail(i), g) by {
                self.child(i).lemma_subtree_satisfies_implies(path.push_tail(i), f, g);
            }
        }
    }

    /// If `f(T::default(lv), path)`, then  `TreeNode::new_default(lv).subtree_satisifies(path,f)`.
    pub proof fn lemma_new_default_subtree_satisfies(
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
    }

    /// If `f(val, path)`, then  `TreeNode::new_val(val,lv).subtree_satisifies(path,f)`.
    pub proof fn lemma_new_val_subtree_satisfies(
        val: T,
        lv: nat,
        path: TreePath<N>,
        f: spec_fn(T, TreePath<N>) -> bool,
    )
        requires
            Self::new_val(val, lv).inv(),
            f(val, path),
        ensures
            Self::new_val(val, lv).subtree_satisfies(path, f),
    {
    }

    /// Proves `subtree_satisfies(self, path, g)` from two source predicates `f1`, `f2`,
    /// and the implication `forall |v, p| v.inv() && f1(v, p) && f2(v, p) ==> g(v, p)`.
    pub proof fn lemma_subtree_satisfies_implies_and(
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
                0 <= i < self.children().len() && self.has_child(i) implies self.child(
                i,
            ).subtree_satisfies(path.push_tail(i), g) by {
                self.child(i).lemma_subtree_satisfies_implies_and(path.push_tail(i), f1, f2, g);
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

    pub proof fn lemma_new_default_preserves_inv(lv: nat)
        requires
            0 <= lv < L,
            N > 0,
            forall|i: int| 0 <= i < N ==> #[trigger] T::default(lv).rel_children(i, None),
        ensures
            Self::new_default(lv).inv(),
    {
        T::lemma_default_preserves_inv();
        T::lemma_default_preserves_la_inv();
    }

    /// Insert the child at the given index.
    pub open spec fn insert(self, key: int, node: Self) -> Self
        recommends
            0 <= key < Self::size(),
            node.level() == self.level() + 1,
    {
        Self::new(self.value(), self.level(), self.children().update(key, Some(node)))
    }

    pub broadcast proof fn lemma_insert_preserves_inv(self, key: int, node: Self)
        requires
            self.inv(),
            node.inv(),
            node.level() == self.level() + 1,
            self.value().rel_children(key, Some(node.value())),
        ensures
            #![trigger self.insert(key, node)]
            self.insert(key, node).inv(),
    {
    }

    pub broadcast proof fn lemma_insert_property(self, key: int, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #![trigger self.insert(key, node)]
            self.insert(key, node).value() == self.value(),
            self.insert(key, node).children()[key] == Some(node),
            self.insert(key, node).children() == self.children().update(key, Some(node)),
    {
    }

    pub proof fn lemma_insert_same_child_identical(self, key: int, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.has_child(key),
            self.child(key) == node,
        ensures
            self.insert(key, node) == self,
    {
        self.lemma_insert_property(key, node);
        assert(self.insert(key, node).children() == self.children());
    }

    pub open spec fn remove(self, key: int) -> Self
        recommends
            0 <= key < Self::size(),
    {
        Self::new(self.value(), self.level(), self.children().update(key, None))
    }

    pub broadcast proof fn lemma_remove_preserves_inv(self, key: int)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.children()[key] is None || self.value().rel_children(key, None),
        ensures
            (#[trigger] self.remove(key)).inv(),
    {
    }

    pub broadcast proof fn lemma_remove_property(self, key: int)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #![trigger self.remove(key)]
            self.remove(key).value() == self.value(),
            self.remove(key).children()[key] is None,
            self.remove(key).children() == self.children().update(key, None),
    {
    }

    pub proof fn lemma_insert_child_is_child(self, key: int, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level() < L - 1,
            node.level() == self.level() + 1,
        ensures
            self.insert(key, node).has_child(key),
            self.insert(key, node).child(key) == node,
    {
        self.lemma_insert_property(key, node);
    }

    pub proof fn lemma_remove_child_is_none(self, key: int)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            !self.remove(key).has_child(key),
    {
        self.lemma_remove_property(key);
    }

    pub open spec fn set_value(self, value: T) -> Self
        recommends
            self.inv(),
            value.inv(),
    {
        Self::new(value, self.level(), self.children())
    }

    /// Exposes the observable fields changed and preserved by `set_value`.
    pub broadcast proof fn lemma_set_value_observable_fields(self, value: T)
        ensures
            #![trigger self.set_value(value)]
            (#[trigger] self.set_value(value)).value() == value,
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

    pub open spec fn is_leaf(self) -> bool {
        forall|i: int| 0 <= i < Self::size() ==> !#[trigger] self.has_child(i)
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
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
        decreases path.len(),
    {
        if path.is_empty() {
            self
        } else if path.len() == 1 {
            self.insert(path[0], node)
        } else {
            let (hd, tl) = path.pop_head();
            let child = if self.has_child(hd) {
                self.child(hd)
            } else {
                TreeNode::new_default(self.level() + 1)
            };
            let updated_child = child.recursive_insert(tl, node);
            self.insert(hd, updated_child)
        }
    }

    pub proof fn lemma_recursive_insert_path_empty_identical(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            node.inv(),
            path.inv(),
            path.is_empty(),
        ensures
            self.recursive_insert(path, node) == self,
    {
    }

    pub proof fn lemma_recursive_insert_path_len_1(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            node.inv(),
            path.inv(),
            path.len() == 1,
            1 < L - self.level(),
            node.level() == self.level() + 1,
        ensures
            self.recursive_insert(path, node) == self.insert(path[0], node),
    {
    }

    pub proof fn lemma_recursive_insert_path_len_step(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
            path.len() > 1,
        ensures
            self.has_child(path[0]) ==> self.recursive_insert(path, node) == self.insert(
                path[0],
                self.child(path[0]).recursive_insert(path.pop_head().1, node),
            ),
            !self.has_child(path[0]) ==> self.recursive_insert(path, node) == self.insert(
                path[0],
                TreeNode::new_default(self.level() + 1).recursive_insert(path.pop_head().1, node),
            ),
    {
    }

    pub proof fn lemma_recursive_insert_preserves_level(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
            forall|lv: nat|
                lv < L ==> #[trigger] T::default(lv).rel_children(path.pop_tail().0 as int, None),
        ensures
            self.recursive_insert(path, node).level() == self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
            self.lemma_recursive_insert_path_empty_identical(path, node);
        } else if path.len() == 1 {
            path.lemma_index_satisfies_elem_inv(0);
            self.lemma_recursive_insert_path_len_1(path, node);
            assert(self.insert(path[0], node).level() == self.level());
        } else {
            self.lemma_recursive_insert_path_len_step(path, node);
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                let c = self.child(hd);
                assert(self.insert(hd, c.recursive_insert(tl, node)).level() == self.level());
            } else {
                let c = TreeNode::new_default(self.level() + 1);
                assert(self.insert(hd, c.recursive_insert(tl, node)).level() == self.level());
            }
        }
    }

    pub proof fn lemma_recursive_insert_preserves_value(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level(),
            node.level() == self.level() + path.len() as nat,
            forall|lv: nat, i: int|
                lv < L && 0 <= i < N ==> #[trigger] T::default(lv).rel_children(i, None),
        ensures
            self.recursive_insert(path, node).value() == self.value(),
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
            if self.has_child(hd) {
                let c = self.child(hd);
                c.lemma_recursive_insert_preserves_value(tl, node);
            } else {
                let c = TreeNode::new_default(self.level() + 1);
                Self::lemma_new_default_preserves_inv(self.level() + 1);
                c.lemma_recursive_insert_preserves_value(tl, node);
            }
        }
    }

    pub proof fn lemma_recursive_insert_preserves_inv(self, path: TreePath<N>, node: Self)
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
            self.recursive_insert(path, node).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
            self.lemma_recursive_insert_path_empty_identical(path, node);
        } else if path.len() == 1 {
            path.lemma_index_satisfies_elem_inv(0);
            self.lemma_recursive_insert_path_len_1(path, node);
            self.lemma_insert_preserves_inv(path[0], node);
        } else {
            self.lemma_recursive_insert_path_len_step(path, node);
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                let c = self.child(hd);
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
            if self.has_child(hd) {
                seq![self.value()].add(self.child(hd).recursive_trace(tl))
            } else {
                seq![self.value()]
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
            if self.has_child(hd) {
                self.child(hd).lemma_recursive_trace_length(tl);
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
            if self.has_child(hd1) {
                path1.lemma_pop_head_preserves_inv();
                path2.lemma_pop_head_preserves_inv();
                self.child(hd1).lemma_recursive_trace_up_to(tl1, tl2, n - 1);
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
            if self.has_child(hd) {
                self.child(hd).recursive_seek(tl)
            } else {
                None
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
            if self.has_child(hd) {
                path.lemma_pop_head_preserves_inv();
                self.child(hd).lemma_recursive_seek_trace_length(tl)
            }
        }
    }

    pub proof fn lemma_recursive_seek_trace_next(self, path: TreePath<N>, idx: usize)
        requires
            self.recursive_seek(path) is Some,
            self.recursive_seek(path)->0.has_child(idx as int),
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            0 <= idx < N,
        ensures
            self.recursive_trace(path.push_tail(idx as int)).len() == path.len() + 2,
            self.recursive_seek(path)->0.child(idx as int).value() == self.recursive_trace(
                path.push_tail(idx as int),
            )[path.len() as int + 1],
        decreases path.len(),
    {
        let path2 = path.push_tail(idx as int);

        if path.len() == 0 {
            assert(self.recursive_trace(path2) == seq![
                self.value(),
                self.child(idx as int).value(),
            ]) by { reveal_with_fuel(TreeNode::recursive_trace, 2) }
        } else {
            let (_, tl1) = path.pop_head();
            let (hd2, tl2) = path2.pop_head();
            assert(tl2 == tl1.push_tail(idx as int)) by {}
            assert(tl1.inv()) by { path.lemma_pop_head_preserves_inv() }
            if self.has_child(hd2) {
                self.child(hd2).lemma_recursive_seek_trace_next(tl1, idx);
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
            if self.has_child(path[0]) {
                seq![self.child(path[0])]
            } else {
                Seq::empty()
            }
        } else {
            let (hd, tl) = path.pop_head();
            if self.has_child(hd) {
                let child = self.child(hd);
                seq![child].add(child.recursive_visit(tl))
            } else {
                Seq::empty()
            }
        }
    }

    pub proof fn lemma_recursive_visited_node_inv(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        ensures
            forall|i: int|
                0 <= i < self.recursive_visit(path).len() ==> #[trigger] self.recursive_visit(
                    path,
                )[i].inv(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
            if self.has_child(path[0]) {
            }
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                let c = self.child(hd);
                assert(self.recursive_visit(path) == seq![c].add(c.recursive_visit(tl)));
                c.lemma_recursive_visited_node_inv(tl);
            }
        }
    }

    pub proof fn lemma_recursive_visited_node_levels(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        ensures
            forall|i: int|
                0 <= i < self.recursive_visit(path).len() ==> #[trigger] self.recursive_visit(
                    path,
                )[i].level() == self.level() + i + 1,
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
            if self.has_child(path[0]) {
            }
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                let c = self.child(hd);
                assert(self.recursive_visit(path) == seq![c].add(c.recursive_visit(tl)));
                c.lemma_recursive_visited_node_levels(tl);
            }
        }
    }

    pub proof fn lemma_recursive_visit_head(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            !path.is_empty(),
            self.recursive_visit(path).len() > 0,
        ensures
            self.recursive_visit(path)[0] == self.child(path[0]),
    {
    }

    pub proof fn lemma_recursive_visit_induction(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            !path.is_empty(),
            self.recursive_visit(path).len() > 0,
        ensures
            self.recursive_visit(path) == seq![self.child(path.pop_head().0)].add(
                self.child(path.pop_head().0).recursive_visit(path.pop_head().1),
            ),
    {
        if path.len() == 1 {
            path.lemma_pop_head_preserves_inv();
        } else {
            let (hd, _) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                self.lemma_recursive_visit_head(path);
            }
        }
    }

    pub proof fn lemma_recursive_visit_one_is_child(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
            path.len() == 1,
        ensures
            self.has_child(path[0]) ==> self.recursive_visit(path) == seq![self.child(path[0])],
            !self.has_child(path[0]) ==> self.recursive_visit(path) == seq![],
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

    pub broadcast proof fn lemma_child_on_subtree(self, key: int)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.has_child(key),
        ensures
            #[trigger] self.on_subtree(self.child(key)),
    {
        assert(TreePath::<N>::new(seq![key]).inv());
    }

    pub broadcast proof fn lemma_insert_on_subtree(self, key: int, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level() < L - 1,
            node.level() == self.level() + 1,
            self.value().rel_children(key, Some(node.value())),
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
            self.remove(path[0])
        } else {
            let (hd, tl) = path.pop_head();
            if self.children()[hd as int] is None {
                self
            } else {
                let child = self.child(hd);
                let updated_child = child.recursive_remove(tl);
                self.insert(hd, updated_child)
            }
        }
    }

    pub proof fn lemma_recursive_remove_preserves_level(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        ensures
            self.recursive_remove(path).level() == self.level(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                let c = self.child(hd);
                c.lemma_recursive_remove_preserves_level(tl);
            }
        }
    }

    pub proof fn lemma_recursive_remove_preserves_value(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level(),
        ensures
            self.recursive_remove(path).value() == self.value(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                let c = self.child(hd);
                c.lemma_recursive_remove_preserves_value(tl);
            }
        }
    }

    pub proof fn lemma_recursive_remove_preserves_inv(self, path: TreePath<N>)
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
            self.recursive_remove(path).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
        } else if path.len() == 1 {
            self.lemma_remove_preserves_inv(path[0]);
        } else {
            let (hd, tl) = path.pop_head();
            path.lemma_pop_head_preserves_inv();
            if self.has_child(hd) {
                let c = self.child(hd);
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
    if src.inv() && dst.inv() && dst.level() >= src.level() && dst.level() < L && src.on_subtree(
        dst,
    ) {
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

pub broadcast proof fn lemma_path_between_properties<
    T: TreeNodeValue<L>,
    const N: usize,
    const L: usize,
>(src: TreeNode<T, N, L>, dst: TreeNode<T, N, L>)
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
            (#[trigger] Self::new()).inv(),
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
            self.seek(path)->0.has_child(idx as int),
            self.inv(),
            path.inv(),
            path.len() < L,
            0 <= idx < N,
        ensures
            self.trace(path.push_tail(idx as int)).len() == path.len() + 2,
            self.seek(path)->0.child(idx as int).value() == self.trace(
                path.push_tail(idx as int),
            )[path.len() as int + 1],
    {
        self.root.lemma_recursive_seek_trace_next(path, idx)
    }

    pub broadcast proof fn lemma_insert_preserves_inv(
        self,
        path: TreePath<N>,
        node: TreeNode<T, N, L>,
    )
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L,
            node.level() == path.len() as nat,
            self.seek(path.pop_tail().1) is Some ==> self.seek(
                path.pop_tail().1,
            )->0.value().rel_children(path[path.len() - 1] as int, Some(node.value())),
            self.seek(path.pop_tail().1) is None ==> T::default(
                (path.len() - 1) as nat,
            ).rel_children(path[path.len() - 1] as int, Some(node.value())),
            forall|lv: nat, i: int|
                lv < L ==> 0 <= i < N ==> #[trigger] T::default(lv).rel_children(i, None),
        ensures
            (#[trigger] self.insert(path, node)).inv(),
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
            )->0.value().rel_children(path[path.len() - 1] as int, None),
        ensures
            (#[trigger] self.remove(path)).inv(),
    {
        self.root.lemma_recursive_remove_preserves_inv(path);
    }

    pub broadcast proof fn lemma_visited_nodes_inv(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L,
        ensures
            #![trigger self.visit(path)]
            forall|i: int|
                0 <= i < self.visit(path).len() ==> #[trigger] self.visit(path)[i].inv(),
    {
        self.root.lemma_recursive_visited_node_inv(path);
    }

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
            (#[trigger] self.get_path(node)).inv(),
            self.get_path(node).len() == node.level(),
            node.level() == 0 ==> self.get_path(node).is_empty(),
            node.level() > 0 ==> self.visit(self.get_path(node)).last() == node,
    {
        lemma_path_between_properties(self.root, node);
    }
}

} // verus!
verus! {

pub broadcast group group_ghost_tree_lemmas {
    TreePath::lemma_index_satisfies_elem_inv,
    TreePath::lemma_empty_satisfies_inv,
    TreePath::lemma_pop_head_preserves_inv,
    TreePath::lemma_pop_head_index,
    TreePath::lemma_pop_tail_preserves_inv,
    TreePath::lemma_pop_tail_index,
    TreePath::lemma_push_head_index,
    TreePath::lemma_push_head_preserves_inv,
    TreePath::lemma_push_tail_len,
    TreePath::lemma_push_tail_index,
    TreePath::lemma_push_tail_preserves_inv,
    TreePath::lemma_new_preserves_inv,
    TreeNode::lemma_new_properties,
    TreeNode::lemma_new_val_properties,
    TreeNode::lemma_ext_equal,
    TreeNode::lemma_insert_preserves_inv,
    TreeNode::lemma_insert_property,
    TreeNode::lemma_remove_preserves_inv,
    TreeNode::lemma_remove_property,
    TreeNode::lemma_set_value_observable_fields,
    TreeNode::lemma_is_leaf_bounded,
    TreeNode::lemma_on_subtree_property,
    TreeNode::lemma_not_on_subtree_property,
    TreeNode::lemma_on_subtree_reflexive,
    TreeNode::lemma_child_on_subtree,
    TreeNode::lemma_insert_on_subtree,
    lemma_path_between_properties,
}

} // verus!
