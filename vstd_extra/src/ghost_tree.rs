use vstd::prelude::*;

verus! {

/// Path from the current node to the leaf of the tree
/// `N` is the maximum number of children of a tree node
/// `TreePath.index(i)` returns the `i`-th element of the path
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

    pub open spec fn elem_inv(e: usize) -> bool {
        0 <= e < N
    }

    pub open spec fn inv(self) -> bool {
        forall|i: int| 0 <= i < self.len() ==> Self::elem_inv(#[trigger] self.index(i))
    }

    pub broadcast proof fn inv_property(self)
        requires
            #[trigger] self.inv(),
        ensures
            forall|i: int| 0 <= i < self.len() ==> #[trigger] Self::elem_inv(self.index(i)),
    {
    }

    pub broadcast proof fn index_satisfies_elem_inv(self, i: int)
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

    pub broadcast proof fn empty_satisfies_inv(self)
        requires
            #[trigger] self.is_empty(),
        ensures
            #[trigger] self.inv(),
    {
    }

    pub broadcast proof fn drop_head_property(self)
        requires
            !#[trigger] self.is_empty(),
        ensures
            self.0.drop_first().len() == self.len() - 1,
            forall|i: int|
                0 <= i < self.0.drop_first().len() ==> #[trigger] self.0.drop_first().index(i)
                    == self.index(i + 1),
    {
    }

    pub broadcast proof fn drop_last_property(self)
        requires
            !#[trigger] self.is_empty(),
        ensures
            self.0.drop_last().len() == self.len() - 1,
            forall|i: int|
                0 <= i < self.0.drop_last().len() ==> #[trigger] self.0.drop_last().index(i)
                    == self.index(i),
    {
    }

    pub open spec fn pop_head(self) -> (usize, TreePath<N>)
        recommends
            !self.is_empty(),
    {
        (self.index(0), TreePath(self.0.drop_first()))
    }

    pub broadcast proof fn pop_head_preserves_inv(self)
        requires
            #[trigger] self.inv(),
            !self.is_empty(),
        ensures
            Self::elem_inv(self.pop_head().0),
            self.pop_head().1.inv(),
    {
        let (hd, s1) = self.pop_head();
        assert(0 <= hd < N);
        assert(forall|i: int| 0 <= i < s1.len() ==> s1.index(i) == self.index(i + 1));
        assert(s1.inv());
    }

    pub broadcast proof fn pop_head_decreases_len(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #[trigger] self.pop_head().1.len() == self.len() - 1,
    {
    }

    pub broadcast proof fn pop_head_head_satisfies_inv(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #[trigger] Self::elem_inv(self.pop_head().0),
    {
    }

    pub broadcast proof fn pop_head_property(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #[trigger] self.pop_head().0 == self.index(0),
            self.pop_head().1.len() == self.len() - 1,
            Self::elem_inv(self.pop_head().0),
            self.pop_head().1.inv(),
    {
        self.pop_head_preserves_inv();
    }

    pub open spec fn pop_tail(self) -> (usize, TreePath<N>)
        recommends
            !self.is_empty(),
    {
        (self.index(self.len() as int - 1), TreePath(self.0.drop_last()))
    }

    pub broadcast proof fn pop_tail_preserves_inv(self)
        requires
            #[trigger] self.inv(),
            !self.is_empty(),
        ensures
            Self::elem_inv(self.pop_tail().0),
            self.pop_tail().1.inv(),
    {
        let (tl, s1) = self.pop_tail();
        assert(Self::elem_inv(tl));
        if s1.is_empty() {
            assert(s1.inv());
        } else {
            assert(forall|i: int| 0 <= i < s1.len() ==> s1.index(i) == self.index(i));
            assert(s1.inv());
        }
    }

    pub broadcast proof fn pop_tail_decreases_len(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #[trigger] self.pop_tail().1.len() == self.len() - 1,
    {
    }

    pub broadcast proof fn pop_tail_tail_satisfies_inv(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #[trigger] Self::elem_inv(self.pop_tail().0),
    {
    }

    pub broadcast proof fn pop_tail_property(self)
        requires
            self.inv(),
            !self.is_empty(),
        ensures
            #[trigger] self.pop_tail().0 == self.index(self.len() as int - 1),
            self.pop_tail().1.len() == self.len() - 1,
            Self::elem_inv(self.pop_tail().0),
            self.pop_tail().1.inv(),
    {
        self.pop_tail_preserves_inv();
    }

    pub open spec fn push_head(self, hd: usize) -> TreePath<N>
        recommends
            0 <= hd < N,
    {
        TreePath(seq![hd].add(self.0))
    }

    pub proof fn push_head_property_len(self, hd: usize)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            self.push_head(hd).len() == self.len() + 1,
    {
    }

    pub proof fn push_head_property_index(self, hd: usize)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            self.push_head(hd).index(0) == hd,
            forall|i: int| 0 <= i < self.len() ==> self.push_head(hd).index(i + 1) == self.index(i),
    {
    }

    pub proof fn push_head_preserves_inv(self, hd: usize)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            self.push_head(hd).inv(),
    {
        let s1 = self.push_head(hd);
        assert(s1.len() == self.len() + 1);
        assert(s1.index(0) == hd);
        assert forall|i: int| 0 <= i < s1.len() implies Self::elem_inv(#[trigger] s1.index(i)) by {
            if i == 0 {
                assert(Self::elem_inv(hd));
            } else {
                assert(s1.index(i) == self.index(i - 1));
                assert(Self::elem_inv(self.index(i - 1)));
            }
        }
    }

    pub broadcast proof fn push_head_property(self, hd: usize)
        requires
            self.inv(),
            0 <= hd < N,
        ensures
            #[trigger] self.push_head(hd).inv(),
            self.push_head(hd).len() == self.len() + 1,
            self.push_head(hd).index(0) == hd,
            forall|i: int| 0 <= i < self.len() ==> self.push_head(hd).index(i + 1) == self.index(i),
    {
        self.push_head_property_len(hd);
        self.push_head_property_index(hd);
        self.push_head_preserves_inv(hd);
    }

    pub open spec fn push_tail(self, val: usize) -> TreePath<N>
        recommends
            0 <= val < N,
    {
        TreePath(self.0.push(val))
    }

    pub proof fn push_tail_property_len(self, val: usize)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            self.push_tail(val).len() == self.len() + 1,
    {
    }

    pub proof fn push_tail_property_index(self, val: usize)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            self.push_tail(val).index(self.len() as int) == val,
            forall|i: int|
                0 <= i < self.len() ==> #[trigger] self.push_tail(val).index(i) == self.index(i),
    {
    }

    pub proof fn push_tail_preserves_inv(self, val: usize)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            self.push_tail(val).inv(),
    {
        let s1 = self.push_tail(val);
        assert(s1.len() == self.len() + 1);
        assert(s1.index(self.len() as int) == val);
        assert forall|i: int| 0 <= i < s1.len() implies Self::elem_inv(#[trigger] s1.index(i)) by {
            if i == self.len() {
                assert(Self::elem_inv(val));
            } else {
                assert(s1.index(i) == self.index(i));
                assert(Self::elem_inv(self.index(i)));
            }
        }
    }

    pub broadcast proof fn push_tail_property(self, val: usize)
        requires
            self.inv(),
            0 <= val < N,
        ensures
            #[trigger] self.push_tail(val).inv(),
            self.push_tail(val).len() == self.len() + 1,
            self.push_tail(val).index(self.len() as int) == val,
            forall|i: int|
                0 <= i < self.len() ==> #[trigger] self.push_tail(val).index(i) == self.index(i),
    {
        self.push_tail_property_len(val);
        self.push_tail_property_index(val);
        self.push_tail_preserves_inv(val);
    }

    pub open spec fn new(path: Seq<usize>) -> TreePath<N>
        recommends
            forall|i: int| 0 <= i < path.len() ==> Self::elem_inv(#[trigger] path[i]),
    {
        TreePath(path)
    }

    pub broadcast proof fn new_preserves_inv(path: Seq<usize>)
        requires
            forall|i: int| 0 <= i < path.len() ==> Self::elem_inv(#[trigger] path[i]),
        ensures
            #[trigger] Self::new(path).inv(),
    {
    }

    pub broadcast proof fn new_empty_preserves_inv()
        ensures
            #[trigger] Self::new(Seq::empty()).inv(),
    {
    }
}

} // verus!
verus! {

pub trait TreeNodeValue: Sized {
    spec fn default() -> Self;

    spec fn inv(&self) -> bool;

    proof fn default_preserves_inv()
        ensures
            #[trigger] Self::default().inv(),
    ;
}

} // verus!
verus! {

/// A ghost tree node with maximum `N` children,
/// the maximum depth of the tree is `L`
/// Each tree node has a value of type `T` and a sequence of children
pub tracked struct Node<T: TreeNodeValue, const N: usize, const L: usize> {
    pub tracked value: T,
    pub ghost level: nat,
    pub tracked children: Seq<Option<Node<T, N, L>>>,
}

impl<T: TreeNodeValue, const N: usize, const L: usize> Node<T, N, L> {
    #[verifier::inline]
    pub open spec fn size() -> nat {
        N as nat
    }

    #[verifier::inline]
    pub open spec fn max_depth() -> nat {
        L as nat
    }

    pub proof fn borrow_value(tracked &self) -> (tracked res: &T)
        ensures
            *res == self.value,
    {
        &self.value
    }

    pub axiom fn axiom_size_positive()
        ensures
            Self::size() > 0,
    ;

    pub axiom fn axiom_max_depth_positive()
        ensures
            Self::max_depth() > 0,
    ;

    pub open spec fn inv_node(self) -> bool {
        &&& self.value.inv()
        &&& self.level < L
        &&& self.children.len() == Self::size()
    }

    pub open spec fn inv_children(self) -> bool {
        if self.level == L - 1 {
            forall|i: int| 0 <= i < Self::size() ==> #[trigger] self.children[i].is_none()
        } else {
            forall|i: int|
                0 <= i < Self::size() ==> match #[trigger] self.children[i] {
                    Some(child) => child.level == self.level + 1,
                    None => true,
                }
        }
    }

    pub open spec fn inv(self) -> bool
        decreases (L - self.level),
    {
        &&& self.inv_node()
        &&& self.inv_children()
        &&& if L - self.level == 1 {
            // leaf nodes
            true
        } else {
            // pass invariants to children
            forall|i: int|
                0 <= i < Self::size() ==> match #[trigger] self.children[i] {
                    Some(child) => child.inv(),
                    None => true,
                }
        }
    }

    pub open spec fn new(lv: nat) -> Self {
        Node { value: T::default(), level: lv, children: Seq::new(N as nat, |i| None) }
    }

    pub broadcast proof fn new_preserves_inv(lv: nat)
        requires
            lv < L,
        ensures
            #[trigger] Self::new(lv).inv(),
    {
        let n = Self::new(lv);
        T::default_preserves_inv();
        assert(n.value.inv());
        assert(n.level < L);
        assert(n.children.len() == Self::size());
    }

    pub open spec fn insert(self, key: usize, node: Self) -> Self
        recommends
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level < L - 1,
            node.level == self.level + 1,
    {
        Node { children: self.children.update(key as int, Some(node)), ..self }
    }

    pub broadcast proof fn insert_preserves_inv(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level < L - 1,
            node.level == self.level + 1,
        ensures
            #[trigger] self.insert(key, node).inv(),
    {
    }

    pub broadcast proof fn insert_property(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level < L - 1,
            node.level == self.level + 1,
        ensures
            #[trigger] self.insert(key, node).value == self.value,
            self.insert(key, node).children[key as int] == Some(node),
            forall|i: int|
                0 <= i < Self::size() && i != key ==> #[trigger] self.insert(key, node).children[i]
                    == self.children[i],
    {
    }

    pub broadcast proof fn insert_same_child_identical(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.child(key) == Some(node),
        ensures
            #[trigger] self.insert(key, node) == self,
    {
        self.child_some_properties(key);
        self.insert_property(key, node);
        assert(self.insert(key, node).value == self.value);
        assert(self.insert(key, node).level == self.level);
        assert(self.insert(key, node).children =~= self.children);
    }

    pub open spec fn remove(self, key: usize) -> Self
        recommends
            0 <= key < Self::size(),
            self.inv(),
    {
        Node { children: self.children.update(key as int, None), ..self }
    }

    pub broadcast proof fn remove_preserves_inv(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #[trigger] self.remove(key).inv(),
    {
    }

    pub broadcast proof fn remove_property(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #[trigger] self.remove(key).value == self.value,
            self.remove(key).children[key as int].is_none(),
            forall|i: int|
                0 <= i < Self::size() && i != key ==> #[trigger] self.remove(key).children[i]
                    == self.children[i],
    {
    }

    pub open spec fn child(self, key: usize) -> Option<Self>
        recommends
            0 <= key < Self::size(),
            self.inv(),
    {
        self.children[key as int]
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn tracked_child(self, key: usize) -> (res: Option<Self>)
        requires
            0 <= key < Self::size(),
        ensures
            res == self.child(key),
    {
        self.children[key as int]
    }

    pub broadcast proof fn child_property(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #[trigger] self.child(key) == self.children[key as int],
    {
    }

    pub broadcast proof fn child_property_cases(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            self.level == L - 1 ==> #[trigger] self.child(key).is_none(),
            self.level < L - 1 && self.children[key as int].is_none() ==> #[trigger] self.child(
                key,
            ).is_none(),
            self.level < L - 1 && self.children[key as int].is_some() ==> #[trigger] self.child(
                key,
            ).is_some() && self.child(key).unwrap().level == self.level + 1 && self.child(
                key,
            ).unwrap().inv(),
    {
    }

    pub proof fn child_some_properties(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
            self.child(key).is_some(),
        ensures
            self.level < L - 1,
            self.child(key).unwrap().level == self.level + 1,
            self.child(key).unwrap().inv(),
    {
        self.child_property(key);
        self.child_property_cases(key);
    }

    pub broadcast proof fn lemma_insert_child_is_child(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level < L - 1,
            node.level == self.level + 1,
        ensures
            #[trigger] self.insert(key, node).child(key) == Some(node),
    {
        self.insert_property(key, node);
        self.child_property(key);
    }

    pub broadcast proof fn lemma_remove_child_is_none(self, key: usize)
        requires
            0 <= key < Self::size(),
            self.inv(),
        ensures
            #[trigger] self.remove(key).child(key).is_none(),
    {
        self.remove_property(key);
        self.child_property(key);
    }

    pub open spec fn get_value(self) -> T {
        self.value
    }

    pub broadcast proof fn get_value_property(self)
        requires
            self.inv(),
        ensures
            #[trigger] self.get_value() == self.value,
            self.get_value().inv(),
    {
    }

    pub open spec fn set_value(self, value: T) -> Self
        recommends
            self.inv(),
            value.inv(),
    {
        Node { value: value, ..self }
    }

    pub broadcast proof fn set_value_property(self, value: T)
        requires
            self.inv(),
            value.inv(),
        ensures
            #[trigger] self.set_value(value).value == value,
            self.set_value(value).children == self.children,
            self.set_value(value).inv(),
    {
    }

    pub open spec fn is_leaf(self) -> bool {
        forall|i: int| 0 <= i < Self::size() ==> self.children[i].is_none()
    }

    pub broadcast proof fn is_leaf_bounded(self)
        requires
            self.inv(),
            self.level == L - 1,
        ensures
            #[trigger] self.is_leaf(),
    {
    }

    pub open spec fn recursive_insert(self, path: TreePath<N>, node: Self) -> Self
        recommends
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level,
            node.level == self.level + path.len() as nat,
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
                None => Node::new(self.level + 1),
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
            1 < L - self.level,
            node.level == self.level + 1,
        ensures
            #[trigger] self.recursive_insert(path, node) == self.insert(path.index(0), node),
    {
    }

    pub broadcast proof fn lemma_recursive_insert_path_len_step(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level,
            node.level == self.level + path.len() as nat,
            path.len() > 1,
        ensures
            self.child(path.index(0)).is_some() ==> #[trigger] self.recursive_insert(path, node)
                == self.insert(
                path.index(0),
                self.child(path.index(0)).unwrap().recursive_insert(path.pop_head().1, node),
            ),
            self.child(path.index(0)).is_none() ==> #[trigger] self.recursive_insert(path, node)
                == self.insert(
                path.index(0),
                Node::new(self.level + 1).recursive_insert(path.pop_head().1, node),
            ),
    {
    }

    pub broadcast proof fn lemma_recursive_insert_preserves_inv(self, path: TreePath<N>, node: Self)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L - self.level,
            node.level == self.level + path.len() as nat,
        ensures
            #[trigger] self.recursive_insert(path, node).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
            self.lemma_recursive_insert_path_empty_identical(path, node);
        } else if path.len() == 1 {
            path.index_satisfies_elem_inv(0);
            self.lemma_recursive_insert_path_len_1(path, node);
            assert(self.recursive_insert(path, node).inv());
        } else {
            self.lemma_recursive_insert_path_len_step(path, node);
            let (hd, tl) = path.pop_head();
            path.pop_head_preserves_inv();
            assert(tl.inv());
            if self.child(hd).is_some() {
                let c = self.child(hd).unwrap();
                assert(c.inv());
                c.lemma_recursive_insert_preserves_inv(tl, node);
            } else {
                let c = Node::new(self.level + 1);
                Self::new_preserves_inv(self.level + 1);
                assert(c.inv());
                c.lemma_recursive_insert_preserves_inv(tl, node);
            }
            assert(self.recursive_insert(path, node).inv());
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
            path.len() < L - self.level,
        decreases path.len(),
    {
        if path.is_empty() {
            seq![self.value]
        } else {
            let (hd, tl) = path.pop_head();
            match self.child(hd) {
                Some(child) => seq![self.value].add(child.recursive_trace(tl)),
                None => seq![self.value],
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
            path.pop_head_preserves_inv();
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
                    path1.pop_head_preserves_inv();
                    path2.pop_head_preserves_inv();
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
            path.len() < L - self.level,
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
            path.len() < L - self.level,
            self.recursive_seek(path) is Some,
        ensures
            self.recursive_trace(path).len() == path.len() + 1,
        decreases path.len(),
    {
        if path.len() == 0 {
        } else {
            let (hd, tl) = path.pop_head();
            match self.child(hd) {
                None => { assert(false) },
                Some(child) => {
                    path.pop_head_preserves_inv();
                    child.lemma_recursive_seek_trace_length(tl)
                },
            }
        }
    }

    pub proof fn lemma_recursive_seek_trace_next(self, path: TreePath<N>, idx: usize)
        requires
            self.recursive_seek(path) is Some,
            self.recursive_seek(path).unwrap().children[idx as int] is Some,
            self.inv(),
            path.inv(),
            path.len() < L - self.level,
            0 <= idx < N,
        ensures
            self.recursive_trace(path.push_tail(idx)).len() == path.len() + 2,
            self.recursive_seek(path).unwrap().children[idx as int].unwrap().value
                == self.recursive_trace(path.push_tail(idx))[path.len() as int + 1],
        decreases path.len(),
    {
        assert(self.recursive_trace(path).len() == path.len() + 1) by {
            self.lemma_recursive_seek_trace_length(path)
        }
        let path2 = path.push_tail(idx);
        assert(path2.inv()) by {
            path.push_tail_preserves_inv(idx);
        }
        assert(forall|i: int| 0 <= i < path.len() ==> path.0[i] == path2.0[i]);
        assert(self.recursive_trace(path2).len() >= path.len() + 1) by {
            self.lemma_recursive_trace_up_to(path, path2, path.len() as int)
        }

        if path.len() == 0 {
            assert(path.is_empty());
            assert(self.recursive_seek(path) == Some(self));
            assert(self.recursive_trace(path2) =~= seq![
                self.value,
                self.children[idx as int].unwrap().value,
            ]) by { reveal_with_fuel(Node::recursive_trace, 2) }
        } else {
            let (hd1, tl1) = path.pop_head();
            let (hd2, tl2) = path2.pop_head();
            assert(tl2 == tl1.push_tail(idx)) by {
                assert(tl2.0 =~= tl1.0.push(idx));
            }
            assert(tl1.inv()) by { path.pop_head_preserves_inv() }
            match self.child(hd2) {
                None => {},
                Some(child) => {
                    assert(self.recursive_trace(path2) =~= seq![self.value] + child.recursive_trace(
                        tl2,
                    ));
                    child.lemma_recursive_seek_trace_next(tl1, idx);
                    assert(child.recursive_trace(tl2).len() >= path.len() + 1);
                    assert(self.recursive_trace(path2).len() >= path.len() + 2);

                    assert(self.recursive_trace(path2)[path.len() as int + 1]
                        == child.recursive_trace(tl2)[path.len() as int]);
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
            path.len() < L - self.level,
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
            path.len() < L - self.level,
        ensures
            forall|i: int|
                0 <= i < self.recursive_visit(path).len() ==> #[trigger] self.recursive_visit(
                    path,
                ).index(i).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
            assert(self.recursive_visit(path).len() == 0);
        } else if path.len() == 1 {
            if self.child(path.index(0)).is_some() {
                assert(self.recursive_visit(path).len() == 1);
                assert(self.recursive_visit(path).index(0).inv());
            } else {
                assert(self.recursive_visit(path).len() == 0);
            }
        } else {
            let (hd, tl) = path.pop_head();
            path.pop_head_preserves_inv();
            if self.child(hd).is_some() {
                let c = self.child(hd).unwrap();
                assert(c.inv());
                assert(self.recursive_visit(path) =~= seq![c].add(c.recursive_visit(tl)));
                c.lemma_recursive_visited_node_inv(tl);
            } else {
                assert(self.recursive_visit(path).len() == 0);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_visited_node_levels(self, path: TreePath<N>)
        requires
            #[trigger] self.inv(),
            #[trigger] path.inv(),
            path.len() < L - self.level,
        ensures
            forall|i: int|
                0 <= i < self.recursive_visit(path).len() ==> #[trigger] self.recursive_visit(
                    path,
                ).index(i).level == self.level + i + 1,
        decreases path.len(),
    {
        if path.is_empty() {
            assert(self.recursive_visit(path).len() == 0);
        } else if path.len() == 1 {
            if self.child(path.index(0)).is_some() {
                assert(self.recursive_visit(path).len() == 1);
                assert(self.inv());
                assert(self.recursive_visit(path).index(0).level == self.level + 1);
            } else {
                assert(self.recursive_visit(path).len() == 0);
            }
        } else {
            let (hd, tl) = path.pop_head();
            path.pop_head_preserves_inv();
            assert(TreePath::<N>::elem_inv(hd));
            assert(tl.inv());
            if self.child(hd).is_some() {
                let c = self.child(hd).unwrap();
                assert(c.level == self.level + 1);
                assert(c.inv());
                assert(tl.len() == path.len() - 1);
                assert(tl.len() < L - c.level);
                assert(self.recursive_visit(path) =~= seq![c].add(c.recursive_visit(tl)));
                c.lemma_recursive_visited_node_levels(tl);
            } else {
                assert(self.recursive_visit(path).len() == 0);
            }
        }
    }

    pub broadcast proof fn lemma_recursive_visit_head(self, path: TreePath<N>)
        requires
            #[trigger] self.inv(),
            #[trigger] path.inv(),
            path.len() < L - self.level,
            !path.is_empty(),
            self.recursive_visit(path).len() > 0,
        ensures
            self.recursive_visit(path).index(0) == self.child(path.index(0)).unwrap(),
    {
        if path.len() == 0 {
            assert(!path.is_empty());
        } else if path.len() == 1 {
            if self.child(path.index(0)).is_none() {
                assert(self.recursive_visit(path).len() == 0);
            } else {
                assert(self.recursive_visit(path).len() == 1);
                assert(self.recursive_visit(path).index(0) == self.child(path.index(0)).unwrap());
            }
        } else {
            if self.child(path.index(0)).is_none() {
                assert(self.recursive_visit(path).len() == 0);
            } else {
                assert(self.recursive_visit(path).len() > 0);
                assert(self.recursive_visit(path) =~= seq![self.child(path.index(0)).unwrap()].add(
                    self.child(path.index(0)).unwrap().recursive_visit(path.pop_head().1),
                ));
                assert(self.recursive_visit(path).index(0) == self.child(path.index(0)).unwrap());
            }
        }
    }

    // #[verifier::external_body]
    pub broadcast proof fn lemma_recursive_visit_induction(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level,
            !path.is_empty(),
            self.recursive_visit(path).len() > 0,
        ensures
            #[trigger] self.recursive_visit(path) == seq![
                self.child(path.pop_head().0).unwrap(),
            ].add(self.child(path.pop_head().0).unwrap().recursive_visit(path.pop_head().1)),
    {
        assert(path.len() > 0);
        if path.len() == 1 {
            let (hd, tl) = path.pop_head();
            path.pop_head_preserves_inv();
            path.pop_head_property();
            assert(tl.len() == 0);
            assert(TreePath::<N>::elem_inv(hd));
            assert(tl.inv());
            let c = self.child(hd);
            if c.is_none() {
                assert(self.recursive_visit(path).len() == 0);
            } else {
                let c = c.unwrap();
                assert(c.level == self.level + 1);
                assert(self.recursive_visit(path).len() == 1);
                assert(self.recursive_visit(path).index(0) == c);
                assert(c.inv());
                assert(c.recursive_visit(tl) =~= seq![]);
                assert(self.recursive_visit(path) == seq![c].add(c.recursive_visit(tl)));
            }
        } else {
            let (hd, tl) = path.pop_head();
            path.pop_head_preserves_inv();
            path.pop_head_property();
            assert(TreePath::<N>::elem_inv(hd));
            assert(tl.inv());

            let c = self.child(hd);
            if c.is_none() {
                assert(self.recursive_visit(path).len() == 0);
            } else {
                let c = c.unwrap();
                assert(self.recursive_visit(path).len() > 0);
                self.lemma_recursive_visit_head(path);
                assert(self.recursive_visit(path).index(0) == c);
                assert(c.inv());
                assert(c.level == self.level + 1);
                assert(tl.inv());
                assert(tl.len() > 0);
                assert(tl.len() == path.len() - 1);
                assert(self.recursive_visit(path) =~= seq![c].add(c.recursive_visit(tl)));
            }
        }
    }

    pub broadcast proof fn lemma_recursive_visit_one_is_child(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level,
            path.len() == 1,
        ensures
            self.child(path.index(0)).is_some() ==> #[trigger] self.recursive_visit(path) =~= seq![
                self.child(path.index(0)).unwrap(),
            ],
            self.child(path.index(0)).is_none() ==> #[trigger] self.recursive_visit(path)
                =~= seq![],
    {
        if self.child(path.index(0)).is_none() {
            assert(self.recursive_visit(path).len() == 0);
        } else {
            assert(self.recursive_visit(path).len() == 1);
            assert(self.recursive_visit(path).index(0) == self.child(path.index(0)).unwrap());
        }
    }

    // pub broadcast proof fn lemma_recursive_visit_step(self, path: TreePath<N>)
    //     requires
    //         self.inv(),
    //         path.inv(),
    //         path.len() < L - self.level,
    //         path.len() > 1,
    //         self.recursive_visit(path).len() == path.len(),
    //     ensures
    //         #[trigger]
    //         self.recursive_visit(path.pop_tail().1) =~= self.recursive_visit(path).drop_last(),
    //         self.recursive_visit(path.pop_tail().1).last().child(path.pop_tail().0) == Some(self.recursive_visit(path).last()),
    // {
    //     admit();
    // }
    pub open spec fn on_subtree(self, node: Self) -> bool
        recommends
            self.inv(),
            node.inv(),
            node.level >= self.level,
            node.level < L,
    {
        node == self || exists|path: TreePath<N>| #[trigger]
            path.inv() && path.len() > 0 && path.len() == node.level - self.level
                && self.recursive_visit(path).last() == node
    }

    pub broadcast proof fn on_subtree_property(self, node: Self)
        requires
            self.inv(),
            node.inv(),
            node.level >= self.level,
            node.level < L,
            #[trigger] self.on_subtree(node),
        ensures
            node.level == self.level ==> self == node,
            node.level > self.level ==> exists|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level - self.level && self.recursive_visit(
                    path,
                ).last() == node,
    {
    }

    pub broadcast proof fn not_on_subtree_property(self, node: Self)
        requires
            self.inv(),
            node.inv(),
            node.level < L,
            !#[trigger] self.on_subtree(node),
        ensures
            self != node,
            node.level > self.level ==> forall|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level - self.level ==> self.recursive_visit(
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
            self.child(key).is_some(),
        ensures
            #[trigger] self.on_subtree(self.child(key).unwrap()),
    {
        let path = TreePath::<N>::new(seq![key]);
        let c = self.child(key).unwrap();
        assert(path.inv());
        assert(path.len() == 1);
        assert(self.recursive_visit(path).last() == c);
    }

    pub broadcast proof fn lemma_insert_on_subtree(self, key: usize, node: Self)
        requires
            0 <= key < Self::size(),
            self.inv(),
            node.inv(),
            self.level < L - 1,
            node.level == self.level + 1,
        ensures
            #[trigger] self.insert(key, node).on_subtree(node),
    {
        self.lemma_insert_child_is_child(key, node);
        self.insert(key, node).lemma_child_on_subtree(key);
    }

    // pub broadcast proof fn lemma_remove_not_on_subtree(self, key: usize, node: Self)
    //     requires
    //         0 <= key < Self::size(),
    //         self.inv(),
    //         node.inv(),
    //         node.level == self.level + 1,
    //         self.child(key) == Some(node),
    //     ensures
    //         !#[trigger] self.remove(key).on_subtree(node),
    // {
    //     admit();  // TODO
    // }
    // pub broadcast proof fn lemma_recursive_insert_on_subtree(self, path: TreePath<N>, node: Self)
    //     requires
    //         self.inv(),
    //         path.inv(),
    //         node.inv(),
    //         path.len() < L - self.level,
    //         node.level == self.level + path.len() as nat,
    //     ensures
    //         #[trigger] self.recursive_insert(path, node).on_subtree(node),
    //     decreases path.len(),
    // {
    //     admit();  // TODO
    // }
    // pub broadcast proof fn lemma_recursive_remove_not_on_subtree(
    //     self,
    //     path: TreePath<N>,
    //     node: Self,
    // )
    //     requires
    //         self.inv(),
    //         path.inv(),
    //         node.inv(),
    //         path.len() < L - self.level,
    //         node.level == self.level + path.len() as nat,
    //         self.recursive_visit(path).last() == node,
    //     ensures
    //         !#[trigger] self.recursive_remove(path).on_subtree(node),
    //     decreases path.len(),
    // {
    //     admit();  // TODO
    // }
    // pub broadcast proof fn lemma_recursive_visit_on_subtree(self, path: TreePath<N>)
    //     requires
    //         self.inv(),
    //         path.inv(),
    //         path.len() < L - self.level,
    //         path.len() > 0,
    //         #[trigger] self.recursive_visit(path).len() > 0,
    //     ensures
    //         forall|i: int|
    //             0 <= i < self.recursive_visit(path).len() ==> #[trigger] self.on_subtree(
    //                 self.recursive_visit(path)[i],
    //             ),
    // {
    //     admit();  // TODO
    // }
    pub proof fn level_increases(self)
        requires
            self.inv(),
            self.level < L,
        ensures
            forall|i: int|
                0 <= i < Self::size() && #[trigger] self.children[i].is_some()
                    ==> self.children[i].unwrap().level > self.level,
    {
        if self.level == Self::max_depth() - 1 {
            assert(self.is_leaf());
        } else {
            assert(self.level < L - 1);
            assert(self.inv_children());
        }
    }

    pub broadcast proof fn remaining_level_decreases(self)
        requires
            #[trigger] self.inv(),
            #[trigger] self.level < L,
        ensures
            forall|i: int|
                0 <= i < Self::size() && #[trigger] self.children[i].is_some() ==> (L
                    - self.children[i].unwrap().level) < (L - self.level),
    {
        self.level_increases();
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
            path.len() < L - self.level,
        decreases path.len(),
    {
        if path.is_empty() {
            self
        } else if path.len() == 1 {
            self.remove(path.index(0))
        } else {
            let (hd, tl) = path.pop_head();
            if self.child(hd).is_none() {
                self
            } else {
                let child = self.child(hd).unwrap();
                let updated_child = child.recursive_remove(tl);
                self.insert(hd, updated_child)
            }
        }
    }

    pub broadcast proof fn lemma_recursive_remove_preserves_inv(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L - self.level,
        ensures
            #[trigger] self.recursive_remove(path).inv(),
        decreases path.len(),
    {
        if path.is_empty() {
            assert(self.recursive_remove(path).inv());
        } else if path.len() == 1 {
            path.index_satisfies_elem_inv(0);
            self.remove_preserves_inv(path.index(0));
            assert(self.recursive_remove(path).inv());
        } else {
            let (hd, tl) = path.pop_head();
            path.pop_head_preserves_inv();
            if self.child(hd).is_some() {
                let c = self.child(hd).unwrap();
                assert(c.inv());
                c.lemma_recursive_remove_preserves_inv(tl);
                assert(self.recursive_remove(path).inv());
            } else {
                assert(self.recursive_remove(path).inv());
            }
        }
    }
}

} // verus!
verus! {

pub closed spec fn path_between<T: TreeNodeValue, const N: usize, const L: usize>(
    src: Node<T, N, L>,
    dst: Node<T, N, L>,
) -> TreePath<N>
    recommends
        src.inv(),
        dst.inv(),
        src.level <= dst.level,
        src.on_subtree(dst),
{
    if src.inv() && dst.inv() && dst.level >= src.level && dst.level < L && src.on_subtree(dst) {
        if src == dst {
            TreePath::new(seq![])
        } else {
            choose|path: TreePath<N>| #[trigger]
                path.inv() && path.len() > 0 && path.len() == dst.level - src.level
                    && src.recursive_visit(path).last() == dst
        }
    } else {
        vstd::pervasive::arbitrary()
    }
}

pub broadcast proof fn path_between_properties<T: TreeNodeValue, const N: usize, const L: usize>(
    src: Node<T, N, L>,
    dst: Node<T, N, L>,
)
    requires
        src.inv(),
        dst.inv(),
        src.level <= dst.level,
        #[trigger] src.on_subtree(dst),
    ensures
        path_between(src, dst).inv(),
        path_between(src, dst).len() == dst.level - src.level,
        dst.level == src.level ==> path_between(src, dst).is_empty() && src == dst,
        dst.level > src.level ==> src.recursive_visit(path_between(src, dst)).last() == dst,
{
}

} // verus!
verus! {

pub tracked struct Tree<T: TreeNodeValue, const N: usize, const L: usize> {
    pub tracked root: Node<T, N, L>,
}

impl<T: TreeNodeValue, const N: usize, const L: usize> Tree<T, N, L> {
    pub axiom fn axiom_depth_positive()
        ensures
            L > 0,
    ;

    pub axiom fn axiom_size_positive()
        ensures
            N > 0,
    ;

    pub open spec fn inv(self) -> bool {
        &&& self.root.inv()
        &&& self.root.level == 0
    }

    pub open spec fn new() -> Self {
        Tree { root: Node::new(0) }
    }

    pub broadcast proof fn new_preserves_inv()
        ensures
            #[trigger] Self::new().inv(),
    {
        let t = Self::new();
        Self::axiom_depth_positive();
        Node::<T, N, L>::new_preserves_inv(0);
        assert(t.root.inv());
        assert(t.root.level == 0);
    }

    pub open spec fn insert(self, path: TreePath<N>, node: Node<T, N, L>) -> Self
        recommends
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L,
            node.level == path.len() as nat,
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

    pub open spec fn visit(self, path: TreePath<N>) -> Seq<Node<T, N, L>>
        recommends
            self.inv(),
            path.inv(),
            path.len() < L,
        decreases path.len(),
    {
        self.root.recursive_visit(path)
    }

    pub broadcast proof fn visit_is_recursive_visit(self, path: TreePath<N>)
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

    pub broadcast proof fn trace_empty_is_head(self, path: TreePath<N>)
        requires
            path.len() == 0,
        ensures
            #[trigger] self.trace(path) == seq![self.root.value],
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

    pub open spec fn seek(self, path: TreePath<N>) -> Option<Node<T, N, L>> {
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
            self.seek(path).unwrap().children[idx as int] is Some,
            self.inv(),
            path.inv(),
            path.len() < L,
            0 <= idx < N,
        ensures
            self.trace(path.push_tail(idx)).len() == path.len() + 2,
            self.seek(path).unwrap().children[idx as int].unwrap().value == self.trace(
                path.push_tail(idx),
            )[path.len() as int + 1],
    {
        self.root.lemma_recursive_seek_trace_next(path, idx)
    }

    pub broadcast proof fn insert_preserves_inv(self, path: TreePath<N>, node: Node<T, N, L>)
        requires
            self.inv(),
            path.inv(),
            node.inv(),
            path.len() < L,
            node.level == path.len() as nat,
        ensures
            #[trigger] self.insert(path, node).inv(),
    {
        self.root.lemma_recursive_insert_preserves_inv(path, node);
    }

    pub broadcast proof fn remove_preserves_inv(self, path: TreePath<N>)
        requires
            self.inv(),
            path.inv(),
            path.len() < L,
        ensures
            #[trigger] self.remove(path).inv(),
    {
        self.root.lemma_recursive_remove_preserves_inv(path);
    }

    pub broadcast proof fn visited_nodes_inv(self, path: TreePath<N>)
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
    pub open spec fn on_tree(self, node: Node<T, N, L>) -> bool
        recommends
            self.inv(),
            node.inv(),
    {
        self.root.on_subtree(node)
    }

    pub broadcast proof fn on_tree_property(self, node: Node<T, N, L>)
        requires
            self.inv(),
            node.inv(),
            #[trigger] self.on_tree(node),
        ensures
            node.level == 0 ==> self.root == node,
            node.level > 0 ==> exists|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level && self.visit(path).last() == node,
    {
    }

    pub broadcast proof fn not_on_tree_property(self, node: Node<T, N, L>)
        requires
            self.inv(),
            node.inv(),
            !#[trigger] self.on_tree(node),
        ensures
            node != self.root,
            node.level > 0 ==> forall|path: TreePath<N>| #[trigger]
                path.inv() && path.len() == node.level ==> self.visit(path).last() != node,
    {
    }

    #[verifier::inline]
    pub open spec fn get_path(self, node: Node<T, N, L>) -> TreePath<N>
        recommends
            self.inv(),
            node.inv(),
            self.on_tree(node),
    {
        path_between::<T, N, L>(self.root, node)
    }

    pub broadcast proof fn get_path_properties(self, node: Node<T, N, L>)
        requires
            self.inv(),
            node.inv(),
            self.on_tree(node),
        ensures
            #[trigger] self.get_path(node).inv(),
            #[trigger] self.get_path(node).len() == node.level,
            node.level == 0 ==> #[trigger] self.get_path(node).is_empty(),
            node.level > 0 ==> #[trigger] self.visit(self.get_path(node)).last() == node,
    {
        path_between_properties(self.root, node);
    }
}

} // verus!
verus! {

pub broadcast group group_ghost_tree {
    TreePath::inv_property,
    TreePath::index_satisfies_elem_inv,
    TreePath::empty_satisfies_inv,
    TreePath::drop_head_property,
    TreePath::drop_last_property,
    TreePath::pop_head_preserves_inv,
    TreePath::pop_head_decreases_len,
    TreePath::pop_head_head_satisfies_inv,
    TreePath::pop_head_property,
    TreePath::pop_tail_preserves_inv,
    TreePath::pop_tail_decreases_len,
    TreePath::pop_tail_tail_satisfies_inv,
    TreePath::pop_tail_property,
    TreePath::push_head_property,
    TreePath::new_empty_preserves_inv,
    TreePath::new_preserves_inv,
    Node::insert_preserves_inv,
    Node::insert_property,
    Node::insert_same_child_identical,
    Node::remove_preserves_inv,
    Node::remove_property,
    Node::child_property,
    Node::child_property_cases,
    Node::lemma_insert_child_is_child,
    Node::lemma_remove_child_is_none,
    Node::get_value_property,
    Node::set_value_property,
    Node::is_leaf_bounded,
    Node::lemma_recursive_visited_node_inv,
    Node::lemma_recursive_visited_node_levels,
    Node::lemma_recursive_visit_head,
    Node::lemma_recursive_visit_induction,
    Node::lemma_recursive_visit_one_is_child,
    Node::on_subtree_property,
    Node::not_on_subtree_property,
    Node::lemma_on_subtree_reflexive,
    Node::lemma_child_on_subtree,
    Node::lemma_insert_on_subtree,
    // Node::lemma_remove_not_on_subtree,
    // Node::lemma_recursive_insert_on_subtree,
    // Node::lemma_recursive_remove_not_on_subtree,
    // Node::lemma_recursive_visit_on_subtree,
    Node::remaining_level_decreases,
    Node::lemma_recursive_remove_preserves_inv,
    path_between_properties,
    Tree::new_preserves_inv,
    Tree::visit_is_recursive_visit,
    Tree::insert_preserves_inv,
    Tree::remove_preserves_inv,
    Tree::visited_nodes_inv,
    Tree::on_tree_property,
    Tree::not_on_tree_property,
}

} // verus!
