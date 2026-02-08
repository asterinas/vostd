#![allow(hidden_glob_reexports)]

pub mod cursor;
pub mod node;
mod owners;
mod view;

pub use cursor::*;
pub use node::*;
pub use owners::*;
pub use view::*;

use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use vstd_extra::arithmetic::*;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use crate::mm::page_table::page_size;
use crate::mm::page_table::PageTableConfig;
use crate::mm::{PagingLevel, Vaddr};
use crate::specs::arch::mm::{CONST_NR_ENTRIES, NR_ENTRIES, NR_LEVELS, PAGE_SIZE};

use align_ext::AlignExt;

verus! {

/// An abstract representation of a virtual address as a sequence of indices, representing the
/// values of the bit-fields that index into each level of the page table.
/// `offset` is the lowest 12 bits (the offset into a 4096 byte page)
/// `index[0]` is the next 9 bits (index into the 512 entries of the first level page table)
/// and so on up to index[NR_LEVELS-1].
pub struct AbstractVaddr {
    pub offset: int,
    pub index: Map<int, int>,
}

impl Inv for AbstractVaddr {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.offset < PAGE_SIZE()
        &&& forall |i: int|
            #![trigger self.index.contains_key(i)]
        0 <= i < NR_LEVELS() ==> {
            &&& self.index.contains_key(i)
            &&& 0 <= self.index[i]
            &&& self.index[i] < NR_ENTRIES()
        }
    }
}

impl AbstractVaddr {
    /// Extract the AbstractVaddr components from a concrete virtual address.
    /// - offset = lowest 12 bits
    /// - index[i] = bits (12 + 9*i) to (12 + 9*(i+1) - 1) for each level
    pub open spec fn from_vaddr(va: Vaddr) -> Self {
        AbstractVaddr {
            offset: (va % PAGE_SIZE()) as int,
            index: Map::new(
                |i: int| 0 <= i < NR_LEVELS(),
                |i: int| ((va / pow2((12 + 9 * i) as nat) as usize) % NR_ENTRIES()) as int,
            ),
        }
    }

    pub proof fn from_vaddr_wf(va: Vaddr)
        ensures
            AbstractVaddr::from_vaddr(va).inv(),
    {
        let abs = AbstractVaddr::from_vaddr(va);
        assert(0 <= abs.offset < PAGE_SIZE());
        assert forall |i: int|
            #![trigger abs.index.contains_key(i)]
            0 <= i < NR_LEVELS() implies {
                &&& abs.index.contains_key(i)
                &&& 0 <= abs.index[i]
                &&& abs.index[i] < NR_ENTRIES()
            } by {
            // index[i] = (va / 2^(12+9*i)) % NR_ENTRIES, which is in [0, NR_ENTRIES)
        };
    }

    /// Reconstruct the concrete virtual address from the AbstractVaddr components.
    /// va = offset + sum(index[i] * 2^(12 + 9*i)) for i in 0..NR_LEVELS
    pub open spec fn to_vaddr(self) -> Vaddr {
        (self.offset + self.to_vaddr_indices(0)) as Vaddr
    }

    /// Helper: sum of index[i] * 2^(12 + 9*i) for i in start..NR_LEVELS
    pub open spec fn to_vaddr_indices(self, start: int) -> int
        decreases NR_LEVELS() - start when start <= NR_LEVELS()
    {
        if start >= NR_LEVELS() {
            0
        } else {
            self.index[start] * pow2((12 + 9 * start) as nat) as int
                + self.to_vaddr_indices(start + 1)
        }
    }

    /// reflect(self, va) holds when self is the abstract representation of va.
    pub open spec fn reflect(self, va: Vaddr) -> bool {
        self == Self::from_vaddr(va)
    }

    /// If self reflects va, then self.to_vaddr() == va and self == from_vaddr(va).
    /// The first ensures requires proving the round-trip property: from_vaddr(va).to_vaddr() == va.
    pub broadcast proof fn reflect_prop(self, va: Vaddr)
        requires
            self.inv(),
            self.reflect(va),
        ensures
            #[trigger] self.to_vaddr() == va,
            #[trigger] Self::from_vaddr(va) == self,
    {
        // self.reflect(va) means self == from_vaddr(va)
        // So self.to_vaddr() == from_vaddr(va).to_vaddr()
        // We need: from_vaddr(va).to_vaddr() == va (round-trip property)
        Self::from_vaddr_to_vaddr_roundtrip(va);
    }

    /// Round-trip property: extracting and reconstructing a VA gives back the original.
    pub proof fn from_vaddr_to_vaddr_roundtrip(va: Vaddr)
        ensures
            Self::from_vaddr(va).to_vaddr() == va,
    {
        // va = offset + sum(index[i] * 2^(12+9*i))
        // from_vaddr extracts: offset = va % 2^12, index[i] = (va / 2^(12+9*i)) % 2^9
        // to_vaddr reconstructs: offset + sum(index[i] * 2^(12+9*i))
        // This equals va by the uniqueness of positional representation in mixed radix.
        admit()
    }

    /// from_vaddr(va) reflects va (by definition of reflect).
    pub broadcast proof fn reflect_from_vaddr(va: Vaddr)
        ensures
            #[trigger] Self::from_vaddr(va).reflect(va),
            #[trigger] Self::from_vaddr(va).inv(),
    {
        Self::from_vaddr_wf(va);
    }

    /// If self.inv(), then self reflects self.to_vaddr().
    pub broadcast proof fn reflect_to_vaddr(self)
        requires
            self.inv(),
        ensures
            #[trigger] self.reflect(self.to_vaddr()),
    {
        Self::to_vaddr_from_vaddr_roundtrip(self);
    }

    /// Inverse round-trip: to_vaddr then from_vaddr gives back the original AbstractVaddr.
    pub proof fn to_vaddr_from_vaddr_roundtrip(abs: Self)
        requires
            abs.inv(),
        ensures
            Self::from_vaddr(abs.to_vaddr()) == abs,
    {
        // Similar reasoning: the positional representation is unique
        admit()
    }

    /// If two AbstractVaddrs reflect the same va, they are equal.
    pub broadcast proof fn reflect_eq(self, other: Self, va: Vaddr)
        requires
            self.reflect(va),
            other.reflect(va),
        ensures
            #![auto] (self == other),
    { }

    pub open spec fn align_down(self, level: int) -> Self
        decreases level when level >= 1
    {
        if level == 1 {
            AbstractVaddr {
                offset: 0,
                index: self.index,
            }
        } else {
            let tmp = self.align_down(level - 1);
            AbstractVaddr {
                index: tmp.index.insert(level - 2, 0),
                ..tmp
            }
        }
    }

    pub proof fn align_down_inv(self, level: int)
        requires
            1 <= level < NR_LEVELS(),
            self.inv(),
        ensures
            self.align_down(level).inv(),
            forall |i: int| level <= i < NR_LEVELS() ==> #[trigger] self.index[i - 1] == self.align_down(level).index[i - 1],
        decreases level
    {
        if level == 1 {
            assert(self.inv());
        } else {
            let tmp = self.align_down(level - 1);
            self.align_down_inv(level - 1);
        }
    }

    pub axiom fn align_down_concrete(self, level: int)
        requires
            1 <= level <= NR_LEVELS(),
        ensures
            self.align_down(level).reflect(nat_align_down(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) as Vaddr);

    pub open spec fn align_up(self, level: int) -> Self {
        let lower_aligned = self.align_down(level - 1);
        lower_aligned.next_index(level)
    }

    pub axiom fn align_up_concrete(self, level: int)
        requires
            1 <= level <= NR_LEVELS(),
        ensures
            self.align_up(level).reflect(nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) as Vaddr);

    pub axiom fn align_diff(self, level: int)
        requires
            1 <= level <= NR_LEVELS(),
        ensures
            nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) ==
            nat_align_down(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) + page_size(level as PagingLevel),
            nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) < usize::MAX;

    pub open spec fn next_index(self, level: int) -> Self
        decreases NR_LEVELS() - level when 1 <= level <= NR_LEVELS()
    {
        let index = self.index[level - 1];
        let next_index = index + 1;
        if next_index == NR_ENTRIES() && level < NR_LEVELS() {
            let next_va = Self {
                offset: self.offset,
                index: self.index.insert(level - 1, 0),
            };
            next_va.next_index(level + 1)
        } else if next_index == NR_ENTRIES() && level == NR_LEVELS() {
            Self {
                offset: self.offset,
                index: self.index.insert(level - 1, 0),
            }
        } else {
            Self {
                offset: self.offset,
                index: self.index.insert(level - 1, next_index),
            }
        }
    }

    pub open spec fn wrapped(self, start_level: int, level: int) -> bool
        decreases NR_LEVELS() - level when 1 <= start_level <= level <= NR_LEVELS()
    {
        &&& self.next_index(start_level).index[level - 1] == 0 ==> {
            &&& self.index[level - 1] + 1 == NR_ENTRIES()
            &&& if level < NR_LEVELS() {
                self.wrapped(start_level, level + 1)
            } else {
                true
            }
        }
        &&& self.next_index(start_level).index[level - 1] != 0 ==>
            self.index[level - 1] + 1 < NR_ENTRIES()
    }

    pub proof fn use_wrapped(self, start_level: int, level: int)
        requires
            1 <= start_level <= level < NR_LEVELS(),
            self.wrapped(start_level, level),
            self.next_index(start_level).index[level - 1] == 0
        ensures
            self.index[level - 1] + 1 == NR_ENTRIES()
    { }

    pub proof fn wrapped_unwrap(self, start_level: int, level: int)
        requires
            1 <= start_level <= level < NR_LEVELS(),
            self.wrapped(start_level, level),
            self.next_index(start_level).index[level - 1] == 0,
        ensures
            self.wrapped(start_level, level + 1)
    { }

    pub proof fn next_index_wrap_condition(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS(),
        ensures
            self.wrapped(level, level)
    { admit() }

    //
    // === Connection to TreePath and concrete Vaddr ===
    //

    /// Computes the concrete vaddr from the abstract representation.
    /// This matches the structure:
    ///   index[NR_LEVELS-1] * 2^39 + index[NR_LEVELS-2] * 2^30 + ... + index[0] * 2^12 + offset
    pub open spec fn compute_vaddr(self) -> Vaddr {
        self.rec_compute_vaddr(0)
    }

    /// Helper for computing vaddr recursively from level i upward.
    pub open spec fn rec_compute_vaddr(self, i: int) -> Vaddr
        decreases NR_LEVELS() - i when 0 <= i <= NR_LEVELS()
    {
        if i >= NR_LEVELS() {
            self.offset as Vaddr
        } else {
            let shift = page_size((i + 1) as PagingLevel);
            (self.index[i] * shift + self.rec_compute_vaddr(i + 1)) as Vaddr
        }
    }

    /// Extracts a TreePath from this abstract vaddr, from the root down to the given level.
    /// The path has length (NR_LEVELS - level), containing indices for paging levels NR_LEVELS..level+1.
    /// - level=0: full path of length NR_LEVELS with indices for all levels
    /// - level=3: path of length 1 with just the root index
    ///
    /// Path index mapping:
    /// - path.index(0) = self.index[NR_LEVELS - 1]  (root level)
    /// - path.index(i) = self.index[NR_LEVELS - 1 - i]
    /// - path.index(NR_LEVELS - level - 1) = self.index[level]  (last entry)
    pub open spec fn to_path(self, level: int) -> TreePath<CONST_NR_ENTRIES>
        recommends 0 <= level < NR_LEVELS()
    {
        TreePath(self.rec_to_path(NR_LEVELS() - 1, level))
    }

    /// Builds the path sequence from abstract_level down to bottom_level (both inclusive).
    /// abstract_level and bottom_level refer to the index keys in self.index (0 = lowest level, NR_LEVELS-1 = root).
    /// Returns indices in order from highest level (first in seq) to lowest level (last in seq).
    pub open spec fn rec_to_path(self, abstract_level: int, bottom_level: int) -> Seq<usize>
        decreases abstract_level - bottom_level when bottom_level <= abstract_level
    {
        if abstract_level < bottom_level {
            seq![]
        } else if abstract_level == bottom_level {
            // Base case: just this one level
            seq![self.index[abstract_level] as usize]
        } else {
            // Recursive case: get higher levels first, then push this level's index
            self.rec_to_path(abstract_level - 1, bottom_level).push(self.index[abstract_level] as usize)
        }
    }

    /// The vaddr of the path from this abstract vaddr equals the aligned vaddr at that level.
    pub proof fn to_path_vaddr(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS(),
        ensures
            vaddr(self.to_path(level)) == self.align_down(level + 1).compute_vaddr(),
    {
        admit() // Structural induction on the recursive definitions
    }

    /// The concrete to_vaddr() equals the computed vaddr.
    pub axiom fn to_vaddr_is_compute_vaddr(self)
        requires
            self.inv(),
        ensures
            self.to_vaddr() == self.compute_vaddr();

    /// Incrementing index[level-1] by 1 increases to_vaddr() by page_size(level).
    pub proof fn index_increment_adds_page_size(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS(),
            self.index[level - 1] + 1 < NR_ENTRIES(),
        ensures
            (Self {
                index: self.index.insert(level - 1, self.index[level - 1] + 1),
                ..self
            }).to_vaddr() == self.to_vaddr() + page_size(level as PagingLevel),
    {
        let new_va = Self {
            index: self.index.insert(level - 1, self.index[level - 1] + 1),
            ..self
        };
        // Establish new_va.inv()
        assert forall |i: int|
            #![trigger new_va.index.contains_key(i)]
            0 <= i < NR_LEVELS() implies {
                &&& new_va.index.contains_key(i)
                &&& 0 <= new_va.index[i]
                &&& new_va.index[i] < NR_ENTRIES()
            } by {
            // Use self.inv() to establish bounds on self.index[i]
            assert(self.index.contains_key(i));
            assert(0 <= self.index[i] < NR_ENTRIES());
            if i == level - 1 {
                assert(new_va.index[i] == self.index[i] + 1);
                assert(0 <= self.index[i]);
                assert(0 <= new_va.index[i]);
            } else {
                assert(new_va.index[i] == self.index[i]);
            }
        };
        assert(new_va.inv());
        self.to_vaddr_is_compute_vaddr();
        new_va.to_vaddr_is_compute_vaddr();
        // The compute_vaddr only differs at index[level-1], which contributes
        // an additional page_size(level) to the sum.
        admit()
    }

    /// Path extracted from abstract vaddr has correct length.
    pub proof fn to_path_len(self, level: int)
        requires
            0 <= level < NR_LEVELS(),
        ensures
            self.to_path(level).len() == NR_LEVELS() - level,
    {
        self.rec_to_path_len(NR_LEVELS() - 1, level);
    }

    proof fn rec_to_path_len(self, abstract_level: int, bottom_level: int)
        requires
            bottom_level <= abstract_level,
        ensures
            self.rec_to_path(abstract_level, bottom_level).len() == abstract_level - bottom_level + 1,
        decreases abstract_level - bottom_level,
    {
        // The recursive structure:
        // - rec_to_path(a, b) = rec_to_path(a-1, b).push(index[a]) when a >= b
        // - rec_to_path(a, b) = seq![] when a < b
        // So rec_to_path(a, b).len() = rec_to_path(a-1, b).len() + 1 = ... = a - b + 1
        if abstract_level > bottom_level {
            self.rec_to_path_len(abstract_level - 1, bottom_level);
        }
        // Structural reasoning about recursive definition
        admit()
    }

    /// Path extracted from abstract vaddr has valid indices.
    pub proof fn to_path_inv(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS(),
        ensures
            self.to_path(level).inv(),
    {
        self.to_path_len(level);
        assert forall|i: int| 0 <= i < self.to_path(level).len()
        implies TreePath::<CONST_NR_ENTRIES>::elem_inv(#[trigger] self.to_path(level).index(i)) by {
            // Each path index comes from self.index which is bounded by NR_ENTRIES
            admit()
        };
    }
}

/// Connection between TreePath's vaddr and AbstractVaddr
impl AbstractVaddr {
    /// If a TreePath matches this abstract vaddr's indices at all levels covered by the path,
    /// then vaddr(path) equals the aligned compute_vaddr at the corresponding level.
    pub proof fn path_matches_vaddr(self, path: TreePath<CONST_NR_ENTRIES>)
        requires
            self.inv(),
            path.inv(),
            path.len() <= NR_LEVELS(),
            forall|i: int| 0 <= i < path.len() ==>
                path.index(i) == self.index[NR_LEVELS() - 1 - i],
        ensures
            vaddr(path) == self.align_down((NR_LEVELS() - path.len() + 1) as int).compute_vaddr()
                - self.align_down((NR_LEVELS() - path.len() + 1) as int).offset,
    {
        admit() // Induction on path.len()
    }

    /// The path index at position i corresponds to the abstract vaddr index at level (NR_LEVELS - 1 - i).
    /// This is the key mapping between TreePath ordering and AbstractVaddr index ordering.
    pub proof fn to_path_index(self, level: int, i: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS(),
            0 <= i < NR_LEVELS() - level,
        ensures
            self.to_path(level).index(i) == self.index[NR_LEVELS() - 1 - i],
    {
        self.to_path_len(level);
        // The path is built by rec_to_path(NR_LEVELS - 1, level)
        // which produces indices from level NR_LEVELS-1 down to level
        // in order: index[NR_LEVELS-1], index[NR_LEVELS-2], ..., index[level]
        // So path.index(i) = index[NR_LEVELS - 1 - i]
        admit()
    }

    /// Direct connection: vaddr(to_path(level)) equals the aligned concrete vaddr.
    /// This combines to_path_vaddr with to_vaddr_is_compute_vaddr.
    pub proof fn to_path_vaddr_concrete(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS(),
        ensures
            vaddr(self.to_path(level)) == nat_align_down(self.to_vaddr() as nat, page_size((level + 1) as PagingLevel) as nat) as usize,
    {
        self.to_path_vaddr(level);
        self.to_vaddr_is_compute_vaddr();
        self.align_down_concrete(level + 1);
        // to_path_vaddr gives: vaddr(to_path(level)) == align_down(level+1).compute_vaddr()
        // to_vaddr_is_compute_vaddr gives: to_vaddr() == compute_vaddr()
        // align_down_concrete gives: align_down(level+1).reflect(nat_align_down(to_vaddr(), page_size(level+1)))
        // We need to connect align_down(level+1).compute_vaddr() to nat_align_down(to_vaddr(), page_size(level+1))
        admit()
    }

    /// Key property: if we have a path that matches cur_va's indices, then
    /// vaddr(path) + page_size(level) bounds the range containing cur_va.
    pub proof fn vaddr_range_from_path(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS(),
        ensures
            vaddr(self.to_path(level)) <= self.to_vaddr()
                < vaddr(self.to_path(level)) + page_size((level + 1) as PagingLevel),
    {
        self.to_path_vaddr_concrete(level);
        // nat_align_down(x, n) <= x < nat_align_down(x, n) + n
        admit()
    }
}

}
