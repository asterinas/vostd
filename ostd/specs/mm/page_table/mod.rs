#![allow(hidden_glob_reexports)]

pub mod cursor;
pub mod mapping_set_lemmas;
pub mod node;
mod owners;
mod view;

pub use cursor::*;
pub use node::*;
pub use owners::*;
pub use view::*;

use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd_extra::arithmetic::*;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use crate::mm::page_table::page_size;
use crate::mm::page_table::PageTableConfig;
use crate::mm::{PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};

use align_ext::AlignExt;

verus! {

/// An abstract representation of a virtual address as a sequence of indices, representing the
/// values of the bit-fields that index into each level of the page table.
/// - `offset` is the lowest 12 bits (the offset into a 4096 byte page).
/// - `index[0]` is the next 9 bits, `index[1]` the 9 above that, up to
///   `index[NR_LEVELS-1]`, covering a total of `12 + 9 * NR_LEVELS = 48` bits.
/// - `leading_bits` holds whatever's in bits `[48, 64)` of the original `Vaddr`.
///   For canonical x86_64 addresses this is either `0` (user half) or the
///   sign-extended high bits (kernel half, e.g. `0xffff`). `next_index`
///   carries into `leading_bits` on overflow at `NR_LEVELS`, so `align_up`
///   preserves `inv()` for any cursor state that stays inside the 64-bit
///   address space.
pub struct AbstractVaddr {
    pub offset: int,
    pub index: Map<int, int>,
    pub leading_bits: int,
}

impl Inv for AbstractVaddr {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.offset < PAGE_SIZE
        // `index` has exactly `[0, NR_LEVELS)` as its domain.
        &&& self.index.dom() =~= Set::new(|i: int| 0 <= i < NR_LEVELS)
        &&& forall|i: int|
            #![trigger self.index.contains_key(i)]
            0 <= i < NR_LEVELS ==> {
                &&& self.index.contains_key(i)
                &&& 0 <= self.index[i] < NR_ENTRIES
            }
        // `leading_bits` is the 16-bit slot above the 48-bit positional body.
        &&& 0 <= self.leading_bits < 0x1_0000int
    }
}

impl AbstractVaddr {
    /// Extract the AbstractVaddr components from a concrete virtual address.
    /// - offset = lowest 12 bits
    /// - index[i] = bits (12 + 9*i) to (12 + 9*(i+1) - 1) for each level
    /// - leading_bits = bits [48, 64)
    pub open spec fn from_vaddr(va: Vaddr) -> Self {
        AbstractVaddr {
            offset: (va % PAGE_SIZE) as int,
            index: Map::new(
                |i: int| 0 <= i < NR_LEVELS,
                |i: int| ((va / pow2((12 + 9 * i) as nat) as usize) % NR_ENTRIES) as int,
            ),
            leading_bits: (va as int / 0x1_0000_0000_0000int),
        }
    }

    pub proof fn from_vaddr_wf(va: Vaddr)
        ensures
            AbstractVaddr::from_vaddr(va).inv(),
    {
        let abs = AbstractVaddr::from_vaddr(va);
        assert forall|i: int| #![trigger abs.index.contains_key(i)] 0 <= i < NR_LEVELS implies {
            &&& abs.index.contains_key(i)
            &&& 0 <= abs.index[i]
            &&& abs.index[i] < NR_ENTRIES
        } by {};
        let va_i = va as int;
        assert(0 <= abs.leading_bits < 0x1_0000int) by (nonlinear_arith)
            requires
                abs.leading_bits == va_i / 0x1_0000_0000_0000int,
                0 <= va_i < 0x1_0000_0000_0000_0000int;
    }

    /// Reconstruct the concrete virtual address from the AbstractVaddr components.
    /// va = offset + sum(index[i] * 2^(12 + 9*i)) + leading_bits * 2^48
    pub open spec fn to_vaddr(self) -> Vaddr {
        (self.offset + self.to_vaddr_indices(0)
            + self.leading_bits * 0x1_0000_0000_0000int) as Vaddr
    }

    /// Helper: sum of index[i] * 2^(12 + 9*i) for i in start..NR_LEVELS
    pub open spec fn to_vaddr_indices(self, start: int) -> int
        decreases NR_LEVELS - start,
        when start <= NR_LEVELS
    {
        if start >= NR_LEVELS {
            0
        } else {
            self.index[start] * pow2((12 + 9 * start) as nat) as int + self.to_vaddr_indices(
                start + 1,
            )
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
    ///
    /// With `leading_bits` carrying the high 16 bits of the VA, this now
    /// holds **unconditionally** for any 64-bit `Vaddr` — the positional
    /// decomposition covers all 64 bits (12 offset + 4×9 index + 16 top).
    pub proof fn from_vaddr_to_vaddr_roundtrip(va: Vaddr)
        ensures
            Self::from_vaddr(va).to_vaddr() == va,
    {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        let abs = Self::from_vaddr(va);
        assert(abs.to_vaddr_indices(4) == 0);
        assert(abs.to_vaddr_indices(3)
            == abs.index[3] * pow2(39nat) as int + abs.to_vaddr_indices(4));
        assert(abs.to_vaddr_indices(2)
            == abs.index[2] * pow2(30nat) as int + abs.to_vaddr_indices(3));
        assert(abs.to_vaddr_indices(1)
            == abs.index[1] * pow2(21nat) as int + abs.to_vaddr_indices(2));
        assert(abs.to_vaddr_indices(0)
            == abs.index[0] * pow2(12nat) as int + abs.to_vaddr_indices(1));
        assert(
            va == (va % 4096usize)
                + ((va / 4096usize) % 512usize) * 4096usize
                + ((va / 0x20_0000usize) % 512usize) * 0x20_0000usize
                + ((va / 0x4000_0000usize) % 512usize) * 0x4000_0000usize
                + ((va / 0x80_0000_0000usize) % 512usize) * 0x80_0000_0000usize
                + (va / 0x1_0000_0000_0000usize) * 0x1_0000_0000_0000usize
        ) by (bit_vector);
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

    /// Inverse round-trip: reconstruct then extract gives back the
    /// original `AbstractVaddr`.
    pub proof fn to_vaddr_from_vaddr_roundtrip(abs: Self)
        requires
            abs.inv(),
        ensures
            Self::from_vaddr(abs.to_vaddr()) == abs,
    {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        abs.to_vaddr_bounded();
        assert(abs.to_vaddr_indices(4) == 0);
        assert(abs.to_vaddr_indices(3)
            == abs.index[3] * pow2(39nat) as int + abs.to_vaddr_indices(4));
        assert(abs.to_vaddr_indices(2)
            == abs.index[2] * pow2(30nat) as int + abs.to_vaddr_indices(3));
        assert(abs.to_vaddr_indices(1)
            == abs.index[1] * pow2(21nat) as int + abs.to_vaddr_indices(2));
        assert(abs.to_vaddr_indices(0)
            == abs.index[0] * pow2(12nat) as int + abs.to_vaddr_indices(1));

        assert(abs.index.contains_key(0));
        assert(abs.index.contains_key(1));
        assert(abs.index.contains_key(2));
        assert(abs.index.contains_key(3));
        let i0 = abs.index[0] as usize;
        let i1 = abs.index[1] as usize;
        let i2 = abs.index[2] as usize;
        let i3 = abs.index[3] as usize;
        let o = abs.offset as usize;
        let tb = abs.leading_bits as usize;
        let va = abs.to_vaddr();
        assert(i0 < 512usize);
        assert(i1 < 512usize);
        assert(i2 < 512usize);
        assert(i3 < 512usize);
        assert(
            va == o
                + i0 * 4096usize
                + i1 * 0x20_0000usize
                + i2 * 0x4000_0000usize
                + i3 * 0x80_0000_0000usize
                + tb * 0x1_0000_0000_0000usize
        );

        assert(va % 4096usize == o) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize
                    + i3 * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize, i0 < 512usize, i1 < 512usize, i2 < 512usize,
                i3 < 512usize, tb < 0x1_0000usize;
        assert((va / 4096usize) % 512usize == i0) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize
                    + i3 * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize, i0 < 512usize, i1 < 512usize, i2 < 512usize,
                i3 < 512usize, tb < 0x1_0000usize;
        assert((va / 0x20_0000usize) % 512usize == i1) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize
                    + i3 * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize, i0 < 512usize, i1 < 512usize, i2 < 512usize,
                i3 < 512usize, tb < 0x1_0000usize;
        assert((va / 0x4000_0000usize) % 512usize == i2) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize
                    + i3 * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize, i0 < 512usize, i1 < 512usize, i2 < 512usize,
                i3 < 512usize, tb < 0x1_0000usize;
        assert((va / 0x80_0000_0000usize) % 512usize == i3) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize
                    + i3 * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize, i0 < 512usize, i1 < 512usize, i2 < 512usize,
                i3 < 512usize, tb < 0x1_0000usize;
        assert(va / 0x1_0000_0000_0000usize == tb) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize
                    + i3 * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize, i0 < 512usize, i1 < 512usize, i2 < 512usize,
                i3 < 512usize, tb < 0x1_0000usize;

        let back = Self::from_vaddr(va);
        assert forall|i: int| 0 <= i < NR_LEVELS
            implies #[trigger] back.index[i] == abs.index[i] by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {}
        }
        assert(back.index =~= abs.index);
    }

    /// If two AbstractVaddrs reflect the same va, they are equal.
    pub broadcast proof fn reflect_eq(self, other: Self, va: Vaddr)
        requires
            #[trigger] self.reflect(va),
            #[trigger] other.reflect(va),
        ensures
            self == other,
    {
    }

    pub open spec fn align_down(self, level: int) -> Self
        decreases level,
        when level >= 1
    {
        if level == 1 {
            AbstractVaddr { offset: 0, ..self }
        } else {
            let tmp = self.align_down(level - 1);
            AbstractVaddr { index: tmp.index.insert(level - 2, 0), ..tmp }
        }
    }

    pub proof fn align_down_inv(self, level: int)
        requires
            1 <= level < NR_LEVELS,
            self.inv(),
        ensures
            self.align_down(level).inv(),
            forall|i: int|
                level <= i < NR_LEVELS ==> #[trigger] self.index[i - 1] == self.align_down(
                    level,
                ).index[i - 1],
        decreases level,
    {
        if level == 1 {
            assert(self.align_down(1).index =~= self.index);
        } else {
            let tmp = self.align_down(level - 1);
            self.align_down_inv(level - 1);
            let new = self.align_down(level);
            assert(new.index.dom() =~= Set::new(|i: int| 0 <= i < NR_LEVELS));
            assert forall |i: int|
                #![trigger new.index.contains_key(i)]
                0 <= i < NR_LEVELS implies {
                    &&& new.index.contains_key(i)
                    &&& 0 <= new.index[i]
                    &&& new.index[i] < NR_ENTRIES
                } by {
                if i != level - 2 {
                    assert(tmp.index.contains_key(i));
                }
            }
        }
    }

    pub proof fn align_down_leading_bits(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
        ensures
            self.align_down(level).leading_bits == self.leading_bits,
        decreases level,
    {
        if level > 1 {
            self.align_down_leading_bits(level - 1);
        }
    }

    pub proof fn align_down_shape(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
            self.inv(),
        ensures
            self.align_down(level).inv(),
            self.align_down(level).offset == 0,
            forall|i: int| 0 <= i < level - 1 ==> #[trigger] self.align_down(level).index[i] == 0,
            forall|i: int|
                level - 1 <= i < NR_LEVELS ==> #[trigger] self.align_down(level).index[i]
                    == self.index[i],
        decreases level,
    {
        if level == 1 {
            assert(self.align_down(1).index =~= self.index);
        } else {
            let tmp = self.align_down(level - 1);
            self.align_down_shape(level - 1);
            let new = self.align_down(level);
            assert(new.index.dom() =~= Set::new(|i: int| 0 <= i < NR_LEVELS));
            assert forall |i: int|
                #![trigger new.index.contains_key(i)]
                0 <= i < NR_LEVELS implies {
                    &&& new.index.contains_key(i)
                    &&& 0 <= new.index[i]
                    &&& new.index[i] < NR_ENTRIES
                } by {
                if i != level - 2 {
                    assert(tmp.index.contains_key(i));
                }
            }
        }
    }

    pub proof fn to_vaddr_indices_drop_zero_range(self, from: int, to: int)
        requires
            self.inv(),
            0 <= from <= to <= NR_LEVELS,
            forall|i: int| from <= i < to ==> self.index[i] == 0,
        ensures
            self.to_vaddr_indices(from) == self.to_vaddr_indices(to),
        decreases to - from,
    {
        if from < to {
            self.to_vaddr_indices_drop_zero_range(from + 1, to);
        }
    }

    pub proof fn to_vaddr_indices_eq_if_indices_eq(self, other: Self, start: int)
        requires
            self.inv(),
            other.inv(),
            0 <= start <= NR_LEVELS,
            forall|i: int| start <= i < NR_LEVELS ==> self.index[i] == other.index[i],
        ensures
            self.to_vaddr_indices(start) == other.to_vaddr_indices(start),
        decreases NR_LEVELS - start,
    {
        if start < NR_LEVELS {
            self.to_vaddr_indices_eq_if_indices_eq(other, start + 1);
        }
    }

    /// If two AbstractVaddrs share the same indices at levels >= level-1 (i.e., index[level-1] and above),
    /// then aligning them down to `level` gives the same to_vaddr() result.
    /// This is because align_down(level) zeroes offset and indices 0 through level-2,
    /// so only indices level-1 and above affect the to_vaddr() result.
    pub proof fn align_down_to_vaddr_eq_if_upper_indices_eq(self, other: Self, level: int)
        requires
            1 <= level <= NR_LEVELS,
            self.inv(),
            other.inv(),
            // Indices at level-1 and above are equal
            forall|i: int| level - 1 <= i < NR_LEVELS ==> self.index[i] == other.index[i],
            // Both live in the same canonical half.
            self.leading_bits == other.leading_bits,
        ensures
            self.align_down(level).to_vaddr() == other.align_down(level).to_vaddr(),
        decreases level,
    {
        let lhs = self.align_down(level);
        let rhs = other.align_down(level);

        self.align_down_shape(level);
        other.align_down_shape(level);
        self.align_down_leading_bits(level);
        other.align_down_leading_bits(level);

        lhs.to_vaddr_indices_drop_zero_range(0, level - 1);
        rhs.to_vaddr_indices_drop_zero_range(0, level - 1);
        lhs.to_vaddr_indices_eq_if_indices_eq(rhs, level - 1);
        assert(lhs.leading_bits == rhs.leading_bits);
    }

    pub axiom fn align_down_concrete(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
        ensures
            self.align_down(level).reflect(
                nat_align_down(
                    self.to_vaddr() as nat,
                    page_size(level as PagingLevel) as nat,
                ) as Vaddr,
            ),
    ;

    /// `align_down(0)` is not recursively reachable by the spec (defined only for level >= 1),
    /// so we axiomatize its key properties: it preserves `inv()` and all index values.
    /// This is consistent with the intended semantics of level-0 "alignment" being a no-op
    /// on the index array (it would only zero a non-existent sub-page offset).
    pub axiom fn align_down_zero_properties(self)
        requires
            self.inv(),
        ensures
            self.align_down(0).inv(),
            forall|i: int|
                #![auto]
                0 <= i < NR_LEVELS ==> self.align_down(0).index[i] == self.index[i],
    ;

    /// Two virtual addresses in the same page_size(level+1) aligned block
    /// have the same from_vaddr().index[i] for all i >= level.
    ///
    /// page_size(level + 1) = 2^(12 + 9*level). Being in the same aligned block means
    /// va / 2^(12 + 9*level) is equal, so (va / 2^(12+9*i)) % 512 is equal for i >= level.
    pub axiom fn same_node_indices_match(
        va1: Vaddr,
        va2: Vaddr,
        node_start: Vaddr,
        level: PagingLevel,
    )
        requires
            1 <= level,
            level < NR_LEVELS,
            node_start <= va1,
            va1 < node_start + page_size((level + 1) as PagingLevel),
            node_start <= va2,
            va2 < node_start + page_size((level + 1) as PagingLevel),
            node_start as nat % page_size((level + 1) as PagingLevel) as nat == 0,
        ensures
            forall|i: int|
                #![auto]
                level as int <= i < NR_LEVELS ==> Self::from_vaddr(va1).index[i]
                    == Self::from_vaddr(va2).index[i],
    ;

    pub open spec fn align_up(self, level: int) -> Self {
        let lower_aligned = self.align_down(level);
        lower_aligned.next_index(level)
    }

    pub axiom fn align_up_concrete(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
        ensures
            self.align_up(level).reflect(
                nat_align_up(
                    self.to_vaddr() as nat,
                    page_size(level as PagingLevel) as nat,
                ) as Vaddr,
            ),
    ;

    pub axiom fn align_diff(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
        ensures
            nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat)
                == nat_align_down(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat)
                + page_size(level as PagingLevel),
            nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat)
                < usize::MAX,
    ;

    /// When at the last entry of a level (index[level-1] == NR_ENTRIES - 1),
    /// align_up carries: align_up(level) == align_up(level + 1).
    pub proof fn align_up_carry(self, level: int)
        requires
            self.inv(),
            1 <= level,
            level < NR_LEVELS,
            self.index[level - 1] == NR_ENTRIES - 1,
        ensures
            self.align_up(level) == self.align_up(level + 1),
        decreases NR_LEVELS - level,
    {
        self.align_down_shape(level);
        self.align_down_shape(level + 1);
        assert(self.align_down(level).index.insert(level - 1, 0)
            =~= self.align_down(level + 1).index);
    }

    pub open spec fn next_index(self, level: int) -> Self
        decreases NR_LEVELS - level,
        when 1 <= level <= NR_LEVELS
    {
        let index = self.index[level - 1];
        let next_index = index + 1;
        if next_index == NR_ENTRIES && level < NR_LEVELS {
            let next_va = Self { index: self.index.insert(level - 1, 0), ..self };
            next_va.next_index(level + 1)
        } else if next_index == NR_ENTRIES && level == NR_LEVELS {
            // Top-level carry: wrap the top index and bump `leading_bits`.
            Self {
                index: self.index.insert(level - 1, 0),
                leading_bits: self.leading_bits + 1,
                ..self
            }
        } else {
            Self { index: self.index.insert(level - 1, next_index), ..self }
        }
    }

    pub open spec fn wrapped(self, start_level: int, level: int) -> bool
        decreases NR_LEVELS - level,
        when 1 <= start_level <= level <= NR_LEVELS
    {
        &&& self.next_index(start_level).index[level - 1] == 0 ==> {
            &&& self.index[level - 1] + 1 == NR_ENTRIES
            &&& if level < NR_LEVELS {
                self.wrapped(start_level, level + 1)
            } else {
                true
            }
        }
        &&& self.next_index(start_level).index[level - 1] != 0 ==> self.index[level - 1] + 1
            < NR_ENTRIES
    }

    pub proof fn use_wrapped(self, start_level: int, level: int)
        requires
            1 <= start_level <= level < NR_LEVELS,
            self.wrapped(start_level, level),
            self.next_index(start_level).index[level - 1] == 0,
        ensures
            self.index[level - 1] + 1 == NR_ENTRIES,
    {
    }

    pub proof fn wrapped_unwrap(self, start_level: int, level: int)
        requires
            1 <= start_level <= level < NR_LEVELS,
            self.wrapped(start_level, level),
            self.next_index(start_level).index[level - 1] == 0,
        ensures
            self.wrapped(start_level, level + 1),
    {
    }

    pub proof fn wrapped_after_carry_equiv(self, start_level: int, level: int)
        requires
            self.inv(),
            1 <= start_level < level <= NR_LEVELS,
            self.index[start_level - 1] + 1 == NR_ENTRIES,
        ensures
            ({
                let next_va = Self {
                    index: self.index.insert(start_level - 1, 0),
                    ..self
                };
                self.wrapped(start_level, level) == next_va.wrapped(start_level + 1, level)
            }),
        decreases NR_LEVELS - level,
    {
        let next_va = Self { index: self.index.insert(start_level - 1, 0), ..self };
        assert forall|i: int| start_level <= i < NR_LEVELS implies next_va.index[i]
            == self.index[i] by {};
        if level < NR_LEVELS {
            self.wrapped_after_carry_equiv(start_level, level + 1);
        }
    }

    /// Contrapositive of `use_wrapped`: index + 1 < NR_ENTRIES ==> next_index != 0.
    pub proof fn wrapped_index_nonzero(self, start_level: int, level: int)
        requires
            1 <= start_level <= level <= NR_LEVELS,
            self.wrapped(start_level, level),
            self.index[level - 1] + 1 < NR_ENTRIES,
        ensures
            self.next_index(start_level).index[level - 1] != 0,
    {
        if self.next_index(start_level).index[level - 1] == 0 {
            if level < NR_LEVELS { self.use_wrapped(start_level, level); }
        }
    }

    /// Index 0 + wrapped ==> next_index nonzero at that level.
    pub proof fn wrapped_nonzero_at_level(
        abs_va_down: Self, abs_next_va: Self,
        start_level: int, level: int, owner_index_at_level: int,
    )
        requires
            1 <= start_level <= level <= NR_LEVELS,
            abs_va_down.wrapped(start_level, level),
            abs_va_down.next_index(start_level) == abs_next_va,
            abs_va_down.index[level - 1] == owner_index_at_level,
            owner_index_at_level == 0,
        ensures
            abs_next_va.index[level - 1] != 0,
    {
        abs_va_down.wrapped_index_nonzero(start_level, level);
    }

    pub proof fn next_index_preserves_lower_indices(self, start_level: int, lower_level: int)
        requires
            self.inv(),
            1 <= lower_level < start_level <= NR_LEVELS,
        ensures
            self.next_index(start_level).index[lower_level - 1] == self.index[lower_level - 1],
        decreases NR_LEVELS - start_level,
    {
        let index = self.index[start_level - 1];
        let next_index = index + 1;
        if next_index == NR_ENTRIES && start_level < NR_LEVELS {
            let next_va = Self { index: self.index.insert(start_level - 1, 0), ..self };
            next_va.next_index_preserves_lower_indices(start_level + 1, lower_level);
        } else if next_index == NR_ENTRIES && start_level == NR_LEVELS {
        }
    }

    pub proof fn next_index_wrap_condition(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS,
        ensures
            self.wrapped(level, level),
        decreases NR_LEVELS - level,
    {
        let index = self.index[level - 1];
        let next_index = index + 1;
        if next_index == NR_ENTRIES {
            if level < NR_LEVELS {
                let next_va = Self { index: self.index.insert(level - 1, 0), ..self };
                next_va.next_index_wrap_condition(level + 1);
                self.wrapped_after_carry_equiv(level, level + 1);
                next_va.next_index_preserves_lower_indices(level + 1, level);
            }
        } else {
            assert(self.index.contains_key(level - 1));
        }
    }

    //
    // === Connection to TreePath and concrete Vaddr ===
    //
    /// Computes the concrete vaddr from the abstract representation.
    /// This matches the structure:
    ///   index[NR_LEVELS-1] * 2^39 + index[NR_LEVELS-2] * 2^30 + ... + index[0] * 2^12 + offset
    /// Positional vaddr from the index map and offset, excluding the
    /// `leading_bits * 2^48` high-half term. Bounded by `2^48`, which
    /// simplifies path-arithmetic proofs.
    ///
    /// Relates to `to_vaddr()` by `to_vaddr() as int == compute_vaddr() as
    /// int + leading_bits * 2^48` (see `to_vaddr_is_compute_vaddr`).
    pub open spec fn compute_vaddr(self) -> Vaddr {
        self.rec_compute_vaddr(0)
    }

    /// Helper for computing vaddr recursively from level i upward.
    pub open spec fn rec_compute_vaddr(self, i: int) -> Vaddr
        decreases NR_LEVELS - i,
        when 0 <= i <= NR_LEVELS
    {
        if i >= NR_LEVELS {
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
    pub open spec fn to_path(self, level: int) -> TreePath<NR_ENTRIES>
        recommends
            0 <= level < NR_LEVELS,
    {
        TreePath(self.rec_to_path(NR_LEVELS - 1, level))
    }

    /// Builds the path sequence from abstract_level down to bottom_level (both inclusive).
    /// abstract_level and bottom_level refer to the index keys in self.index (0 = lowest level, NR_LEVELS-1 = root).
    /// Returns indices in order from highest level (first in seq) to lowest level (last in seq).
    pub open spec fn rec_to_path(self, abstract_level: int, bottom_level: int) -> Seq<usize>
        decreases abstract_level - bottom_level,
        when bottom_level <= abstract_level
    {
        if abstract_level < bottom_level {
            seq![]
        } else if abstract_level == bottom_level {
            // Base case: just this one level
            seq![self.index[abstract_level] as usize]
        } else {
            // Recursive case: place the current higher level first, then recurse downward.
            seq![self.index[abstract_level] as usize].add(
                self.rec_to_path(abstract_level - 1, bottom_level),
            )
        }
    }

    /// The vaddr of the path from this abstract vaddr equals the aligned
    /// positional value at that level. Matches `compute_vaddr` since it is
    /// positional (ignoring `leading_bits`); add `leading_bits * 2^48`
    /// manually to obtain the canonical form — see `to_path_vaddr_concrete`
    /// for the canonical statement.
    #[verifier::rlimit(400)]
    pub proof fn to_path_vaddr(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS,
        ensures
            vaddr(self.to_path(level)) == self.align_down(level + 1).compute_vaddr(),
    {
        self.to_path_inv(level);
        self.to_path_len(level);
        lemma_page_size_spec_level1();
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
        let path = self.to_path(level);
        if level == 3 {
            let aligned = self.align_down(4);
            self.align_down_shape(4);
            self.to_path_index(3, 0);
            path.index_satisfies_elem_inv(0);
            assert(vaddr(path) == path.index(0) * 0x80_0000_0000usize) by {
                assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, path.index(0)) + rec_vaddr(
                    path,
                    1,
                )) as usize);
            };
            assert(aligned.rec_compute_vaddr(3) == self.index[3] * 0x80_0000_0000usize) by {
                assert(aligned.rec_compute_vaddr(3) == (aligned.index[3] * page_size(4)
                    + aligned.rec_compute_vaddr(4)) as Vaddr);
            };
            assert(aligned.rec_compute_vaddr(1) == self.index[3] * 0x80_0000_0000usize) by {
                assert(aligned.rec_compute_vaddr(1) == (aligned.index[1] * page_size(2)
                    + aligned.rec_compute_vaddr(2)) as Vaddr);
            };
            assert(aligned.compute_vaddr() == aligned.compute_vaddr());
            assert(aligned.compute_vaddr() == (aligned.index[0] * page_size(1)
                + aligned.rec_compute_vaddr(1)) as Vaddr);
            assert(vaddr(path) == aligned.compute_vaddr());
        } else if level == 2 {
            let aligned = self.align_down(3);
            self.align_down_shape(3);
            self.to_path_index(2, 0);
            self.to_path_index(2, 1);
            path.index_satisfies_elem_inv(0);
            path.index_satisfies_elem_inv(1);
            assert(vaddr(path) == path.index(0) * 0x80_0000_0000usize + path.index(1)
                * 0x4000_0000usize) by {
                assert(vaddr(path) == rec_vaddr(path, 0));
                assert(rec_vaddr(path, 1) == (vaddr_make::<NR_LEVELS>(1, path.index(1)) + rec_vaddr(
                    path,
                    2,
                )) as usize);
            };
            assert(aligned.rec_compute_vaddr(3) == self.index[3] * 0x80_0000_0000usize) by {
                assert(aligned.rec_compute_vaddr(3) == (aligned.index[3] * page_size(4)
                    + aligned.rec_compute_vaddr(4)) as Vaddr);
            };
            assert(aligned.rec_compute_vaddr(1) == self.index[2] * 0x4000_0000usize + self.index[3]
                * 0x80_0000_0000usize) by {
                assert(aligned.rec_compute_vaddr(1) == (aligned.index[1] * page_size(2)
                    + aligned.rec_compute_vaddr(2)) as Vaddr);
            };
            assert(vaddr(path) == aligned.compute_vaddr());
        } else if level == 1 {
            let aligned = self.align_down(2);
            self.align_down_shape(2);
            self.to_path_index(1, 0);
            self.to_path_index(1, 1);
            self.to_path_index(1, 2);
            path.index_satisfies_elem_inv(0);
            path.index_satisfies_elem_inv(1);
            path.index_satisfies_elem_inv(2);
            assert(vaddr(path) == path.index(0) * 0x80_0000_0000usize + path.index(1)
                * 0x4000_0000usize + path.index(2) * 0x20_0000usize) by {
                assert(vaddr(path) == rec_vaddr(path, 0));
                assert(rec_vaddr(path, 3) == 0);
                assert(rec_vaddr(path, 2) == (vaddr_make::<NR_LEVELS>(2, path.index(2)) + rec_vaddr(path, 3)) as usize);
                assert(rec_vaddr(path, 1) == (vaddr_make::<NR_LEVELS>(1, path.index(1)) + rec_vaddr(path, 2)) as usize);
                assert(rec_vaddr(path, 0) == (vaddr_make::<NR_LEVELS>(0, path.index(0)) + rec_vaddr(path, 1)) as usize);
                assert(vaddr_make::<NR_LEVELS>(0, path.index(0)) == 0x80_0000_0000usize * path.index(0)) by (compute);
                assert(vaddr_make::<NR_LEVELS>(1, path.index(1)) == 0x4000_0000usize * path.index(1)) by (compute);
                assert(vaddr_make::<NR_LEVELS>(2, path.index(2)) == 0x20_0000usize * path.index(2)) by (compute);
            };
            assert(aligned.rec_compute_vaddr(3) == self.index[3] * 0x80_0000_0000usize) by {
                assert(aligned.rec_compute_vaddr(3) == (aligned.index[3] * page_size(4)
                    + aligned.rec_compute_vaddr(4)) as Vaddr);
            };
            assert(aligned.rec_compute_vaddr(1) == self.index[1] * 0x20_0000usize + self.index[2]
                * 0x4000_0000usize + self.index[3] * 0x80_0000_0000usize) by {
                assert(aligned.rec_compute_vaddr(1) == (aligned.index[1] * page_size(2)
                    + aligned.rec_compute_vaddr(2)) as Vaddr);
            };
            assert(aligned.compute_vaddr() == aligned.compute_vaddr());
            assert(aligned.compute_vaddr() == (aligned.index[0] * page_size(1)
                + aligned.rec_compute_vaddr(1)) as Vaddr);
            assert(vaddr(path) == aligned.compute_vaddr());
        } else {
            let aligned = self.align_down(1);
            self.align_down_shape(1);
            self.to_path_index(0, 0);
            self.to_path_index(0, 1);
            self.to_path_index(0, 2);
            self.to_path_index(0, 3);
            path.index_satisfies_elem_inv(0);
            path.index_satisfies_elem_inv(1);
            path.index_satisfies_elem_inv(2);
            path.index_satisfies_elem_inv(3);
            assert(vaddr(path) == path.index(0) * 0x80_0000_0000usize + path.index(1)
                * 0x4000_0000usize + path.index(2) * 0x20_0000usize + path.index(3) * 0x1000usize)
                by {
                assert(vaddr(path) == rec_vaddr(path, 0));
                assert(rec_vaddr(path, 4) == 0);
                assert(rec_vaddr(path, 2) == (vaddr_make::<NR_LEVELS>(2, path.index(2)) + rec_vaddr(
                    path,
                    3,
                )) as usize);
                assert(rec_vaddr(path, 1) == (vaddr_make::<NR_LEVELS>(1, path.index(1)) + rec_vaddr(
                    path,
                    2,
                )) as usize);
                assert(vaddr_make::<NR_LEVELS>(0, path.index(0)) == 0x80_0000_0000usize
                    * path.index(0)) by (compute);
                assert(vaddr_make::<NR_LEVELS>(1, path.index(1)) == 0x4000_0000usize * path.index(
                    1,
                )) by (compute);
                assert(vaddr_make::<NR_LEVELS>(2, path.index(2)) == 0x20_0000usize * path.index(2))
                    by (compute);
                assert(vaddr_make::<NR_LEVELS>(3, path.index(3)) == 0x1000usize * path.index(3))
                    by (compute);
            };
            assert(aligned.rec_compute_vaddr(4) == 0);
            assert(aligned.rec_compute_vaddr(3) == self.index[3] * 0x80_0000_0000usize) by {
                assert(aligned.rec_compute_vaddr(3) == (aligned.index[3] * page_size(4)
                    + aligned.rec_compute_vaddr(4)) as Vaddr);
            };
            assert(aligned.rec_compute_vaddr(2) == self.index[2] * 0x4000_0000usize + self.index[3]
                * 0x80_0000_0000usize) by {
            };
            assert(aligned.compute_vaddr() == self.index[0] * 0x1000usize + self.index[1]
                * 0x20_0000usize + self.index[2] * 0x4000_0000usize + self.index[3]
                * 0x80_0000_0000usize) by {
                assert(aligned.compute_vaddr() == aligned.compute_vaddr());
                assert(aligned.compute_vaddr() == (aligned.index[0] * page_size(1)
                    + aligned.rec_compute_vaddr(1)) as Vaddr);
            };
            assert(vaddr(path) == aligned.compute_vaddr());
        }
    }

    /// Full identity relating `to_vaddr()` to `compute_vaddr()`:
    /// `to_vaddr = compute_vaddr + leading_bits * 2^48`.
    ///
    /// `compute_vaddr` is positional (excludes `leading_bits * 2^48`), while
    /// `to_vaddr` includes it. Callers that need the two equal (no
    /// canonical shift) should constrain `leading_bits == 0`.
    pub axiom fn to_vaddr_is_compute_vaddr(self)
        requires
            self.inv(),
        ensures
            self.to_vaddr() as int
                == self.compute_vaddr() as int
                    + self.leading_bits * 0x1_0000_0000_0000int,
    ;

    pub proof fn to_vaddr_indices_gap_bound(self, start: int)
        requires
            self.inv(),
            0 <= start <= NR_LEVELS,
        ensures
            0 <= self.to_vaddr_indices(start),
            self.to_vaddr_indices(start) + pow2((12 + 9 * start) as nat) as int <= pow2(
                (12 + 9 * NR_LEVELS) as nat,
            ) as int,
        decreases NR_LEVELS - start,
    {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        vstd::arithmetic::power2::lemma_pow2_pos((12 + 9 * start) as nat);
        if start == NR_LEVELS {
        } else {
            let shift = pow2((12 + 9 * start) as nat) as int;
            let next_shift = pow2((12 + 9 * (start + 1)) as nat) as int;
            let top = pow2((12 + 9 * NR_LEVELS) as nat) as int;
            self.to_vaddr_indices_gap_bound(start + 1);
            assert(self.index.contains_key(start));
                                                                                                                                                                          vstd::arithmetic::power2::lemma_pow2_adds((12 + 9 * start) as nat, 9nat);
            vstd::arithmetic::mul::lemma_mul_inequality(self.index[start] + 1, 0x200int, shift);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                shift,
                self.index[start],
                1,
            );
        }
    }

    pub proof fn to_vaddr_bounded(self)
        requires
            self.inv(),
        ensures
            0 <= self.offset + self.to_vaddr_indices(0) < 0x1_0000_0000_0000int,
            self.to_vaddr() as int
                == self.offset
                    + self.to_vaddr_indices(0)
                    + self.leading_bits * 0x1_0000_0000_0000int,
            self.offset
                + self.to_vaddr_indices(0)
                + self.leading_bits * 0x1_0000_0000_0000int
                < 0x1_0000_0000_0000_0000int,
    {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        self.to_vaddr_indices_gap_bound(0);
        assert(pow2((12 + 9 * NR_LEVELS) as nat) as int == 0x1_0000_0000_0000int)
            by (compute);
        assert(self.leading_bits * 0x1_0000_0000_0000int
            + 0x1_0000_0000_0000int
            <= 0x1_0000 * 0x1_0000_0000_0000int) by (nonlinear_arith)
            requires 0 <= self.leading_bits < 0x1_0000int;
        assert(0x1_0000 * 0x1_0000_0000_0000int == 0x1_0000_0000_0000_0000int)
            by (compute);
    }

    pub proof fn index_increment_adds_page_size(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS,
            self.index[level - 1] + 1 < NR_ENTRIES,
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
        assert forall|i: int| #![trigger new_va.index.contains_key(i)] 0 <= i < NR_LEVELS implies {
            &&& new_va.index.contains_key(i)
            &&& 0 <= new_va.index[i]
            &&& new_va.index[i] < NR_ENTRIES
        } by {
            assert(self.index.contains_key(i));
        };
        assert(new_va.inv());
        self.to_vaddr_bounded();
        new_va.to_vaddr_bounded();
        assert(new_va.to_vaddr() as int - self.to_vaddr() as int
            == new_va.to_vaddr_indices(0) - self.to_vaddr_indices(0));
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        if level == 1 {
            lemma_page_size_spec_level1();
            assert forall|i: int| 1 <= i < NR_LEVELS implies new_va.index[i] == self.index[i] by {};
            new_va.to_vaddr_indices_eq_if_indices_eq(self, 1);
            assert((self.index[0] + 1) * 0x1000 == self.index[0] * 0x1000 + 0x1000)
                by (nonlinear_arith);
        } else if level == 2 {
            vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
            assert forall|i: int| 2 <= i < NR_LEVELS implies new_va.index[i] == self.index[i] by {};
            new_va.to_vaddr_indices_eq_if_indices_eq(self, 2);
            assert(self.to_vaddr_indices(0) == self.index[0] * pow2(12nat) as int
                + self.to_vaddr_indices(1));
            assert((self.index[1] + 1) * 0x20_0000 == self.index[1] * 0x20_0000 + 0x20_0000)
                by (nonlinear_arith);
            assert(new_va.to_vaddr_indices(1) == self.to_vaddr_indices(1) + 0x20_0000);
        } else if level == 3 {
            vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
            assert forall|i: int| 3 <= i < NR_LEVELS implies new_va.index[i] == self.index[i] by {};
            new_va.to_vaddr_indices_eq_if_indices_eq(self, 3);
            assert(new_va.to_vaddr_indices(2) == self.to_vaddr_indices(2) + 0x4000_0000);
            assert(new_va.to_vaddr_indices(1) == self.to_vaddr_indices(1) + 0x4000_0000);
        } else {
            vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
            assert forall|i: int| 4 <= i < NR_LEVELS implies new_va.index[i] == self.index[i] by {};
            new_va.to_vaddr_indices_eq_if_indices_eq(self, 4);
            assert(self.to_vaddr_indices(1) == self.index[1] * pow2(21nat) as int
                + self.to_vaddr_indices(2));
            assert(self.to_vaddr_indices(2) == self.index[2] * pow2(30nat) as int
                + self.to_vaddr_indices(3));
            assert((self.index[3] + 1) * 0x80_0000_0000 == self.index[3] * 0x80_0000_0000
                + 0x80_0000_0000) by (nonlinear_arith);
            assert(new_va.to_vaddr_indices(3) == self.to_vaddr_indices(3) + 0x80_0000_0000);
            assert(new_va.to_vaddr_indices(2) == self.to_vaddr_indices(2) + 0x80_0000_0000);
            assert(new_va.to_vaddr_indices(1) == self.to_vaddr_indices(1) + 0x80_0000_0000);
        }
    }

    /// Path extracted from abstract vaddr has correct length.
    pub proof fn to_path_len(self, level: int)
        requires
            0 <= level < NR_LEVELS,
        ensures
            self.to_path(level).len() == NR_LEVELS - level,
    {
        self.rec_to_path_len(NR_LEVELS - 1, level);
    }

    proof fn rec_to_path_len(self, abstract_level: int, bottom_level: int)
        requires
            bottom_level <= abstract_level,
        ensures
            self.rec_to_path(abstract_level, bottom_level).len() == abstract_level - bottom_level
                + 1,
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

    }

    /// Path extracted from abstract vaddr has valid indices.
    pub proof fn to_path_inv(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS,
        ensures
            self.to_path(level).inv(),
    {
        self.to_path_len(level);
        assert forall|i: int| 0 <= i < self.to_path(level).len() implies TreePath::<
            NR_ENTRIES,
        >::elem_inv(#[trigger] self.to_path(level).index(i)) by {
            let j = NR_LEVELS - 1 - i;
            self.to_path_index(level, i);
            assert(self.index.contains_key(j));
        };
    }
}

/// Connection between TreePath's vaddr and AbstractVaddr
impl AbstractVaddr {
    proof fn rec_vaddr_eq_if_indices_eq(
        path1: TreePath<NR_ENTRIES>,
        path2: TreePath<NR_ENTRIES>,
        idx: int,
    )
        requires
            path1.inv(),
            path2.inv(),
            path1.len() == path2.len(),
            0 <= idx <= path1.len(),
            forall|i: int| idx <= i < path1.len() ==> path1.index(i) == path2.index(i),
        ensures
            rec_vaddr(path1, idx) == rec_vaddr(path2, idx),
        decreases path1.len() - idx,
    {
        if idx < path1.len() {
            path1.index_satisfies_elem_inv(idx);
            path2.index_satisfies_elem_inv(idx);
            Self::rec_vaddr_eq_if_indices_eq(path1, path2, idx + 1);
        }
    }

    /// If a TreePath matches this abstract vaddr's indices at all levels covered by the path,
    /// then vaddr(path) equals the aligned compute_vaddr at the corresponding level.
    pub proof fn path_matches_vaddr(self, path: TreePath<NR_ENTRIES>)
        requires
            self.inv(),
            path.inv(),
            path.len() <= NR_LEVELS,
            forall|i: int| 0 <= i < path.len() ==> path.index(i) == self.index[NR_LEVELS - 1 - i],
        ensures
            vaddr(path) == self.align_down((NR_LEVELS - path.len() + 1) as int).compute_vaddr()
                - self.align_down((NR_LEVELS - path.len() + 1) as int).offset,
    {
        if path.len() == 0 {
            let aligned = self.align_down(5);
            self.align_down_shape(4);
            // align_down(5) zeroes index[3] on top of align_down(4), so all indices + offset are 0.
            assert(aligned.index[3] == 0) by {
                assert(aligned == AbstractVaddr {
                    index: self.align_down(4).index.insert(3, 0),
                    ..self.align_down(4)
                });
            };
            assert(aligned.rec_compute_vaddr(4) == 0);
            assert(aligned.rec_compute_vaddr(3) == 0) by {
                assert(aligned.rec_compute_vaddr(3) == (aligned.index[3] * page_size(4)
                    + aligned.rec_compute_vaddr(4)) as Vaddr);
            };
            assert(aligned.rec_compute_vaddr(2) == 0) by {
                assert(aligned.rec_compute_vaddr(2) == (aligned.index[2] * page_size(3)
                    + aligned.rec_compute_vaddr(3)) as Vaddr);
            };
            assert(aligned.rec_compute_vaddr(1) == 0) by {
                assert(aligned.rec_compute_vaddr(1) == (aligned.index[1] * page_size(2)
                    + aligned.rec_compute_vaddr(2)) as Vaddr);
            };
        } else {
            let level = (NR_LEVELS - path.len()) as int;
            assert(0 <= level < NR_LEVELS);
            self.to_path_inv(level);
            self.to_path_len(level);
            assert forall|i: int| 0 <= i < path.len() implies #[trigger]path.index(i) == self.to_path(
                level,
            ).index(i) by {
                self.to_path_index(level, i);
            };
            Self::rec_vaddr_eq_if_indices_eq(path, self.to_path(level), 0);
            self.to_path_vaddr(level);
            self.align_down_shape(level + 1);
        }
    }

    /// The path index at position i corresponds to the abstract vaddr index at level (NR_LEVELS - 1 - i).
    /// This is the key mapping between TreePath ordering and AbstractVaddr index ordering.
    pub proof fn to_path_index(self, level: int, i: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS,
            0 <= i < NR_LEVELS - level,
        ensures
            self.to_path(level).index(i) == self.index[NR_LEVELS - 1 - i],
    {
        self.to_path_len(level);
        self.rec_to_path_index(NR_LEVELS - 1, level, i);
    }

    proof fn rec_to_path_index(self, abstract_level: int, bottom_level: int, i: int)
        requires
            self.inv(),
            0 <= bottom_level <= abstract_level < NR_LEVELS,
            0 <= i < abstract_level - bottom_level + 1,
        ensures
            self.rec_to_path(abstract_level, bottom_level).index(i) == self.index[abstract_level
                - i],
        decreases abstract_level - bottom_level,
    {
        assert(self.index.contains_key(abstract_level));
        if abstract_level == bottom_level {
        } else {
            let head = seq![self.index[abstract_level] as usize];
            let tail = self.rec_to_path(abstract_level - 1, bottom_level);
            let full = head.add(tail);
            if i == 0 {
            } else {
                self.rec_to_path_index(abstract_level - 1, bottom_level, i - 1);
                assert(0 <= i - 1 < tail.len()) by {
                    self.rec_to_path_len(abstract_level - 1, bottom_level);
                };
            }
        }
    }

    /// Direct connection: `vaddr(to_path(level))` is the positional
    /// component of the aligned concrete vaddr. For canonical-high-half
    /// configs, the full aligned address is
    /// `vaddr(to_path) + leading_bits * 2^48`.
    pub proof fn to_path_vaddr_concrete(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS,
        ensures
            vaddr(self.to_path(level)) as int
                + self.leading_bits * 0x1_0000_0000_0000int
                == nat_align_down(
                    self.to_vaddr() as nat,
                    page_size((level + 1) as PagingLevel) as nat,
                ) as int,
    {
        self.to_path_vaddr(level);
        let aligned = self.align_down(level + 1);
        self.align_down_shape(level + 1);
        aligned.to_vaddr_is_compute_vaddr();
        self.align_down_concrete(level + 1);
        aligned.reflect_prop(
            nat_align_down(
                self.to_vaddr() as nat,
                page_size((level + 1) as PagingLevel) as nat,
            ) as Vaddr,
        );
        self.align_down_leading_bits(level + 1);
        // Chain:
        //   vaddr(to_path) == aligned.compute_vaddr()                    (to_path_vaddr)
        //   aligned.to_vaddr() as int == compute_vaddr() as int + leading_bits * 2^48  (to_vaddr_is_compute_vaddr)
        //   aligned.to_vaddr() == nat_align_down(self.to_vaddr(), ps) as Vaddr          (reflect_prop)
        //   aligned.leading_bits == self.leading_bits                    (align_down_leading_bits)
        let nad = nat_align_down(
            self.to_vaddr() as nat,
            page_size((level + 1) as PagingLevel) as nat,
        );
        // nad fits in usize: nat_align_down is bounded by its argument,
        // which is `self.to_vaddr() as nat <= usize::MAX`.
        lemma_page_size_ge_page_size((level + 1) as PagingLevel);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(
            self.to_vaddr() as nat,
            page_size((level + 1) as PagingLevel) as nat,
        );
        assert(nad <= self.to_vaddr() as nat);
        assert(nad <= usize::MAX);
        assert(aligned.leading_bits == self.leading_bits);
        assert(vaddr(self.to_path(level)) as int == aligned.compute_vaddr() as int);
        assert(aligned.to_vaddr() as int
            == aligned.compute_vaddr() as int
                + aligned.leading_bits * 0x1_0000_0000_0000int);
        assert(aligned.to_vaddr() == nad as Vaddr);
        // `nad <= usize::MAX` ⇒ `nad as usize as int == nad as int`.
        assert(aligned.to_vaddr() as int == nad as int);
    }

    /// Key property: `vaddr(path) + leading_bits * 2^48` (i.e. the canonical
    /// form of the path's VA) bounds the range containing `cur_va`.
    pub proof fn vaddr_range_from_path(self, level: int)
        requires
            self.inv(),
            0 <= level < NR_LEVELS,
        ensures
            vaddr(self.to_path(level)) as int
                + self.leading_bits * 0x1_0000_0000_0000int
                <= self.to_vaddr() as int,
            (self.to_vaddr() as int)
                < vaddr(self.to_path(level)) as int
                    + self.leading_bits * 0x1_0000_0000_0000int
                    + page_size((level + 1) as PagingLevel) as int,
    {
        self.to_path_vaddr_concrete(level);
        let size = page_size((level + 1) as PagingLevel);
        let cur = self.to_vaddr() as nat;
        let start = vaddr(self.to_path(level));

        assert(page_size((level + 1) as PagingLevel) >= PAGE_SIZE) by {
            lemma_page_size_ge_page_size((level + 1) as PagingLevel);
        };
        lemma_nat_align_down_sound(cur, size as nat);
    }
}

} // verus!
