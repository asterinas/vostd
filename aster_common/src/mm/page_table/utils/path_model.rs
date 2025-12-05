use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use vstd_extra::ghost_tree;

use crate::prelude::*;
use vstd_extra::prelude::TreePath;

verus! {

pub tracked struct PageTableTreePathModel {
    pub tracked inner: ghost_tree::TreePath<CONST_NR_ENTRIES>,
}

#[verifier::inline]
pub open spec fn vaddr_index_mask() -> usize {
    low_bits_mask(9) as usize
}

#[verifier::inline]
pub open spec fn vaddr_mask(index: usize) -> usize {
    index & vaddr_index_mask()
}

pub broadcast proof fn vaddr_mask_identical(index: usize)
    requires
        0 <= index < 512,
    ensures
        #[trigger] vaddr_mask(index) == index,
{
    assert(low_bits_mask(9) == 511) by {
        lemma_low_bits_mask_values();
    };
    assert(index & 511 == index % 512) by (bit_vector);
}

pub proof fn lemma_vaddr_make_bounded<const L: usize>(idx: int, offset: usize)
    requires
        0 < L <= 4,
        0 <= idx < L,
        0 <= offset < 512,
    ensures
        offset == 0 ==> vaddr_make::<L>(idx, offset) == 0,
        offset > 0 ==> pow2(12 + 9 * (L - 1 - idx) as nat) <= vaddr_make::<L>(idx, offset) < pow2(
            12 + 9 * (L - idx) as nat,
        ),
{
    admit();
}

#[verifier::inline]
pub open spec fn vaddr_extract<const L: usize>(idx: int, vaddr: usize) -> usize
    recommends
        0 < L,
        idx < L,
{
    vaddr_mask(vaddr / vaddr_shift::<L>(idx))
}

pub proof fn lemma_vaddr_make_extract_idempotent<const L: usize>(idx: int, offset: usize)
    requires
        0 < L <= 4,
        0 <= idx < L,
        0 <= offset < 512,
    ensures
        vaddr_extract::<L>(idx, vaddr_make::<L>(idx, offset)) == offset,
{
    admit();
}

pub open spec fn page_size_at_level<const L: usize>(level: int) -> usize
    recommends
        0 < L,
        0 <= level < L,
{
    pow2(12 + 9 * (L - 1 - level) as nat) as usize
}

impl View for PageTableTreePathModel {
    type V = TreePath<CONST_NR_ENTRIES>;

    open spec fn view(&self) -> Self::V {
        self.inner
    }
}

impl PageTableTreePathModel {
    pub proof fn axiom_max_tree_depth()
        ensures
            0 < NR_LEVELS(),
    {
        admit();
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.inner.len() < NR_LEVELS()
        &&& self.inner.inv()
    }

    pub proof fn rec_vaddr_pop_0(path: TreePath<CONST_NR_ENTRIES>, len: int, idx: int)
        requires
            path.inv(),
            len == path.len(),
            0 <= idx < path.len(),
            path.index(len - 1) == 0,
        ensures
            Self::rec_vaddr(path, idx) == Self::rec_vaddr(path.pop_tail().1, idx),
        decreases (path.len() - idx),
    {
        if idx == len - 1 {
            assert(Self::rec_vaddr(path, idx + 1) == 0);
        } else {
            assert(path.index(idx) == path.pop_tail().1.index(idx)) by { path.pop_tail_property() };
            Self::rec_vaddr_pop_0(path, len, idx + 1);
        }
    }

    pub proof fn rec_vaddr_push_0(path: TreePath<CONST_NR_ENTRIES>, len: int, idx: int)
        requires
            path.inv(),
            len == path.len(),
            0 <= idx <= path.len(),
            NR_ENTRIES() > 0,
        ensures
            Self::rec_vaddr(path, idx) == Self::rec_vaddr(path.push_tail(0 as usize), idx),
        decreases (path.len() - idx),
    {
        let val = 0 as usize;
        assert(0 <= val < NR_ENTRIES());
        let pushed = path.push_tail(val);
        assert(pushed.index(len) == 0) by { path.push_tail_property(val) };
        if idx == len {
            assert(Self::rec_vaddr(path, idx) == 0);
            assert(Self::rec_vaddr(pushed, idx + 1) == 0);
        } else {
            assert(path.index(idx) == pushed.index(idx)) by { path.push_tail_property(0 as usize) };
            Self::rec_vaddr_push_0(path, len, idx + 1);
        }
    }

    #[verifier::inline]
    pub open spec fn from_path(path: TreePath<CONST_NR_ENTRIES>) -> Self {
        Self { inner: path }
    }

    pub open spec fn rec_from_va(va: usize, idx: int) -> Seq<usize>
        recommends
            0 < NR_LEVELS(),
            0 <= idx <= NR_LEVELS(),
        decreases (NR_LEVELS() - idx),
        when 0 <= idx <= NR_LEVELS()
    {
        if idx == NR_LEVELS() {
            Seq::empty()
        } else {
            let offset = vaddr_extract::<CONST_NR_LEVELS>(idx, va);
            seq![offset].add(Self::rec_from_va(va, idx + 1))
        }
    }

    pub open spec fn from_va(va: usize) -> Self {
        Self { inner: TreePath::new(Self::rec_from_va(va, 0)) }
    }

    pub broadcast proof fn lemma_from_vaddr_to_vaddr_mod_page_size(va: usize)
        requires
            0 <= va < pow2(48),
        ensures
            #[trigger] Self::from_va(va).vaddr() == va % PAGE_SIZE(),
    {
        admit();
    }

    #[verifier::inline]
    pub open spec fn len(self) -> nat
        recommends
            self.inv(),
    {
        self.inner.len()
    }
}

} // verus!
