use vstd::pervasive::arbitrary;
use vstd::prelude::*;

use vstd::layout;
use vstd::raw_ptr;
use vstd::set;
use vstd::set_lib;

use core::marker::PhantomData;
use core::ops::Range;

use crate::prelude::Inv;
use crate::mm::{Paddr, Vaddr};
use crate::specs::mm::page_table::Mapping;

verus! {

/// Concrete representation of a pointer
pub struct VirtPtr {
    pub vaddr: Vaddr,
    pub ghost range: Ghost<Range<Vaddr>>,
}

pub struct FrameContents {
    pub contents: Map<Paddr, raw_ptr::MemContents<u8>>,
    pub ghost range: Ghost<Range<Paddr>>,
}

pub tracked struct MemView {
    pub mappings: Set<Mapping>,
    pub memory: Map<Paddr, raw_ptr::MemContents<u8>>
}

impl MemView {
    pub open spec fn addr_transl(self, va: usize) -> Option<usize> {
        let mappings = self.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        if 0 < mappings.len() {
            let m = mappings.choose();  // In a well-formed PT there will only be one, but if malformed this is non-deterministic!
            let off = va - m.va_range.start;
            Some((m.pa_range.start + off) as usize)
        } else {
            None
        }
    }

    pub open spec fn read(self, va: usize) -> Option<raw_ptr::MemContents<u8>> {
        let pa = self.addr_transl(va);
        if pa is Some {
            Some(self.memory[pa.unwrap()])
        } else {
            None
        }
    }

    pub open spec fn write(self, va: usize, x: u8) -> Option<Self> {
        let pa = self.addr_transl(va);
        if pa is Some {
            Some(
                MemView {
                    memory: self.memory.insert(pa.unwrap(), raw_ptr::MemContents::Init(x)),
                    ..self
                },
            )
        } else {
            None
        }
    }

    pub open spec fn eq_at(self, va1: usize, va2: usize) -> bool {
        let pa1 = self.addr_transl(va1);
        let pa2 = self.addr_transl(va2);
        if pa1 is Some && pa2 is Some {
            self.memory[pa1.unwrap()] == self.memory[pa2.unwrap()]
        } else {
            false
        }
    }

    pub open spec fn borrow_at_spec(&self, vaddr: usize, len: usize) -> MemView {
        let range_end = vaddr + len;

        let valid_pas = Set::new(
            |pa: usize|
                exists|va: usize|
                    vaddr <= va < range_end && #[trigger] self.addr_transl(va) == Some(pa),
        );

        MemView {
            mappings: self.mappings.filter(
                |m: Mapping| m.va_range.start < range_end && m.va_range.end > vaddr,
            ),
            memory: self.memory.restrict(valid_pas),
        }
    }

    pub open spec fn mappings_are_disjoint(self) -> bool {
        forall|m1: Mapping, m2: Mapping|
            #![trigger self.mappings.contains(m1), self.mappings.contains(m2)]
            self.mappings.contains(m1) && self.mappings.contains(m2) && m1 != m2 ==> {
                m1.va_range.end <= m2.va_range.start || m2.va_range.end <= m1.va_range.start
            }
    }

    pub open spec fn split_spec(self, vaddr: usize, len: usize) -> (MemView, MemView) {
        let split_end = vaddr + len;

        // The left part.
        let left_mappings = self.mappings.filter(
            |m: Mapping| m.va_range.start < split_end && m.va_range.end > vaddr,
        );
        let right_mappings = self.mappings.filter(|m: Mapping| m.va_range.end > split_end);

        let left_pas = Set::new(
            |pa: usize|
                exists|va: usize| vaddr <= va < split_end && self.addr_transl(va) == Some(pa),
        );
        let right_pas = Set::new(
            |pa: usize| exists|va: usize| va >= split_end && self.addr_transl(va) == Some(pa),
        );

        (
            MemView { mappings: left_mappings, memory: self.memory.restrict(left_pas) },
            MemView { mappings: right_mappings, memory: self.memory.restrict(right_pas) },
        )
    }

    /// Borrows a memory view for a sub-range.
    #[verifier::external_body]
    pub proof fn borrow_at(tracked &self, vaddr: usize, len: usize) -> (tracked r: &MemView)
        requires
            forall|va: usize|
                vaddr <= va < vaddr + len ==> {
                    &&& #[trigger] self.addr_transl(va) is Some
                },
        ensures
            r == self.borrow_at_spec(vaddr, len),
    {
        unimplemented!()
    }

    /// Splits the memory view into two disjoint views.
    ///
    /// Returns the split memory views where the first is
    /// for `[vaddr, vaddr + len)` and the second is for the rest.
    #[verifier::external_body]
    pub proof fn split(tracked self, vaddr: usize, len: usize) -> (tracked r: (Self, Self))
        ensures
            r == self.split_spec(vaddr, len),
    {
        unimplemented!()
    }

    /// This proves that if split is performed and we have
    /// (lhs, rhs) = self.split(vaddr, len), then we have
    /// all translations preserved in lhs and rhs.
    pub proof fn lemma_split_preserves_transl(
        original: MemView,
        vaddr: usize,
        len: usize,
        left: MemView,
        right: MemView,
    )
        requires
            original.split_spec(vaddr, len) == (left, right),
        ensures
            right.memory.dom().subset_of(original.memory.dom()),
            forall|va: usize|
                vaddr <= va < vaddr + len ==> {
                    #[trigger] original.addr_transl(va) == left.addr_transl(va)
                },
            forall|va: usize|
                va >= vaddr + len ==> {
                    #[trigger] original.addr_transl(va) == right.addr_transl(va)
                },
    {
        // Auto.
        assert(right.memory.dom().subset_of(original.memory.dom()));

        assert forall|va: usize| vaddr <= va < vaddr + len implies original.addr_transl(va)
            == left.addr_transl(va) by {
            assert(left.mappings =~= original.mappings.filter(
                |m: Mapping| m.va_range.start < vaddr + len && m.va_range.end > vaddr,
            ));
            let o_mappings = original.mappings.filter(
                |m: Mapping| m.va_range.start <= va < m.va_range.end,
            );
            let l_mappings = left.mappings.filter(
                |m: Mapping| m.va_range.start <= va < m.va_range.end,
            );

            assert(l_mappings.subset_of(o_mappings));
            assert(o_mappings.subset_of(l_mappings)) by {
                assert forall|m: Mapping| #[trigger]
                    o_mappings.contains(m) implies l_mappings.contains(m) by {
                    assume(o_mappings.contains(m));
                    assert(m.va_range.start < vaddr + len);
                    assert(m.va_range.end > vaddr);
                    assert(m.va_range.start <= va < m.va_range.end);
                    assert(left.mappings.contains(m));
                }
            };

            assert(o_mappings =~= l_mappings);
        }

        assert forall|va: usize| va >= vaddr + len implies original.addr_transl(va)
            == right.addr_transl(va) by {
            let split_end = vaddr + len;

            let o_mappings = original.mappings.filter(
                |m: Mapping| m.va_range.start <= va < m.va_range.end,
            );
            let r_mappings = right.mappings.filter(
                |m: Mapping| m.va_range.start <= va < m.va_range.end,
            );

            assert forall|m: Mapping| o_mappings.contains(m) implies r_mappings.contains(m) by {
                assert(m.va_range.end > va);
                assert(va >= split_end);
                assert(m.va_range.end > split_end);

                assert(right.mappings.contains(m));
                assert(r_mappings.contains(m));
            }

            assert(o_mappings =~= r_mappings);
        }
    }

    pub open spec fn join_spec(self, other: MemView) -> MemView {
        MemView {
            mappings: self.mappings.union(other.mappings),
            memory: self.memory.union_prefer_right(other.memory),
        }
    }

    /// Merges two disjoint memory views back into one.
    #[verifier::external_body]
    pub proof fn join(tracked self, tracked other: Self) -> (tracked r: Self)
        requires
            self.memory.dom().disjoint(other.memory.dom()),
        ensures
            r == self.join_spec(other),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn lemma_split_join_identity(
        this: MemView,
        lhs: MemView,
        rhs: MemView,
        vaddr: usize,
        len: usize,
    )
        requires
            this.split_spec(vaddr, len) == (lhs, rhs),
        ensures
            this == lhs.join_spec(rhs),
    {
        // Auto.
    }
}

impl Inv for VirtPtr {
    open spec fn inv(self) -> bool {
        &&& self.range@.start <= self.vaddr <= self.range@.end
        &&& self.range@.start > 0
        &&& self.range@.end >= self.range@.start
    }
}

impl Clone for VirtPtr {
    fn clone(&self) -> (res: Self)
        ensures
            res == self,
    {
        Self { vaddr: self.vaddr, range: Ghost(self.range@) }
    }
}

impl Copy for VirtPtr {

}

impl VirtPtr {
    pub open spec fn is_defined(self) -> bool {
        &&& self.vaddr != 0
        &&& self.range@.start <= self.vaddr <= self.range@.end
    }

    pub open spec fn is_valid(self) -> bool {
        &&& self.is_defined()
        &&& self.vaddr < self.range@.end
    }

    #[verifier::external_body]
    pub fn read(self, Tracked(mem): Tracked<&MemView>) -> u8
        requires
            mem.addr_transl(self.vaddr) is Some,
            mem.memory[mem.addr_transl(self.vaddr).unwrap()] is Init,
            self.is_valid(),
        returns
            mem.read(self.vaddr).unwrap().value(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn write(self, Tracked(mem): Tracked<&mut MemView>, x: u8)
        requires
            old(mem).addr_transl(self.vaddr) is Some,
            self.is_valid(),
        ensures
            mem == old(mem).write(self.vaddr, x).unwrap(),
    {
        unimplemented!()
    }

    pub open spec fn add_spec(self, n: usize) -> Self {
        VirtPtr { vaddr: (self.vaddr + n) as usize, range: self.range }
    }

    pub fn add(&mut self, n: usize)
        requires
    // Option 1: strict C standard compliance
    // old(self).range@.start <= self.vaddr + n <= old(self).range@.end,
    // Option 2: just make sure it doesn't overflow

            0 <= old(self).vaddr + n < usize::MAX,
        ensures
            self == old(self).add_spec(
                n,
            ),
    // If we take option 1, we can also ensure:
    // self.is_defined()

    {
        self.vaddr = self.vaddr + n
    }

    pub open spec fn read_offset_spec(self, mem: MemView, n: usize) -> u8 {
        mem.read((self.vaddr + n) as usize).unwrap().value()
    }

    /// Unlike `add`, we just create a temporary pointer value and read that
    /// When `self.vaddr == self.range.start` this acts like array index notation
    pub fn read_offset(&self, Tracked(mem): Tracked<&MemView>, n: usize) -> u8
        requires
            0 < self.vaddr + n < usize::MAX,
            self.range@.start <= self.vaddr + n < self.range@.end,
            mem.addr_transl((self.vaddr + n) as usize) is Some,
            mem.memory[mem.addr_transl((self.vaddr + n) as usize).unwrap()] is Init,
        returns
            self.read_offset_spec(*mem, n),
    {
        let mut tmp = self.clone();
        tmp.add(n);
        tmp.read(Tracked(mem))
    }

    pub open spec fn write_offset_spec(self, mem: MemView, n: usize, x: u8) -> MemView {
        mem.write((self.vaddr + n) as usize, x).unwrap()
    }

    pub fn write_offset(&self, Tracked(mem): Tracked<&mut MemView>, n: usize, x: u8)
        requires
            self.inv(),
            self.range@.start <= self.vaddr + n < self.range@.end,
            old(mem).addr_transl((self.vaddr + n) as usize) is Some,
    {
        let mut tmp = self.clone();
        tmp.add(n);
        tmp.write(Tracked(mem), x)
    }

    pub open spec fn copy_offset_spec(src: Self, dst: Self, mem: MemView, n: usize) -> MemView {
        let x = src.read_offset_spec(mem, n);
        dst.write_offset_spec(mem, n, x)
    }

    pub fn copy_offset(src: &Self, dst: &Self, Tracked(mem): Tracked<&mut MemView>, n: usize)
        requires
            src.inv(),
            dst.inv(),
            src.range@.start <= src.vaddr + n < src.range@.end,
            dst.range@.start <= dst.vaddr + n < dst.range@.end,
            old(mem).addr_transl((src.vaddr + n) as usize) is Some,
            old(mem).addr_transl((dst.vaddr + n) as usize) is Some,
            old(mem).memory.contains_key(old(mem).addr_transl((src.vaddr + n) as usize).unwrap()),
            old(mem).memory[old(mem).addr_transl((src.vaddr + n) as usize).unwrap()] is Init,
        ensures
            mem == Self::copy_offset_spec(*src, *dst, *old(mem), n),
    {
        let x = src.read_offset(Tracked(mem), n);
        proof { admit() }
        ;
        dst.write_offset(Tracked(mem), n, x)
    }

    pub open spec fn memcpy_spec(src: Self, dst: Self, mem: MemView, n: usize) -> MemView
        decreases n,
    {
        if n == 0 {
            mem
        } else {
            let mem = Self::copy_offset_spec(src, dst, mem, (n - 1) as usize);
            Self::memcpy_spec(src, dst, mem, (n - 1) as usize)
        }
    }

    /// Copies `n` bytes from `src` to `dst` in the given memory view.
    ///
    /// The source and destination must *not* overlap.
    /// `copy_nonoverlapping` is semantically equivalent to C’s `memcpy`,
    /// but with the source and destination arguments swapped.
    pub fn copy_nonoverlapping(
        src: &Self,
        dst: &Self,
        Tracked(mem): Tracked<&mut MemView>,
        n: usize,
    )
        requires
            src.inv(),
            dst.inv(),
            src.range@.start <= src.vaddr,
            src.vaddr + n <= src.range@.end,
            dst.range@.start <= dst.vaddr,
            dst.vaddr + n < dst.range@.end,
            src.range@.end <= dst.range@.start || dst.range@.end <= src.range@.start,
            forall|i: usize|
                src.vaddr <= i < src.vaddr + n ==> {
                    &&& #[trigger] old(mem).addr_transl(i) is Some
                    &&& old(mem).memory.contains_key(old(mem).addr_transl(i).unwrap())
                    &&& old(mem).memory[old(mem).addr_transl(i).unwrap()] is Init
                },
            forall|i: usize|
                dst.vaddr <= i < dst.vaddr + n ==> {
                    &&& old(mem).addr_transl(i) is Some
                },
        ensures
            mem == Self::memcpy_spec(*src, *dst, *old(mem), n),
        decreases n,
    {
        let ghost mem0 = *mem;

        if n == 0 {
            return ;
        } else {
            Self::copy_offset(src, dst, Tracked(mem), n - 1);
            assert(forall|i: usize|
                src.vaddr <= i < src.vaddr + n - 1 ==> mem.addr_transl(i) == mem0.addr_transl(i));
            Self::copy_nonoverlapping(src, dst, Tracked(mem), n - 1);
        }
    }

    pub fn from_vaddr(vaddr: usize, len: usize) -> (r: Self)
        requires
            vaddr != 0,
            0 < len <= usize::MAX - vaddr,
        ensures
            r.is_valid(),
            r.range@.start == vaddr,
            r.range@.end == (vaddr + len) as usize,
    {
        Self { vaddr, range: Ghost(Range { start: vaddr, end: (vaddr + len) as usize }) }
    }

    /// Executable helper to split the VirtPtr struct
    /// This updates the ghost ranges to match a MemView::split operation
    #[verus_spec(r =>
        requires
            self.is_valid(),
            0 <= n <= (self.range@.end - self.range@.start),
            self.vaddr == self.range@.start,
        ensures
            r.0.range@.start == self.range@.start,
            r.0.range@.end == self.range@.start + n,
            r.0.vaddr == self.range@.start,
            r.1.range@.start == self.range@.start + n,
            r.1.range@.end == self.range@.end,
            r.1.vaddr == self.range@.start + n,
    )]
    pub fn split(self, n: usize) -> (Self, Self) {
        let left = VirtPtr {
            vaddr: self.vaddr,
            range: Ghost(Range { start: self.vaddr, end: (self.vaddr + n) as usize }),
        };

        let right = VirtPtr {
            vaddr: self.vaddr + n,
            range: Ghost(Range { start: (self.vaddr + n) as usize, end: self.range@.end }),
        };

        (left, right)
    }
}

} // verus!
