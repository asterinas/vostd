use vstd::pervasive::arbitrary;
use vstd::prelude::*;

use vstd::layout;
use vstd::raw_ptr;
use vstd::set;
use vstd::set_lib;

use core::marker::PhantomData;
use core::ops::Range;

use crate::prelude::Inv;

verus! {

/// Concrete representation of a pointer
pub struct VirtPtr {
    pub vaddr: usize,
    pub ghost range: Ghost<Range<usize>>,
}

pub struct Mapping {
    pub va_range: Range<usize>,
    pub base_paddr: usize,
}

pub tracked struct MemView {
    pub mappings: Set<Mapping>,
    pub memory: Map<usize, raw_ptr::MemContents<u8>>,
}

impl MemView {
    pub open spec fn addr_transl(self, va: usize) -> Option<usize> {
        let mappings = self.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        if 0 < mappings.len() {
            let m = mappings.choose();  // In a well-formed PT there will only be one, but if malformed this is non-deterministic!
            let off = va - m.va_range.start;
            Some((m.base_paddr + off) as usize)
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

    pub open spec fn borrow_at_spec(&self, vaddr: usize, len: usize) -> &MemView {
        arbitrary()
    }

    pub open spec fn split_spec(self, vaddr: usize, len: usize) -> (MemView, MemView) {
        let split_end = vaddr + len;

        // The left part.
        let left = MemView {
            mappings: self.mappings.filter(
                |m: Mapping| m.va_range.start >= vaddr && m.va_range.end <= split_end,
            ),
            memory: self.memory.restrict(Set::new(|k: usize| vaddr <= k && k < split_end)),
        };

        let right = MemView {
            mappings: self.mappings.filter(|m: Mapping| m.va_range.start >= split_end),
            memory: self.memory.restrict(
            // Map restriction: keep keys k where k >= split_end
            Set::new(|k: usize| k >= split_end)),
        };

        (left, right)
    }

    /// Borrows a memory view for a sub-range.
    #[verifier::external_body]
    pub proof fn borrow_at(tracked &self, vaddr: usize, len: usize) -> (tracked r: &MemView)
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

    pub open spec fn join_spec(self, other: MemView) -> MemView {
        arbitrary()
    }

    /// Merges two disjoint memory views back into one.
    #[verifier::external_body]
    pub proof fn join(tracked self, tracked other: Self) -> (tracked r: Self)
        ensures
            r == self.join_spec(other),
    {
        unimplemented!()
    }
}

impl Inv for VirtPtr {
    open spec fn inv(self) -> bool {
        &&& self.range@.start > 0
        &&& self.range@.end - self.range@.start >= 0
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

    pub fn memcpy(src: &Self, dst: &Self, Tracked(mem): Tracked<&mut MemView>, n: usize)
        requires
            src.inv(),
            dst.inv(),
            src.range@.start <= src.vaddr,
            src.vaddr + n < src.range@.end,
            dst.range@.start <= dst.vaddr,
            dst.vaddr + n < dst.range@.end,
            src.range@.end <= dst.range@.start || dst.range@.end <= src.range@.start,
            forall|i: usize|
                src.vaddr <= i < src.vaddr + n ==> {
                    &&& old(mem).addr_transl(i) is Some
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
            Self::memcpy(src, dst, Tracked(mem), n - 1);
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
