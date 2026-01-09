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
    // The virtual address
    pub vaddr: usize,
    // what is the range?
    // so it's the range of the allocated memories?
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
    // pub open spec fn split(vaddr: usize, len: usize) -> (Self, Self) {
    //     arbitrary()
    // }
    // /// Splits the memory view into two disjoint views.
    // #[verifier::external_body]
    // pub proof fn tracked_split(self) -> (r: (Self, Self))
    //     ensures
    //         r == self.split(),
    // {
    //     unimplemented!()
    // }

}

impl Inv for VirtPtr {
    open spec fn inv(self) -> bool {
        &&& self.range@.start > 0
        &&& self.range@.end - self.range@.start > 0
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
}

} // verus!
