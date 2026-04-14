//! Virtual-memory specification model used by [`VmSpace`] proofs.
//!
//! This module defines:
//! - [`VirtPtr`], a specification-level virtual pointer over a bounded virtual range;
//! - [`FrameContents`], a physical-frame content model with alignment and range invariants;
//! - [`MemView`], a projection of virtual-to-physical mappings and frame contents that supports
//!   translation, read/write reasoning, borrowing, splitting, and joining.
//!
//! The model is intentionally verification-oriented (Verus specs/proofs) and is used by
//! [`crate::mm::vm_space`] to state and prove reader/writer permission isolation as well
//! as correctness of low-level virtual memory operations that are used by them.
//!
//! [`VmSpace`]: crate::mm::vm_space::VmSpace

use vstd::pervasive::arbitrary;
use vstd::prelude::*;

use vstd::layout;
use vstd::raw_ptr;
use vstd::set;
use vstd::set_lib;

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::{Paddr, Vaddr};
use crate::prelude::Inv;
use crate::specs::arch::mm::MAX_PADDR;
use crate::specs::mm::page_table::Mapping;

#[path = "virt_mem_example.rs"]
mod virt_mem_example;

verus! {

/// Specification-level virtual pointer with an associated half-open range.
///
/// [`VirtPtr`] models a C-like pointer used by verification code:
/// - `vaddr` is the current cursor position;
/// - `range` is the allocation-like bounds `[start, end)`.
///
/// Most operations require `is_valid()` (i.e., the current pointer is within
/// range and not one-past-end), while offset operations additionally require
/// the computed address to stay inside the same range.
pub struct VirtPtr {
    /// Current virtual address represented by this pointer value.
    pub vaddr: Vaddr,
    /// Logical bounds of the pointer's valid object/range.
    pub range: Ghost<Range<Vaddr>>,
}

/// Byte contents of one physical frame range tracked in a [`MemView`].
///
/// This is the physical-memory side of the model: each frame base `Paddr` maps
/// to a [`FrameContents`] value whose metadata (`size`, `range`) constrains how
/// `contents` can be interpreted.
pub ghost struct FrameContents {
    /// Per-byte initialization/value state for this frame.
    pub contents: Seq<raw_ptr::MemContents<u8>>,
    /// Frame size in bytes.
    pub size: usize,
    /// Physical range covered by this frame, modeled as `[start, end)`.
    pub range: Range<Paddr>,
}

impl Inv for FrameContents {
    /// Well-formedness invariant for [`FrameContents`].
    ///
    /// # Invariant
    /// - `contents.len() == size`.
    /// - `size == range.end - range.start`.
    /// - `range.start` and `range.end` are aligned to `size`.
    /// - `range` is ordered and remains below [`MAX_PADDR`].
    open spec fn inv(self) -> bool {
        &&& self.contents.len() == self.size@
        &&& self.size@ == self.range.end - self.range.start
        &&& self.range.start % self.size == 0
        &&& self.range.end % self.size == 0
        &&& self.range.start <= self.range.end < MAX_PADDR
    }
}


/// A local virtual-memory view used in proofs.
///
/// A [`MemView`] pairs:
/// - [`Self::mappings`]: a set of [`Mapping`] entries used by [`Self::addr_transl`];
/// - [`Self::memory`]: frame bytes keyed by physical frame base (`Paddr`) via [`FrameContents`].
///
/// In practice this view is obtained from [`GlobalMemView`] using
/// [`GlobalMemView::take_view`], then consumed by APIs such as [`VirtPtr::read`],
/// [`VirtPtr::write`], and higher-level ownership proofs in
/// [`VmSpaceOwner`].
///
/// [`VmSpaceOwner`]: crate::mm::vm_space::vm_space_specs::VmSpaceOwner
pub tracked struct MemView {
    /// Virtual-to-physical mapping set used for address translation.
    pub mappings: Set<Mapping>,
    /// Physical frame contents for mapped pages referenced by [`Self::mappings`].
    pub memory: Map<Paddr, FrameContents>
}

impl MemView {
    /// Translates a virtual address to `(frame_base_pa, frame_offset)`.
    ///
    /// Returns [`Option::None`] if no mapping in [`Self::mappings`] covers `va`.
    pub open spec fn addr_transl(self, va: usize) -> Option<(usize, usize)> {
        let mappings = self.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        if 0 < mappings.len() {
            let m = mappings.choose();  // In a well-formed PT there will only be one, but if malformed this is non-deterministic!
            let off = va - m.va_range.start;
            Some((m.pa_range.start, off as usize))
        } else {
            None
        }
    }

    /// Specification read through virtual translation.
    ///
    /// Equivalent to resolving via [`Self::addr_transl`] and reading from [`Self::memory`].
    pub open spec fn read(self, va: usize) -> raw_ptr::MemContents<u8> {
        let (pa, off) = self.addr_transl(va).unwrap();
        self.memory[pa].contents[off as int]
    }

    /// Specification write through virtual translation.
    ///
    /// Returns a new [`MemView`] with one byte updated, preserving all mappings.
    pub open spec fn write(self, va: usize, x: u8) -> Self {
        let (pa, off) = self.addr_transl(va).unwrap();
        MemView {
            memory: self.memory.insert(pa, FrameContents {
                contents: self.memory[pa].contents.update(off as int, raw_ptr::MemContents::Init(x)),
                size: self.memory[pa].size,
                range: self.memory[pa].range,
            }),
            ..self
        }
    }

    /// Whether two virtual addresses denote equal byte contents in this view.
    pub open spec fn eq_at(self, va1: usize, va2: usize) -> bool {
        let (pa1, off1) = self.addr_transl(va1).unwrap();
        let (pa2, off2) = self.addr_transl(va2).unwrap();
        self.memory[pa1].contents[off1 as int] == self.memory[pa2].contents[off2 as int]
    }

    /// Whether `va` is translated and mapped to frame base `pa`.
    pub open spec fn is_mapped(self, va: usize, pa: usize) -> bool {
        self.addr_transl(va) is Some && self.addr_transl(va).unwrap().0 == pa
    }

    /// Specification for borrowing a sub-view covering `[vaddr, vaddr + len)`.
    ///
    /// The result keeps overlapping mappings and restricts memory to physical
    /// frames reachable from that virtual range.
    pub open spec fn borrow_at_spec(&self, vaddr: usize, len: usize) -> MemView {
        let range_end = vaddr + len;

        let valid_pas = Set::new(
            |pa: usize|
                exists|va: usize|
                    vaddr <= va < range_end && #[trigger] self.is_mapped(va, pa),
        );

        MemView {
            mappings: self.mappings.filter(
                |m: Mapping| m.va_range.start < range_end && m.va_range.end > vaddr,
            ),
            memory: self.memory.restrict(valid_pas),
        }
    }

    /// Whether mappings in this view are pairwise VA-disjoint.
    pub open spec fn mappings_are_disjoint(self) -> bool {
        forall|m1: Mapping, m2: Mapping|
            #![trigger self.mappings.contains(m1), self.mappings.contains(m2)]
            self.mappings.contains(m1) && self.mappings.contains(m2) && m1 != m2 ==> {
                m1.va_range.end <= m2.va_range.start || m2.va_range.end <= m1.va_range.start
            }
    }

    /// Specification for splitting this view at `split_end = vaddr + len`.
    ///
    /// Returns `(left, right)` where:
    /// - `left` covers `[vaddr, split_end)`,
    /// - `right` covers addresses `>= split_end`.
    pub open spec fn split_spec(self, vaddr: usize, len: usize) -> (MemView, MemView) {
        let split_end = vaddr + len;

        // The left part.
        let left_mappings = self.mappings.filter(
            |m: Mapping| m.va_range.start < split_end && m.va_range.end > vaddr,
        );
        let right_mappings = self.mappings.filter(|m: Mapping| m.va_range.end > split_end);

        let left_pas = Set::new(
            |pa: usize|
                exists|va: usize| vaddr <= va < split_end && self.is_mapped(va, pa),
        );
        let right_pas = Set::new(
            |pa: usize| exists|va: usize| va >= split_end && self.is_mapped(va, pa),
        );

        (
            MemView { mappings: left_mappings, memory: self.memory.restrict(left_pas) },
            MemView { mappings: right_mappings, memory: self.memory.restrict(right_pas) },
        )
    }

    /// Executable proof wrapper of [`Self::borrow_at_spec`].
    ///
    /// # Verified Properties
    ///
    /// ## Postconditions
    /// - `r == self.borrow_at_spec(vaddr, len)`.
    #[verifier::external_body]
    pub proof fn borrow_at(tracked &self, vaddr: usize, len: usize) -> (tracked r: &MemView)
        ensures
            r == self.borrow_at_spec(vaddr, len),
    {
        unimplemented!()
    }


    /// Executable proof wrapper of [`Self::split_spec`].
    ///
    /// # Verified Properties
    ///
    /// ## Postconditions
    /// - `r == self.split_spec(vaddr, len)`.
    #[verifier::external_body]
    pub proof fn split(tracked self, vaddr: usize, len: usize) -> (tracked r: (Self, Self))
        ensures
            r == self.split_spec(vaddr, len),
    {
        unimplemented!()
    }

    /// Lemma: [`Self::split_spec`] preserves translation semantics on each side.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `original.split_spec(vaddr, len) == (left, right)`.
    ///
    /// ## Postconditions
    /// - `right.memory.dom().subset_of(original.memory.dom())`.
    /// - For any `va` in `[vaddr, vaddr + len)`,
    ///   `original.addr_transl(va) == left.addr_transl(va)`.
    /// - For any `va >= vaddr + len`,
    ///   `original.addr_transl(va) == right.addr_transl(va)`.
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

    /// Specification for merging two views.
    ///
    /// Mappings are unioned, and memory conflicts are resolved by
    /// [`vstd::map::Map::union_prefer_right`] with `other` taking precedence.
    pub open spec fn join_spec(self, other: MemView) -> MemView {
        MemView {
            mappings: self.mappings.union(other.mappings),
            memory: self.memory.union_prefer_right(other.memory),
        }
    }

    /// Executable proof wrapper of [`Self::join_spec`].
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `old(self).mappings.disjoint(other.mappings)`.
    ///
    /// ## Postconditions
    /// - `*self == old(self).join_spec(other)`.
    #[verifier::external_body]
    pub proof fn join(tracked &mut self, tracked other: Self)
        requires
            old(self).mappings.disjoint(other.mappings),
        ensures
            *final(self) == old(self).join_spec(other),
    {
        unimplemented!()
    }

    /// Lemma: splitting and then joining reconstructs the original view.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `this.split_spec(vaddr, len) == (lhs, rhs)`.
    /// - Every mapping in `this` starts at or after `vaddr`.
    /// - Every physical frame tracked by `this.memory` is reachable from some
    ///   virtual address at or after `vaddr`.
    ///
    /// ## Postconditions
    /// - `lhs.join_spec(rhs)` has the same mappings and memory contents as `this`.
    pub proof fn lemma_split_join_identity(
        this: MemView,
        lhs: MemView,
        rhs: MemView,
        vaddr: usize,
        len: usize,
    )
        requires
            this.split_spec(vaddr, len) == (lhs, rhs),
            forall|m: Mapping|
                #[trigger] this.mappings.contains(m) ==> vaddr <= m.va_range.start < m.va_range.end,
            forall|pa: Paddr|
                #[trigger] this.memory.contains_key(pa) ==> exists|va: usize|
                    vaddr <= va && #[trigger] this.is_mapped(va, pa),
        ensures
            this.mappings =~= lhs.join_spec(rhs).mappings,
            this.memory =~= lhs.join_spec(rhs).memory,
    {
    }
}

impl Inv for VirtPtr {
    open spec fn inv(self) -> bool {
        &&& self.range@.start <= self.vaddr <= self.range@.end
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
    /// Pure constructor specification for [`Self::new`].
    pub open spec fn new_spec(vaddr: Vaddr, len: usize) -> Self {
        Self { vaddr, range: Ghost(Range { start: vaddr, end: (vaddr + len) as usize }) }
    }

    /// Creates a pointer at `vaddr` with logical range `[vaddr, vaddr + len)`.
    ///
    /// # Verified Properties
    ///
    /// ## Postconditions
    /// - `result == Self::new_spec(vaddr, len)`.
    pub fn new(vaddr: Vaddr, len: usize) -> Self
        returns Self::new_spec(vaddr, len),
    {
        Self { vaddr, range: Ghost(Range { start: vaddr, end: (vaddr + len) as usize }) }
    }

    /// Whether the pointer has a non-null address and consistent bounds.
    pub open spec fn is_defined(self) -> bool {
        &&& self.vaddr != 0
        &&& self.range@.start <= self.vaddr <= self.range@.end
    }

    /// Whether dereferencing the current pointer position is allowed.
    ///
    /// This excludes the one-past-end position (`vaddr == range.end`).
    pub open spec fn is_valid(self) -> bool {
        &&& self.is_defined()
        &&& self.vaddr < self.range@.end
    }

    /// Reads one byte from `self.vaddr` in the provided memory view.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `mem.addr_transl(self.vaddr) is Some`.
    /// - Target byte is initialized:
    ///   `mem.memory[mem.addr_transl(self.vaddr).unwrap().0].contents[mem.addr_transl(self.vaddr).unwrap().1 as int] is Init`.
    /// - `self.is_valid()`.
    ///
    /// ## Postconditions
    /// - Returns `mem.read(self.vaddr).value()`.
    #[verifier::external_body]
    pub fn read(self, Tracked(mem): Tracked<&MemView>) -> u8
        requires
            mem.addr_transl(self.vaddr) is Some,
            mem.memory[mem.addr_transl(self.vaddr).unwrap().0].contents[mem.addr_transl(self.vaddr).unwrap().1 as int] is Init,
            self.is_valid(),
        returns
            mem.read(self.vaddr).value(),
    {
        unimplemented!()
    }

    /// Writes one byte to `self.vaddr` in the provided memory view.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `old(mem).addr_transl(self.vaddr) is Some`.
    /// - `self.is_valid()`.
    ///
    /// ## Postconditions
    /// - `*mem == old(mem).write(self.vaddr, x)`.
    #[verifier::external_body]
    pub fn write(self, Tracked(mem): Tracked<&mut MemView>, x: u8)
        requires
            old(mem).addr_transl(self.vaddr) is Some,
            self.is_valid(),
        ensures
            *final(mem) == old(mem).write(self.vaddr, x),
    {
        unimplemented!()
    }

    pub open spec fn add_spec(self, n: usize) -> Self {
        VirtPtr { vaddr: (self.vaddr + n) as usize, range: self.range }
    }

    /// Advances the pointer by `n` bytes.
    ///
    /// This operation only updates the cursor; it does not perform memory access.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `0 <= old(self).vaddr + n < usize::MAX`.
    ///
    /// ## Postconditions
    /// - `*self == old(self).add_spec(n)`.
    pub fn add(&mut self, n: usize)
        requires
    // Option 1: strict C standard compliance
    // old(self).range@.start <= self.vaddr + n <= old(self).range@.end,
    // Option 2: just make sure it doesn't overflow

            0 <= old(self).vaddr + n < usize::MAX,
        ensures
            *final(self) == old(self).add_spec(n),
    // If we take option 1, we can also ensure:
    // self.is_defined()

    {
        self.vaddr = self.vaddr + n
    }

    pub open spec fn read_offset_spec(self, mem: MemView, n: usize) -> u8 {
        mem.read((self.vaddr + n) as usize).value()
    }

    /// Reads from `self.vaddr + n` without mutating `self`.
    ///
    /// Implemented by creating a temporary pointer and calling [`Self::read`].
    /// When `self.vaddr == self.range.start`, this behaves like array indexing.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `0 < self.vaddr + n < usize::MAX`.
    /// - `self.range@.start <= self.vaddr + n < self.range@.end`.
    /// - `mem.addr_transl((self.vaddr + n) as usize) is Some`.
    /// - Target byte at offset is initialized.
    ///
    /// ## Postconditions
    /// - Returns `self.read_offset_spec(*mem, n)`.
    pub fn read_offset(&self, Tracked(mem): Tracked<&MemView>, n: usize) -> u8
        requires
            0 < self.vaddr + n < usize::MAX,
            self.range@.start <= self.vaddr + n < self.range@.end,
            mem.addr_transl((self.vaddr + n) as usize) is Some,
            mem.memory[mem.addr_transl((self.vaddr + n) as usize).unwrap().0].contents[mem.addr_transl((self.vaddr + n) as usize).unwrap().1 as int] is Init,
        returns
            self.read_offset_spec(*mem, n),
    {
        let mut tmp = self.clone();
        tmp.add(n);
        tmp.read(Tracked(mem))
    }

    pub open spec fn write_offset_spec(self, mem: MemView, n: usize, x: u8) -> MemView {
        mem.write((self.vaddr + n) as usize, x)
    }

    /// Writes to `self.vaddr + n` without mutating `self`.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `self.inv()`.
    /// - `self.range@.start <= self.vaddr + n < self.range@.end`.
    /// - `old(mem).addr_transl((self.vaddr + n) as usize) is Some`.
    pub fn write_offset(&self, Tracked(mem): Tracked<&mut MemView>, n: usize, x: u8)
        requires
            self.inv(),
            0 < self.vaddr + n < usize::MAX,
            self.range@.start <= self.vaddr + n < self.range@.end,
            old(mem).addr_transl((self.vaddr + n) as usize) is Some,
    {
        let mut tmp = self.clone();
        tmp.add(n);
        tmp.write(Tracked(mem), x)
    }

    pub open spec fn copy_offset_spec(src: Self, dst: Self, mem_src: MemView, mem_dst: MemView, n: usize) -> MemView {
        let x = src.read_offset_spec(mem_src, n);
        dst.write_offset_spec(mem_dst, n, x)
    }

    /// Copies one byte from `src + n` to `dst + n`.
    ///
    /// Source and destination are reasoned about via distinct memory views.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `src.inv()` and `dst.inv()`.
    /// - Source offset and destination offset are both in-range.
    /// - Source offset is mapped and initialized in `mem_src`.
    /// - Destination offset is mapped in `old(mem_dst)`.
    ///
    /// ## Postconditions
    /// - `*mem_dst == Self::copy_offset_spec(*src, *dst, *mem_src, *old(mem_dst), n)`.
    /// - `mem_dst.mappings == old(mem_dst).mappings`.
    /// - `mem_dst.memory.dom() == old(mem_dst).memory.dom()`.
    pub fn copy_offset(src: &Self, dst: &Self, Tracked(mem_src): Tracked<&MemView>, Tracked(mem_dst): Tracked<&mut MemView>, n: usize)
        requires
            src.inv(),
            dst.inv(),
            0 < src.vaddr + n < usize::MAX,
            0 < dst.vaddr + n < usize::MAX,
            src.range@.start <= src.vaddr + n < src.range@.end,
            mem_src.addr_transl((src.vaddr + n) as usize) is Some,
            mem_src.memory.contains_key(mem_src.addr_transl((src.vaddr + n) as usize).unwrap().0),
            mem_src.memory[mem_src.addr_transl((src.vaddr + n) as usize).unwrap().0].contents[mem_src.addr_transl((src.vaddr + n) as usize).unwrap().1 as int] is Init,

            dst.range@.start <= dst.vaddr + n < dst.range@.end,
            old(mem_dst).addr_transl((dst.vaddr + n) as usize) is Some,
        ensures
            *final(mem_dst) == Self::copy_offset_spec(*src, *dst, *mem_src, *old(mem_dst), n),
            final(mem_dst).mappings == old(mem_dst).mappings,
            final(mem_dst).memory.dom() == old(mem_dst).memory.dom(),

    {
        let x = src.read_offset(Tracked(mem_src), n);
        proof { admit() };
        dst.write_offset(Tracked(mem_dst), n, x)
    }

    pub open spec fn memcpy_spec(src: Self, dst: Self, mem_src: MemView, mem_dst: MemView, n: usize) -> MemView
        decreases n,
    {
        if n == 0 {
            mem_dst
        } else {
            let mem_dst_1 = Self::copy_offset_spec(src, dst, mem_src, mem_dst, (n - 1) as usize);

            Self::memcpy_spec(src, dst, mem_src, mem_dst_1, (n - 1) as usize)
        }
    }

    /// Copies `n` bytes from `src` to `dst` in the given memory view.
    ///
    /// The source and destination must *not* overlap.
    /// `copy_nonoverlapping` is semantically equivalent to C’s `memcpy`,
    /// but with the source and destination arguments swapped.
    ///
    /// `mem` points to `src`'s owned memory regions.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `src.inv()` and `dst.inv()`.
    /// - Source and destination ranges are non-overlapping.
    /// - Source slice `[src.vaddr, src.vaddr + n)` is in-range and initialized in `mem_src`.
    /// - Destination slice `[dst.vaddr, dst.vaddr + n)` is in-range and mapped in `old(mem_dst)`.
    ///
    /// ## Postconditions
    /// - `*mem_dst == Self::memcpy_spec(*src, *dst, *mem_src, *old(mem_dst), n)`.
    /// - `mem_dst.mappings == old(mem_dst).mappings`.
    /// - `mem_dst.memory.dom() == old(mem_dst).memory.dom()`.
    /// - Destination slice remains mapped in `mem_dst`.
    pub fn copy_nonoverlapping(
        src: &Self,
        dst: &Self,
        Tracked(mem_src): Tracked<&MemView>,
        Tracked(mem_dst): Tracked<&mut MemView>,
        n: usize,
    )
        requires
            src.inv(),
            dst.inv(),
            src.vaddr > 0,
            dst.vaddr > 0,
            src.range@.end <= dst.range@.start || dst.range@.end <= src.range@.start,
            src.range@.start <= src.vaddr,
            src.vaddr + n <= src.range@.end,
            forall|i: usize|
                #![trigger mem_src.addr_transl(i)]
                src.vaddr <= i < src.vaddr + n ==> {
                    &&& mem_src.addr_transl(i) is Some
                    &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                    &&& mem_src.memory[mem_src.addr_transl(i).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
                },
            dst.range@.start <= dst.vaddr,
            dst.vaddr + n <= dst.range@.end,
            forall|i: usize|
                dst.vaddr <= i < dst.vaddr + n ==> {
                    &&& old(mem_dst).addr_transl(i) is Some
                },
        ensures
            *final(mem_dst) == Self::memcpy_spec(*src, *dst, *mem_src, *old(mem_dst), n),
            final(mem_dst).mappings == old(mem_dst).mappings,
            final(mem_dst).memory.dom() == old(mem_dst).memory.dom(),
            forall|i: usize|
                #![trigger final(mem_dst).addr_transl(i)]
                dst.vaddr <= i < dst.vaddr + n ==> {
                    &&& final(mem_dst).addr_transl(i) is Some
            },
        decreases n,
    {
        if n == 0 {
            return ;
        } else {
            let ghost mem0 = *mem_dst;

            Self::copy_offset(src, dst, Tracked(mem_src), Tracked(mem_dst), n - 1);

            proof {
                assert(forall|i: usize|
                    dst.vaddr <= i < dst.vaddr + n - 1 ==>
                    mem_dst.addr_transl(i) == #[trigger] mem0.addr_transl(i)
                );
                assert forall|i: usize|
                    dst.vaddr <= i < dst.vaddr + n - 1 implies mem_dst.addr_transl(i) is Some by {
                    assert(mem_dst.addr_transl(i) == mem0.addr_transl(i));
                }
            }

            Self::copy_nonoverlapping(src, dst, Tracked(mem_src), Tracked(mem_dst), n - 1);
        }
    }

    /// Builds a valid [`VirtPtr`] from a concrete virtual-address range.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `vaddr != 0`.
    /// - `0 < len <= usize::MAX - vaddr`.
    ///
    /// ## Postconditions
    /// - `r.is_valid()`.
    /// - `r.range@.start == vaddr`.
    /// - `r.range@.end == (vaddr + len) as usize`.
    pub fn from_vaddr(vaddr: usize, len: usize) -> (r: Self)
        requires
            len <= usize::MAX - vaddr,
        ensures
            r.inv(),
            r.vaddr == vaddr,
            r.range@.start == vaddr,
            r.range@.end == (vaddr + len) as usize,
            vaddr != 0 && len > 0 ==> r.is_valid(),
    {
        Self { vaddr, range: Ghost(Range { start: vaddr, end: (vaddr + len) as usize }) }
    }

    /// Executable helper to split the [`VirtPtr`] into two contiguous ranges.
    ///
    /// This updates ghost ranges to match a split operation over the same region.
    ///
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// - `self.is_valid()`.
    /// - `0 <= n <= self.range@.end - self.range@.start`.
    /// - `self.vaddr == self.range@.start`.
    ///
    /// ## Postconditions
    /// - Left pointer covers `[self.range@.start, self.range@.start + n)`.
    /// - Right pointer covers `[self.range@.start + n, self.range@.end)`.
    #[verus_spec(r =>
        requires
            self.is_valid(),
            0 <= n <= self.range@.end - self.range@.start,
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

/// A [`GlobalMemView`] is a more abstract view of memory that elides most of the details. The API specifications
/// of higher-level objects like [`VmSpaceOwner`](crate::specs::mm::vm_space::VmSpaceOwner) use this view.
pub tracked struct GlobalMemView {
    pub pt_mappings: Set<Mapping>,
    pub tlb_mappings: Set<Mapping>,
    pub unmapped_pas: Set<Paddr>,
    pub memory: Map<Paddr, FrameContents>,
}

impl Inv for GlobalMemView {

    open spec fn inv(self) -> bool {
        &&& forall |m: Mapping| #![auto] self.tlb_mappings.contains(m) ==> {
            &&& m.inv()
            &&& forall|pa: Paddr| m.pa_range.start <= pa < m.pa_range.end ==> {
                &&& self.memory.dom().contains(pa)
            }
            &&& self.memory.contains_key(m.pa_range.start)
            &&& self.memory[m.pa_range.start].size == m.page_size
            &&& self.memory[m.pa_range.start].inv()
        }
        &&& forall |m: Mapping|
            forall |n: Mapping| #![auto]
            self.tlb_mappings.contains(m) ==>
            self.tlb_mappings.contains(n) ==>
            m != n ==>
            #[trigger]
            m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start
        &&& self.tlb_mappings.finite()
        &&& self.pt_mappings.finite()
        &&& self.memory.dom().finite()
        &&& self.all_pas_accounted_for()
        &&& self.pas_uniquely_mapped()
        &&& self.unmapped_correct()
    }
}

impl GlobalMemView {

    pub open spec fn addr_transl(self, va: usize) -> Option<(usize, usize)> {
        let mappings = self.tlb_mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        if 0 < mappings.len() {
            let m = mappings.choose();  // In a well-formed TLB there will only be one, but if malformed this is non-deterministic!
            let off = va - m.va_range.start;
            Some((m.pa_range.start, off as usize))
        } else {
            None
        }
    }

    pub open spec fn is_mapped(self, pa: usize) -> bool {
        exists|m: Mapping| self.tlb_mappings.contains(m) && m.pa_range.start <= pa < m.pa_range.end
    }

    pub open spec fn all_pas_accounted_for(self) -> bool {
        forall|pa: Paddr|
            0 <= pa < MAX_PADDR ==>
            #[trigger] self.is_mapped(pa) || #[trigger] self.unmapped_pas.contains(pa)
    }

    pub open spec fn pas_uniquely_mapped(self) -> bool {
        forall|m1: Mapping, m2: Mapping|
             #[trigger] self.tlb_mappings.contains(m1) && #[trigger] self.tlb_mappings.contains(m2) && m1 != m2 ==>
            m1.pa_range.end <= m2.pa_range.start || m2.pa_range.end <= m1.pa_range.start
    }

    pub open spec fn unmapped_correct(self) -> bool {
        forall|pa: Paddr|
            #![auto]
            self.is_mapped(pa) <==> !self.unmapped_pas.contains(pa)
    }

    pub open spec fn take_view_spec(self, vaddr: usize, len: usize) -> (Self, MemView) {
        let range_end = vaddr + len;

        let leave_mappings: Set<Mapping> = self.tlb_mappings.filter(
            |m: Mapping| m.va_range.end <= vaddr || m.va_range.start > range_end
        );

        let take_mappings = self.tlb_mappings.filter(
            |m: Mapping| m.va_range.start < range_end && m.va_range.end > vaddr
        );

        let leave_pas = Set::new(
            |pa: usize|
                exists|m: Mapping| leave_mappings.contains(m) && m.pa_range.start <= pa < m.pa_range.end
        );
        let take_pas = Set::new(
            |pa: usize|
                exists|m: Mapping| take_mappings.contains(m) && m.pa_range.start <= pa < m.pa_range.end
        );

        (
            GlobalMemView {
                tlb_mappings: leave_mappings,
                memory: self.memory.restrict(leave_pas),
                ..self
            },
            MemView { mappings: take_mappings, memory: self.memory.restrict(take_pas) },
        )
    }

    pub axiom fn take_view(tracked &mut self, vaddr: usize, len: usize) -> (tracked view: MemView)
        ensures
            *final(self) == old(self).take_view_spec(vaddr, len).0,
            view == old(self).take_view_spec(vaddr, len).1;

    pub open spec fn return_view_spec(self, view: MemView) -> Self {
        GlobalMemView {
            tlb_mappings: self.tlb_mappings.union(view.mappings),
            memory: self.memory.union_prefer_right(view.memory),
            ..self
        }
    }

    pub axiom fn return_view(&mut self, view: MemView)
        ensures
            *final(self) == old(self).return_view_spec(view);

    pub open spec fn tlb_flush_vaddr_spec(self, vaddr: Vaddr) -> Self {
        let tlb_mappings = self.tlb_mappings.filter(
            |m: Mapping| m.va_range.end <= vaddr || vaddr < m.va_range.start
        );
        GlobalMemView {
            tlb_mappings,
            ..self
        }
    }

    pub axiom fn tlb_flush_vaddr(&mut self, vaddr: Vaddr)
        requires
            old(self).inv()
        ensures
            *final(self) == old(self).tlb_flush_vaddr_spec(vaddr),
            final(self).inv();

    pub open spec fn tlb_soft_fault_spec(self, vaddr: Vaddr) -> Self {
        let mapping = self.pt_mappings.filter(|m: Mapping| m.va_range.start <= vaddr < m.va_range.end).choose();
        GlobalMemView {
            tlb_mappings: self.tlb_mappings.insert(mapping),
            ..self
        }
    }

    pub axiom fn tlb_soft_fault(tracked &mut self, vaddr: Vaddr)
        requires
            old(self).inv(),
            old(self).addr_transl(vaddr) is None,
        ensures
            *final(self) == old(self).tlb_soft_fault_spec(vaddr),
            final(self).inv();

    pub open spec fn pt_map_spec(self, m: Mapping) -> Self {
        let pt_mappings = self.pt_mappings.insert(m);
        let unmapped_pas = self.unmapped_pas.difference(
            Set::new(|pa: usize| m.pa_range.start <= pa < m.pa_range.end)
        );
        GlobalMemView {
            pt_mappings,
            unmapped_pas,
            ..self
        }
    }

    pub axiom fn pt_map(&mut self, m: Mapping)
        requires
            forall|pa: Paddr|
                m.pa_range.start <= pa < m.pa_range.end ==>
                old(self).unmapped_pas.contains(pa),
            old(self).inv()
        ensures
            *final(self) == old(self).pt_map_spec(m);

    pub open spec fn pt_unmap_spec(self, m: Mapping) -> Self {
        let pt_mappings = self.pt_mappings.remove(m);
        let unmapped_pas = self.unmapped_pas.union(
            Set::new(|pa: usize| m.pa_range.start <= pa < m.pa_range.end)
        );
        GlobalMemView {
            pt_mappings,
            unmapped_pas,
            ..self
        }
    }

    pub axiom fn pt_unmap(&mut self, m: Mapping)
        requires
            old(self).pt_mappings.contains(m),
            old(self).inv()
        ensures
            *final(self) == old(self).pt_unmap_spec(m),
            final(self).inv();

    pub proof fn lemma_va_mapping_unique(self, va: usize)
        requires
            self.inv(),
        ensures
            self.tlb_mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end).is_singleton(),
    {
        admit()
    }
}

} // verus!
