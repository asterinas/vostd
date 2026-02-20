// SPDX-License-Identifier: MPL-2.0
//! A contiguous range of frames.
use vstd::prelude::*;
use vstd_extra::seq_extra::{seq_tracked_map_values, seq_tracked_new, seq_tracked_subrange};

use core::{fmt::Debug, mem::ManuallyDrop, ops::Range};

use crate::mm::frame::{inc_frame_ref_count, untyped::AnyUFrameMeta, Frame};

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::meta::mapping::{frame_to_index, frame_to_index_spec, meta_addr, meta_to_frame_spec};
use super::{AnyFrameMeta, GetFrameError, MetaPerm, MetaSlot};
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use vstd_extra::undroppable::*;

verus! {

/// A contiguous range of homogeneous physical memory frames.
///
/// This is a handle to multiple contiguous frames. It will be more lightweight
/// than owning an array of frame handles.
///
/// The ownership is achieved by the reference counting mechanism of frames.
/// When constructing a [`Segment`], the frame handles are created then
/// forgotten, leaving the reference count. When dropping a it, the frame
/// handles are restored and dropped, decrementing the reference count.
///
/// All the metadata of the frames are homogeneous, i.e., they are of the same
/// type.
#[repr(transparent)]
pub struct Segment<M: AnyFrameMeta + ?Sized> {
    /// The physical address range of the segment.
    pub range: Range<Paddr>,
    /// Marker for the metadata type.
    pub _marker: core::marker::PhantomData<M>,
}

// TODO: treat `manually_drop` as equivalent to `into_raw`
impl<M: AnyFrameMeta + ?Sized> Undroppable for Segment<M> {
    type State = MetaRegionOwners;

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        s0 =~= s1
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) {
        admit()
    }
}

/// A [`SegmentOwner<M>`] holds the permission tokens for all frames in the
/// [`Segment<M>`] for verification purposes.
pub tracked struct SegmentOwner<M: AnyFrameMeta + ?Sized> {
    /// The permissions for all frames in the segment, which must be well-formed and valid.
    pub perms: Seq<MetaPerm<M>>,
}

impl<M: AnyFrameMeta + ?Sized> Inv for Segment<M> {
    /// The invariant of a [`Segment`]:
    ///
    /// - the physical addresses of the frames are aligned and within bounds.
    /// - the range is well-formed, i.e., the start is less than or equal to the end.
    open spec fn inv(self) -> bool {
        &&& self.range.start % PAGE_SIZE == 0
        &&& self.range.end % PAGE_SIZE == 0
        &&& self.range.start <= self.range.end < MAX_PADDR
    }
}

impl<M: AnyFrameMeta + ?Sized> Inv for SegmentOwner<M> {
    /// The invariant of a [`Segment`]:
    ///
    /// - the permissions are well-formed and valid;
    /// - the physical addresses of the permissions are aligned and within bounds.
    open spec fn inv(self) -> bool {
        &&& forall|i: int|
            #![trigger self.perms[i]]
            0 <= i < self.perms.len() as int ==> {
                &&& self.perms[i].addr() % PAGE_SIZE == 0
                &&& self.perms[i].addr() < MAX_PADDR
                &&& self.perms[i].wf()
                &&& self.perms[i].is_init()
            }
    }
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The invariant of a [`Segment`] with a specific owner, such that besides [`Self::inv`]:
    ///
    /// - the number of permissions in the owner matches the number of frames in the segment;
    /// - the physical address of each permission matches the corresponding frame in the segment.
    ///
    /// Interested readers are encouraged to see [`frame_to_index`] and [`meta_addr`] for how
    /// we convert between physical addresses and meta region indices.
    pub open spec fn inv_with(&self, owner: &SegmentOwner<M>) -> bool {
        &&& self.inv()
        &&& owner.perms.len() * PAGE_SIZE == self.range.end - self.range.start
        &&& forall|i: int|
            #![trigger owner.perms[i]]
            0 <= i < owner.perms.len() as int ==> owner.perms[i].addr() == meta_addr(
                frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
            )
    }
}

impl<M: AnyFrameMeta + ?Sized> SegmentOwner<M> {
    /// Checks if this [`SegmentOwner`] is disjoint with the meta region in the given
    /// [`MetaRegionOwners`].
    ///
    /// We check the disjointness by ensuring that for each frame in the segment,
    /// its corresponding slot in the meta region is not dropped.
    pub open spec fn is_disjoint_with_meta_region(&self, region: &MetaRegionOwners) -> bool {
        forall|i: int|
            #![trigger self.perms[i]]
            0 <= i < self.perms.len() as int ==> {
                &&& !region.dropped_slots.contains_key(frame_to_index_spec(self.perms[i].addr()))
            }
    }
}

/// A contiguous range of homogeneous untyped physical memory frames that have any metadata.
///
/// In other words, the metadata of the frames are of the same type, and they
/// are untyped, but the type of metadata is not known at compile time. An
/// [`USegment`] as a parameter accepts any untyped segments.
///
/// The usage of this frame will not be changed while this object is alive.
pub type USegment = Segment<dyn AnyUFrameMeta>;

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Segment<M> {
    /// Returns the starting physical address of the contiguous frames.
    #[verifier::inline]
    pub open spec fn start_paddr_spec(&self) -> Paddr
        recommends
            self.inv(),
    {
        self.range.start
    }

    /// Returns the ending physical address of the contiguous frames.
    #[verifier::inline]
    pub open spec fn end_paddr_spec(&self) -> Paddr
        recommends
            self.inv(),
    {
        self.range.end
    }

    /// Returns the length in bytes of the contiguous frames.
    #[verifier::inline]
    pub open spec fn size_spec(&self) -> usize
        recommends
            self.inv(),
    {
        (self.range.end - self.range.start) as usize
    }

    /// Returns the number of pages of the contiguous frames.
    #[verifier::inline]
    pub open spec fn nrpage_spec(&self) -> usize
        recommends
            self.inv(),
    {
        self.size_spec() / PAGE_SIZE
    }

    /// Splits the contiguous frames into two at the given byte offset from the start in spec mode.
    pub open spec fn split_spec(self, offset: usize) -> (Self, Self)
        recommends
            self.inv(),
            offset % PAGE_SIZE == 0,
            0 < offset < self.size_spec(),
    {
        let at = (self.range.start + offset) as usize;
        let idx = at / PAGE_SIZE;
        (
            Self { range: self.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..self.range.end, _marker: core::marker::PhantomData },
        )
    }

    /// Gets the start physical address of the contiguous frames.
    #[inline(always)]
    #[verifier::when_used_as_spec(start_paddr_spec)]
    pub fn start_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        returns
            self.start_paddr_spec(),
    {
        self.range.start
    }

    /// Gets the end physical address of the contiguous frames.
    #[inline(always)]
    #[verifier::when_used_as_spec(end_paddr_spec)]
    pub fn end_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        returns
            self.end_paddr_spec(),
    {
        self.range.end
    }

    /// Gets the length in bytes of the contiguous frames.
    #[inline(always)]
    #[verifier::when_used_as_spec(size_spec)]
    pub fn size(&self) -> (res: usize)
        requires
            self.inv(),
        returns
            self.size_spec(),
    {
        self.range.end - self.range.start
    }

    /// The wrapper for the precondition for [`Self::from_unused`]:
    ///
    /// - the metadata function must be well-formed and valid for all frames in the range;
    /// - the metadata function must ensure that the frames can be created and owned by the segment.
    /// - for any frame created via the closure `metadata_fn`, the corresponding slot in `regions`
    ///   must be unused and not dropped in the owner ([`MetaRegionOwners`]).
    pub open spec fn from_unused_requires(
        regions: MetaRegionOwners,
        range: Range<Paddr>,
        metadata_fn: impl Fn(Paddr) -> (Paddr, M),
    ) -> bool {
        &&& regions.inv()
        &&& range.start % PAGE_SIZE == 0
        &&& range.end % PAGE_SIZE == 0
        &&& range.start <= range.end < MAX_PADDR
        &&& forall|paddr_in: Paddr|
            (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                &&& metadata_fn.requires((paddr_in,))
            }
        &&& forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
            metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                &&& paddr_out < MAX_PADDR
                &&& paddr_out % PAGE_SIZE == 0
                &&& paddr_in == paddr_out
                &&& regions.slots.contains_key(frame_to_index(paddr_out))
                &&& !regions.dropped_slots.contains_key(frame_to_index(paddr_out))
                &&& regions.slot_owners[frame_to_index(paddr_out)].usage is Unused
                &&& regions.slot_owners[frame_to_index(paddr_out)].in_list.points_to(0)
            }
    }

    /// The wrapper for the postcondition for [`Self::from_unused`]:
    ///
    /// - if the result is `Ok`, then the returned segment must satisfy the invariant with the owner;
    /// - the returned segment must have the same physical address range as the input;
    /// - the returned owner must be `Some` if the result is `Ok`, and the owner must satisfy the invariant;
    pub open spec fn from_unused_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        owner: Option<SegmentOwner<M>>,
        range: Range<Paddr>,
        metadata_fn: impl Fn(Paddr) -> (Paddr, M),
        r: Result<Self, GetFrameError>,
    ) -> bool {
        &&& r matches Ok(r) ==> {
            &&& new_regions.inv()
            &&& r.range.start == range.start
            &&& r.range.end == range.end
            &&& owner matches Some(owner) && {
                &&& r.inv_with(&owner)
                &&& forall|i: int|
                    #![trigger owner.perms[i]]
                    0 <= i < owner.perms.len() as int ==> {
                        &&& owner.perms[i].addr() == meta_addr(
                            frame_to_index_spec((range.start + i * PAGE_SIZE) as usize),
                        )
                    }
                &&& new_regions.paddr_range_not_in_region(range)
            }
        }
    }

    /// The wrapper for the precondition for [`Self::split`]:
    ///
    /// - the segment must satisfy the invariant with the owner ([`Self::inv_with`])
    /// - the offset must be aligned and within bounds.
    pub open spec fn split_requires(self, owner: SegmentOwner<M>, offset: usize) -> bool {
        &&& self.inv_with(&owner)
        &&& offset % PAGE_SIZE == 0
        &&& 0 < offset < self.size()
    }

    /// The wrapper for the postcondition for [`Self::split`]:
    ///
    /// - the resulting segments must satisfy the invariant with the corresponding owners;
    /// - the resulting segments must be the same as the result of [`Self::split_spec`];
    /// - the permissions in the original owner must be split into the resulting owners.
    pub open spec fn split_ensures(
        self,
        offset: usize,
        lhs: Self,
        rhs: Self,
        ori_owner: SegmentOwner<M>,
        lhs_owner: SegmentOwner<M>,
        rhs_owner: SegmentOwner<M>,
    ) -> bool {
        &&& lhs.inv_with(&lhs_owner)
        &&& rhs.inv_with(&rhs_owner)
        &&& (lhs, rhs) == self.split_spec(offset)
        &&& ori_owner.perms =~= (lhs_owner.perms + rhs_owner.perms)
    }

    /// The wrapper for the precondition for [`Self::into_raw`]:
    ///
    /// - the segment must satisfy the invariant with the owner;
    /// - the meta region in `regions` must satisfy the invariant and be disjoint with the segment
    ///   (see [`SegmentOwner::is_disjoint_with_meta_region`]).
    pub open spec fn into_raw_requires(
        self,
        regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
    ) -> bool {
        &&& self.inv_with(&owner)
        &&& regions.inv()
        &&& owner.inv()
        &&& owner.is_disjoint_with_meta_region(&regions)
    }

    /// The wrapper for the postcondition for [`Self::into_raw`]:
    ///
    /// - the returned physical address range must be the same as the segment's range;
    /// - the corresponding slots in `regions` must be dropped and match the type `M`
    ///   for all frames in the range (see [`MetaRegionOwners::paddr_range_in_dropped_region`]);
    pub open spec fn into_raw_ensures(
        self,
        regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
        r: Range<Paddr>,
    ) -> bool {
        &&& r == self.range
        &&& regions.inv()
        &&& regions.paddr_range_in_dropped_region(self.range)
    }

    /// The wrapper for the precondition for [`Self::from_raw`]:
    ///
    /// - the range must be a forgotten [`Segment`] that matches the type `M`;
    /// - the corresponding slots in `regions` must be dropped and match the type `M`
    ///   for all frames in the range (see [`MetaRegionOwners::paddr_range_in_dropped_region`]);
    /// - the range must be aligned and within bounds.
    pub open spec fn from_raw_requires(regions: MetaRegionOwners, range: Range<Paddr>) -> bool {
        &&& regions.inv()
        &&& regions.paddr_range_in_dropped_region(range)
        &&& range.start % PAGE_SIZE == 0
        &&& range.end % PAGE_SIZE == 0
        &&& range.start < range.end < MAX_PADDR
    }

    /// The wrapper for the postcondition for [`Self::from_raw`]:
    ///
    /// - the returned segment must satisfy the invariant with the returned owner;
    /// - the returned segment must have the same physical address range as the input;
    ///
    /// See also [`MetaRegionOwners::paddr_range_not_in_region`].
    pub open spec fn from_raw_ensures(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        owner: SegmentOwner<M>,
        range: Range<Paddr>,
    ) -> bool {
        &&& self.inv_with(&owner)
        &&& self.range == range
        &&& new_regions.inv()
        &&& new_regions.paddr_range_not_in_region(range)
    }

    /// The wrapper for the precondition for slicing a segment with a given range:
    ///
    /// - the segment must satisfy the invariant with the owner ([`Self::inv_with`])
    /// - the slicing range must be aligned and within bounds of the segment.
    pub open spec fn slice_requires(self, owner: SegmentOwner<M>, range: Range<Paddr>) -> bool {
        &&& self.inv_with(&owner)
        &&& range.start % PAGE_SIZE == 0
        &&& range.end % PAGE_SIZE == 0
        &&& self.range.start + range.start <= self.range.start + range.end <= self.range.end
    }

    /// The wrapper for the postcondition for slicing a segment with a given range:
    ///
    /// - the resulting slice must satisfy the invariant with the owner;
    /// - the resulting slice must have the same physical address range as the slicing range.
    ///
    /// See also [`vstd::seq::Seq::subrange`].
    pub open spec fn slice_ensures(
        self,
        owner: SegmentOwner<M>,
        range: Range<Paddr>,
        res: Self,
    ) -> bool {
        &&& res.inv_with(
            &SegmentOwner {
                perms: owner.perms.subrange(
                    (range.start / PAGE_SIZE) as int,
                    (range.end / PAGE_SIZE) as int,
                ),
            },
        )
    }

    /// Checks if the current segment can be iterated to get the next frame:
    ///
    /// - the segment and meta regions must satisfy their respective invariants;
    /// - the next frame (the one right after the end of the segment) must be dropped in `regions` and not in `slots`.
    pub open spec fn next_requires(self, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& regions.dropped_slots.contains_key(frame_to_index(self.range.start))
        &&& !regions.slots.contains_key(frame_to_index(self.range.start))
    }

    /// The wrapper for the postcondition for iterating to the next frame:
    ///
    /// - if the result is [`None`], then the segment must be extended by one frame;
    /// - if the result is [`Some`], then the segment must be extended by one frame and
    ///   the returned frame must be the next frame, and the corresponding slot in `regions`
    ///   must be not dropped and match the type `M`.
    pub open spec fn next_ensures(
        old_self: Self,
        new_self: Self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        res: Option<Frame<M>>,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_self.inv()
        &&& match res {
            None => { &&& new_self.range.start == old_self.range.end },
            Some(f) => {
                &&& new_self.range.start == old_self.range.start + PAGE_SIZE
                &&& f.paddr() == old_self.range.start
                &&& forall|i: usize|
                    #![trigger new_regions.dropped_slots[i], old_regions.dropped_slots[i]]
                    {
                        &&& i != frame_to_index(f.paddr()) ==> old_regions.dropped_slots[i]
                            == new_regions.dropped_slots[i]
                        &&& i == frame_to_index(f.paddr())
                            ==> !new_regions.dropped_slots.contains_key(i)
                    }
            },
        }
    }

    /// Creates a new [`Segment`] from unused frames.
    ///
    /// The caller must provide a closure to initialize metadata for all the frames.
    /// The closure receives the physical address of the frame and returns the
    /// metadata, which is similar to [`core::array::from_fn`].
    ///
    /// It returns an error if:
    ///  - any of the frames cannot be created with a specific reason.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::from_unused_requires`].
    /// ## Postconditions
    /// See [`Self::from_unused_ensures`].
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> owner: Tracked<Option<SegmentOwner<M>>>,
        requires
            Self::from_unused_requires(*old(regions), range, metadata_fn),
        ensures
            Self::from_unused_ensures(*old(regions), *regions, owner@, range, metadata_fn, r),
    )]
    pub fn from_unused(range: Range<Paddr>, metadata_fn: impl Fn(Paddr) -> (Paddr, M)) -> (res:
        Result<Self, GetFrameError>) {
        proof_decl! {
            let tracked mut owner: Option<SegmentOwner<M>> = None;
            let tracked mut addrs = Seq::<usize>::tracked_empty();
        }
        // Construct a segment early to recycle previously forgotten frames if
        // the subsequent operations fails in the middle.
        let mut segment = Self {
            range: range.start..range.start,
            _marker: core::marker::PhantomData,
        };

        let mut i = 0;
        let addr_len = (range.end - range.start) / PAGE_SIZE;

        #[verus_spec(
            invariant
                i <= addr_len,
                i as int == addrs.len(),
                range.start % PAGE_SIZE == 0,
                range.end % PAGE_SIZE == 0,
                range.start <= range.start + i * PAGE_SIZE <= range.end,
                range.end == range.start + addr_len * PAGE_SIZE,
                addr_len == (range.end - range.start) / PAGE_SIZE as int,
                i <= addr_len,
                forall|paddr_in: Paddr|
                    (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                        &&& metadata_fn.requires((paddr_in,))
                    },
                forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                    metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                        &&& paddr_out < MAX_PADDR
                        &&& paddr_out % PAGE_SIZE == 0
                        &&& paddr_in == paddr_out
                        &&& regions.slots.contains_key(frame_to_index(paddr_out))
                        &&& !regions.dropped_slots.contains_key(frame_to_index(paddr_out))
                        &&& regions.slot_owners[frame_to_index(paddr_out)].usage is Unused
                        &&& regions.slot_owners[frame_to_index(paddr_out)].in_list.points_to(0)
                    },
                forall|j: int|
                    0 <= j < addrs.len() as int ==> {
                        &&& regions.slots.contains_key(frame_to_index_spec(addrs[j]))
                        &&& !regions.dropped_slots.contains_key(frame_to_index_spec(addrs[j]))
                        &&& addrs[j] % PAGE_SIZE == 0
                        &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                    },
                forall|paddr: Paddr| #[trigger]
                    old(regions).slots.contains_key(frame_to_index(paddr))
                        ==> regions.slots.contains_key(frame_to_index(paddr)),
                regions.inv(),
                segment.range.start == range.start,
                segment.range.end == range.start + i * PAGE_SIZE,
            decreases addr_len - i,
        )]
        while i < addr_len {
            let paddr = range.start + i * PAGE_SIZE;
            let (paddr, meta) = metadata_fn(paddr);

            let frame = match #[verus_spec(with Tracked(regions))]
            Frame::<M>::from_unused(paddr, meta) {
                Ok(f) => f,
                Err(e) => {
                    return {
                        proof_with!(|= Tracked(owner));
                        Err(e)
                    };
                },
            };

            proof {
                assert(forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                    metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                        &&& regions.slot_owners[frame_to_index(paddr_out)].usage is Unused
                        &&& regions.slot_owners[frame_to_index(paddr_out)].in_list.points_to(0)
                    }) by {
                    admit();
                }
                assert(frame.constructor_requires(*old(regions))) by { admit() };
            }

            let _ = NeverDrop::new(frame, Tracked(regions));
            segment.range.end = paddr + PAGE_SIZE;
            proof {
                addrs.tracked_push(paddr);
                admit();
            }

            i += 1;
        }

        proof {
            broadcast use vstd_extra::map_extra::lemma_map_remove_keys_finite;
            broadcast use vstd_extra::seq_extra::lemma_seq_to_set_map_contains;
            broadcast use vstd::map::group_map_axioms;
            broadcast use vstd::map_lib::group_map_extra;

            let tracked owner_seq = seq_tracked_map_values(
                addrs,
                |addr: usize|
                    {
                        let perm = regions.slots[frame_to_index(addr)];
                        MetaPerm {
                            addr: meta_addr(frame_to_index(addr)),
                            points_to: perm,
                            _T: core::marker::PhantomData,
                        }
                    },
            );
            owner = Some(SegmentOwner { perms: owner_seq });

            let index = addrs.map_values(|addr: Paddr| frame_to_index(addr)).to_set();
            regions.slots.tracked_remove_keys(index);

            assert forall|addr: usize|
                #![trigger frame_to_index_spec(addr)]
                range.start <= addr < range.end && addr % PAGE_SIZE == 0 implies {
                &&& !regions.slots.contains_key(frame_to_index_spec(addr))
                &&& !regions.dropped_slots.contains_key(frame_to_index_spec(addr))
            } by {
                // proof by contradiction
                assert(addrs.contains(addr)) by {
                    if !addrs.contains(addr) {
                        let j = (addr - range.start) / PAGE_SIZE as int;
                        assert(0 <= j < addrs.len() as usize) by {
                            assert(addr >= range.start);
                            assert(addr < range.end);
                            assert(addr % PAGE_SIZE == 0);
                        };
                        assert(addrs[j as int] == addr);
                    }
                }
            }
        }

        proof_with!(|= Tracked(owner));
        Ok(segment)
    }

    /// Splits the frames into two at the given byte offset from the start.
    ///
    /// The resulting frames cannot be empty. So the offset cannot be neither
    /// zero nor the length of the frames.
    /// 
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::split_requires`].
    /// 
    /// ## Postconditions
    /// See [`Self::split_ensures`].
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> frame_perms: (Tracked<SegmentOwner<M>>, Tracked<SegmentOwner<M>>),
        requires
            Self::split_requires(self, owner, offset),
        ensures
            Self::split_ensures(self, offset, r.0, r.1, owner, frame_perms.0@, frame_perms.1@),
    )]
    pub fn split(self, offset: usize) -> (Self, Self) {
        let at = self.range.start + offset;
        let idx = offset / PAGE_SIZE;
        let res = (
            Self { range: self.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..self.range.end, _marker: core::marker::PhantomData },
        );

        let _ = NeverDrop::new(self, Tracked(regions));

        let tracked frame_perms1 = SegmentOwner {
            perms: seq_tracked_subrange(owner.perms, 0, idx as int),
        };
        let tracked frame_perms2 = SegmentOwner {
            perms: seq_tracked_subrange(owner.perms, idx as int, owner.perms.len() as int),
        };

        proof {
            owner.perms.lemma_split_at(idx as int);
        }

        proof_with!(|= (Tracked(frame_perms1), Tracked(frame_perms2)));
        res
    }

    /// Forgets the [`Segment`] and gets a raw range of physical addresses.
    // NOTE: forgotten frames will be released from `owner`'s permission and
    //       later added back to `regions.dropped_slots`, and `owner` is moved.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<SegmentOwner<M>>,
        requires
            Self::into_raw_requires(self, *old(regions), owner),
        ensures
            Self::into_raw_ensures(self, *regions, owner, r),
    )]
    pub(crate) fn into_raw(self) -> Range<Paddr> {
        proof {
            broadcast use vstd_extra::seq_extra::lemma_seq_to_set_map_contains;
            broadcast use crate::mm::frame::meta::mapping::lemma_paddr_to_meta_biinjective;
            // Adjust the permission by transferring all
            // PointsTo perms from `owner` into `regions.dropped_slots`.

            let new_keys = owner.perms.map_values(|v: MetaPerm<M>| meta_to_frame_spec(v.addr()));
            let new_dropped_slots = Map::new(
                |i: usize| new_keys.contains(i),
                |k: usize| { owner.perms[k as int].points_to },
            );

            regions.dropped_slots.tracked_union_prefer_right(new_dropped_slots);

            assert forall|paddr: Paddr|
                self.range.start <= paddr < self.range.end && paddr % PAGE_SIZE == 0 implies {
                &&& regions.dropped_slots.contains_key(#[trigger] frame_to_index_spec(paddr))
            } by {
                assert(new_keys.to_set().contains(frame_to_index_spec(paddr))) by {
                    let j = (paddr - self.range.start) / PAGE_SIZE as int;
                    assert(0 <= j < owner.perms.len() as int);
                    assert(owner.perms[j].addr() == meta_addr(frame_to_index_spec(paddr)));
                }
            }
        }

        let range = self.range.clone();
        let _ = NeverDrop::new(self, Tracked(regions));
        range
    }

    /// Restores the [`Segment`] from the raw physical address range.
    ///
    /// # Verified Properties
    /// #`# P`reconditions
    /// See [`Self::from_raw_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::from_raw_ensures`].
    ///
    /// # Safety
    ///
    /// The range must be a forgotten [`Segment`] that matches the type `M`.
    /// It could be manually forgotten by [`core::mem::forget`],
    /// [`ManuallyDrop`], or [`Self::into_raw`].
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> frame_perms: Tracked<SegmentOwner<M>>,
        requires
            Self::from_raw_requires(*old(regions), range),
        ensures
            Self::from_raw_ensures(r, *old(regions), *regions, frame_perms@, range),
    )]
    pub(crate) unsafe fn from_raw(range: Range<Paddr>) -> Self {
        proof_decl! {
            let tracked mut frame_perms: SegmentOwner<M>;
        }
        // We create new permissions from stealing the `PointsTo` perms
        // from `regions.dropped_slots` so we must ensure that all frames
        // cannot be restored again.
        proof {
            broadcast use vstd::arithmetic::div_mod::group_div_basics;

            let len = (range.end - range.start) / PAGE_SIZE as int;
            let tracked owner_seq = seq_tracked_new(
                len as nat,
                |i: int|
                    {
                        let paddr = (range.start + (i as u64) * PAGE_SIZE as int) as Paddr;
                        MetaPerm {
                            addr: meta_addr(frame_to_index(paddr)),
                            points_to: regions.dropped_slots[frame_to_index(paddr)],
                            _T: core::marker::PhantomData,
                        }
                    },
            );
            frame_perms = SegmentOwner { perms: owner_seq };

            // Then remove the frames from `regions.dropped_slots`.
            let keys = Set::new(
                |paddr: Paddr| { range.start <= paddr < range.end && paddr % PAGE_SIZE == 0 },
            );
            let keys_to_remove = keys.map(|paddr: Paddr| frame_to_index(paddr));

            regions.dropped_slots.tracked_remove_keys(keys_to_remove);

            assert forall|paddr: Paddr|
                #![trigger frame_to_index(paddr)]
                range.start <= paddr < range.end && paddr % PAGE_SIZE == 0 implies {
                &&& !regions.dropped_slots.contains_key(#[trigger] frame_to_index(paddr))
            } by {
                assert(keys.contains(paddr));

                if regions.dropped_slots.contains_key(frame_to_index(paddr)) {
                    assert(!keys_to_remove.contains(frame_to_index(paddr)));
                }
            }
        }

        proof_with!(|= Tracked(frame_perms));
        Self { range, _marker: core::marker::PhantomData }
    }

    /// Gets an extra handle to the frames in the byte offset range.
    ///
    /// The sliced byte offset range in indexed by the offset from the start of
    /// the contiguous frames. The resulting frames holds extra reference counts.
    /// 
    /// # Verified Properties
    ///
    /// ## Preconditions
    /// See [`Self::slice_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::slice_ensures`].
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&SegmentOwner<M>>,
        requires
            Self::slice_requires(*self, *owner, *range),
        ensures
            Self::slice_ensures(*self, *owner, *range, r),
    )]
    pub fn slice(&self, range: &Range<Paddr>) -> Self {
        let start = self.range.start + range.start;
        let end = self.range.start + range.end;

        let mut i = 0;
        let addr_len = (end - start) / PAGE_SIZE;
        while i < addr_len
            invariant
                start % PAGE_SIZE == 0,
                end % PAGE_SIZE == 0,
                start + i * PAGE_SIZE <= end,
                i <= addr_len,
                addr_len == (end - start) / PAGE_SIZE as int,
            decreases addr_len - i,
        {
            let paddr = start + i * PAGE_SIZE;
            // SAFETY: We already have reference counts for the frames since
            // for each frame there would be a forgotten handle when creating
            // the `Segment` object.
            // unsafe { inc_frame_ref_count(paddr); }
            i += 1;
        }

        Self { range: start..end, _marker: core::marker::PhantomData }
    }

    /// Gets the next frame in the segment (raw), if any.
    ///
    /// Since the segments here must be "non-active" where
    /// there is no extra Verus-tracked permission [`SegmentOwner`]
    /// associated with it; [`Segment`] becomes a kind of "zombie"
    /// container through which we can only iterate the frames and
    /// get the frame out of the `regions` instead.
    ///
    /// # Note
    ///
    /// We chose to make `next` the member function of [`Segment`] rather than a trait method
    /// because the current Verus standard library has limited support for [`core::iter::Iterator`]
    /// and associated types, and we want to avoid the complexity of defining a custom iterator trait
    /// and implementing it for `Segment`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// See [`Self::next_requires`].
    ///
    /// ## Postconditions
    /// See [`Self::next_ensures`].
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut SegmentOwner<M>>
        requires
            Self::next_requires(*old(self), *old(regions)),
            old(owner).perms.len() > 0
        ensures
            Self::next_ensures(*old(self), *self, *old(regions), *regions, res),
    )]
    pub fn next(&mut self) -> Option<Frame<M>> {
        if self.range.start < self.range.end {
            let tracked perm = owner.perms.tracked_remove(0);
            // SAFETY: each frame in the range would be a handle forgotten
            // when creating the `Segment` object.
            let frame = unsafe {
                #[verus_spec(with Tracked(regions), Tracked(&perm))]
                Frame::<M>::from_raw(self.range.start)
            };

            self.range.start = self.range.start + PAGE_SIZE;
            Some(frame)
        } else {
            None
        }
    }
}

} // verus!
