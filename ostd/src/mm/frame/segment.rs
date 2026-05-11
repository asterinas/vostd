// SPDX-License-Identifier: MPL-2.0
//! A contiguous range of frames.
use vstd::prelude::*;
use vstd_extra::seq_extra::seq_tracked_split_at;

use core::{fmt::Debug, ops::Range};

use crate::mm::frame::{has_safe_slot, untyped::AnyUFrameMeta, Frame};
use crate::mm::page_table::RCClone;

use vstd_extra::assert;
use vstd_extra::cast_ptr::*;
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::meta::mapping::{frame_to_index, frame_to_index_spec, frame_to_meta, meta_addr};
use super::{AnyFrameMeta, GetFrameError, MetaSlot};
use crate::mm::{paddr_to_vaddr, Paddr, PagingLevel, Vaddr};
use vstd::simple_pptr;
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::segment::{frame_idx_at, SegmentOwner};
use crate::specs::mm::virt_mem_newer::MemView;
use vstd_extra::drop_tracking::*;

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
    /// - the metadata function must be well-formed and valid for all frames in the range;
    /// - the metadata function must ensure that the frames can be created and owned by the segment;
    /// - for any frame created via the closure `metadata_fn`, the corresponding slot in `regions`
    ///   must be unused and not dropped in the owner ([`MetaRegionOwners`]).
    ///
    /// Range constraints (alignment, `range.end <= MAX_PADDR`, non-emptiness) are runtime-checked
    /// in the body — see the postconditions below for the corresponding error variants.
    /// ## Postconditions
    /// - if the result is `Ok`, the returned segment satisfies its invariant with the owner,
    ///   has the same physical address range as the input, and the owner is `Some`;
    /// - if the input range is misaligned, the result is `Err(NotAligned)`;
    /// - if the input range exceeds `MAX_PADDR`, the result is `Err(OutOfBound)`;
    /// - if the input is aligned and within `MAX_PADDR` and the function terminated,
    ///   then `range.start < range.end` (the runtime `assert!` would otherwise diverge).
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> owner: Tracked<Option<SegmentOwner<M>>>,
        requires
            old(regions).inv(),
            forall|paddr_in: Paddr|
                (range.start <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                    &&& metadata_fn.requires((paddr_in,))
                },
            forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                    &&& paddr_out < MAX_PADDR
                    &&& paddr_out % PAGE_SIZE == 0
                    &&& paddr_in == paddr_out
                    &&& old(regions).slots.contains_key(frame_to_index(paddr_out))
                    &&& old(regions).slot_owners[frame_to_index(paddr_out)].usage is Unused
                    &&& old(regions).slot_owners[frame_to_index(paddr_out)].inner_perms.in_list.points_to(0)
                },
        ensures
            (range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0)
                ==> r == Err::<Self, _>(GetFrameError::NotAligned),
            (range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.end > MAX_PADDR)
                ==> r == Err::<Self, _>(GetFrameError::OutOfBound),
            (range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.end <= MAX_PADDR)
                ==> range.start < range.end,
            r matches Ok(r) ==> {
                &&& final(regions).inv()
                &&& r.range.start == range.start
                &&& r.range.end == range.end
                &&& r.range.start < r.range.end
                &&& owner@ matches Some(owner) && {
                    &&& r.inv()
                    &&& r.wf(&owner)
                    &&& forall|i: int|
                        #![trigger owner.perms[i]]
                        0 <= i < owner.perms.len() as int ==> {
                            &&& owner.perms[i].addr() == meta_addr(
                                frame_to_index_spec((range.start + i * PAGE_SIZE) as usize),
                            )
                        }
                    &&& forall|paddr: Paddr|
                        #![trigger frame_to_index_spec(paddr)]
                        (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                            ==> !final(regions).slots.contains_key(frame_to_index_spec(paddr))
                }
            },
    )]
    pub fn from_unused(range: Range<Paddr>, metadata_fn: impl Fn(Paddr) -> (Paddr, M)) -> (res:
        Result<Self, GetFrameError>) {
        proof_decl! {
            let tracked mut owner: Option<SegmentOwner<M>> = None;
            let tracked mut addrs = Seq::<usize>::tracked_empty();
            let tracked mut perms = Seq::<simple_pptr::PointsTo<MetaSlot>>::tracked_empty();
            let tracked mut perm_opt: Option<simple_pptr::PointsTo<MetaSlot>>;
        }

        if range.start % PAGE_SIZE != 0 || range.end % PAGE_SIZE != 0 {
            return {
                proof_with!(|= Tracked(owner));
                Err(GetFrameError::NotAligned)
            };
        }
        if range.end > MAX_PADDR {
            return {
                proof_with!(|= Tracked(owner));
                Err(GetFrameError::OutOfBound)
            };
        }
        assert!(range.start < range.end);
        // Construct a segment early to recycle previously forgotten frames if
        // the subsequent operations fails in the middle.
        let mut segment = Self {
            range: range.start..range.start,
            _marker: core::marker::PhantomData,
        };

        let mut i = 0;
        let addr_len = (range.end - range.start) / PAGE_SIZE;

        while i < addr_len
            invariant
                i <= addr_len,
                i as int == addrs.len(),
                i as int == perms.len(),
                range.start % PAGE_SIZE == 0,
                range.end % PAGE_SIZE == 0,
                range.end <= MAX_PADDR,
                range.start <= range.start + i * PAGE_SIZE <= range.end,
                range.end == range.start + addr_len * PAGE_SIZE,
                addr_len == (range.end - range.start) / PAGE_SIZE as int,
                i <= addr_len,
                forall|paddr_in: Paddr|
                    (range.start + i * PAGE_SIZE <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0) ==> {
                        &&& metadata_fn.requires((paddr_in,))
                    },
                forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
                    range.start + i * PAGE_SIZE <= paddr_in < range.end
                        && paddr_in % PAGE_SIZE == 0
                        && metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> {
                        &&& paddr_out < MAX_PADDR
                        &&& paddr_out % PAGE_SIZE == 0
                        &&& paddr_in == paddr_out
                        &&& regions.slots.contains_key(frame_to_index(paddr_out))
                        &&& regions.slot_owners[frame_to_index(paddr_out)].usage is Unused
                        &&& regions.slot_owners[frame_to_index(paddr_out)].inner_perms.in_list.points_to(0)
                    },
                forall|j: int|
                    0 <= j < addrs.len() as int ==> {
                        &&& !regions.slots.contains_key(frame_to_index_spec(addrs[j]))
                        &&& addrs[j] % PAGE_SIZE == 0
                        &&& addrs[j] < MAX_PADDR
                        &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
                    },
                forall|j: int|
                    #![trigger perms[j]]
                    0 <= j < perms.len() as int ==> {
                        &&& perms[j].addr() == frame_to_meta(addrs[j])
                        &&& perms[j].is_init()
                    },
                regions.inv(),
                segment.range.start == range.start,
                segment.range.end == range.start + i * PAGE_SIZE,
            ensures
                i == addr_len,
            decreases addr_len - i,
        {
            let paddr_in = range.start + i * PAGE_SIZE;
            let (paddr, meta) = metadata_fn(paddr_in);

            let res = #[verus_spec(with Tracked(regions) => Tracked(perm_opt))]
            Frame::<M>::from_unused(paddr, meta);
            let frame = match res {
                Ok(f) => f,
                Err(e) => {
                    return {
                        proof_with!(|= Tracked(owner));
                        Err(e)
                    };
                },
            };

            proof {
                let tracked frame_perm = perm_opt.tracked_unwrap();
                perms.tracked_push(frame_perm);
            }

            let _ = ManuallyDrop::new(frame, Tracked(regions));
            segment.range.end = paddr + PAGE_SIZE;
            proof {
                addrs.tracked_push(paddr);
            }

            i += 1;
        }

        proof {
            broadcast use vstd_extra::seq_extra::lemma_seq_to_set_map_contains;

            owner = Some(SegmentOwner { range, perms, _marker: core::marker::PhantomData });

            assert forall|addr: usize|
                #![trigger frame_to_index_spec(addr)]
                range.start <= addr < range.end && addr % PAGE_SIZE == 0 implies {
                &&& !regions.slots.contains_key(frame_to_index_spec(addr))
            } by {
                if !addrs.contains(addr) {
                    let j = (addr - range.start) / PAGE_SIZE as int;
                    assert(addrs[j as int] == addr);
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
    /// - the segment must satisfy its invariant ([`Self::inv`]) and the well-formedness
    ///   relation with the owner ([`Self::wf`]);
    /// - the offset must be aligned and within bounds;
    /// - the meta region must be valid and the owner must relate to it.
    ///
    /// ## Postconditions
    /// - the resulting segments satisfy their invariants with the corresponding owners;
    /// - they match [`Self::split_spec`];
    /// - the original owner's permissions are split between the two new owners;
    /// - both halves continue to relate correctly to `regions` (which is unchanged).
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
                -> frame_perms: (Tracked<SegmentOwner<M>>, Tracked<SegmentOwner<M>>),
        requires
            self.inv(),
            self.wf(&owner),
            offset % PAGE_SIZE == 0,
            0 < offset < self.size(),
            old(regions).inv(),
            owner.relate_regions(*old(regions)),
        ensures
            *final(regions) =~= *old(regions),
            r.0.inv(),
            r.0.wf(&frame_perms.0@),
            r.1.inv(),
            r.1.wf(&frame_perms.1@),
            (r.0, r.1) == self.split_spec(offset),
            owner.perms =~= (frame_perms.0@.perms + frame_perms.1@.perms),
            frame_perms.0@.relate_regions(*final(regions)),
            frame_perms.1@.relate_regions(*final(regions)),
    )]
    pub fn split(self, offset: usize) -> (Self, Self) {
        assert!(offset % PAGE_SIZE == 0);
        assert!(0 < offset && offset < self.size());

        let old = ManuallyDrop::new(self, Tracked(regions));
        let at = old.range.start + offset;

        let ghost old_start = old@.range.start;
        let ghost old_end = old@.range.end;

        let tracked mut perms = owner.perms;
        let tracked rest = seq_tracked_split_at(&mut perms, (offset / PAGE_SIZE) as int);
        let tracked frame_own1 = SegmentOwner {
            range: old_start..at,
            perms,
            _marker: core::marker::PhantomData,
        };
        let tracked frame_own2 = SegmentOwner {
            range: at..old_end,
            perms: rest,
            _marker: core::marker::PhantomData,
        };

        proof_with!(|= (Tracked(frame_own1), Tracked(frame_own2)));
        (
            Self { range: old.range.start..at, _marker: core::marker::PhantomData },
            Self { range: at..old.range.end, _marker: core::marker::PhantomData },
        )
    }

    /// Forgets the [`Segment`] and gets a raw range of physical addresses.
    ///
    /// The segment's permissions are returned to the caller via `frame_perms`.
    /// The caller is responsible for holding onto the permissions and providing
    /// them back when restoring the segment with [`Self::from_raw`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the segment must satisfy the invariant with the owner;
    /// - the meta region in `regions` must satisfy the invariant;
    /// - the owner must relate correctly to `regions`.
    ///
    /// ## Postconditions
    /// - the returned physical address range matches the segment's range;
    /// - the meta region is unchanged (preserving the relation with the returned owner).
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<SegmentOwner<M>>,
                -> frame_perms: Tracked<SegmentOwner<M>>,
        requires
            self.inv(),
            self.wf(&owner),
            old(regions).inv(),
            owner.inv(),
            owner.relate_regions(*old(regions)),
        ensures
            r == self.range,
            final(regions).inv(),
            *final(regions) =~= *old(regions),
            frame_perms@ == owner,
    )]
    pub(crate) fn into_raw(self) -> Range<Paddr> {
        let range = self.range.clone();
        let _ = ManuallyDrop::new(self, Tracked(regions));

        proof_with!(|= Tracked(owner));
        range
    }

    /// Restores the [`Segment`] from the raw physical address range.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - the meta region must satisfy its invariant;
    /// - the segment-to-be (with the supplied `range`) must satisfy its invariant
    ///   ([`Self::inv`]) and the well-formedness relation with `owner` ([`Self::wf`]);
    /// - `owner` must relate correctly to `regions`.
    ///
    /// Following the [`UniqueFrame::from_raw`] pattern, the contract here ties
    /// `range` and `owner` together up front so that the postcondition can
    /// directly advertise `r.inv()` and `r.wf(&owner)` for the caller.
    ///
    /// ## Postconditions
    /// - the returned segment satisfies its invariant and is well-formed with `owner`;
    /// - the returned segment has the same physical address range as the input;
    /// - the meta region is unchanged (preserving the relation with `owner`).
    ///
    /// # Safety
    ///
    /// The range must be a forgotten [`Segment`] that matches the type `M`.
    /// The caller must provide the permissions that were returned by [`Self::into_raw`].
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<SegmentOwner<M>>,
        requires
            old(regions).inv(),
            owner.inv(),
            (Segment::<M> { range, _marker: core::marker::PhantomData }).wf(&owner),
            owner.relate_regions(*old(regions)),
        ensures
            r.range == range,
            r.inv(),
            r.wf(&owner),
            final(regions).inv(),
            *final(regions) =~= *old(regions),
    )]
    pub(crate) unsafe fn from_raw(range: Range<Paddr>) -> Self {
        Self { range, _marker: core::marker::PhantomData }
    }

    /// Gets an extra handle to the frames in the byte offset range.
    ///
    /// The sliced byte offset range in indexed by the offset from the start of
    /// the contiguous frames. The resulting frames holds extra reference counts.
    ///
    /// # Verified Properties
    /// ## Postconditions
    /// - the resulting slice's range matches the slicing range and is in-bounds
    ///   (the in-bounds check follows from the diverging `assert!` in the body);
    /// - `regions` preserves invariants and key domains. Per-frame state — e.g.
    ///   that a hypothetical `sub_owner.relate_regions(regions)` would hold —
    ///   is *not* exposed; threading that through the per-frame ref-count bump
    ///   loop would require a much heavier proof. Mirrors [`Segment::clone`].
    ///
    /// See also [`vstd::seq::Seq::subrange`].
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.inv(),
            self.wf(&owner),
            owner.inv(),
            old(regions).inv(),
            owner.relate_regions(*old(regions)),
        ensures
            r.inv(),
            r.range.start == self.range.start + range.start,
            r.range.end == self.range.start + range.end,
            r.range.end <= self.range.end,
            final(regions).inv(),
            final(regions).slots =~= old(regions).slots,
            final(regions).slot_owners.dom() =~= old(regions).slot_owners.dom(),
    )]
    pub fn slice(&self, range: &Range<usize>) -> Self {
        assert!(range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0);

        // KNOWN BUG: potential overflows
        assume(self.range.start + range.start <= usize::MAX);
        assume(self.range.start + range.end <= usize::MAX);

        let start = self.range.start + range.start;
        let end = self.range.start + range.end;
        assert!(start <= end && end <= self.range.end);

        assert!(start <= end && end <= self.range.end);

        let mut i: usize = 0;
        let addr_len = (end - start) / PAGE_SIZE;
        let ghost first_perm_idx: int = (range.start / PAGE_SIZE) as int;
        let ghost last_perm_idx: int = (range.end / PAGE_SIZE) as int;
        let ghost old_regions = *regions;
        while i < addr_len
            invariant
                // Pin the snapshot to the function-entry value so that
                // facts stated against `old_regions` and `*old(regions)`
                // are interchangeable inside the loop.
                old_regions == *old(regions),
                regions.inv(),
                regions.slots =~= old_regions.slots,
                regions.slot_owners.dom() =~= old_regions.slot_owners.dom(),
                start == self.range.start + range.start,
                end == self.range.start + range.end,
                start <= end <= self.range.end,
                start % PAGE_SIZE == 0,
                end % PAGE_SIZE == 0,
                start + i * PAGE_SIZE <= end,
                i <= addr_len,
                addr_len == (end - start) / PAGE_SIZE as int,
                self.inv(),
                self.wf(&owner),
                owner.inv(),
                owner.relate_regions(old_regions),
                first_perm_idx == range.start / PAGE_SIZE,
                last_perm_idx == range.end / PAGE_SIZE,
                first_perm_idx + addr_len as int == last_perm_idx,
                first_perm_idx + i as int <= last_perm_idx,
                // For frames not yet processed, the entry is unchanged from
                // `old_regions`. This lets the next iteration recover the
                // ref-count/wf facts via `relate_regions`.
                forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    first_perm_idx + i as int <= j < last_perm_idx ==>
                        (*regions).slot_owners[frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                            == old_regions.slot_owners[frame_to_index((self.range.start + j * PAGE_SIZE) as usize)],
            decreases addr_len - i,
        {
            let paddr = start + i * PAGE_SIZE;
            let ghost slot_idx: usize = frame_to_index(paddr);
            let ghost perm_idx: int = first_perm_idx + i as int;

            proof {
                // Trigger `owner.relate_regions`'s `owner.perms[i]` forall at
                // this iteration's index, and the loop invariant's
                // unchanged-at-`slot_idx` clause.
                let _ = owner.perms[perm_idx];
                assert(regions.slot_owners[slot_idx] == old_regions.slot_owners[slot_idx]);
            }

            let tracked mut slot_own = regions.slot_owners.tracked_remove(slot_idx);
            let tracked mut inner_perms = slot_own.take_inner_perms();

            let vaddr: Vaddr = frame_to_meta(paddr);
            let ptr = vstd::simple_pptr::PPtr::<super::MetaSlot>::from_addr(vaddr);

            // Borrow the slot perm out of `owner.perms` (rather than out of
            // `regions.slots`, where it doesn't live for an active segment),
            // and feed it to `inc_ref_count` via `ptr.borrow`.
            #[verus_spec(with Tracked(&mut inner_perms.ref_count))]
            ptr.borrow(Tracked(owner.perms.tracked_borrow(perm_idx))).inc_ref_count();

            proof {
                slot_own.sync_inner(&inner_perms);
                regions.slot_owners.tracked_insert(slot_idx, slot_own);
            }

            i += 1;

            proof {
                // Re-establish the "not yet processed" invariant for the
                // post-`i += 1` range: distinct-indices (from
                // `relate_regions`) tells us the just-touched `slot_idx`
                // can't collide with any remaining `j > perm_idx`.
                assert forall|j: int|
                    #![trigger frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                    first_perm_idx + i as int <= j < last_perm_idx implies
                        (*regions).slot_owners[frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                            == old_regions.slot_owners[frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
                by {
                    let _ = owner.perms[j];
                    let _ = owner.perms[perm_idx];
                };
            }
        }

        Self { range: start..end, _marker: core::marker::PhantomData }
    }

    /// Gets the next frame in the segment.
    ///
    /// This is the verified counterpart of [`Iterator::next`] for `Segment<M>`.
    /// The trait method is `external_body` because Verus's `core::iter::Iterator`
    /// support can't thread `Tracked` metadata through the trait method's
    /// fixed signature.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - segment, owner, and meta regions must satisfy their respective invariants;
    /// - the segment is well-formed with the owner;
    /// - the owner relates correctly to `regions` (forgotten reference, slot
    ///   present and consistent, etc. — see [`SegmentOwner::relate_regions`]).
    ///
    /// All the per-frame coherence conditions previously listed inline are now
    /// consequences of `owner.relate_regions(regions)` instantiated at `i = 0`.
    ///
    /// ## Postconditions
    /// - if the result is [`None`], then the segment has been exhausted;
    /// - if the result is [`Some`], then the segment is advanced by one frame and
    ///   the returned frame is the next frame, with its slot restored to `regions`;
    /// - the new owner continues to relate correctly to the new regions.
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut SegmentOwner<M>>
        requires
            old(self).inv(),
            old(self).wf(old(owner)),
            old(owner).inv(),
            old(regions).inv(),
            old(owner).relate_regions(*old(regions)),
        ensures
            final(regions).inv(),
            final(self).inv(),
            final(owner).relate_regions(*final(regions)),
            match res {
                None => final(self).range.start == old(self).range.end,
                Some(f) => {
                    &&& final(self).range.start == old(self).range.start + PAGE_SIZE
                    &&& f.paddr() == old(self).range.start
                    &&& final(regions).slots.contains_key(frame_to_index(f.paddr()))
                    &&& final(regions).slot_owners[frame_to_index(f.paddr())].raw_count == 0
                },
            },
    )]
    pub fn next(&mut self) -> Option<Frame<M>> {
        if self.range.start < self.range.end {
            let tracked perm = owner.perms.tracked_remove(0);

            proof_decl! {
                let tracked from_raw_debt: crate::specs::mm::frame::frame_specs::BorrowDebt;
            }

            let frame = unsafe {
                #[verus_spec(with Tracked(regions), Tracked(&perm) => Tracked(from_raw_debt))]
                Frame::<M>::from_raw(self.range.start)
            };

            proof {
                from_raw_debt.discharge_bookkeeping();
                owner.range = ((self.range.start + PAGE_SIZE) as usize)..self.range.end;
            }

            self.range.start = self.range.start + PAGE_SIZE;
            Some(frame)
        } else {
            None
        }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta> From<Frame<M>> for Segment<M> {
    /// Converts a single [`Frame`] into a one-page [`Segment`] by forgetting
    /// the frame and recording its paddr range. Symmetric to vostd's
    /// `From<Frame<M>> for Segment<M>`.
    //
    // Trusted at the trait boundary: the `From::from` signature can't thread
    // `Tracked` metadata to bump the frame's `raw_count` via the verified
    // `vstd_extra::drop_tracking::ManuallyDrop`, so we use `core::mem`'s
    // version. Same trust pattern as the `Iterator` impl.
    #[verifier::external_body]
    fn from(frame: Frame<M>) -> Self {
        let pa = frame.start_paddr();
        let _ = core::mem::ManuallyDrop::new(frame);
        Self {
            range: pa..(pa + PAGE_SIZE),
            _marker: core::marker::PhantomData,
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Iterator for Segment<M> {
    type Item = Frame<M>;

    /// Gets the next frame in the segment.
    //
    // Verus's `core::iter::Iterator` support doesn't allow threading `Tracked`
    // metadata through the trait method's fixed signature, so the verified
    // `next` lives as an inherent method on `Segment<M>` and the trait body
    // is trusted at the trait boundary.
    #[verifier::external_body]
    fn next(&mut self) -> Option<Self::Item> {
        if self.range.start < self.range.end {
            // SAFETY: each frame in the range was a forgotten handle when
            // creating the `Segment` object.
            let frame = unsafe { Frame::<M>::from_raw(self.range.start) };
            self.range.start = self.range.start + PAGE_SIZE;
            Some(frame)
        } else {
            None
        }
    }
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// Verified drop: iterates over each frame in the segment, decrements its
    /// reference count, and (when last ref) tears down the metadata.
    ///
    /// Custom drop method (not an impl of [`vstd_extra::drop_tracking::Drop`]):
    /// `regions` flows through [`TrackDrop::State`] (= [`MetaRegionOwners`])
    /// so `ManuallyDrop::new(self, Tracked(regions))` stays callable, while
    /// `owner` is threaded in separately via `verus_spec`.
    #[verus_spec(
        with Tracked(owner): Tracked<SegmentOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            self.inv(),
            self.wf(&owner),
            owner.inv(),
            old(regions).inv(),
            owner.relate_regions(*old(regions)),
            forall|i: int|
                #![trigger owner.perms[i]]
                0 <= i < owner.perms.len() as int ==> {
                    let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                    old(regions).slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                        &&& old(regions).slot_owners[idx].inner_perms.storage.is_init()
                        &&& old(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                    }
                },
        ensures
            final(regions).inv(),
    )]
    pub fn drop(self) {
        let tracked mut owner = owner;
        let ghost n = owner.perms.len();
        let mut paddr = self.range.start;

        let ghost mut k: int = 0;

        let ghost old_owner = owner;

        // Re-trigger the precondition's `forall|i| owner.perms[i] => ...`
        // under `frame_idx_at(self.range.start, i)`, which is the trigger the
        // loop invariant uses.
        assert forall|i: int|
            #![trigger frame_idx_at(self.range.start, i)]
            0 <= i < n implies {
                let idx = frame_idx_at(self.range.start, i);
                old(regions).slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                    &&& old(regions).slot_owners[idx].inner_perms.storage.is_init()
                    &&& old(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                }
            } by {
            let _ = owner.perms[i];
        };

        loop
            invariant
                regions.inv(),
                self.inv(),
                self.range.start <= paddr <= self.range.end,
                paddr == (self.range.start + k * PAGE_SIZE) as usize,
                paddr % PAGE_SIZE == 0,
                paddr <= MAX_PADDR,
                0 <= k <= n,
                n == (self.range.end - self.range.start) as int / PAGE_SIZE as int,
                owner.perms.len() == n - k,
                paddr < self.range.end <==> k < n,
                // Remaining owner.perms are the suffix of the original
                forall|j: int|
                    #![trigger owner.perms[j]]
                    0 <= j < (n - k) ==>
                        owner.perms[j] == old_owner.perms[j + k],
                // Unprocessed frames' slot_owners are present and unchanged
                forall|j: int|
                    #![trigger frame_idx_at(self.range.start, j)]
                    k <= j < n ==>
                        regions.slot_owners.contains_key(frame_idx_at(self.range.start, j))
                        && regions.slot_owners[frame_idx_at(self.range.start, j)] == old(regions).slot_owners[frame_idx_at(self.range.start, j)],
                regions.slot_owners.dom() =~= old(regions).slot_owners.dom(),
                // Re-state the function-entry preconditions over the
                // immutable `old_owner`/`old(regions)` snapshots so each
                // iteration's `from_raw`/`drop` can satisfy them.
                self.inv(),
                self.wf(&old_owner),
                old_owner.inv(),
                old(regions).inv(),
                old_owner.relate_regions(*old(regions)),
                forall|i: int|
                    #![trigger frame_idx_at(self.range.start, i)]
                    0 <= i < n ==> {
                        let idx = frame_idx_at(self.range.start, i);
                        old(regions).slot_owners[idx].inner_perms.ref_count.value() == 1 ==> {
                            &&& old(regions).slot_owners[idx].inner_perms.storage.is_init()
                            &&& old(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                        }
                    },
            decreases n - k,
        {
            if paddr >= self.range.end {
                break;
            }

            let tracked slot_perm = owner.perms.tracked_remove(0);
            proof_decl! {
                let tracked from_raw_debt: crate::specs::mm::frame::frame_specs::BorrowDebt;
            }

            // SAFETY: each segment frame holds a forgotten reference
            // (`relate_regions` ⇒ `raw_count == 1`), which `from_raw`
            // reclaims; the subsequent `frame.drop` decrements `ref_count`
            // and (when last ref) tears down the metadata.
            let frame = unsafe {
                #[verus_spec(with Tracked(regions), Tracked(&slot_perm) => Tracked(from_raw_debt))]
                Frame::<M>::from_raw(paddr)
            };

            proof {
                from_raw_debt.discharge_bookkeeping();
            }

            frame.drop(Tracked(regions));

            paddr = paddr + PAGE_SIZE;

            proof {
                k = k + 1;
            }
        }

    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> RCClone for Segment<M> {
    open spec fn clone_requires(self, perm: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& perm.inv()
        &&& forall|pa: Paddr|
            #![trigger frame_to_index(pa)]
            (self.range.start <= pa < self.range.end && pa % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(pa);
                &&& perm.slots.contains_key(idx)
                &&& has_safe_slot(pa)
                &&& perm.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& perm.slot_owners[idx].inner_perms.ref_count.value() + 1
                    < super::meta::REF_COUNT_MAX
                &&& !MetaSlot::inc_ref_count_panic_cond(
                    perm.slot_owners[idx].inner_perms.ref_count)
            }
    }

    open spec fn clone_ensures(self, old_perm: MetaRegionOwners, new_perm: MetaRegionOwners, res: Self) -> bool {
        &&& res.range == self.range
        &&& res.inv()
        &&& new_perm.inv()
    }

    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self)
    {
        let mut paddr = self.range.start;

        let ghost old_perm = *perm;
        loop
            invariant
                perm.inv(),
                self.inv(),
                perm.slots =~= old_perm.slots,
                perm.slot_owners.dom() =~= old_perm.slot_owners.dom(),
                self.range.start <= paddr <= self.range.end,
                paddr % PAGE_SIZE == 0,
                paddr <= MAX_PADDR,
                forall|pa: Paddr|
                    #![trigger frame_to_index(pa)]
                    (paddr <= pa < self.range.end && pa % PAGE_SIZE == 0) ==> {
                        let idx = frame_to_index(pa);
                        &&& perm.slots.contains_key(idx)
                        &&& has_safe_slot(pa)
                        &&& perm.slot_owners[idx].inner_perms.ref_count.value() > 0
                        &&& perm.slot_owners[idx].inner_perms.ref_count.value() + 1
                            < super::meta::REF_COUNT_MAX
                        &&& !MetaSlot::inc_ref_count_panic_cond(
                            perm.slot_owners[idx].inner_perms.ref_count)
                    },
            decreases self.range.end - paddr,
        {
            if paddr >= self.range.end {
                break;
            }

            proof {
                assert(paddr + PAGE_SIZE <= self.range.end);
                assert(paddr + PAGE_SIZE <= MAX_PADDR);
            }

            #[verus_spec(with Tracked(perm))]
            crate::mm::frame::inc_frame_ref_count(paddr);

            paddr = paddr + PAGE_SIZE;
        }

        Self {
            range: self.range.start..self.range.end,
            _marker: core::marker::PhantomData,
        }
    }
}

} // verus!
