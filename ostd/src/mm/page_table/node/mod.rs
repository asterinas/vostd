// SPDX-License-Identifier: MPL-2.0
//! This module defines page table node abstractions and the handle.
//!
//! The page table node is also frequently referred to as a page table in many architectural
//! documentations. It is essentially a page that contains page table entries (PTEs) that map
//! to child page tables nodes or mapped pages.
//!
//! This module leverages the page metadata to manage the page table pages, which makes it
//! easier to provide the following guarantees:
//!
//! The page table node is not freed when it is still in use by:
//!    - a parent page table node,
//!    - or a handle to a page table node,
//!    - or a processor.
//!
//! This is implemented by using a reference counter in the page metadata. If the above
//! conditions are not met, the page table node is ensured to be freed upon dropping the last
//! reference.
//!
//! One can acquire exclusive access to a page table node using merely the physical address of
//! the page table node. This is implemented by a lock in the page metadata. Here the
//! exclusiveness is only ensured for kernel code, and the processor's MMU is able to access the
//! page table node while a lock is held. So the modification to the PTEs should be done after
//! the initialization of the entity that the PTE points to. This is taken care in this module.
//!
mod child;
mod entry;

#[path = "../../../../specs/mm/page_table/node/child.rs"]
mod child_specs;
#[path = "../../../../specs/mm/page_table/node/entry.rs"]
mod entry_specs;

pub use crate::specs::mm::page_table::node::{entry_owners::*, owners::*};
pub use child::*;
pub use entry::*;

use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;

use vstd::atomic::PAtomicU8;

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::Drop as VerifiedDrop;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::allocator::FrameAllocOptions;
use crate::mm::frame::meta::MetaSlot;
use crate::mm::frame::{frame_to_index, AnyFrameMeta, Frame};
use crate::mm::kspace::VMALLOC_BASE_VADDR;
use crate::mm::page_table::*;
use crate::mm::{kspace::LINEAR_MAPPING_BASE_VADDR, paddr_to_vaddr, Paddr, Vaddr};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::mm::frame::mapping::{frame_to_meta, meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_owners::{
    MetaSlotOwner, MetaSlotStorage, Metadata, REF_COUNT_UNUSED,
};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::owners::*;

use core::{marker::PhantomData, ops::Deref, sync::atomic::Ordering};

use super::nr_subpage_per_huge;

use crate::{
    mm::{
        page_table::{load_pte, store_pte},
        //        FrameAllocOptions, Infallible,
        //        VmReader,
    },
    specs::task::InAtomicMode,
};

verus! {

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The number of valid PTEs. It is mutable if the lock is held.
    pub nr_children: pcell_maybe_uninit::PCell<u16>,
    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub stray: pcell_maybe_uninit::PCell<bool>,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// The lock for the page table page.
    pub lock: PAtomicU8,
    pub _phantom: core::marker::PhantomData<C>,
}

/// A smart pointer to a page table node.
///
/// This smart pointer is an owner of a page table node. Thus creating and
/// dropping it will affect the reference count of the page table node. If
/// dropped it as the last reference, the page table node and subsequent
/// children will be freed.
///
/// [`PageTableNode`] is read-only. To modify the page table node, lock and use
/// [`PageTableGuard`].
pub type PageTableNode<C> = Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    /// Caller invariants the PT-node `on_drop` body relies on:
    /// - Reader well-formedness + `vm_io_owner` matching + read view
    ///   initialized + at least `PAGE_SIZE` bytes remaining for the
    ///   PT-node walk.
    /// - Global region table invariant.
    /// - Embedding ([`child_perms_embedding`]): for every paddr in
    ///   `child_perms.dom()`, the slot and perm match `from_raw` /
    ///   `VerifiedDrop::drop`'s expected shape.
    /// - Walk coverage ([`walk_coverage_from_view`]): for every present
    ///   non-last PTE in the page bytes, `frame_to_index(pte.paddr()) ∈
    ///   child_perms.dom()`.
    /// - Walk uniqueness ([`walk_uniqueness_from_view`]): distinct PTE
    ///   positions with present non-last PTEs have distinct paddrs.
    ///
    /// The body now discharges the dom-membership obligation in full via
    /// byte-level chaining (`decode_pod` + `read_once`'s strengthened
    /// ensures + the byte-preservation loop invariant) plus the two
    /// walk-* preconditions; see [`lemma_coverage_at`] and
    /// [`lemma_uniqueness_at_pair`].
    open spec fn on_drop_pre(
        &self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        args: crate::mm::frame::meta::OnDropArgs,
    ) -> bool {
        &&& reader.inv()
        &&& reader.wf(args.vm_io_owner)
        &&& reader.remain_spec() >= crate::specs::arch::mm::PAGE_SIZE
        &&& reader.cursor.vaddr % core::mem::align_of::<C::E>() == 0
        &&& args.vm_io_owner.inv()
        &&& args.vm_io_owner.read_view_initialized()
        &&& args.regions.inv()
        &&& Self::child_perms_embedding(args)
        &&& self.walk_coverage_from_view(
            reader,
            args.vm_io_owner.read_view_of(),
            args.child_perms.dom(),
        )
        &&& self.walk_uniqueness_from_view(reader, args.vm_io_owner.read_view_of())
    }

    /// Drops the children of a page-table node: walks each present PTE and
    /// drops the referenced child page-table-node frame or mapped item.
    #[verifier::rlimit(400)]
    #[verifier::spinoff_prover]
    fn on_drop(
        &mut self,
        reader: &mut crate::mm::VmReader<'_, crate::mm::Infallible>,
        Tracked(args): Tracked<&mut crate::mm::frame::meta::OnDropArgs>,
    ) {
        let level = self.level;
        let range = if level == C::NR_LEVELS() {
            C::TOP_LEVEL_INDEX_RANGE()
        } else {
            0..nr_subpage_per_huge::<C>()
        };

        proof {
            C::axiom_pte_walk_fills_page();
            C::axiom_top_level_index_range_within_nr_entries();
            C::axiom_nr_subpage_per_huge_eq_nr_entries();
            crate::mm::page_table::axiom_top_level_index_range_bounds::<C>();
            vstd::arithmetic::mul::lemma_mul_inequality(
                range.start as int,
                NR_ENTRIES as int,
                core::mem::size_of::<C::E>() as int,
            );
        }

        let ghost size_of_e: int = core::mem::size_of::<C::E>() as int;
        let ghost align_of_e: int = core::mem::align_of::<C::E>() as int;
        let ghost pre_skip_cursor: int = reader.cursor.vaddr as int;

        let ghost initial_view: crate::specs::mm::virt_mem::MemView =
            args.vm_io_owner.read_view_of();
        let ghost initial_dom: vstd::set::Set<usize> = args.child_perms.dom();
        let ghost initial_reader: crate::mm::VmReader<'_, crate::mm::Infallible> = *reader;

        #[verus_spec(with Tracked(&mut args.vm_io_owner))]
        reader.skip_in_place(range.start * core::mem::size_of::<C::E>());

        proof {
            C::axiom_pte_align_divides_size();
            let k = size_of_e / align_of_e;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size_of_e, align_of_e);
            assert(size_of_e == align_of_e * k);
            vstd::arithmetic::mul::lemma_mul_is_commutative(align_of_e, k);
            vstd::arithmetic::mul::lemma_mul_is_associative(range.start as int, k, align_of_e);
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                range.start as int * k,
                align_of_e,
            );
            assert((range.start as int * size_of_e) % align_of_e == 0);
            vstd::arithmetic::div_mod::lemma_mod_adds(
                pre_skip_cursor,
                range.start as int * size_of_e,
                align_of_e,
            );
        }

        let ghost post_skip_remain: int = reader.remain_spec() as int;
        let ghost range_start: int = range.start as int;
        let ghost range_end: int = range.end as int;
        let n_iters: usize = range.end - range.start;
        let mut iter_count: usize = 0;
        let ghost mut removed_indices: vstd::set::Set<usize> = vstd::set::Set::empty();

        proof {
            C::axiom_pte_walk_fills_page();
            C::axiom_top_level_index_range_within_nr_entries();
            C::axiom_nr_subpage_per_huge_eq_nr_entries();
            crate::mm::page_table::axiom_top_level_index_range_bounds::<C>();
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(
                size_of_e,
                NR_ENTRIES as int,
                range_start,
            );
            vstd::arithmetic::mul::lemma_mul_inequality(
                range_end - range_start,
                NR_ENTRIES as int - range_start,
                size_of_e,
            );
            assert(post_skip_remain >= (range_end - range_start) * size_of_e);
            assert(args.child_perms.dom() == initial_dom.difference(removed_indices)) by {
                assert(removed_indices == vstd::set::Set::<usize>::empty());
                assert(initial_dom.difference(vstd::set::Set::<usize>::empty()) == initial_dom);
            }
        }

        while iter_count < n_iters
            invariant
                reader.inv(),
                reader.wf(args.vm_io_owner),
                args.vm_io_owner.inv(),
                args.vm_io_owner.read_view_initialized(),
                args.regions.inv(),
                reader.cursor.vaddr as int % align_of_e == 0,
                size_of_e == core::mem::size_of::<C::E>() as int,
                align_of_e == core::mem::align_of::<C::E>() as int,
                size_of_e % align_of_e == 0,
                align_of_e > 0,
                size_of_e > 0,
                iter_count <= n_iters,
                n_iters as int == range_end - range_start,
                // Verus loses non-negativity of `range_start` / `range_end`
                // across the loop boundary; pin it via these invariants so
                // `lemma_mul_nonnegative` preconditions discharge in the body.
                0 <= range_start,
                range_start <= range_end,
                range_end <= NR_ENTRIES as int,
                reader.remain_spec() as int == post_skip_remain - iter_count as int * size_of_e,
                post_skip_remain >= (range_end - range_start) * size_of_e,
                Self::child_perms_embedding(*args),
                self.walk_coverage_from_view(initial_reader, initial_view, initial_dom),
                self.walk_uniqueness_from_view(initial_reader, initial_view),
                // Without this, Verus treats `self.level` as potentially
                // mutated by `&mut self` and the level-comparison facts go
                // missing inside walk_coverage / walk_uniqueness instances.
                self.level == level,
                reader.end == initial_reader.end,
                reader.cursor.vaddr == initial_reader.cursor.vaddr + range_start * size_of_e
                    + iter_count as int * size_of_e,
                forall|i: usize|
                    #![trigger initial_view.addr_transl(i)]
                    initial_reader.cursor.vaddr <= i < initial_reader.end.vaddr ==> {
                        &&& initial_view.addr_transl(i) is Some
                        &&& initial_view.memory.contains_key(initial_view.addr_transl(i).unwrap().0)
                    },
                forall|va: usize|
                    #![trigger args.vm_io_owner.read_view_of().read(va)]
                    reader.cursor.vaddr <= va < initial_reader.end.vaddr ==> {
                        &&& initial_view.addr_transl(va)
                            == args.vm_io_owner.read_view_of().addr_transl(va)
                        &&& initial_view.read(va) == args.vm_io_owner.read_view_of().read(va)
                    },
                removed_indices.subset_of(initial_dom),
                args.child_perms.dom() == initial_dom.difference(removed_indices),
                // Witness past iter for each removed idx — the discharge
                // proof picks it up via `choose|j|` and invokes
                // `walk_uniqueness` at (current_cursor, witness_cursor).
                forall|idx: usize| #[trigger]
                    removed_indices.contains(idx) ==> exists|j: int|
                        #![trigger Self::walk_pte_at_view(
                            initial_view,
                            (initial_reader.cursor.vaddr
                                + range_start * size_of_e
                                + j * size_of_e) as usize,
                        )]
                        0 <= j < iter_count as int && {
                            let cj = (initial_reader.cursor.vaddr + range_start * size_of_e + j
                                * size_of_e) as usize;
                            let pte_j = Self::walk_pte_at_view(initial_view, cj);
                            &&& pte_j.is_present()
                            &&& !pte_j.is_last(self.level)
                            &&& idx == frame_to_index(pte_j.paddr())
                        },
            decreases n_iters - iter_count,
        {
            proof {
                vstd::arithmetic::mul::lemma_mul_is_distributive_sub(
                    size_of_e,
                    range_end - range_start,
                    iter_count as int,
                );
                vstd::arithmetic::mul::lemma_mul_inequality(
                    1,
                    range_end - range_start - iter_count as int,
                    size_of_e,
                );
            }
            let ghost cursor_pre_read: usize = reader.cursor.vaddr;
            let ghost pre_view: crate::specs::mm::virt_mem::MemView =
                args.vm_io_owner.read_view_of();
            proof {
                crate::specs::mm::virt_mem::MemView::lemma_read_bytes_eq_pointwise(
                    pre_view,
                    initial_view,
                    cursor_pre_read,
                    core::mem::size_of::<C::E>(),
                );
            }
            let pte = #[verus_spec(with Tracked(&mut args.vm_io_owner))]
            reader.read_once::<C::E>();
            let pte = pte.unwrap();
            proof {
                crate::mm::pod::lemma_decode_pod_inverse::<C::E>(pte);
                assert(pte == Self::walk_pte_at_view(initial_view, cursor_pre_read));
                vstd::arithmetic::mul::lemma_mul_nonnegative(range_start, size_of_e);
                vstd::arithmetic::mul::lemma_mul_nonnegative(iter_count as int, size_of_e);
                assert(initial_reader.cursor.vaddr <= cursor_pre_read);
            }
            if pte.is_present() {
                let paddr = pte.paddr();
                if !pte.is_last(level) {
                    proof {
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                            size_of_e,
                            range_start,
                            iter_count as int,
                        );
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                            range_start + iter_count as int,
                            size_of_e,
                        );
                        Self::lemma_coverage_at(
                            *self,
                            initial_reader,
                            initial_view,
                            initial_dom,
                            cursor_pre_read,
                        );
                        broadcast use crate::mm::frame::meta::mapping::lemma_frame_to_index_injective;

                        assert forall|idx: usize| #[trigger]
                            removed_indices.contains(idx) implies idx != frame_to_index(
                            pte.paddr(),
                        ) by {
                            let j = choose|j: int|
                                #![trigger Self::walk_pte_at_view(
                                    initial_view,
                                    (initial_reader.cursor.vaddr
                                        + range_start * size_of_e
                                        + j * size_of_e) as usize,
                                )]
                                0 <= j < iter_count as int && {
                                    let cj = (initial_reader.cursor.vaddr + range_start * size_of_e
                                        + j * size_of_e) as usize;
                                    let pte_j = Self::walk_pte_at_view(initial_view, cj);
                                    &&& pte_j.is_present()
                                    &&& !pte_j.is_last(self.level)
                                    &&& idx == frame_to_index(pte_j.paddr())
                                };
                            let cj: usize = (initial_reader.cursor.vaddr + range_start * size_of_e
                                + j * size_of_e) as usize;
                            let pte_j = Self::walk_pte_at_view(initial_view, cj);
                            vstd::arithmetic::mul::lemma_mul_nonnegative(range_start, size_of_e);
                            vstd::arithmetic::mul::lemma_mul_nonnegative(j, size_of_e);
                            vstd::arithmetic::mul::lemma_mul_strict_inequality(
                                j,
                                iter_count as int,
                                size_of_e,
                            );
                            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                                size_of_e,
                                range_start,
                                j,
                            );
                            vstd::arithmetic::mul::lemma_mul_inequality(
                                range_start + j + 1,
                                range_end,
                                size_of_e,
                            );
                            vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(
                                size_of_e,
                                range_end,
                                range_start,
                            );
                            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                                range_start + j,
                                size_of_e,
                            );
                            Self::lemma_uniqueness_at_pair(
                                *self,
                                initial_reader,
                                initial_view,
                                cursor_pre_read,
                                cj,
                            );
                            pte.axiom_present_paddr_aligned();
                            pte_j.axiom_present_paddr_aligned();
                        };
                        // Pinning these in SMT context lets `tracked_remove`'s
                        // dom-containment precondition and `from_raw`'s
                        // `from_raw_requires_safety` (via embedding) discharge.
                        assert(args.child_perms.dom().contains(frame_to_index(paddr)));
                    }
                    let tracked child_perm = args.child_perms.tracked_remove(frame_to_index(paddr));
                    proof {
                        removed_indices = removed_indices.insert(frame_to_index(paddr));
                        // Witness for the just-inserted idx: j = iter_count
                        // (before the end-of-body increment), cursor_j ==
                        // cursor_pre_read, pte_j == pte. Required to keep
                        // the witness-exists loop invariant true.
                        assert({
                            let cj = (initial_reader.cursor.vaddr + range_start * size_of_e
                                + iter_count as int * size_of_e) as usize;
                            let pte_j = Self::walk_pte_at_view(initial_view, cj);
                            &&& cj == cursor_pre_read
                            &&& pte_j == pte
                            &&& pte_j.is_present()
                            &&& !pte_j.is_last(self.level)
                            &&& frame_to_index(paddr) == frame_to_index(pte_j.paddr())
                        });
                    }
                    let frame = unsafe {
                        #[verus_spec(
                            with Tracked(&mut args.regions),
                                 Tracked(&child_perm) => _debt
                        )]
                        Frame::<Self>::from_raw(paddr)
                    };
                    VerifiedDrop::drop(frame, Tracked(&mut args.regions));
                } else {
                    // SAFETY: The PTE points to a mapped item. The ownership
                    // of the item is transferred here then dropped.
                    let _item = unsafe { C::item_from_raw(paddr, level, pte.prop()) };
                }
            }
            proof {
                vstd::arithmetic::div_mod::lemma_mod_adds(
                    reader.cursor.vaddr as int - size_of_e,
                    size_of_e,
                    align_of_e,
                );
            }
            let ghost iter_count_old: int = iter_count as int;
            iter_count = iter_count + 1;
            proof {
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                    size_of_e,
                    iter_count_old,
                    1,
                );
            }
        }
    }

    fn is_untyped(&self) -> bool {
        false
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

#[verus_verify]
impl<C: PageTableConfig> PageTableNode<C> {
    /// Gets the level of a page table node.
    /// # Verified Properties
    /// ## Preconditions
    /// - The node must be well-formed, and the caller must provide a permission token for its metadata.
    /// ## Postconditions
    /// - Returns the level of the node.
    /// ## Safety
    /// - We require the caller to provide a permission token to ensure that this function is only called on a valid page table node.
    #[verus_spec(
        with Tracked(perm) : Tracked<&PointsTo<MetaSlot, Metadata<PageTablePageMeta<C>>>>
    )]
    pub(super) fn level(&self) -> PagingLevel
        requires
            self.ptr.addr() == perm.addr(),
            self.ptr.addr() == perm.points_to.addr(),
            perm.is_init(),
            perm.wf(&perm.inner_perms),
        returns
            perm.value().metadata.level,
    {
        #[verus_spec(with Tracked(perm))]
        let meta = self.meta();
        meta.level
    }

    /// Allocates a new empty page table node.
    #[verus_spec(res =>
        with Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&Guards<'rcu, C>>,
            Ghost(idx): Ghost<usize>,
        -> owner: Tracked<OwnerSubtree<C>>
        requires
            1 <= level < NR_LEVELS,
            idx < NR_ENTRIES,
            old(regions).inv(),
            old(parent_owner).inv(),
        ensures
            final(regions).inv(),
            final(parent_owner).inv(),
            allocated_empty_node_owner(owner@, level),
            allocated_empty_node_grandchildren_none(owner@),
            res.ptr.addr() == owner@.value.node.unwrap().meta_perm.addr(),
            guards.unlocked(owner@.value.node.unwrap().meta_perm.addr()),
            MetaSlot::get_from_unused_spec(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr()), false, *old(regions), *final(regions)),
            old(regions).slots.contains_key(frame_to_index(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr()))),
            // Allocator trust boundary: PT-node allocations come from the regular
            // RAM pool, never from MMIO ranges. Used by `alloc_if_none_metaregion_sound_preserved`
            // to rule out untracked-frame collisions at the freshly-allocated idx.
            !crate::specs::mm::frame::meta_owners::is_mmio_paddr(
                meta_to_frame(owner@.value.node.unwrap().meta_perm.addr())),
            owner@.value.metaregion_sound(*final(regions)),
            // Note: `owner@.value.in_scope` was previously asserted here, but
            // `allocated_empty_node_owner` already requires `owner.inv()`, which
            // through `EntryOwner::inv` forces `!in_scope`. Asserting both was
            // an unsoundness that allowed `assert(false)` post-alloc.
            //
            // Disjointness: the alloc'd slot's idx is different from any
            // previously-active slot's idx. Derived from the unused pre-state
            // (`pre.slot_owners[new_alloc_idx].ref_count == UNUSED` per
            // `get_from_unused_spec`). Stated as an explicit ensures so it's
            // easy to trigger from split/alloc_if_none loop invariants.
            forall|i: usize|
                #[trigger] old(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> i != frame_to_index(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr())),
            owner@.value.match_pte(C::E::new_pt_spec(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr())), level as PagingLevel),
            *final(parent_owner) == old(parent_owner).set_children_perm(idx, C::E::new_pt_spec(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr()))),
    )]
    #[verifier::external_body]
    pub fn alloc<'rcu>(level: PagingLevel) -> Self {
        let tracked entry_owner = EntryOwner::tracked_new_absent(
            TreePath::new(Seq::empty()),
            level,
        );

        let tracked mut owner = OwnerSubtree::<C>::new_val_tracked(entry_owner, level as nat);
        let meta = PageTablePageMeta::new(level);
        let mut frame = FrameAllocOptions::new();
        frame.zeroed(true);
        let allocated_frame = frame.alloc_frame_with(meta).expect(
            "Failed to allocate a page table node",
        );
        // The allocated frame is zeroed. Make sure zero is absent PTE.
        //debug_assert_eq!(C::E::new_absent().as_usize(), 0);

        proof_with!(|= Tracked(owner));

        allocated_frame
    }/*
    /// Activates the page table assuming it is a root page table.
    ///
    /// Here we ensure not dropping an active page table by making a
    /// processor a page table owner. When activating a page table, the
    /// reference count of the last activated page table is decremented.
    /// And that of the current page table is incremented.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the page table to be activated has
    /// proper mappings for the kernel and has the correct const parameters
    /// matching the current CPU.
    ///
    /// # Panics
    ///
    /// Only top-level page tables can be activated using this function.
    pub(crate) unsafe fn activate(&self) {
        use crate::{
            arch::mm::{activate_page_table, current_page_table_paddr},
            mm::page_prop::CachePolicy,
        };

        #[cfg(feature = "allow_panic")]
        assert_eq!(self.level(), C::NR_LEVELS());

        let last_activated_paddr = current_page_table_paddr();
        if last_activated_paddr == self.start_paddr() {
            return;
        }

        // SAFETY: The safety is upheld by the caller.
        unsafe { activate_page_table(self.clone().into_raw(), CachePolicy::Writeback) };

        // Restore and drop the last activated page table.
        // SAFETY: The physical address is valid and points to a forgotten page table node.
        drop(unsafe { Self::from_raw(last_activated_paddr) });
    }

    /// Activates the (root) page table assuming it is the first activation.
    ///
    /// It will not try dropping the last activate page table. It is the same
    /// with [`Self::activate()`] in other senses.
    pub(super) unsafe fn first_activate(&self) {
        use crate::{arch::mm::activate_page_table, mm::page_prop::CachePolicy};

        // SAFETY: The safety is upheld by the caller.
        unsafe { activate_page_table(self.clone().into_raw(), CachePolicy::Writeback) };
    }*/

}

#[verus_verify]
impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    pub open spec fn locks_preserved_except<'rcu>(
        addr: usize,
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>,
    ) -> bool {
        &&& OwnerSubtree::implies(
            CursorOwner::node_unlocked(guards0),
            CursorOwner::node_unlocked_except(guards1, addr),
        )
        &&& forall|i: usize| guards0.lock_held(i) ==> guards1.lock_held(i)
        &&& forall|i: usize| guards0.unlocked(i) && i != addr ==> guards1.unlocked(i)
    }

    /// Locks the page table node.
    ///
    /// An atomic mode guard is required to
    ///  1. prevent deadlocks;
    ///  2. provide a lifetime (`'rcu`) that the nodes are guaranteed to outlive.
    /// # Verification Design
    /// As of when we verified this library, we didn't have a spin lock implementation, so we axiomatize
    /// what happens when it's successful.
    #[verifier::external_body]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            self.inner@.invariants(*owner),
            old(guards).unlocked(owner.meta_perm.addr()),
        ensures
            final(guards).lock_held(owner.meta_perm.addr()),
            Self::locks_preserved_except(owner.meta_perm.addr(), *old(guards), *final(guards)),
            owner.relate_guard(res),
    )]
    pub fn lock<'rcu, A: InAtomicMode>(self, _guard: &'rcu A) -> PageTableGuard<'rcu, C> where
        'a: 'rcu,
     {
        unimplemented!()
    }

    /// Creates a new [`PageTableGuard`] without checking if the page table lock is held.
    ///
    /// # Safety
    ///
    /// This function must be called if this task logically holds the lock.
    ///
    /// Calling this function when a guard is already created is undefined behavior
    /// unless that guard was already forgotten.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            self.inner@.invariants(*owner),
            old(guards).unlocked(owner.meta_perm.addr()),
        ensures
            final(guards).lock_held(owner.meta_perm.addr()),
            Self::locks_preserved_except(owner.meta_perm.addr(), *old(guards), *final(guards)),
            owner.relate_guard(res),
    )]
    pub fn make_guard_unchecked<'rcu, A: InAtomicMode>(self, _guard: &'rcu A) -> PageTableGuard<
        'rcu,
        C,
    > where 'a: 'rcu {
        let guard = PageTableGuard { inner: self };

        proof {
            let ghost guards0 = *guards;
            guards.guards.tracked_insert(owner.meta_perm.addr(), None);
            assert(owner.relate_guard(guard));

            assert(forall|other: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                owner.inv() && CursorOwner::node_unlocked(guards0)(other, path)
                    ==> #[trigger] CursorOwner::node_unlocked_except(
                    *guards,
                    owner.meta_perm.addr(),
                )(other, path));
        }

        guard
    }
}

//}
impl<'rcu, C: PageTableConfig> PageTableGuard<'rcu, C> {
    /// Borrows an entry in the node at a given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is not within the bound of
    /// [`nr_subpage_per_huge<C>`].
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
            Tracked(child_owner): Tracked<&EntryOwner<C>>,
    )]
    pub fn entry<'a>(&'a mut self, idx: usize) -> (res: Entry<'a, 'rcu, C>)
        requires
            owner.inv(),
            !child_owner.in_scope,
            child_owner.inv(),
            owner.relate_guard(*old(self)),
            child_owner.match_pte(
                owner.children_perm.value()[idx as int],
                child_owner.parent_level,
            ),
            // Panic condition
            idx < NR_ENTRIES,
        ensures
            res.wf(*child_owner),
            res.idx == idx,
            owner.relate_guard(*res.node),
            *final(self) == *old(self),
    {
        #[cfg(feature = "allow_panic")]
        assert!(idx < nr_subpage_per_huge::<C>());
        // SAFETY: The index is within the bound. `*self` is unchanged because
        // Entry::new_at's `*res.node == *old(guard)` ensures says the wrapped
        // node equals the input guard's value, and the reborrow makes
        // `*final(self) == *res.node`.
        #[verus_spec(with Tracked(child_owner), Tracked(owner))]
        Entry::new_at(self, idx)
    }

    /// Gets the number of valid PTEs in a page table node.
    /// # Verified Properties
    /// ## Preconditions
    /// - The node must be well-formed.
    /// ## Postconditions
    /// - Returns the number of valid PTEs in the node.
    /// ## Safety
    /// - We require the caller to provide a permission token to ensure that this function is only called on a valid page table node.
    #[verus_spec(
        with Tracked(owner) : Tracked<&NodeOwner<C>>
    )]
    pub fn nr_children(&self) -> (nr: u16)
        requires
    // Node invariants: owner well-formedness and node-owner consistency

            self.inner.inner@.invariants(*owner),
        returns
            owner.meta_own.nr_children.value(),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.meta();

        *meta.nr_children.borrow(Tracked(&owner.meta_own.nr_children))
    }

    /// Returns if the page table node is detached from its parent.
    #[verus_spec(
        with Tracked(meta_perm): Tracked<&'a PointsTo<MetaSlot, Metadata<PageTablePageMeta<C>>>>
    )]
    pub(super) fn stray_mut<'a>(&'a mut self) -> (res: &'a pcell_maybe_uninit::PCell<bool>)
        requires
            old(self).inner.inner@.ptr.addr() == meta_perm.addr(),
            old(self).inner.inner@.ptr.addr() == meta_perm.points_to.addr(),
            meta_perm.is_init(),
            meta_perm.wf(&meta_perm.inner_perms),
        ensures
            res.id() == meta_perm.value().metadata.stray.id(),
            *final(self) == *old(self),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(meta_perm))]
        let meta = self.meta();
        &meta.stray
    }

    /// Reads a non-owning PTE at the given index.
    ///
    /// A non-owning PTE means that it does not account for a reference count
    /// of the a page if the PTE points to a page. The original PTE still owns
    /// the child page.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    #[verus_spec(
        with Tracked(owner): Tracked<&NodeOwner<C>>
    )]
    pub fn read_pte(&self, idx: usize) -> (pte: C::E)
        requires
            self.inner.inner@.invariants(*owner),
            idx < NR_ENTRIES,
        ensures
            pte == owner.children_perm.value()[idx as int],
    {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(
                #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
                self.start_paddr(),
            ),
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
        #[verus_spec(with Tracked(&owner.children_perm))]
        load_pte(ptr.add(idx), Ordering::Relaxed)
    }

    /// Writes a page table entry at a given index.
    ///
    /// This operation will leak the old child if the old PTE is present.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  1. The index must be within the bound;
    ///  2. The PTE must represent a valid [`Child`] whose level is compatible
    ///     with the page table node.
    ///  3. The page table node will have the ownership of the [`Child`]
    ///     after this method.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut NodeOwner<C>>
    )]
    pub fn write_pte(&mut self, idx: usize, pte: C::E)
        requires
            old(self).inner.inner@.invariants(*old(owner)),
            idx < NR_ENTRIES,
        ensures
            final(owner).inv(),
            final(owner).meta_perm.addr() == old(owner).meta_perm.addr(),
            final(owner).level == old(owner).level,
            final(owner).meta_own == old(owner).meta_own,
            final(owner).meta_perm.points_to == old(owner).meta_perm.points_to,
            final(owner).meta_perm.inner_perms == old(owner).meta_perm.inner_perms,
            final(owner).children_perm.value() == old(owner).children_perm.value().update(
                idx as int,
                pte,
            ),
            *final(self) == *old(self),
    {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        #[verusfmt::skip]
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(
                #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
                self.start_paddr()
            ),
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
        #[verus_spec(with Tracked(&mut owner.children_perm))]
        store_pte(ptr.add(idx), pte, Ordering::Release)
    }

    /// Gets the mutable reference to the number of valid PTEs in the node.
    #[verus_spec(
        with Tracked(meta_perm): Tracked<&'a PointsTo<MetaSlot, Metadata<PageTablePageMeta<C>>>>
    )]
    fn nr_children_mut<'a>(&'a mut self) -> (res: &'a pcell_maybe_uninit::PCell<u16>)
        requires
            old(self).inner.inner@.ptr.addr() == meta_perm.addr(),
            old(self).inner.inner@.ptr.addr() == meta_perm.points_to.addr(),
            meta_perm.is_init(),
            meta_perm.wf(&meta_perm.inner_perms),
        ensures
            res.id() == meta_perm.value().metadata.nr_children.id(),
            *final(self) == *old(self),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(meta_perm))]
        let meta = self.meta();
        &meta.nr_children
    }
}

/*impl<C: PageTableConfig> Drop for PageTableGuard<'_, C> {
    fn drop(&mut self) {
        self.inner.meta().lock.store(0, Ordering::Release);
    }
}*/

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub fn new(level: PagingLevel) -> Self {
        Self {
            nr_children: pcell_maybe_uninit::PCell::new(0).0,
            stray: pcell_maybe_uninit::PCell::new(false).0,
            level,
            lock: PAtomicU8::new(0).0,
            _phantom: PhantomData,
        }
    }

    /// The PTE value that `read_once::<C::E>` would produce at cursor `c`
    /// against the given memory view. Linked to `read_once` via
    /// `pod_bytes(v) == read_view.read_bytes(...)` (strengthened ensures)
    /// + [`lemma_decode_pod_inverse`].
    pub open spec fn walk_pte_at_view(view: crate::specs::mm::virt_mem::MemView, c: usize) -> C::E {
        crate::mm::pod::decode_pod::<C::E>(view.read_bytes(c, core::mem::size_of::<C::E>()))
    }

    /// Single-cursor projection of [`walk_coverage_from_view`]. Extracting
    /// the forall body to a named predicate lets the body invoke
    /// [`lemma_coverage_at`] for one specific `c` instead of relying on
    /// auto-trigger matching across the loop invariant's `forall|c|`.
    pub open spec fn walk_coverage_at(
        self,
        view: crate::specs::mm::virt_mem::MemView,
        dom: vstd::set::Set<usize>,
        c: usize,
    ) -> bool {
        let pte = Self::walk_pte_at_view(view, c);
        pte.is_present() && !pte.is_last(self.level) ==> dom.contains(frame_to_index(pte.paddr()))
    }

    /// Instantiate [`walk_coverage_from_view`]'s forall at one cursor.
    pub proof fn lemma_coverage_at(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
        dom: vstd::set::Set<usize>,
        c: usize,
    )
        requires
            self.walk_coverage_from_view(reader, view, dom),
            reader.cursor.vaddr <= c,
            c + core::mem::size_of::<C::E>() <= reader.cursor.vaddr + reader.remain_spec(),
            (c - reader.cursor.vaddr) % core::mem::size_of::<C::E>() as int == 0,
        ensures
            self.walk_coverage_at(view, dom, c),
    {
        assert(Self::walk_pte_at_view(view, c) == Self::walk_pte_at_view(view, c));
    }

    /// Instantiate [`walk_uniqueness_from_view`]'s forall at one cursor pair.
    pub proof fn lemma_uniqueness_at_pair(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
        c1: usize,
        c2: usize,
    )
        requires
            self.walk_uniqueness_from_view(reader, view),
            reader.cursor.vaddr <= c1,
            c1 + core::mem::size_of::<C::E>() <= reader.cursor.vaddr + reader.remain_spec(),
            (c1 - reader.cursor.vaddr) % core::mem::size_of::<C::E>() as int == 0,
            reader.cursor.vaddr <= c2,
            c2 + core::mem::size_of::<C::E>() <= reader.cursor.vaddr + reader.remain_spec(),
            (c2 - reader.cursor.vaddr) % core::mem::size_of::<C::E>() as int == 0,
            c1 != c2,
            Self::walk_pte_at_view(view, c1).is_present(),
            !Self::walk_pte_at_view(view, c1).is_last(self.level),
            Self::walk_pte_at_view(view, c2).is_present(),
            !Self::walk_pte_at_view(view, c2).is_last(self.level),
        ensures
            Self::walk_pte_at_view(view, c1).paddr() != Self::walk_pte_at_view(view, c2).paddr(),
    {
    }

    /// Caller-side dom-membership obligation: every present non-last PTE
    /// position in the walk (over `view`) has its child-frame index in
    /// `dom`. Phrased over a frozen `(view, dom)` pair so the body can
    /// carry it as a loop invariant against an entry-state snapshot
    /// while `args.vm_io_owner` advances per iteration.
    pub open spec fn walk_coverage_from_view(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
        dom: vstd::set::Set<usize>,
    ) -> bool {
        forall|c: usize|
            #![trigger Self::walk_pte_at_view(view, c)]
            reader.cursor.vaddr <= c && c + core::mem::size_of::<C::E>() <= reader.cursor.vaddr
                + reader.remain_spec() && (c - reader.cursor.vaddr) % core::mem::size_of::<
                C::E,
            >() as int == 0 ==> {
                let pte = Self::walk_pte_at_view(view, c);
                pte.is_present() && !pte.is_last(self.level) ==> dom.contains(
                    frame_to_index(pte.paddr()),
                )
            }
    }

    /// Caller-side uniqueness obligation: distinct cursor positions with
    /// present non-last PTEs (in `view`) map to distinct paddrs.
    pub open spec fn walk_uniqueness_from_view(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
    ) -> bool {
        forall|c1: usize, c2: usize|
            #![trigger Self::walk_pte_at_view(view, c1), Self::walk_pte_at_view(view, c2)]
            reader.cursor.vaddr <= c1 && c1 + core::mem::size_of::<C::E>() <= reader.cursor.vaddr
                + reader.remain_spec() && (c1 - reader.cursor.vaddr) % core::mem::size_of::<
                C::E,
            >() as int == 0 && reader.cursor.vaddr <= c2 && c2 + core::mem::size_of::<C::E>()
                <= reader.cursor.vaddr + reader.remain_spec() && (c2 - reader.cursor.vaddr)
                % core::mem::size_of::<C::E>() as int == 0 && c1 != c2 ==> {
                let pte1 = Self::walk_pte_at_view(view, c1);
                let pte2 = Self::walk_pte_at_view(view, c2);
                pte1.is_present() && !pte1.is_last(self.level) && pte2.is_present()
                    && !pte2.is_last(self.level) ==> pte1.paddr() != pte2.paddr()
            }
    }

    /// Caller-side shape obligation: every paddr in `child_perms.dom()`
    /// has a slot perm matching the shape `from_raw` + `VerifiedDrop::drop`
    /// expect (init, alignment, refcount within bounds, last-reference
    /// shape when refcount == 1).
    pub open spec fn child_perms_embedding(args: crate::mm::frame::meta::OnDropArgs) -> bool {
        forall|paddr: crate::mm::Paddr|
            #![trigger args.child_perms.dom().contains(frame_to_index(paddr))]
            args.child_perms.dom().contains(frame_to_index(paddr)) ==> {
                let idx = frame_to_index(paddr);
                let so = args.regions.slot_owners[idx];
                &&& args.regions.slot_owners.contains_key(idx)
                &&& <Frame<Self>>::from_raw_requires_safety(args.regions, paddr)
                &&& so.raw_count <= 1
                &&& args.child_perms[idx].is_init()
                &&& args.child_perms[idx].addr() == frame_to_meta(paddr)
                &&& args.child_perms[idx].value().wf(
                    so,
                )
                // Live frame: refcount in [1, REF_COUNT_MAX]. Needed for
                // `Drop::drop_requires` after `from_raw` reconstructs the
                // child Frame.
                &&& so.inner_perms.ref_count.value() > 0
                &&& so.inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                &&& so.inner_perms.ref_count.value()
                    <= crate::specs::mm::frame::meta_owners::REF_COUNT_MAX
                // If refcount == 1, the child is in last-reference shape
                // (drop will tear it down). PT-children at drop time have
                // refcount == 1 (only the parent's PTE holds them).
                &&& so.inner_perms.ref_count.value() == 1 ==> {
                    &&& so.inner_perms.storage.is_init()
                    &&& so.inner_perms.in_list.value() == 0
                    &&& so.paths_in_pt.is_empty()
                }
            }
    }
}

} // verus!
