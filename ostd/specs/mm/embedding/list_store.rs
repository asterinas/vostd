//! Self-contained one-step-soundness harness for the frame `LinkedList`
//! ([`crate::mm::frame::LinkedList`]) — the embedding's companion to
//! [`super::VmStore`], specialised to linked-list operations.
//!
//! # Why a separate, generic store
//!
//! Unlike `VmStore` (which fixes concrete configs such as
//! `UserPtConfig`), `ListStore<M>` is *generic* over the link metadata
//! `M`. The kernel's `LinkedList<M>` is a generic library with no
//! canonical concrete instantiation in ostd, and `LinkedListOwner<M>`
//! cannot be type-erased to `dyn`: its per-link permission is the
//! associated type `<M as Repr<MetaSlotSmall>>::Perm`, embedded in
//! `LinkInnerPerms<M>`, so the trait is not object-safe (cf.
//! `Frame<dyn AnyFrameMeta>`, which works only because it exposes no
//! associated type post-erasure).
//!
//! # Why `in_list` is a non-issue here
//!
//! `ListStore<M>` requires only `regions.inv()`
//! ([`MetaRegionOwners::inv`]), which — unlike
//! `VmStore::structural_inv` — does **not** constrain `in_list`. A
//! listed frame sits at `rc == REF_COUNT_UNIQUE` with
//! `in_list == list_id != 0`; the UNIQUE branch of `MetaSlotOwner::inv`
//! pins only `storage`/`vtable_ptr` init, leaving `in_list` free. So
//! listed frames are admitted with *no* invariant weakening — the
//! `in_list == 0` constraint is purely a `VmStore` concern and does not
//! arise in this harness.
//!
//! # State
//!
//! - `regions`: the shared metadata-region ownership.
//! - `lists`: held [`LinkedListOwner`]s. Each link is a forgotten
//!   `UniqueFrame<Link<M>>` (its drop-obligation was consumed by
//!   `into_raw` on push); the owner's [`LinkedListOwner::relate_region`]
//!   ties every link to its UNIQUE region slot and pins the
//!   `next`/`prev` pointer wiring.
//! - `loose`: held-but-unlisted [`UniqueFrameOwner`]s — live
//!   `UniqueFrame<Link<M>>` handles (drop-obligation present) eligible
//!   to be pushed. `push` moves one from `loose` into a list; `pop`
//!   moves a list's end link out into `loose`.
//!
//! # Roadmap
//!
//! Landed: the store + invariant, the front/back
//! allocate-build-teardown suite (`new`, `push_front` / `pop_front`,
//! `push_back` / `pop_back`), the general cursor surgery —
//! `insert_before` / `take_current` at an *arbitrary* index
//! ([`ListStore::step_insert_before_at`] / [`ListStore::step_take_at`]),
//! which subsume the front/back ops — the read-only accessors
//! ([`ListStore::step_size`] / [`ListStore::step_is_empty`]), and the
//! full **persistent cursor** lifecycle: a cursor checks its list out of
//! `lists` into `cursors` ([`ListStore::step_cursor_front_mut`] /
//! `step_cursor_back_mut` / `step_cursor_mut_at`), walks it
//! (`step_move_next` / `step_move_prev` / `step_current_meta`), mutates
//! through it (`step_cursor_insert_before` / `step_cursor_take_current`),
//! and checks it back in on drop ([`ListStore::step_cursor_drop`]).
use vstd::prelude::*;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ownership::*;

use crate::mm::Paddr;
use crate::mm::frame::meta::mapping::frame_to_index;
use crate::mm::frame::{AnyFrameMeta, Link};
use crate::specs::arch::has_safe_slot;
use crate::specs::mm::frame::linked_list::linked_list_owners::{
    CursorOwner, LinkOwner, LinkedListOwner, MetaSlotSmall,
};
use crate::specs::mm::frame::meta_owners::{PageUsage, REF_COUNT_UNIQUE};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::unique::UniqueFrameOwner;

verus! {

/// Logical identifier for a held [`LinkedListOwner`] in the store.
pub type ListId = int;

/// Logical identifier for a loose (held-but-unlisted)
/// `UniqueFrame<Link<M>>` in the store.
pub type LooseId = int;

/// Logical identifier for a live [`CursorOwner`] in the store. A cursor
/// is keyed by the *home* [`ListId`] whose list it checked out, so a
/// list is cursored iff its id is in `cursors` (and then absent from
/// `lists`).
pub type CursorId = ListId;

/// The membership registry relating one (held or checked-out) list `lo`
/// to the physical `in_list` tags in `regions`:
///   - **forward**: every link's region slot carries `lo.list_id` (the
///     exec `insert_before` stamps it via `store(lazy_get_id())`);
///   - **reverse** (only for a real, non-zero id): every region slot
///     carrying that id is one of `lo`'s links — the global
///     `in_list`-uniqueness the id allocator guarantees (a freshly
///     minted id is system-wide unused; ids are never reused).
/// Together they make `in_list == list_id` an *exact* membership test,
/// which is exactly what [`crate::mm::frame::LinkedList::contains`]
/// computes.
pub open spec fn list_registry_ok<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    regions: MetaRegionOwners,
    lo: LinkedListOwner<M>,
) -> bool {
    &&& forall|i: int|
        #![trigger lo.slot_index_at(i)]
        0 <= i < lo.list.len() ==> regions.slot_owners[lo.slot_index_at(
            i,
        )].inner_perms.in_list.value() == lo.list_id
    &&& lo.list_id != 0 ==> forall|idx: usize|
        #![trigger regions.slot_owners[idx]]
        regions.slot_owners.contains_key(idx)
            && regions.slot_owners[idx].inner_perms.in_list.value() == lo.list_id ==> exists|i: int|

            0 <= i < lo.list.len() && lo.slot_index_at(i) == idx
}

/// One-step-soundness store for the frame `LinkedList`. Holds the shared
/// `regions`, the set of held lists, the pool of loose
/// (push-eligible) `UniqueFrame<Link<M>>` handles, and the live cursors.
///
/// A cursor *checks out* its list: a live `CursorMut` borrows the
/// `LinkedList` exclusively, so while a cursor exists its
/// `LinkedListOwner` lives inside the [`CursorOwner`] (`cursors`) rather
/// than in `lists`. Dropping the cursor returns the list to `lists`.
pub tracked struct ListStore<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub regions: MetaRegionOwners,
    pub lists: Map<ListId, LinkedListOwner<M>>,
    pub loose: Map<LooseId, UniqueFrameOwner<Link<M>>>,
    pub cursors: Map<CursorId, CursorOwner<M>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> ListStore<M> {
    /// The store's top-level invariant.
    pub open spec fn inv(self) -> bool {
        &&& self.regions.inv()
        &&& self.lists.dom().finite()
        &&& self.loose.dom().finite()
        // Each held list is well-formed and every link relates to its
        // UNIQUE region slot (incl. the `next`/`prev` pointer wiring).
        &&& forall|id: ListId| #[trigger]
            self.lists.dom().contains(id) ==> {
                &&& self.lists[id].inv()
                &&& self.lists[id].relate_region(self.regions)
            }
            // Each loose handle is a valid live `UniqueFrame<Link<M>>`:
            // a UNIQUE slot with a pending drop-obligation, sitting
            // *outside* every list — `in_list == 0` and unlinked
            // (`frame_link_inv`: no `prev`/`next`). The `in_list == 0`
            // fact makes list-vs-loose slot disjointness derivable (a
            // listed slot has `in_list == list_id != 0`).
        &&& forall|lid: LooseId| #[trigger]
            self.loose.dom().contains(lid) ==> {
                &&& self.loose[lid].inv()
                &&& self.loose[lid].global_inv(self.regions)
                &&& self.loose[lid].frame_link_inv(self.regions)
                &&& self.regions.slot_owners[self.loose[lid].slot_index].inner_perms.in_list.value()
                    == 0
            }
            // Distinct lists carry distinct *nonzero* ids (`lazy_get_id`
            // mints a globally fresh id per list — even a list emptied by
            // pops keeps its unique id; only never-pushed lists share the
            // placeholder `list_id == 0`). With each link's
            // `in_list == list_id`, this makes cross-list slot
            // disjointness derivable.
        &&& forall|id1: ListId, id2: ListId|
            #![trigger self.lists.dom().contains(id1), self.lists.dom().contains(id2)]
            self.lists.dom().contains(id1) && self.lists.dom().contains(id2)
                && self.lists[id1].list_id == self.lists[id2].list_id && self.lists[id1].list_id
                != 0 ==> id1
                == id2
            // Distinct loose handles occupy distinct slots (a UNIQUE frame
            // is held in at most one place).
        &&& forall|lid1: LooseId, lid2: LooseId|
            #![trigger self.loose.dom().contains(lid1), self.loose.dom().contains(lid2)]
            self.loose.dom().contains(lid1) && self.loose.dom().contains(lid2)
                && self.loose[lid1].slot_index == self.loose[lid2].slot_index ==> lid1 == lid2
        &&& self.cursors.dom().finite()
        // A cursored list is *checked out*: it lives in `cursors`
        // (keyed by its home id), never simultaneously in `lists`. This
        // is the borrow — a live `CursorMut` holds the list exclusively.
        &&& self.lists.dom().disjoint(
            self.cursors.dom(),
        )
        // Each live cursor's checked-out list is well-formed and every
        // link relates to its UNIQUE region slot, exactly as for a held
        // list; additionally the cursor index is in range
        // (`inv_region`). `list_own.inv()` is carried so the trusted
        // per-op other-lists frame (stated over `inv() && relate_region`)
        // applies to a cursor's list under region-changing ops.
        &&& forall|cid: CursorId| #[trigger]
            self.cursors.dom().contains(cid) ==> {
                &&& self.cursors[cid].list_own.inv()
                &&& self.cursors[cid].inv_region(self.regions)
            }
            // A cursor's list shares no nonzero id with any held list —
            // cross list/cursor slot disjointness, mirroring lists×lists.
        &&& forall|id: ListId, cid: CursorId|
            #![trigger self.lists.dom().contains(id), self.cursors.dom().contains(cid)]
            self.lists.dom().contains(id) && self.cursors.dom().contains(cid)
                && self.lists[id].list_id == self.cursors[cid].list_own.list_id
                && self.lists[id].list_id != 0
                ==> false
            // Distinct cursors carry distinct *nonzero* list ids.
        &&& forall|cid1: CursorId, cid2: CursorId|
            #![trigger self.cursors.dom().contains(cid1), self.cursors.dom().contains(cid2)]
            self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                && self.cursors[cid1].list_own.list_id != 0 ==> cid1
                == cid2
            // Membership registry: each held list's id tags exactly its own
            // links in the region (forward + reverse — see [`list_registry_ok`]).
            // This is what makes `contains` an exact membership test.
        &&& forall|id: ListId| #[trigger]
            self.lists.dom().contains(id) ==> list_registry_ok(
                self.regions,
                self.lists[id],
            )
        // Same registry for each checked-out cursor's list.
        &&& forall|cid: CursorId| #[trigger]
            self.cursors.dom().contains(cid) ==> list_registry_ok(
                self.regions,
                self.cursors[cid].list_own,
            )
    }
}

// =============================================================================
// Fresh-id helpers + tracked constructors
// =============================================================================
/// Tracked constructor for a fresh *empty* list owner. Sound: an empty
/// `LinkedListOwner` claims no permissions (cf.
/// [`LinkedListOwner::tracked_destroy_empty`]), and carries
/// `list_id == 0` — the real id is minted lazily on first push.
pub axiom fn axiom_empty_list_owner<M: AnyFrameMeta + Repr<MetaSlotSmall>>() -> (tracked res:
    LinkedListOwner<M>)
    ensures
        res.list =~= Seq::<LinkOwner>::empty(),
        res.list_id == 0,
;

/// Fresh-id helper for the list id space. The id must avoid both held
/// lists *and* checked-out cursors (a cursored list's home id is absent
/// from `lists` but reserved in `cursors`).
pub open spec fn fresh_list_id<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    lists: Map<ListId, LinkedListOwner<M>>,
    cursors: Map<CursorId, CursorOwner<M>>,
) -> ListId {
    choose|id: ListId| !lists.dom().contains(id) && !cursors.dom().contains(id)
}

pub axiom fn axiom_fresh_list_id_not_in_dom<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    lists: Map<ListId, LinkedListOwner<M>>,
    cursors: Map<CursorId, CursorOwner<M>>,
)
    requires
        lists.dom().finite(),
        cursors.dom().finite(),
    ensures
        !lists.dom().contains(fresh_list_id(lists, cursors)) && !cursors.dom().contains(
            fresh_list_id(lists, cursors),
        ),
;

/// Trusted reflection of [`crate::mm::frame::LinkedList::push_front`]'s
/// effect on `(regions, owner, frame_own)`. The first block of `ensures`
/// mirrors the now-verified exec `push_front` ensures verbatim
/// (`relate_region` of the pushed owner, the list / id / `in_list`
/// effects, `frame_obligations` consumption, and the outside-the-list
/// slot-preservation frame). The last two add facts that *follow* from
/// them — sound, hence safe to assert here:
///   - **fresh minted id** (`old.list_id == 0 ==> final.list_id ∉
///     used_ids`): the exec mints the id from a global counter, so it is
///     fresh w.r.t. any finite in-use set; the caller passes the other
///     lists' ids, keeping cross-list id uniqueness.
///   - **other lists preserved**: any well-formed list `l` with a
///     *different* id keeps its `relate_region`. The only slots the
///     surgery touches are the loose frame's (`in_list == 0`, required
///     below) and the old front's (`in_list == new id`); both are
///     disjoint from `l`'s slots (which carry `in_list == l.list_id`),
///     so by the slot-preservation frame `l` is untouched.
pub axiom fn push_front_embedded<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    tracked regions: &mut MetaRegionOwners,
    tracked owner: &mut LinkedListOwner<M>,
    tracked frame_own: &mut UniqueFrameOwner<Link<M>>,
    used_ids: Set<u64>,
)
    requires
        old(regions).inv(),
        old(owner).inv(),
        old(owner).relate_region(*old(regions)),
        old(frame_own).inv(),
        old(frame_own).global_inv(*old(regions)),
        old(frame_own).frame_link_inv(*old(regions)),
        old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.value() == 0,
    ensures
        final(regions).inv(),
        final(owner).inv(),
        final(owner).relate_region(*final(regions)),
        final(owner).list == old(owner).list.insert(0, final(frame_own).meta_own),
        old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
        final(owner).list_id != 0,
        old(owner).list_id == 0 ==> !used_ids.contains(final(owner).list_id),
        final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
        final(frame_own).meta_own.in_list == final(owner).list_id,
        final(regions).frame_obligations =~= old(regions).frame_obligations.remove(
            old(frame_own).slot_index,
        ),
        forall|k: usize|
            #![trigger final(regions).slots[k]]
            #![trigger final(regions).slot_owners[k]]
            k != old(frame_own).slot_index && (old(owner).list.len() > 0 ==> k != old(
                owner,
            ).slot_index_at(0)) ==> final(regions).slots[k] == old(regions).slots[k]
                && final(regions).slot_owners[k] == old(regions).slot_owners[k],
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && l.list_id != final(owner).list_id
                ==> l.relate_region(*final(regions)),
        // Membership registry for the operated list: forward stamp of
        // the (minted or preserved) id + reverse global uniqueness (see
        // [`list_registry_ok`]).
        list_registry_ok(*final(regions), *final(owner)),
        // Every other list/cursor list keeps its registry: the only slot
        // the surgery retags now carries `final(owner).list_id` (or 0),
        // never another list's id — so no foreign list gains or loses a
        // tagged slot.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && list_registry_ok(*old(regions), l)
                && l.list_id != final(owner).list_id ==> list_registry_ok(*final(regions), l),
        // **other loose handles preserved**: a loose frame `fo` sitting
        // at a different `in_list == 0` slot is untouched. Sound by the
        // same disjointness — a list slot carries `in_list == list_id
        // != 0`, so `fo`'s slot is neither the pushed frame's nor the
        // old front's.
        forall|fo: UniqueFrameOwner<Link<M>>|
            #![trigger fo.global_inv(*old(regions))]
            fo.global_inv(*old(regions)) && fo.frame_link_inv(*old(regions)) && old(
                regions,
            ).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0 && fo.slot_index != old(
                frame_own,
            ).slot_index ==> fo.global_inv(*final(regions)) && fo.frame_link_inv(*final(regions))
                && final(regions).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0,
;

/// Fresh-id helper for the loose-frame id space.
pub open spec fn fresh_loose_id<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    m: Map<LooseId, UniqueFrameOwner<Link<M>>>,
) -> LooseId {
    choose|id: LooseId| !m.dom().contains(id)
}

pub axiom fn axiom_fresh_loose_id_not_in_dom<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    m: Map<LooseId, UniqueFrameOwner<Link<M>>>,
)
    ensures
        !m.dom().contains(fresh_loose_id(m)),
;

/// Trusted reflection of the (now properly `&mut owner`-threaded and
/// fully verified) [`crate::mm::frame::LinkedList::pop_front`]. Pops the
/// front link off `owner`, restoring it to a loose
/// `UniqueFrame<Link<M>>` (its drop-obligation re-minted by `from_raw`,
/// `in_list` reset to 0, `prev`/`next` cleared). The list shrinks by one
/// from the front with `list_id` preserved.
///
/// The first block of `ensures` mirrors the verified exec `pop_front`
/// verbatim. The last two are the sound companion facts (cf.
/// [`push_front_embedded`]): other lists and other loose frames are
/// untouched, and — additionally — the popped slot is *distinct* from
/// every loose slot (it was a list link, `in_list == list_id != 0`),
/// which keeps loose-slot disjointness when the popped frame joins
/// `loose`.
pub axiom fn pop_front_embedded<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    tracked regions: &mut MetaRegionOwners,
    tracked owner: &mut LinkedListOwner<M>,
) -> (tracked frame_own: UniqueFrameOwner<Link<M>>)
    requires
        old(regions).inv(),
        old(owner).inv(),
        old(owner).relate_region(*old(regions)),
        old(owner).list.len() > 0,
    ensures
        final(regions).inv(),
        final(owner).inv(),
        final(owner).relate_region(*final(regions)),
        final(owner).list == old(owner).list.remove(0),
        final(owner).list_id == old(owner).list_id,
        // The popped frame is a valid loose handle at the old front slot.
        frame_own.inv(),
        frame_own.global_inv(*final(regions)),
        frame_own.frame_link_inv(*final(regions)),
        frame_own.slot_index == old(owner).slot_index_at(0),
        final(regions).slot_owners[frame_own.slot_index].inner_perms.in_list.value() == 0,
        // `from_raw` re-mints the drop-obligation.
        final(regions).frame_obligations =~= old(regions).frame_obligations.insert(
            old(owner).slot_index_at(0),
        ),
        // Outside-the-list slot preservation (front specialisation:
        // popped slot + the new front at `slot_index_at(1)`).
        forall|j: usize|
            #![trigger final(regions).slots[j]]
            #![trigger final(regions).slot_owners[j]]
            j != old(owner).slot_index_at(0) && (old(owner).list.len() > 1 ==> j != old(
                owner,
            ).slot_index_at(1)) ==> final(regions).slots[j] == old(regions).slots[j]
                && final(regions).slot_owners[j] == old(regions).slot_owners[j],
        // Other lists preserved.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && l.list_id != final(owner).list_id
                ==> l.relate_region(*final(regions)),
        // Membership registry for the operated list: forward stamp of
        // the (minted or preserved) id + reverse global uniqueness (see
        // [`list_registry_ok`]).
        list_registry_ok(*final(regions), *final(owner)),
        // Every other list/cursor list keeps its registry: the only slot
        // the surgery retags now carries `final(owner).list_id` (or 0),
        // never another list's id — so no foreign list gains or loses a
        // tagged slot.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && list_registry_ok(*old(regions), l)
                && l.list_id != final(owner).list_id ==> list_registry_ok(*final(regions), l),
        // Other loose frames preserved, and the popped slot is disjoint
        // from every loose slot.
        forall|fo: UniqueFrameOwner<Link<M>>|
            #![trigger fo.global_inv(*old(regions))]
            fo.global_inv(*old(regions)) && fo.frame_link_inv(*old(regions)) && old(
                regions,
            ).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0 ==> fo.global_inv(
                *final(regions),
            ) && fo.frame_link_inv(*final(regions))
                && final(regions).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0
                && fo.slot_index != old(owner).slot_index_at(0),
;

/// Trusted reflection of the (verified) [`crate::mm::frame::LinkedList::push_back`].
/// Identical to [`push_front_embedded`] except the frame is spliced in
/// at the *tail* (touching the back neighbours instead of the front).
pub axiom fn push_back_embedded<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    tracked regions: &mut MetaRegionOwners,
    tracked owner: &mut LinkedListOwner<M>,
    tracked frame_own: &mut UniqueFrameOwner<Link<M>>,
    used_ids: Set<u64>,
)
    requires
        old(regions).inv(),
        old(owner).inv(),
        old(owner).relate_region(*old(regions)),
        old(frame_own).inv(),
        old(frame_own).global_inv(*old(regions)),
        old(frame_own).frame_link_inv(*old(regions)),
        old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.value() == 0,
    ensures
        final(regions).inv(),
        final(owner).inv(),
        final(owner).relate_region(*final(regions)),
        old(owner).list.len() > 0 ==> final(owner).list == old(owner).list.insert(
            old(owner).list.len() as int - 1,
            final(frame_own).meta_own,
        ),
        old(owner).list.len() == 0 ==> final(owner).list == old(owner).list.insert(
            0,
            final(frame_own).meta_own,
        ),
        old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
        final(owner).list_id != 0,
        old(owner).list_id == 0 ==> !used_ids.contains(final(owner).list_id),
        final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
        final(frame_own).meta_own.in_list == final(owner).list_id,
        final(regions).frame_obligations =~= old(regions).frame_obligations.remove(
            old(frame_own).slot_index,
        ),
        forall|k: usize|
            #![trigger final(regions).slots[k]]
            #![trigger final(regions).slot_owners[k]]
            k != old(frame_own).slot_index && (old(owner).list.len() > 1 ==> k != old(
                owner,
            ).slot_index_at(old(owner).list.len() - 2)) && (old(owner).list.len() > 0 ==> k != old(
                owner,
            ).slot_index_at(old(owner).list.len() - 1)) ==> final(regions).slots[k] == old(
                regions,
            ).slots[k] && final(regions).slot_owners[k] == old(regions).slot_owners[k],
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && l.list_id != final(owner).list_id
                ==> l.relate_region(*final(regions)),
        // Membership registry for the operated list: forward stamp of
        // the (minted or preserved) id + reverse global uniqueness (see
        // [`list_registry_ok`]).
        list_registry_ok(*final(regions), *final(owner)),
        // Every other list/cursor list keeps its registry: the only slot
        // the surgery retags now carries `final(owner).list_id` (or 0),
        // never another list's id — so no foreign list gains or loses a
        // tagged slot.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && list_registry_ok(*old(regions), l)
                && l.list_id != final(owner).list_id ==> list_registry_ok(*final(regions), l),
        forall|fo: UniqueFrameOwner<Link<M>>|
            #![trigger fo.global_inv(*old(regions))]
            fo.global_inv(*old(regions)) && fo.frame_link_inv(*old(regions)) && old(
                regions,
            ).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0 && fo.slot_index != old(
                frame_own,
            ).slot_index ==> fo.global_inv(*final(regions)) && fo.frame_link_inv(*final(regions))
                && final(regions).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0,
;

/// Trusted reflection of the (verified) [`crate::mm::frame::LinkedList::pop_back`].
/// Identical to [`pop_front_embedded`] except the *last* link is popped
/// (touching the back neighbour at `slot_index_at(len - 2)`).
pub axiom fn pop_back_embedded<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    tracked regions: &mut MetaRegionOwners,
    tracked owner: &mut LinkedListOwner<M>,
) -> (tracked frame_own: UniqueFrameOwner<Link<M>>)
    requires
        old(regions).inv(),
        old(owner).inv(),
        old(owner).relate_region(*old(regions)),
        old(owner).list.len() > 0,
    ensures
        final(regions).inv(),
        final(owner).inv(),
        final(owner).relate_region(*final(regions)),
        final(owner).list == old(owner).list.remove(old(owner).list.len() - 1),
        final(owner).list_id == old(owner).list_id,
        frame_own.inv(),
        frame_own.global_inv(*final(regions)),
        frame_own.frame_link_inv(*final(regions)),
        frame_own.slot_index == old(owner).slot_index_at(old(owner).list.len() - 1),
        final(regions).slot_owners[frame_own.slot_index].inner_perms.in_list.value() == 0,
        final(regions).frame_obligations =~= old(regions).frame_obligations.insert(
            old(owner).slot_index_at(old(owner).list.len() - 1),
        ),
        forall|j: usize|
            #![trigger final(regions).slots[j]]
            #![trigger final(regions).slot_owners[j]]
            j != old(owner).slot_index_at(old(owner).list.len() - 1) && (old(owner).list.len() > 1
                ==> j != old(owner).slot_index_at(old(owner).list.len() - 2))
                ==> final(regions).slots[j] == old(regions).slots[j]
                && final(regions).slot_owners[j] == old(regions).slot_owners[j],
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && l.list_id != final(owner).list_id
                ==> l.relate_region(*final(regions)),
        // Membership registry for the operated list: forward stamp of
        // the (minted or preserved) id + reverse global uniqueness (see
        // [`list_registry_ok`]).
        list_registry_ok(*final(regions), *final(owner)),
        // Every other list/cursor list keeps its registry: the only slot
        // the surgery retags now carries `final(owner).list_id` (or 0),
        // never another list's id — so no foreign list gains or loses a
        // tagged slot.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && list_registry_ok(*old(regions), l)
                && l.list_id != final(owner).list_id ==> list_registry_ok(*final(regions), l),
        forall|fo: UniqueFrameOwner<Link<M>>|
            #![trigger fo.global_inv(*old(regions))]
            fo.global_inv(*old(regions)) && fo.frame_link_inv(*old(regions)) && old(
                regions,
            ).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0 ==> fo.global_inv(
                *final(regions),
            ) && fo.frame_link_inv(*final(regions))
                && final(regions).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0
                && fo.slot_index != old(owner).slot_index_at(old(owner).list.len() - 1),
;

/// Trusted reflection of [`crate::mm::frame::CursorMut::insert_before`]
/// applied to a cursor at an arbitrary index `n` over `owner`. The
/// general form of [`push_front_embedded`] (`n == 0`) /
/// [`push_back_embedded`]: splices the loose frame in at position `n`
/// (`0 <= n <= len`), touching `n`'s ≤2 link neighbours.
pub axiom fn insert_before_at_embedded<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    tracked regions: &mut MetaRegionOwners,
    tracked owner: &mut LinkedListOwner<M>,
    tracked frame_own: &mut UniqueFrameOwner<Link<M>>,
    n: int,
    used_ids: Set<u64>,
)
    requires
        old(regions).inv(),
        old(owner).inv(),
        old(owner).relate_region(*old(regions)),
        old(frame_own).inv(),
        old(frame_own).global_inv(*old(regions)),
        old(frame_own).frame_link_inv(*old(regions)),
        old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.value() == 0,
        0 <= n <= old(owner).list.len(),
    ensures
        final(regions).inv(),
        final(owner).inv(),
        final(owner).relate_region(*final(regions)),
        final(owner).list == old(owner).list.insert(n, final(frame_own).meta_own),
        old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
        final(owner).list_id != 0,
        old(owner).list_id == 0 ==> !used_ids.contains(final(owner).list_id),
        final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
        final(frame_own).meta_own.in_list == final(owner).list_id,
        final(regions).frame_obligations =~= old(regions).frame_obligations.remove(
            old(frame_own).slot_index,
        ),
        forall|k: usize|
            #![trigger final(regions).slots[k]]
            #![trigger final(regions).slot_owners[k]]
            k != old(frame_own).slot_index && (n > 0 ==> k != old(owner).slot_index_at(n - 1)) && (n
                < old(owner).list.len() ==> k != old(owner).slot_index_at(n))
                ==> final(regions).slots[k] == old(regions).slots[k]
                && final(regions).slot_owners[k] == old(regions).slot_owners[k],
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && l.list_id != final(owner).list_id
                ==> l.relate_region(*final(regions)),
        // Membership registry for the operated list: forward stamp of
        // the (minted or preserved) id + reverse global uniqueness (see
        // [`list_registry_ok`]).
        list_registry_ok(*final(regions), *final(owner)),
        // Every other list/cursor list keeps its registry: the only slot
        // the surgery retags now carries `final(owner).list_id` (or 0),
        // never another list's id — so no foreign list gains or loses a
        // tagged slot.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && list_registry_ok(*old(regions), l)
                && l.list_id != final(owner).list_id ==> list_registry_ok(*final(regions), l),
        forall|fo: UniqueFrameOwner<Link<M>>|
            #![trigger fo.global_inv(*old(regions))]
            fo.global_inv(*old(regions)) && fo.frame_link_inv(*old(regions)) && old(
                regions,
            ).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0 && fo.slot_index != old(
                frame_own,
            ).slot_index ==> fo.global_inv(*final(regions)) && fo.frame_link_inv(*final(regions))
                && final(regions).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0,
;

/// Trusted reflection of [`crate::mm::frame::CursorMut::take_current`]
/// at an arbitrary index `n` over `owner`. The general form of
/// [`pop_front_embedded`] (`n == 0`) / [`pop_back_embedded`]: removes
/// the link at position `n` (`0 <= n < len`) back into a loose handle,
/// touching `n`'s ≤2 bridged neighbours.
pub axiom fn take_at_embedded<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    tracked regions: &mut MetaRegionOwners,
    tracked owner: &mut LinkedListOwner<M>,
    n: int,
) -> (tracked frame_own: UniqueFrameOwner<Link<M>>)
    requires
        old(regions).inv(),
        old(owner).inv(),
        old(owner).relate_region(*old(regions)),
        0 <= n < old(owner).list.len(),
    ensures
        final(regions).inv(),
        final(owner).inv(),
        final(owner).relate_region(*final(regions)),
        final(owner).list == old(owner).list.remove(n),
        final(owner).list_id == old(owner).list_id,
        frame_own.inv(),
        frame_own.global_inv(*final(regions)),
        frame_own.frame_link_inv(*final(regions)),
        frame_own.slot_index == old(owner).slot_index_at(n),
        final(regions).slot_owners[frame_own.slot_index].inner_perms.in_list.value() == 0,
        final(regions).frame_obligations =~= old(regions).frame_obligations.insert(
            old(owner).slot_index_at(n),
        ),
        forall|j: usize|
            #![trigger final(regions).slots[j]]
            #![trigger final(regions).slot_owners[j]]
            j != old(owner).slot_index_at(n) && (n > 0 ==> j != old(owner).slot_index_at(n - 1))
                && (n < old(owner).list.len() - 1 ==> j != old(owner).slot_index_at(n + 1))
                ==> final(regions).slots[j] == old(regions).slots[j]
                && final(regions).slot_owners[j] == old(regions).slot_owners[j],
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && l.list_id != final(owner).list_id
                ==> l.relate_region(*final(regions)),
        // Membership registry for the operated list: forward stamp of
        // the (minted or preserved) id + reverse global uniqueness (see
        // [`list_registry_ok`]).
        list_registry_ok(*final(regions), *final(owner)),
        // Every other list/cursor list keeps its registry: the only slot
        // the surgery retags now carries `final(owner).list_id` (or 0),
        // never another list's id — so no foreign list gains or loses a
        // tagged slot.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && list_registry_ok(*old(regions), l)
                && l.list_id != final(owner).list_id ==> list_registry_ok(*final(regions), l),
        forall|fo: UniqueFrameOwner<Link<M>>|
            #![trigger fo.global_inv(*old(regions))]
            fo.global_inv(*old(regions)) && fo.frame_link_inv(*old(regions)) && old(
                regions,
            ).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0 ==> fo.global_inv(
                *final(regions),
            ) && fo.frame_link_inv(*final(regions))
                && final(regions).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0
                && fo.slot_index != old(owner).slot_index_at(n),
;

/// Trusted reflection of the (now-strengthened, verified) whole-list
/// teardown [`crate::mm::frame::LinkedList`]'s `Drop`/`TrackDrop`. The
/// destructor pops every link via `take_current` and `UniqueFrame::drop`s
/// the recovered frame, so each former link's slot is **freed** —
/// `rc → REF_COUNT_UNUSED`, `in_list → 0` — not orphaned. `owner` is
/// consumed (emptied). The per-link `frame_obligations.count == 0`
/// precondition mirrors the exec `drop_requires` (a listed frame was
/// forgotten via `into_raw`); `ListStore` doesn't track that accounting
/// fact, so it is surfaced here for an accounting-aware caller to supply.
///
/// `ensures` mirror the verified `drop_ensures` (freed slots + full
/// preservation of every out-of-list slot, `slots.dom()`, `inv()`) plus
/// the sound companion frames (cf. the push/pop axioms): other lists /
/// cursors keep `relate_region` + [`list_registry_ok`], other loose
/// frames are untouched, and — when the list was empty — the region is
/// unchanged outright.
pub axiom fn list_drop_embedded<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    tracked regions: &mut MetaRegionOwners,
    tracked owner: LinkedListOwner<M>,
)
    requires
        old(regions).inv(),
        owner.inv(),
        owner.relate_region(*old(regions)),
        forall|i: int|
            #![trigger owner.slot_index_at(i)]
            0 <= i < owner.list.len() ==> old(regions).frame_obligations.count(
                owner.slot_index_at(i),
            ) == 0,
        // Mirrors the exec `TrackDrop for LinkedList::drop_requires`
        // conjunct (`linked_list.rs`): each link's slot has no live PTE
        // mapping. The destructor `UniqueFrame::drop`s each link to
        // `REF_COUNT_UNUSED`, which is only valid for an unmapped frame
        // (a mapping is itself a reference). Discharged in `step_list_drop`
        // from `MetaSlotOwner::inv`'s UNIQUE branch (a UNIQUE slot — which
        // every link is, via `relate_region`) has empty `paths_in_pt`).
        forall|i: int|
            #![trigger owner.slot_index_at(i)]
            0 <= i < owner.list.len() ==> old(regions).slot_owners[owner.slot_index_at(
                i,
            )].paths_in_pt.is_empty(),
    ensures
        final(regions).inv(),
        final(regions).slots.dom() =~= old(regions).slots.dom(),
        // An empty list frees nothing — the region is untouched.
        owner.list.len() == 0 ==> *final(regions) == *old(regions),
        // Each former link is freed: its slot is UNUSED with `in_list` 0.
        forall|i: int|
            #![trigger owner.slot_index_at(i)]
            0 <= i < owner.list.len() ==> {
                let idx = owner.slot_index_at(i);
                &&& final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                &&& final(regions).slot_owners[idx].inner_perms.in_list.value() == 0
            },
        // Every slot outside the dropped list is fully preserved.
        forall|idx: usize|
            #![trigger final(regions).slot_owners[idx]]
            (forall|i: int| 0 <= i < owner.list.len() ==> idx != owner.slot_index_at(i))
                ==> final(regions).slot_owners[idx] == old(regions).slot_owners[idx]
                && final(regions).slots[idx] == old(regions).slots[idx]
                && final(regions).frame_obligations.count(idx) == old(
                regions,
            ).frame_obligations.count(idx),
        // Other lists / cursors keep their `relate_region` and registry.
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && l.list_id != owner.list_id
                ==> l.relate_region(*final(regions)),
        forall|l: LinkedListOwner<M>|
            #![trigger l.relate_region(*old(regions))]
            l.inv() && l.relate_region(*old(regions)) && list_registry_ok(*old(regions), l)
                && l.list_id != owner.list_id ==> list_registry_ok(*final(regions), l),
        // Other loose frames (at `in_list == 0` slots disjoint from the
        // dropped list's) are untouched.
        forall|fo: UniqueFrameOwner<Link<M>>|
            #![trigger fo.global_inv(*old(regions))]
            fo.global_inv(*old(regions)) && fo.frame_link_inv(*old(regions)) && old(
                regions,
            ).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0 ==> fo.global_inv(
                *final(regions),
            ) && fo.frame_link_inv(*final(regions))
                && final(regions).slot_owners[fo.slot_index].inner_perms.in_list.value() == 0,
;

// =============================================================================
// Operations
// =============================================================================
impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> ListStore<M> {
    /// `LinkedList::size`: the number of links in list `id`. A read-only
    /// query — the store is unchanged.
    pub proof fn step_size(tracked &self, id: ListId) -> (res: nat)
        requires
            self.inv(),
            self.lists.dom().contains(id),
        ensures
            res == self.lists[id].list.len(),
    {
        self.lists[id].list.len()
    }

    /// `LinkedList::is_empty`: whether list `id` has no links. Read-only.
    pub proof fn step_is_empty(tracked &self, id: ListId) -> (res: bool)
        requires
            self.inv(),
            self.lists.dom().contains(id),
        ensures
            res <==> self.lists[id].list.len() == 0,
    {
        self.lists[id].list.len() == 0
    }

    /// `LinkedList::contains`: whether `frame` is a link of list `id`. A
    /// read-only query mirroring exec `contains(frame) -> bool`. `res`
    /// holds iff `frame` is a safe managed slot AND one of the list's
    /// links: for a real (non-zero) id the membership registry
    /// ([`list_registry_ok`], an `inv` clause) makes the
    /// `in_list[frame] == list_id` comparison an exact membership test;
    /// an empty/never-pushed list (`list_id == 0`, hence empty) or a
    /// `frame` that is not a safe slot (which exec's `get_slot` rejects)
    /// contains nothing.
    pub proof fn step_contains(tracked &self, id: ListId, frame: Paddr) -> (res: bool)
        requires
            self.inv(),
            self.lists.dom().contains(id),
        ensures
            res <==> (has_safe_slot(frame) && exists|i: int|
                0 <= i < self.lists[id].list.len() && self.lists[id].slot_index_at(i)
                    == frame_to_index(frame)),
    {
        let idx = frame_to_index(frame);
        if has_safe_slot(frame) {
            // A safe slot is a managed region key.
            self.regions.inv_implies_correct_addr(frame);
            assert(self.regions.slot_owners.contains_key(idx));
            if self.lists[id].list_id != 0 {
                // The registry for list `id` (forward + reverse) from `inv`.
                assert(list_registry_ok(self.regions, self.lists[id]));
                let res = self.regions.slot_owners[idx].inner_perms.in_list.value()
                    == self.lists[id].list_id;
                if res {
                    // reverse: a slot tagged with the id is one of the links.
                    assert(exists|i: int|
                        0 <= i < self.lists[id].list.len() && self.lists[id].slot_index_at(i)
                            == idx);
                } else {
                    // forward: every link's slot is tagged, so an untagged
                    // slot is no link.
                    assert forall|i: int|
                        0 <= i < self.lists[id].list.len() implies self.lists[id].slot_index_at(i)
                        != idx by {
                        assert(self.regions.slot_owners[self.lists[id].slot_index_at(
                            i,
                        )].inner_perms.in_list.value() == self.lists[id].list_id);
                    };
                }
                res
            } else {
                // `list_id == 0` ⟹ the list is empty (`LinkedListOwner::inv`:
                // `len > 0 ==> list_id != 0`), so it has no links.
                assert(self.lists[id].inv());
                assert(self.lists[id].list.len() == 0);
                false
            }
        } else {
            // `!has_safe_slot(frame)`: exec `get_slot` rejects it, so the
            // guarded membership is vacuously false.
            false
        }
    }

    /// `LinkedList::new`: register a fresh *empty* list. No region
    /// change; the new list is empty with `list_id == 0` (minted on
    /// first push). Returns the fresh list id.
    pub proof fn step_list_new(tracked &mut self) -> (res: ListId)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).regions == old(self).regions,
            final(self).loose == old(self).loose,
            !old(self).lists.dom().contains(res),
            final(self).lists == old(self).lists.insert(res, final(self).lists[res]),
            final(self).lists[res].list.len() == 0,
    {
        let ghost old_self = *self;
        let ghost id = fresh_list_id(self.lists, self.cursors);
        axiom_fresh_list_id_not_in_dom(self.lists, self.cursors);
        let tracked empty = axiom_empty_list_owner::<M>();
        self.lists.tracked_insert(id, empty);
        assert(self.lists[id].list.len() == 0);
        // The new list is empty: `inv()` (`len > 0 ==> ...` vacuous,
        // per-link forall vacuous) and `relate_region` (both foralls
        // vacuous over an empty `list`) hold. Every other list / loose
        // entry is unchanged, and `regions` is untouched.
        assert(self.lists[id].inv());
        assert(self.lists[id].relate_region(self.regions));
        // Cursors untouched; `id` is fresh w.r.t. `cursors` (so
        // disjointness holds), and the new list's `list_id == 0` makes
        // the cross list/cursor id clause vacuous for it.
        assert(self.cursors == old_self.cursors);
        assert(self.lists.dom().disjoint(self.cursors.dom()));
        assert(self.lists[id].list_id == 0);
        id
    }

    /// Drop of `LinkedList` `id`: tear the whole list down, *freeing*
    /// every link's frame (slot → UNUSED, `in_list` → 0) and removing the
    /// list from the store. Faithful to the verified destructor (each
    /// link is popped and `UniqueFrame::drop`ped — no orphaning).
    ///
    /// The per-link `frame_obligations.count == 0` precondition mirrors
    /// the exec `drop_requires` (listed frames are forgotten); the
    /// accounting-free `ListStore` cannot itself supply it, so it is left
    /// to the caller. The freed frames leave the store entirely (they
    /// return to the allocator's UNUSED pool, tracked by nobody here).
    pub proof fn step_list_drop(tracked &mut self, id: ListId)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
            forall|i: int|
                0 <= i < old(self).lists[id].list.len() ==> old(
                    self,
                ).regions.frame_obligations.count(old(self).lists[id].slot_index_at(i)) == 0,
        ensures
            final(self).inv(),
            !final(self).lists.dom().contains(id),
            final(self).loose == old(self).loose,
            final(self).cursors == old(self).cursors,
    {
        let ghost old_self = *self;
        let ghost old_regions = self.regions;
        let ghost dropped_id = self.lists[id].list_id;
        let ghost is_empty = self.lists[id].list.len() == 0;
        assert(self.lists[id].inv());
        assert(self.lists[id].relate_region(self.regions));

        // Discharge the axiom's unmapped-link precondition: every link's
        // slot is a non-MMIO UNIQUE frame (via `relate_region_at`:
        // `ref_count == REF_COUNT_UNIQUE` + `usage == Frame`), and
        // `regions.inv()`'s UNIQUE branch (`usage != MMIO ==> empty`) then
        // gives it an empty `paths_in_pt`.
        assert forall|i: int|
            #![trigger self.lists[id].slot_index_at(i)]
            0 <= i
                < self.lists[id].list.len() implies self.regions.slot_owners[self.lists[id].slot_index_at(
        i)].paths_in_pt.is_empty() by {
            let idx = self.lists[id].slot_index_at(i);
            // Instantiate `relate_region`'s per-link forall (trigger
            // `self.list[i]`) to get `relate_region_at(regions, i)`.
            let _ = self.lists[id].list[i];
            self.lists[id].relate_region_at_facts(self.regions, i);
            assert(self.regions.slot_owners.contains_key(idx));
            assert(self.regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNIQUE);
            assert(self.regions.slot_owners[idx].usage == PageUsage::Frame);
            assert(self.regions.slot_owners[idx].inv());
        };

        let tracked owner = self.lists.tracked_remove(id);
        list_drop_embedded(&mut self.regions, owner);
        assert(self.lists =~= old_self.lists.remove(id));
        if is_empty {
            assert(self.regions == old_regions);
        }
        // A non-empty dropped list has a real (non-zero) id, so every
        // other list/cursor is separated from it by the id uniqueness;
        // an empty drop left `regions` untouched outright.

        if !is_empty {
            assert(dropped_id != 0);
        }
        // --- per-list: remaining lists preserved ---

        assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
            &&& self.lists[i].inv()
            &&& self.lists[i].relate_region(self.regions)
        } by {
            assert(i != id);
            assert(old_self.lists.dom().contains(i));
            assert(old_self.lists[i] == self.lists[i]);
            assert(old_self.lists[i].relate_region(old_regions));
            if !is_empty {
                assert(self.lists[i].list_id != dropped_id);
            }
        };

        // --- per-loose preserved ---
        assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
            &&& self.loose[lid2].inv()
            &&& self.loose[lid2].global_inv(self.regions)
            &&& self.loose[lid2].frame_link_inv(self.regions)
            &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(old_self.loose.dom().contains(lid2));
            assert(old_self.loose[lid2].global_inv(old_regions));
            assert(old_self.loose[lid2].frame_link_inv(old_regions));
            assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0);
        };

        // --- per-cursor preserved (cursor lists are "other lists") ---
        assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
            &&& self.cursors[cid].list_own.inv()
            &&& self.cursors[cid].inv_region(self.regions)
        } by {
            assert(old_self.cursors.dom().contains(cid));
            assert(old_self.cursors[cid].list_own.inv());
            assert(old_self.cursors[cid].inv_region(old_regions));
            assert(self.cursors[cid].list_own.relate_region(old_regions));
            if !is_empty {
                assert(self.cursors[cid].list_own.list_id != dropped_id);
            }
        };

        // --- lists×lists uniqueness (subset of old) ---
        assert forall|i1: ListId, i2: ListId|
            self.lists.dom().contains(i1) && self.lists.dom().contains(i2) && self.lists[i1].list_id
                == self.lists[i2].list_id && self.lists[i1].list_id != 0 implies i1 == i2 by {
            assert(old_self.lists.dom().contains(i1));
            assert(old_self.lists.dom().contains(i2));
        };

        // --- loose-internal disjointness (loose unchanged) ---
        assert forall|l1: LooseId, l2: LooseId|
            self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
            assert(old_self.loose.dom().contains(l1));
            assert(old_self.loose.dom().contains(l2));
        };

        // --- disjointness + cross/cursor uniqueness (lists lost `id`) ---
        assert(self.lists.dom().disjoint(self.cursors.dom()));
        assert forall|id2: ListId, cid: CursorId|
            self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                && self.lists[id2].list_id != 0 implies false by {
            assert(old_self.lists.dom().contains(id2));
            assert(old_self.cursors.dom().contains(cid));
        };
        assert forall|cid1: CursorId, cid2: CursorId|
            self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            assert(old_self.cursors.dom().contains(cid1));
            assert(old_self.cursors.dom().contains(cid2));
        };

        // --- membership registry (remaining lists & cursors) ---
        assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies list_registry_ok(
            self.regions,
            self.lists[i],
        ) by {
            assert(old_self.lists.dom().contains(i));
            assert(old_self.lists[i] == self.lists[i]);
            assert(old_self.lists[i].relate_region(old_regions));
            if !is_empty {
                assert(self.lists[i].list_id != dropped_id);
            }
        };
        assert forall|cid: CursorId| #[trigger]
            self.cursors.dom().contains(cid) implies list_registry_ok(
            self.regions,
            self.cursors[cid].list_own,
        ) by {
            assert(old_self.cursors.dom().contains(cid));
            assert(old_self.cursors[cid].list_own.relate_region(old_regions));
            if !is_empty {
                assert(self.cursors[cid].list_own.list_id != dropped_id);
            }
        };
    }

    /// `LinkedList::push_front`: move the loose handle `lid` to the front
    /// of list `id`. The frame is forgotten into the list (its
    /// drop-obligation consumed); the `loose` entry is removed.
    pub proof fn step_push_front(tracked &mut self, id: ListId, lid: LooseId)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
            old(self).loose.dom().contains(lid),
        ensures
            final(self).inv(),
    {
        let ghost old_self = *self;
        let ghost old_regions = self.regions;
        let ghost fidx = self.loose[lid].slot_index;
        // The other lists' ids — the lazily-minted id must avoid these.
        let ghost used = Set::new_assuming_finite(
            |x: u64|
                (exists|i: ListId| #[trigger]
                    old_self.lists.dom().contains(i) && i != id && old_self.lists[i].list_id == x)
                    || (exists|cid: CursorId| #[trigger]
                    old_self.cursors.dom().contains(cid) && old_self.cursors[cid].list_own.list_id
                        == x),
        );
        // Push preconditions, sourced from `inv`.
        assert(self.lists[id].inv());
        assert(self.lists[id].relate_region(self.regions));
        assert(self.loose[lid].inv());
        assert(self.loose[lid].global_inv(self.regions));
        assert(self.loose[lid].frame_link_inv(self.regions));
        assert(self.regions.slot_owners[fidx].inner_perms.in_list.value() == 0);

        let tracked mut owner = self.lists.tracked_remove(id);
        let tracked mut frame_own = self.loose.tracked_remove(lid);
        push_front_embedded(&mut self.regions, &mut owner, &mut frame_own, used);
        self.lists.tracked_insert(id, owner);
        assert(self.loose =~= old_self.loose.remove(lid));
        assert(self.lists =~= old_self.lists.remove(id).insert(id, owner));
        let ghost new_id = self.lists[id].list_id;

        // Other lists with a nonzero id keep it distinct from `new_id`:
        // the pushed list either kept its (uniquely-minted) id or minted
        // one outside `used` (which holds every other list's id).
        assert forall|i: ListId|
            self.lists.dom().contains(i) && i != id && self.lists[i].list_id
                != 0 implies self.lists[i].list_id != new_id by {
            assert(old_self.lists.dom().contains(i));
            assert(old_self.lists[i] == self.lists[i]);
            if old_self.lists[id].list_id != 0 {
                // `new_id == old id`; old nonzero-id uniqueness separates `i`.
                assert(new_id == old_self.lists[id].list_id);
            } else {
                assert(used.contains(self.lists[i].list_id));
            }
        };

        // --- per-list: inv + relate_region ---
        assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
            &&& self.lists[i].inv()
            &&& self.lists[i].relate_region(self.regions)
        } by {
            if i != id {
                assert(old_self.lists.dom().contains(i));
                assert(old_self.lists[i] == self.lists[i]);
                assert(old_self.lists[i].inv());
                assert(old_self.lists[i].relate_region(old_regions));
                if self.lists[i].list.len() > 0 {
                    assert(self.lists[i].list_id != new_id);
                }
            }
        };

        // --- per-loose: a different loose frame is at a `!= fidx` slot,
        // so the axiom's other-loose clause carries it. ---
        assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
            &&& self.loose[lid2].inv()
            &&& self.loose[lid2].global_inv(self.regions)
            &&& self.loose[lid2].frame_link_inv(self.regions)
            &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(lid2 != lid);
            assert(old_self.loose.dom().contains(lid2));
            assert(old_self.loose[lid2] == self.loose[lid2]);
            assert(old_self.loose[lid2].global_inv(old_regions));
            assert(old_self.loose[lid2].frame_link_inv(old_regions));
            assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0);
            assert(self.loose[lid2].slot_index != fidx);
        };

        // --- list_id uniqueness (non-empty lists) ---
        assert forall|i1: ListId, i2: ListId|
            self.lists.dom().contains(i1) && self.lists.dom().contains(i2)
                && self.lists[i1].list.len() > 0 && self.lists[i2].list.len() > 0
                && self.lists[i1].list_id == self.lists[i2].list_id implies i1 == i2 by {
            if i1 != id && i2 != id {
                assert(old_self.lists[i1] == self.lists[i1]);
                assert(old_self.lists[i2] == self.lists[i2]);
            } else if i1 == id && i2 != id {
                assert(self.lists[i2].list_id != new_id);
            } else if i2 == id && i1 != id {
                assert(self.lists[i1].list_id != new_id);
            }
        };

        // --- loose-internal slot disjointness (subset of old) ---
        assert forall|l1: LooseId, l2: LooseId|
            self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
            assert(old_self.loose.dom().contains(l1));
            assert(old_self.loose.dom().contains(l2));
        };

        // --- cursors: checked-out lists are untouched ---
        // `cursors` is not read or written by a list op, and every
        // cursor's list carries an id distinct from the just-minted
        // `new_id` (other cursors' ids are in `used`, or — when the id
        // was preserved — separated by the old list/cursor uniqueness),
        // so the axiom's other-lists frame preserves each cursor's
        // `relate_region`. Index bounds are unchanged.
        assert(self.cursors == old_self.cursors);
        assert(self.lists.dom() =~= old_self.lists.dom());
        assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
            &&& self.cursors[cid].list_own.inv()
            &&& self.cursors[cid].inv_region(self.regions)
        } by {
            assert(old_self.cursors.dom().contains(cid));
            assert(old_self.cursors[cid].list_own.inv());
            assert(old_self.cursors[cid].inv_region(old_regions));
            assert(self.cursors[cid].list_own.relate_region(old_regions));
            if old_self.lists[id].list_id != 0 {
                assert(new_id == old_self.lists[id].list_id);
            } else {
                assert(used.contains(self.cursors[cid].list_own.list_id));
            }
            assert(self.cursors[cid].list_own.list_id != new_id);
            assert(self.cursors[cid].list_own.relate_region(self.regions));
        };
        assert forall|id2: ListId, cid: CursorId|
            self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                && self.lists[id2].list_id != 0 implies false by {
            assert(old_self.cursors.dom().contains(cid));
            if id2 == id {
                assert(self.lists[id].list_id == new_id);
                if old_self.lists[id].list_id != 0 {
                    assert(new_id == old_self.lists[id].list_id);
                } else {
                    assert(used.contains(self.cursors[cid].list_own.list_id));
                }
            } else {
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2] == self.lists[id2]);
            }
        };
        assert forall|cid1: CursorId, cid2: CursorId|
            self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            assert(old_self.cursors.dom().contains(cid1));
            assert(old_self.cursors.dom().contains(cid2));
        };
    }

    /// `LinkedList::pop_front`: pop the front link of list `id` back into
    /// the loose pool as a fresh `UniqueFrame<Link<M>>`. Requires the
    /// list be non-empty. Returns the fresh loose id.
    pub proof fn step_pop_front(tracked &mut self, id: ListId) -> (res: Option<LooseId>)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
        ensures
            final(self).inv(),
            old(self).lists[id].list.len() == 0 ==> res is None && *final(self) == *old(self),
            old(self).lists[id].list.len() > 0 ==> res is Some,
    {
        if self.lists[id].list.len() == 0 {
            // Exec `LinkedList::pop_front` returns `None` on an empty
            // list; the store is unchanged.
            Option::None
        } else {
            let ghost old_self = *self;
            let ghost old_regions = self.regions;
            let ghost popped_idx = self.lists[id].slot_index_at(0);
            let ghost old_list_id = self.lists[id].list_id;
            // Pop preconditions from `inv`.
            assert(self.lists[id].inv());
            assert(self.lists[id].relate_region(self.regions));

            let tracked mut owner = self.lists.tracked_remove(id);
            let tracked frame_own = pop_front_embedded(&mut self.regions, &mut owner);
            self.lists.tracked_insert(id, owner);
            let ghost new_loose = fresh_loose_id(self.loose);
            axiom_fresh_loose_id_not_in_dom(self.loose);
            self.loose.tracked_insert(new_loose, frame_own);

            assert(self.lists =~= old_self.lists.remove(id).insert(id, owner));
            assert(self.loose =~= old_self.loose.insert(new_loose, frame_own));
            assert(self.lists[id].list_id == old_list_id);
            assert(frame_own.slot_index == popped_idx);

            // --- per-list: inv + relate_region ---
            assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
                &&& self.lists[i].inv()
                &&& self.lists[i].relate_region(self.regions)
            } by {
                if i != id {
                    assert(old_self.lists.dom().contains(i));
                    assert(old_self.lists[i] == self.lists[i]);
                    assert(old_self.lists[i].inv());
                    assert(old_self.lists[i].relate_region(old_regions));
                    if self.lists[i].list.len() > 0 {
                        // non-empty ⟹ nonzero id, distinct from `id`'s
                        // (preserved) id by old uniqueness.
                        assert(self.lists[i].list_id != old_list_id);
                    }
                }
            };

            // --- per-loose: new entry from the axiom; others preserved ---
            assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
                &&& self.loose[lid2].inv()
                &&& self.loose[lid2].global_inv(self.regions)
                &&& self.loose[lid2].frame_link_inv(self.regions)
                &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                    == 0
            } by {
                if lid2 != new_loose {
                    assert(old_self.loose.dom().contains(lid2));
                    assert(old_self.loose[lid2] == self.loose[lid2]);
                    assert(old_self.loose[lid2].global_inv(old_regions));
                    assert(old_self.loose[lid2].frame_link_inv(old_regions));
                    assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                        == 0);
                }
            };

            // --- list_id uniqueness (all ids unchanged) ---
            assert forall|i1: ListId, i2: ListId|
                self.lists.dom().contains(i1) && self.lists.dom().contains(i2)
                    && self.lists[i1].list_id == self.lists[i2].list_id && self.lists[i1].list_id
                    != 0 implies i1 == i2 by {
                assert(old_self.lists.dom().contains(i1));
                assert(old_self.lists.dom().contains(i2));
                assert(self.lists[i1].list_id == old_self.lists[i1].list_id);
                assert(self.lists[i2].list_id == old_self.lists[i2].list_id);
            };

            // --- loose-internal disjointness ---
            assert forall|l1: LooseId, l2: LooseId|
                self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                    && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
                if l1 == new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l2));
                    assert(self.loose[l2].slot_index != popped_idx);
                } else if l2 == new_loose && l1 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(self.loose[l1].slot_index != popped_idx);
                } else if l1 != new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(old_self.loose.dom().contains(l2));
                }
            };

            // --- cursors: checked-out lists are untouched ---
            // `id`'s (preserved, nonzero) `old_list_id` is separated from
            // every cursor's list id by the old list/cursor uniqueness, so
            // the axiom's other-lists frame preserves each cursor.
            assert(self.cursors == old_self.cursors);
            assert(self.lists.dom() =~= old_self.lists.dom());
            assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
                &&& self.cursors[cid].list_own.inv()
                &&& self.cursors[cid].inv_region(self.regions)
            } by {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.cursors[cid].list_own.inv());
                assert(old_self.cursors[cid].inv_region(old_regions));
                assert(self.cursors[cid].list_own.relate_region(old_regions));
                assert(old_self.lists.dom().contains(id));
                assert(old_self.lists[id].list_id == old_list_id);
                assert(self.cursors[cid].list_own.list_id != old_list_id);
                assert(self.cursors[cid].list_own.relate_region(self.regions));
            };
            assert forall|id2: ListId, cid: CursorId|
                self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                    && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                    && self.lists[id2].list_id != 0 implies false by {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2].list_id == self.lists[id2].list_id);
            };
            assert forall|cid1: CursorId, cid2: CursorId|
                self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                    && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                    && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
                assert(old_self.cursors.dom().contains(cid1));
                assert(old_self.cursors.dom().contains(cid2));
            };
            Option::Some(new_loose)
        }
    }

    /// `LinkedList::push_back`: move the loose handle `lid` to the back
    /// of list `id`. Same global effect as [`Self::step_push_front`] —
    /// only the link's position within the list differs.
    pub proof fn step_push_back(tracked &mut self, id: ListId, lid: LooseId)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
            old(self).loose.dom().contains(lid),
        ensures
            final(self).inv(),
    {
        let ghost old_self = *self;
        let ghost old_regions = self.regions;
        let ghost fidx = self.loose[lid].slot_index;
        let ghost used = Set::new_assuming_finite(
            |x: u64|
                (exists|i: ListId| #[trigger]
                    old_self.lists.dom().contains(i) && i != id && old_self.lists[i].list_id == x)
                    || (exists|cid: CursorId| #[trigger]
                    old_self.cursors.dom().contains(cid) && old_self.cursors[cid].list_own.list_id
                        == x),
        );
        assert(self.lists[id].inv());
        assert(self.lists[id].relate_region(self.regions));
        assert(self.loose[lid].inv());
        assert(self.loose[lid].global_inv(self.regions));
        assert(self.loose[lid].frame_link_inv(self.regions));
        assert(self.regions.slot_owners[fidx].inner_perms.in_list.value() == 0);

        let tracked mut owner = self.lists.tracked_remove(id);
        let tracked mut frame_own = self.loose.tracked_remove(lid);
        push_back_embedded(&mut self.regions, &mut owner, &mut frame_own, used);
        self.lists.tracked_insert(id, owner);
        assert(self.loose =~= old_self.loose.remove(lid));
        assert(self.lists =~= old_self.lists.remove(id).insert(id, owner));
        let ghost new_id = self.lists[id].list_id;

        assert forall|i: ListId|
            self.lists.dom().contains(i) && i != id && self.lists[i].list_id
                != 0 implies self.lists[i].list_id != new_id by {
            assert(old_self.lists.dom().contains(i));
            assert(old_self.lists[i] == self.lists[i]);
            if old_self.lists[id].list_id != 0 {
                assert(new_id == old_self.lists[id].list_id);
            } else {
                assert(used.contains(self.lists[i].list_id));
            }
        };

        assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
            &&& self.lists[i].inv()
            &&& self.lists[i].relate_region(self.regions)
        } by {
            if i != id {
                assert(old_self.lists.dom().contains(i));
                assert(old_self.lists[i] == self.lists[i]);
                assert(old_self.lists[i].inv());
                assert(old_self.lists[i].relate_region(old_regions));
                if self.lists[i].list.len() > 0 {
                    assert(self.lists[i].list_id != new_id);
                }
            }
        };

        assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
            &&& self.loose[lid2].inv()
            &&& self.loose[lid2].global_inv(self.regions)
            &&& self.loose[lid2].frame_link_inv(self.regions)
            &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(lid2 != lid);
            assert(old_self.loose.dom().contains(lid2));
            assert(old_self.loose[lid2] == self.loose[lid2]);
            assert(old_self.loose[lid2].global_inv(old_regions));
            assert(old_self.loose[lid2].frame_link_inv(old_regions));
            assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0);
            assert(self.loose[lid2].slot_index != fidx);
        };

        assert forall|i1: ListId, i2: ListId|
            self.lists.dom().contains(i1) && self.lists.dom().contains(i2)
                && self.lists[i1].list.len() > 0 && self.lists[i2].list.len() > 0
                && self.lists[i1].list_id == self.lists[i2].list_id implies i1 == i2 by {
            if i1 != id && i2 != id {
                assert(old_self.lists[i1] == self.lists[i1]);
                assert(old_self.lists[i2] == self.lists[i2]);
            } else if i1 == id && i2 != id {
                assert(self.lists[i2].list_id != new_id);
            } else if i2 == id && i1 != id {
                assert(self.lists[i1].list_id != new_id);
            }
        };

        assert forall|l1: LooseId, l2: LooseId|
            self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
            assert(old_self.loose.dom().contains(l1));
            assert(old_self.loose.dom().contains(l2));
        };

        // --- cursors: checked-out lists are untouched ---
        // `cursors` is not read or written by a list op, and every
        // cursor's list carries an id distinct from the just-minted
        // `new_id` (other cursors' ids are in `used`, or — when the id
        // was preserved — separated by the old list/cursor uniqueness),
        // so the axiom's other-lists frame preserves each cursor's
        // `relate_region`. Index bounds are unchanged.
        assert(self.cursors == old_self.cursors);
        assert(self.lists.dom() =~= old_self.lists.dom());
        assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
            &&& self.cursors[cid].list_own.inv()
            &&& self.cursors[cid].inv_region(self.regions)
        } by {
            assert(old_self.cursors.dom().contains(cid));
            assert(old_self.cursors[cid].list_own.inv());
            assert(old_self.cursors[cid].inv_region(old_regions));
            assert(self.cursors[cid].list_own.relate_region(old_regions));
            if old_self.lists[id].list_id != 0 {
                assert(new_id == old_self.lists[id].list_id);
            } else {
                assert(used.contains(self.cursors[cid].list_own.list_id));
            }
            assert(self.cursors[cid].list_own.list_id != new_id);
            assert(self.cursors[cid].list_own.relate_region(self.regions));
        };
        assert forall|id2: ListId, cid: CursorId|
            self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                && self.lists[id2].list_id != 0 implies false by {
            assert(old_self.cursors.dom().contains(cid));
            if id2 == id {
                assert(self.lists[id].list_id == new_id);
                if old_self.lists[id].list_id != 0 {
                    assert(new_id == old_self.lists[id].list_id);
                } else {
                    assert(used.contains(self.cursors[cid].list_own.list_id));
                }
            } else {
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2] == self.lists[id2]);
            }
        };
        assert forall|cid1: CursorId, cid2: CursorId|
            self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            assert(old_self.cursors.dom().contains(cid1));
            assert(old_self.cursors.dom().contains(cid2));
        };
    }

    /// `LinkedList::pop_back`: pop the back link of list `id` back into
    /// the loose pool. Same global effect as [`Self::step_pop_front`] —
    /// only which link is removed differs.
    pub proof fn step_pop_back(tracked &mut self, id: ListId) -> (res: Option<LooseId>)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
        ensures
            final(self).inv(),
            old(self).lists[id].list.len() == 0 ==> res is None && *final(self) == *old(self),
            old(self).lists[id].list.len() > 0 ==> res is Some,
    {
        if self.lists[id].list.len() == 0 {
            // Exec `LinkedList::pop_back` returns `None` on an empty list;
            // the store is unchanged.
            Option::None
        } else {
            let ghost old_self = *self;
            let ghost old_regions = self.regions;
            let ghost popped_idx = self.lists[id].slot_index_at(self.lists[id].list.len() - 1);
            let ghost old_list_id = self.lists[id].list_id;
            assert(self.lists[id].inv());
            assert(self.lists[id].relate_region(self.regions));

            let tracked mut owner = self.lists.tracked_remove(id);
            let tracked frame_own = pop_back_embedded(&mut self.regions, &mut owner);
            self.lists.tracked_insert(id, owner);
            let ghost new_loose = fresh_loose_id(self.loose);
            axiom_fresh_loose_id_not_in_dom(self.loose);
            self.loose.tracked_insert(new_loose, frame_own);

            assert(self.lists =~= old_self.lists.remove(id).insert(id, owner));
            assert(self.loose =~= old_self.loose.insert(new_loose, frame_own));
            assert(self.lists[id].list_id == old_list_id);
            assert(frame_own.slot_index == popped_idx);

            assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
                &&& self.lists[i].inv()
                &&& self.lists[i].relate_region(self.regions)
            } by {
                if i != id {
                    assert(old_self.lists.dom().contains(i));
                    assert(old_self.lists[i] == self.lists[i]);
                    assert(old_self.lists[i].inv());
                    assert(old_self.lists[i].relate_region(old_regions));
                    if self.lists[i].list.len() > 0 {
                        assert(self.lists[i].list_id != old_list_id);
                    }
                }
            };

            assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
                &&& self.loose[lid2].inv()
                &&& self.loose[lid2].global_inv(self.regions)
                &&& self.loose[lid2].frame_link_inv(self.regions)
                &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                    == 0
            } by {
                if lid2 != new_loose {
                    assert(old_self.loose.dom().contains(lid2));
                    assert(old_self.loose[lid2] == self.loose[lid2]);
                    assert(old_self.loose[lid2].global_inv(old_regions));
                    assert(old_self.loose[lid2].frame_link_inv(old_regions));
                    assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                        == 0);
                }
            };

            assert forall|i1: ListId, i2: ListId|
                self.lists.dom().contains(i1) && self.lists.dom().contains(i2)
                    && self.lists[i1].list_id == self.lists[i2].list_id && self.lists[i1].list_id
                    != 0 implies i1 == i2 by {
                assert(old_self.lists.dom().contains(i1));
                assert(old_self.lists.dom().contains(i2));
                assert(self.lists[i1].list_id == old_self.lists[i1].list_id);
                assert(self.lists[i2].list_id == old_self.lists[i2].list_id);
            };

            assert forall|l1: LooseId, l2: LooseId|
                self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                    && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
                if l1 == new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l2));
                    assert(self.loose[l2].slot_index != popped_idx);
                } else if l2 == new_loose && l1 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(self.loose[l1].slot_index != popped_idx);
                } else if l1 != new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(old_self.loose.dom().contains(l2));
                }
            };

            // --- cursors: checked-out lists are untouched ---
            // `id`'s (preserved, nonzero) `old_list_id` is separated from
            // every cursor's list id by the old list/cursor uniqueness, so
            // the axiom's other-lists frame preserves each cursor.
            assert(self.cursors == old_self.cursors);
            assert(self.lists.dom() =~= old_self.lists.dom());
            assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
                &&& self.cursors[cid].list_own.inv()
                &&& self.cursors[cid].inv_region(self.regions)
            } by {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.cursors[cid].list_own.inv());
                assert(old_self.cursors[cid].inv_region(old_regions));
                assert(self.cursors[cid].list_own.relate_region(old_regions));
                assert(old_self.lists.dom().contains(id));
                assert(old_self.lists[id].list_id == old_list_id);
                assert(self.cursors[cid].list_own.list_id != old_list_id);
                assert(self.cursors[cid].list_own.relate_region(self.regions));
            };
            assert forall|id2: ListId, cid: CursorId|
                self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                    && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                    && self.lists[id2].list_id != 0 implies false by {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2].list_id == self.lists[id2].list_id);
            };
            assert forall|cid1: CursorId, cid2: CursorId|
                self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                    && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                    && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
                assert(old_self.cursors.dom().contains(cid1));
                assert(old_self.cursors.dom().contains(cid2));
            };
            Option::Some(new_loose)
        }
    }

    /// Cursor `insert_before` at an arbitrary position `n`: move the
    /// loose handle `lid` into list `id` at index `n` (`0 <= n <= len`).
    /// The general form of [`Self::step_push_front`] /
    /// [`Self::step_push_back`]; same global effect.
    pub proof fn step_insert_before_at(tracked &mut self, id: ListId, n: int, lid: LooseId)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
            old(self).loose.dom().contains(lid),
            0 <= n <= old(self).lists[id].list.len(),
        ensures
            final(self).inv(),
    {
        let ghost old_self = *self;
        let ghost old_regions = self.regions;
        let ghost fidx = self.loose[lid].slot_index;
        let ghost used = Set::new_assuming_finite(
            |x: u64|
                (exists|i: ListId| #[trigger]
                    old_self.lists.dom().contains(i) && i != id && old_self.lists[i].list_id == x)
                    || (exists|cid: CursorId| #[trigger]
                    old_self.cursors.dom().contains(cid) && old_self.cursors[cid].list_own.list_id
                        == x),
        );
        assert(self.lists[id].inv());
        assert(self.lists[id].relate_region(self.regions));
        assert(self.loose[lid].inv());
        assert(self.loose[lid].global_inv(self.regions));
        assert(self.loose[lid].frame_link_inv(self.regions));
        assert(self.regions.slot_owners[fidx].inner_perms.in_list.value() == 0);

        let tracked mut owner = self.lists.tracked_remove(id);
        let tracked mut frame_own = self.loose.tracked_remove(lid);
        insert_before_at_embedded(&mut self.regions, &mut owner, &mut frame_own, n, used);
        self.lists.tracked_insert(id, owner);
        assert(self.loose =~= old_self.loose.remove(lid));
        assert(self.lists =~= old_self.lists.remove(id).insert(id, owner));
        let ghost new_id = self.lists[id].list_id;

        assert forall|i: ListId|
            self.lists.dom().contains(i) && i != id && self.lists[i].list_id
                != 0 implies self.lists[i].list_id != new_id by {
            assert(old_self.lists.dom().contains(i));
            assert(old_self.lists[i] == self.lists[i]);
            if old_self.lists[id].list_id != 0 {
                assert(new_id == old_self.lists[id].list_id);
            } else {
                assert(used.contains(self.lists[i].list_id));
            }
        };

        assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
            &&& self.lists[i].inv()
            &&& self.lists[i].relate_region(self.regions)
        } by {
            if i != id {
                assert(old_self.lists.dom().contains(i));
                assert(old_self.lists[i] == self.lists[i]);
                assert(old_self.lists[i].inv());
                assert(old_self.lists[i].relate_region(old_regions));
                if self.lists[i].list.len() > 0 {
                    assert(self.lists[i].list_id != new_id);
                }
            }
        };

        assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
            &&& self.loose[lid2].inv()
            &&& self.loose[lid2].global_inv(self.regions)
            &&& self.loose[lid2].frame_link_inv(self.regions)
            &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(lid2 != lid);
            assert(old_self.loose.dom().contains(lid2));
            assert(old_self.loose[lid2] == self.loose[lid2]);
            assert(old_self.loose[lid2].global_inv(old_regions));
            assert(old_self.loose[lid2].frame_link_inv(old_regions));
            assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0);
            assert(self.loose[lid2].slot_index != fidx);
        };

        assert forall|i1: ListId, i2: ListId|
            self.lists.dom().contains(i1) && self.lists.dom().contains(i2)
                && self.lists[i1].list.len() > 0 && self.lists[i2].list.len() > 0
                && self.lists[i1].list_id == self.lists[i2].list_id implies i1 == i2 by {
            if i1 != id && i2 != id {
                assert(old_self.lists[i1] == self.lists[i1]);
                assert(old_self.lists[i2] == self.lists[i2]);
            } else if i1 == id && i2 != id {
                assert(self.lists[i2].list_id != new_id);
            } else if i2 == id && i1 != id {
                assert(self.lists[i1].list_id != new_id);
            }
        };

        assert forall|l1: LooseId, l2: LooseId|
            self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
            assert(old_self.loose.dom().contains(l1));
            assert(old_self.loose.dom().contains(l2));
        };

        // --- cursors: checked-out lists are untouched ---
        // `cursors` is not read or written by a list op, and every
        // cursor's list carries an id distinct from the just-minted
        // `new_id` (other cursors' ids are in `used`, or — when the id
        // was preserved — separated by the old list/cursor uniqueness),
        // so the axiom's other-lists frame preserves each cursor's
        // `relate_region`. Index bounds are unchanged.
        assert(self.cursors == old_self.cursors);
        assert(self.lists.dom() =~= old_self.lists.dom());
        assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
            &&& self.cursors[cid].list_own.inv()
            &&& self.cursors[cid].inv_region(self.regions)
        } by {
            assert(old_self.cursors.dom().contains(cid));
            assert(old_self.cursors[cid].list_own.inv());
            assert(old_self.cursors[cid].inv_region(old_regions));
            assert(self.cursors[cid].list_own.relate_region(old_regions));
            if old_self.lists[id].list_id != 0 {
                assert(new_id == old_self.lists[id].list_id);
            } else {
                assert(used.contains(self.cursors[cid].list_own.list_id));
            }
            assert(self.cursors[cid].list_own.list_id != new_id);
            assert(self.cursors[cid].list_own.relate_region(self.regions));
        };
        assert forall|id2: ListId, cid: CursorId|
            self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                && self.lists[id2].list_id != 0 implies false by {
            assert(old_self.cursors.dom().contains(cid));
            if id2 == id {
                assert(self.lists[id].list_id == new_id);
                if old_self.lists[id].list_id != 0 {
                    assert(new_id == old_self.lists[id].list_id);
                } else {
                    assert(used.contains(self.cursors[cid].list_own.list_id));
                }
            } else {
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2] == self.lists[id2]);
            }
        };
        assert forall|cid1: CursorId, cid2: CursorId|
            self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            assert(old_self.cursors.dom().contains(cid1));
            assert(old_self.cursors.dom().contains(cid2));
        };
    }

    /// Cursor `take_current` at an arbitrary position `n`: pop the link
    /// at index `n` (`0 <= n < len`) of list `id` back into the loose
    /// pool. The general form of [`Self::step_pop_front`] /
    /// [`Self::step_pop_back`]; same global effect.
    pub proof fn step_take_at(tracked &mut self, id: ListId, n: int) -> (res: Option<LooseId>)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
        ensures
            final(self).inv(),
            !(0 <= n < old(self).lists[id].list.len()) ==> res is None && *final(self) == *old(
                self,
            ),
            0 <= n < old(self).lists[id].list.len() ==> res is Some,
    {
        if !(0 <= n < self.lists[id].list.len()) {
            // Exec take-at-position returns `None` when `n` is out of
            // range; the store is unchanged.
            Option::None
        } else {
            let ghost old_self = *self;
            let ghost old_regions = self.regions;
            let ghost popped_idx = self.lists[id].slot_index_at(n);
            let ghost old_list_id = self.lists[id].list_id;
            assert(self.lists[id].inv());
            assert(self.lists[id].relate_region(self.regions));

            let tracked mut owner = self.lists.tracked_remove(id);
            let tracked frame_own = take_at_embedded(&mut self.regions, &mut owner, n);
            self.lists.tracked_insert(id, owner);
            let ghost new_loose = fresh_loose_id(self.loose);
            axiom_fresh_loose_id_not_in_dom(self.loose);
            self.loose.tracked_insert(new_loose, frame_own);

            assert(self.lists =~= old_self.lists.remove(id).insert(id, owner));
            assert(self.loose =~= old_self.loose.insert(new_loose, frame_own));
            assert(self.lists[id].list_id == old_list_id);
            assert(frame_own.slot_index == popped_idx);

            assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
                &&& self.lists[i].inv()
                &&& self.lists[i].relate_region(self.regions)
            } by {
                if i != id {
                    assert(old_self.lists.dom().contains(i));
                    assert(old_self.lists[i] == self.lists[i]);
                    assert(old_self.lists[i].inv());
                    assert(old_self.lists[i].relate_region(old_regions));
                    if self.lists[i].list.len() > 0 {
                        assert(self.lists[i].list_id != old_list_id);
                    }
                }
            };

            assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
                &&& self.loose[lid2].inv()
                &&& self.loose[lid2].global_inv(self.regions)
                &&& self.loose[lid2].frame_link_inv(self.regions)
                &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                    == 0
            } by {
                if lid2 != new_loose {
                    assert(old_self.loose.dom().contains(lid2));
                    assert(old_self.loose[lid2] == self.loose[lid2]);
                    assert(old_self.loose[lid2].global_inv(old_regions));
                    assert(old_self.loose[lid2].frame_link_inv(old_regions));
                    assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                        == 0);
                }
            };

            assert forall|i1: ListId, i2: ListId|
                self.lists.dom().contains(i1) && self.lists.dom().contains(i2)
                    && self.lists[i1].list_id == self.lists[i2].list_id && self.lists[i1].list_id
                    != 0 implies i1 == i2 by {
                assert(old_self.lists.dom().contains(i1));
                assert(old_self.lists.dom().contains(i2));
                assert(self.lists[i1].list_id == old_self.lists[i1].list_id);
                assert(self.lists[i2].list_id == old_self.lists[i2].list_id);
            };

            assert forall|l1: LooseId, l2: LooseId|
                self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                    && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
                if l1 == new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l2));
                    assert(self.loose[l2].slot_index != popped_idx);
                } else if l2 == new_loose && l1 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(self.loose[l1].slot_index != popped_idx);
                } else if l1 != new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(old_self.loose.dom().contains(l2));
                }
            };

            // --- cursors: checked-out lists are untouched ---
            // `id`'s (preserved, nonzero) `old_list_id` is separated from
            // every cursor's list id by the old list/cursor uniqueness, so
            // the axiom's other-lists frame preserves each cursor.
            assert(self.cursors == old_self.cursors);
            assert(self.lists.dom() =~= old_self.lists.dom());
            assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
                &&& self.cursors[cid].list_own.inv()
                &&& self.cursors[cid].inv_region(self.regions)
            } by {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.cursors[cid].list_own.inv());
                assert(old_self.cursors[cid].inv_region(old_regions));
                assert(self.cursors[cid].list_own.relate_region(old_regions));
                assert(old_self.lists.dom().contains(id));
                assert(old_self.lists[id].list_id == old_list_id);
                assert(self.cursors[cid].list_own.list_id != old_list_id);
                assert(self.cursors[cid].list_own.relate_region(self.regions));
            };
            assert forall|id2: ListId, cid: CursorId|
                self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                    && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                    && self.lists[id2].list_id != 0 implies false by {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2].list_id == self.lists[id2].list_id);
            };
            assert forall|cid1: CursorId, cid2: CursorId|
                self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                    && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                    && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
                assert(old_self.cursors.dom().contains(cid1));
                assert(old_self.cursors.dom().contains(cid2));
            };
            Option::Some(new_loose)
        }
    }

    // -------------------------------------------------------------------
    // Persistent cursor lifecycle
    // -------------------------------------------------------------------
    /// Invariant-preservation lemma for *checking a list out* into a
    /// cursor: `lists[id]` (a held list) moves to `cursors[id]` (the
    /// same list, now position-tracked at `index`). Region-free — only
    /// the `lists`/`cursors` bookkeeping moves. All disjointness /
    /// uniqueness facts transfer from the old store (a checked-out list
    /// keeps its id, distinct by the same arguments as a held list).
    proof fn lemma_checkout_inv(old_self: Self, new_self: Self, id: ListId, index: int)
        requires
            old_self.inv(),
            old_self.lists.dom().contains(id),
            0 <= index <= old_self.lists[id].list.len(),
            new_self.regions == old_self.regions,
            new_self.loose == old_self.loose,
            new_self.lists == old_self.lists.remove(id),
            new_self.cursors == old_self.cursors.insert(
                id,
                CursorOwner::cursor_mut_at_owner(old_self.lists[id], index),
            ),
        ensures
            new_self.inv(),
    {
        assert forall|i: ListId| #[trigger] new_self.lists.dom().contains(i) implies {
            &&& new_self.lists[i].inv()
            &&& new_self.lists[i].relate_region(new_self.regions)
        } by {
            assert(i != id);
            assert(old_self.lists.dom().contains(i));
            assert(old_self.lists[i] == new_self.lists[i]);
        };
        assert forall|lid: LooseId| #[trigger] new_self.loose.dom().contains(lid) implies {
            &&& new_self.loose[lid].inv()
            &&& new_self.loose[lid].global_inv(new_self.regions)
            &&& new_self.loose[lid].frame_link_inv(new_self.regions)
            &&& new_self.regions.slot_owners[new_self.loose[lid].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(old_self.loose.dom().contains(lid));
        };
        assert forall|i1: ListId, i2: ListId|
            new_self.lists.dom().contains(i1) && new_self.lists.dom().contains(i2)
                && new_self.lists[i1].list_id == new_self.lists[i2].list_id
                && new_self.lists[i1].list_id != 0 implies i1 == i2 by {
            assert(old_self.lists.dom().contains(i1));
            assert(old_self.lists.dom().contains(i2));
        };
        assert forall|l1: LooseId, l2: LooseId|
            new_self.loose.dom().contains(l1) && new_self.loose.dom().contains(l2)
                && new_self.loose[l1].slot_index == new_self.loose[l2].slot_index implies l1
            == l2 by {
            assert(old_self.loose.dom().contains(l1));
            assert(old_self.loose.dom().contains(l2));
        };
        assert(new_self.lists.dom().disjoint(new_self.cursors.dom()));
        assert forall|cid: CursorId| #[trigger] new_self.cursors.dom().contains(cid) implies {
            &&& new_self.cursors[cid].list_own.inv()
            &&& new_self.cursors[cid].inv_region(new_self.regions)
        } by {
            if cid != id {
                assert(old_self.cursors.dom().contains(cid));
            } else {
                assert(new_self.cursors[id].list_own == old_self.lists[id]);
                assert(old_self.lists[id].inv());
                assert(old_self.lists[id].relate_region(old_self.regions));
            }
        };
        assert forall|id2: ListId, cid: CursorId|
            new_self.lists.dom().contains(id2) && new_self.cursors.dom().contains(cid)
                && new_self.lists[id2].list_id == new_self.cursors[cid].list_own.list_id
                && new_self.lists[id2].list_id != 0 implies false by {
            assert(id2 != id);
            assert(old_self.lists.dom().contains(id2));
            assert(old_self.lists[id2] == new_self.lists[id2]);
            if cid == id {
                assert(new_self.cursors[id].list_own == old_self.lists[id]);
                assert(old_self.lists.dom().contains(id));
            } else {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.cursors[cid] == new_self.cursors[cid]);
            }
        };
        assert forall|cid1: CursorId, cid2: CursorId|
            new_self.cursors.dom().contains(cid1) && new_self.cursors.dom().contains(cid2)
                && new_self.cursors[cid1].list_own.list_id
                == new_self.cursors[cid2].list_own.list_id
                && new_self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            if cid1 == id && cid2 != id {
                assert(old_self.cursors.dom().contains(cid2));
                assert(new_self.cursors[id].list_own == old_self.lists[id]);
                assert(old_self.lists.dom().contains(id));
            } else if cid2 == id && cid1 != id {
                assert(old_self.cursors.dom().contains(cid1));
                assert(new_self.cursors[id].list_own == old_self.lists[id]);
                assert(old_self.lists.dom().contains(id));
            } else if cid1 != id && cid2 != id {
                assert(old_self.cursors.dom().contains(cid1));
                assert(old_self.cursors.dom().contains(cid2));
            }
        };
    }

    /// Invariant-preservation lemma for *checking a list back in* on
    /// cursor drop: `cursors[id]`'s list moves back to `lists[id]`. The
    /// exact inverse of [`Self::lemma_checkout_inv`].
    proof fn lemma_checkin_inv(old_self: Self, new_self: Self, id: CursorId)
        requires
            old_self.inv(),
            old_self.cursors.dom().contains(id),
            new_self.regions == old_self.regions,
            new_self.loose == old_self.loose,
            new_self.cursors == old_self.cursors.remove(id),
            new_self.lists == old_self.lists.insert(id, old_self.cursors[id].list_own),
        ensures
            new_self.inv(),
    {
        assert(!old_self.lists.dom().contains(id));
        assert forall|i: ListId| #[trigger] new_self.lists.dom().contains(i) implies {
            &&& new_self.lists[i].inv()
            &&& new_self.lists[i].relate_region(new_self.regions)
        } by {
            if i == id {
                assert(new_self.lists[id] == old_self.cursors[id].list_own);
                assert(old_self.cursors[id].list_own.inv());
                assert(old_self.cursors[id].inv_region(old_self.regions));
            } else {
                assert(old_self.lists.dom().contains(i));
                assert(old_self.lists[i] == new_self.lists[i]);
            }
        };
        assert forall|lid: LooseId| #[trigger] new_self.loose.dom().contains(lid) implies {
            &&& new_self.loose[lid].inv()
            &&& new_self.loose[lid].global_inv(new_self.regions)
            &&& new_self.loose[lid].frame_link_inv(new_self.regions)
            &&& new_self.regions.slot_owners[new_self.loose[lid].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(old_self.loose.dom().contains(lid));
        };
        assert forall|i1: ListId, i2: ListId|
            new_self.lists.dom().contains(i1) && new_self.lists.dom().contains(i2)
                && new_self.lists[i1].list_id == new_self.lists[i2].list_id
                && new_self.lists[i1].list_id != 0 implies i1 == i2 by {
            // The reinstated list at `id` carries the cursor's id; any
            // other list with the same nonzero id is separated by the old
            // cross list/cursor uniqueness.
            if i1 == id && i2 != id {
                assert(old_self.lists.dom().contains(i2));
                assert(new_self.lists[id] == old_self.cursors[id].list_own);
                assert(old_self.cursors.dom().contains(id));
            } else if i2 == id && i1 != id {
                assert(old_self.lists.dom().contains(i1));
                assert(new_self.lists[id] == old_self.cursors[id].list_own);
                assert(old_self.cursors.dom().contains(id));
            } else if i1 != id && i2 != id {
                assert(old_self.lists.dom().contains(i1));
                assert(old_self.lists.dom().contains(i2));
            }
        };
        assert forall|l1: LooseId, l2: LooseId|
            new_self.loose.dom().contains(l1) && new_self.loose.dom().contains(l2)
                && new_self.loose[l1].slot_index == new_self.loose[l2].slot_index implies l1
            == l2 by {
            assert(old_self.loose.dom().contains(l1));
            assert(old_self.loose.dom().contains(l2));
        };
        assert(new_self.lists.dom().disjoint(new_self.cursors.dom()));
        assert forall|cid: CursorId| #[trigger] new_self.cursors.dom().contains(cid) implies {
            &&& new_self.cursors[cid].list_own.inv()
            &&& new_self.cursors[cid].inv_region(new_self.regions)
        } by {
            assert(cid != id);
            assert(old_self.cursors.dom().contains(cid));
            assert(old_self.cursors[cid] == new_self.cursors[cid]);
        };
        assert forall|id2: ListId, cid: CursorId|
            new_self.lists.dom().contains(id2) && new_self.cursors.dom().contains(cid)
                && new_self.lists[id2].list_id == new_self.cursors[cid].list_own.list_id
                && new_self.lists[id2].list_id != 0 implies false by {
            assert(cid != id);
            assert(old_self.cursors.dom().contains(cid));
            assert(old_self.cursors[cid] == new_self.cursors[cid]);
            if id2 == id {
                assert(new_self.lists[id] == old_self.cursors[id].list_own);
                assert(old_self.cursors.dom().contains(id));
            } else {
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2] == new_self.lists[id2]);
            }
        };
        assert forall|cid1: CursorId, cid2: CursorId|
            new_self.cursors.dom().contains(cid1) && new_self.cursors.dom().contains(cid2)
                && new_self.cursors[cid1].list_own.list_id
                == new_self.cursors[cid2].list_own.list_id
                && new_self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            assert(old_self.cursors.dom().contains(cid1));
            assert(old_self.cursors.dom().contains(cid2));
        };
    }

    /// Invariant-preservation lemma for *revising a cursor's position in
    /// place*: `cursors[id]` keeps its checked-out list (same `list_own`)
    /// but adopts a new in-range `index`. Region-free; everything else is
    /// untouched, so every fact transfers from the old store.
    proof fn lemma_revise_cursor_inv(old_self: Self, new_self: Self, id: CursorId)
        requires
            old_self.inv(),
            old_self.cursors.dom().contains(id),
            new_self.regions == old_self.regions,
            new_self.lists == old_self.lists,
            new_self.loose == old_self.loose,
            new_self.cursors.dom() == old_self.cursors.dom(),
            new_self.cursors[id].list_own == old_self.cursors[id].list_own,
            0 <= new_self.cursors[id].index <= new_self.cursors[id].list_own.list.len(),
            forall|c: CursorId| #[trigger]
                new_self.cursors.dom().contains(c) && c != id ==> new_self.cursors[c]
                    == old_self.cursors[c],
        ensures
            new_self.inv(),
    {
        assert forall|i: ListId| #[trigger] new_self.lists.dom().contains(i) implies {
            &&& new_self.lists[i].inv()
            &&& new_self.lists[i].relate_region(new_self.regions)
        } by {
            assert(old_self.lists.dom().contains(i));
        };
        assert forall|lid: LooseId| #[trigger] new_self.loose.dom().contains(lid) implies {
            &&& new_self.loose[lid].inv()
            &&& new_self.loose[lid].global_inv(new_self.regions)
            &&& new_self.loose[lid].frame_link_inv(new_self.regions)
            &&& new_self.regions.slot_owners[new_self.loose[lid].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(old_self.loose.dom().contains(lid));
        };
        assert forall|i1: ListId, i2: ListId|
            new_self.lists.dom().contains(i1) && new_self.lists.dom().contains(i2)
                && new_self.lists[i1].list_id == new_self.lists[i2].list_id
                && new_self.lists[i1].list_id != 0 implies i1 == i2 by {
            assert(old_self.lists.dom().contains(i1));
            assert(old_self.lists.dom().contains(i2));
        };
        assert forall|l1: LooseId, l2: LooseId|
            new_self.loose.dom().contains(l1) && new_self.loose.dom().contains(l2)
                && new_self.loose[l1].slot_index == new_self.loose[l2].slot_index implies l1
            == l2 by {
            assert(old_self.loose.dom().contains(l1));
            assert(old_self.loose.dom().contains(l2));
        };
        assert(new_self.lists.dom().disjoint(new_self.cursors.dom()));
        assert forall|cid: CursorId| #[trigger] new_self.cursors.dom().contains(cid) implies {
            &&& new_self.cursors[cid].list_own.inv()
            &&& new_self.cursors[cid].inv_region(new_self.regions)
        } by {
            assert(old_self.cursors.dom().contains(cid));
            if cid != id {
                assert(new_self.cursors[cid] == old_self.cursors[cid]);
            } else {
                assert(new_self.cursors[id].list_own == old_self.cursors[id].list_own);
                assert(old_self.cursors[id].list_own.inv());
                assert(old_self.cursors[id].inv_region(old_self.regions));
            }
        };
        assert forall|id2: ListId, cid: CursorId|
            new_self.lists.dom().contains(id2) && new_self.cursors.dom().contains(cid)
                && new_self.lists[id2].list_id == new_self.cursors[cid].list_own.list_id
                && new_self.lists[id2].list_id != 0 implies false by {
            assert(old_self.lists.dom().contains(id2));
            assert(old_self.cursors.dom().contains(cid));
            assert(new_self.cursors[cid].list_own.list_id
                == old_self.cursors[cid].list_own.list_id);
        };
        assert forall|cid1: CursorId, cid2: CursorId|
            new_self.cursors.dom().contains(cid1) && new_self.cursors.dom().contains(cid2)
                && new_self.cursors[cid1].list_own.list_id
                == new_self.cursors[cid2].list_own.list_id
                && new_self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            assert(old_self.cursors.dom().contains(cid1));
            assert(old_self.cursors.dom().contains(cid2));
            assert(new_self.cursors[cid1].list_own.list_id
                == old_self.cursors[cid1].list_own.list_id);
            assert(new_self.cursors[cid2].list_own.list_id
                == old_self.cursors[cid2].list_own.list_id);
        };
    }

    /// `LinkedList::cursor_front_mut`: check list `id` out into a cursor
    /// positioned at the front (index 0). The list leaves `lists` and
    /// enters `cursors` under the same id (its borrow).
    pub proof fn step_cursor_front_mut(tracked &mut self, id: ListId)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
        ensures
            final(self).inv(),
            !final(self).lists.dom().contains(id),
            final(self).cursors.dom().contains(id),
            final(self).cursors[id] == CursorOwner::front_owner(old(self).lists[id]),
    {
        let ghost old_self = *self;
        let tracked owner = self.lists.tracked_remove(id);
        let tracked cur = CursorOwner::tracked_front_owner(owner);
        self.cursors.tracked_insert(id, cur);
        assert(self.lists =~= old_self.lists.remove(id));
        assert(self.cursors =~= old_self.cursors.insert(
            id,
            CursorOwner::cursor_mut_at_owner(old_self.lists[id], 0),
        ));
        Self::lemma_checkout_inv(old_self, *self, id, 0);
    }

    /// `LinkedList::cursor_back_mut`: check list `id` out into a cursor
    /// at the back (the last element, or the ghost slot when empty).
    pub proof fn step_cursor_back_mut(tracked &mut self, id: ListId)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
        ensures
            final(self).inv(),
            !final(self).lists.dom().contains(id),
            final(self).cursors.dom().contains(id),
            final(self).cursors[id] == CursorOwner::back_owner(old(self).lists[id]),
    {
        let ghost old_self = *self;
        let tracked owner = self.lists.tracked_remove(id);
        let ghost bidx = CursorOwner::back_owner(owner).index;
        let tracked cur = CursorOwner::tracked_back_owner(owner);
        self.cursors.tracked_insert(id, cur);
        assert(self.lists =~= old_self.lists.remove(id));
        assert(self.cursors =~= old_self.cursors.insert(
            id,
            CursorOwner::cursor_mut_at_owner(old_self.lists[id], bidx),
        ));
        Self::lemma_checkout_inv(old_self, *self, id, bidx);
    }

    /// `LinkedList::cursor_mut_at`: search list `id` for `frame` and, if
    /// it is one of the list's links, check the list out into a cursor
    /// positioned at that link; otherwise (the frame is absent — or not a
    /// safe managed slot, which can never be a link) leave the store
    /// unchanged. Mirrors exec `cursor_mut_at(frame) -> Option<CursorMut>`
    /// (the `Some`/`None` outcome is returned as `res`).
    pub proof fn step_cursor_mut_at(tracked &mut self, id: ListId, frame: Paddr) -> (res: bool)
        requires
            old(self).inv(),
            old(self).lists.dom().contains(id),
        ensures
            final(self).inv(),
            // `res` is exactly list membership of `frame`.
            res == (exists|i: int|
                0 <= i < old(self).lists[id].list.len() && old(self).lists[id].slot_index_at(i)
                    == frame_to_index(frame)),
            // On a hit: the list is checked out into a cursor positioned
            // at the matching link.
            res ==> !final(self).lists.dom().contains(id) && final(self).cursors.dom().contains(id)
                && exists|i: int|
                0 <= i < old(self).lists[id].list.len() && old(self).lists[id].slot_index_at(i)
                    == frame_to_index(frame) && final(self).cursors[id]
                    == CursorOwner::cursor_mut_at_owner(old(self).lists[id], i),
            // On a miss: no checkout, the store is unchanged.
            !res ==> *final(self) == *old(self),
    {
        if exists|i: int|
            0 <= i < self.lists[id].list.len() && self.lists[id].slot_index_at(i) == frame_to_index(
                frame,
            ) {
            let ghost index = choose|i: int|
                0 <= i < self.lists[id].list.len() && self.lists[id].slot_index_at(i)
                    == frame_to_index(frame);
            let ghost old_self = *self;
            let tracked owner = self.lists.tracked_remove(id);
            let tracked cur = CursorOwner::tracked_cursor_mut_at_owner(owner, index);
            self.cursors.tracked_insert(id, cur);
            assert(self.lists =~= old_self.lists.remove(id));
            assert(self.cursors =~= old_self.cursors.insert(
                id,
                CursorOwner::cursor_mut_at_owner(old_self.lists[id], index),
            ));
            Self::lemma_checkout_inv(old_self, *self, id, index);
            true
        } else {
            false
        }
    }

    /// `CursorMut::move_next`: advance cursor `id` one step toward the
    /// back (wrapping through the ghost slot). Pure position change.
    pub proof fn step_move_next(tracked &mut self, id: CursorId)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(id),
        ensures
            final(self).inv(),
            final(self).regions == old(self).regions,
            final(self).cursors[id] == old(self).cursors[id].move_next_owner_spec(),
    {
        let ghost old_self = *self;
        let tracked cur = self.cursors.tracked_remove(id);
        let ghost ni = cur.move_next_owner_spec().index;
        let tracked CursorOwner { list_own, index: _ } = cur;
        let tracked cur2 = CursorOwner::tracked_cursor_mut_at_owner(list_own, ni);
        self.cursors.tracked_insert(id, cur2);
        assert(self.cursors[id] == old_self.cursors[id].move_next_owner_spec());
        assert(self.cursors.dom() =~= old_self.cursors.dom());
        Self::lemma_revise_cursor_inv(old_self, *self, id);
    }

    /// `CursorMut::move_prev`: retreat cursor `id` one step toward the
    /// front (wrapping through the ghost slot). Pure position change.
    pub proof fn step_move_prev(tracked &mut self, id: CursorId)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(id),
        ensures
            final(self).inv(),
            final(self).regions == old(self).regions,
            final(self).cursors[id] == old(self).cursors[id].move_prev_owner_spec(),
    {
        let ghost old_self = *self;
        let tracked cur = self.cursors.tracked_remove(id);
        let ghost ni = cur.move_prev_owner_spec().index;
        let tracked CursorOwner { list_own, index: _ } = cur;
        let tracked cur2 = CursorOwner::tracked_cursor_mut_at_owner(list_own, ni);
        self.cursors.tracked_insert(id, cur2);
        assert(self.cursors[id] == old_self.cursors[id].move_prev_owner_spec());
        assert(self.cursors.dom() =~= old_self.cursors.dom());
        Self::lemma_revise_cursor_inv(old_self, *self, id);
    }

    /// `CursorMut::current_meta`: read the link the cursor `id` is on.
    /// A read-only query — returns the current [`LinkOwner`] (`None` at
    /// the ghost slot); the store is unchanged.
    pub proof fn step_current_meta(tracked &self, id: CursorId) -> (res: Option<LinkOwner>)
        requires
            self.inv(),
            self.cursors.dom().contains(id),
        ensures
            res == self.cursors[id].current(),
            res.is_some() <==> 0 <= self.cursors[id].index < self.cursors[id].length(),
    {
        self.cursors[id].current()
    }

    /// `CursorMut::as_list`: borrow the cursor's checked-out list for
    /// reading. A pure no-op — `&self` on the store, so `regions` /
    /// `lists` / `loose` / `cursors` are all untouched; it merely exposes
    /// the list's contents (the model `Seq` of links). Modeled for
    /// completeness, to demonstrate the read-only view changes nothing.
    pub proof fn step_as_list(tracked &self, id: CursorId) -> (res: Seq<LinkOwner>)
        requires
            self.inv(),
            self.cursors.dom().contains(id),
        ensures
            res == self.cursors[id].list_own.list,
            res.len() == self.cursors[id].length(),
    {
        self.cursors[id].list_own.list
    }

    /// Drop of a `CursorMut`: check the cursor's list back into `lists`
    /// under its home id, ending the borrow. Inverse of
    /// [`Self::step_cursor_front_mut`] et al.
    pub proof fn step_cursor_drop(tracked &mut self, id: CursorId)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(id),
        ensures
            final(self).inv(),
            !final(self).cursors.dom().contains(id),
            final(self).lists.dom().contains(id),
            final(self).lists[id] == old(self).cursors[id].list_own,
    {
        let ghost old_self = *self;
        let tracked cur = self.cursors.tracked_remove(id);
        let tracked CursorOwner { list_own, index: _ } = cur;
        self.lists.tracked_insert(id, list_own);
        assert(self.cursors =~= old_self.cursors.remove(id));
        assert(self.lists =~= old_self.lists.insert(id, old_self.cursors[id].list_own));
        Self::lemma_checkin_inv(old_self, *self, id);
    }

    /// `CursorMut::insert_before`: through the checked-out cursor `id`,
    /// move the loose handle `lid` into the cursor's list at the current
    /// position (index `n`), advancing the cursor to `n + 1`. The general
    /// [`Self::step_insert_before_at`], but on the list parked in
    /// `cursors` rather than `lists` — so *every* held list is an "other
    /// list" preserved by the axiom's frame.
    pub proof fn step_cursor_insert_before(tracked &mut self, id: CursorId, lid: LooseId)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(id),
            old(self).loose.dom().contains(lid),
        ensures
            final(self).inv(),
    {
        let ghost old_self = *self;
        let ghost old_regions = self.regions;
        let ghost fidx = self.loose[lid].slot_index;
        let ghost n = self.cursors[id].index;
        // Avoid every other list's *and* every other cursor's id.
        let ghost used = Set::new_assuming_finite(
            |x: u64|
                (exists|i: ListId| #[trigger]
                    old_self.lists.dom().contains(i) && old_self.lists[i].list_id == x) || (exists|
                    cid: CursorId,
                | #[trigger]
                    old_self.cursors.dom().contains(cid) && cid != id
                        && old_self.cursors[cid].list_own.list_id == x),
        );
        assert(self.cursors[id].list_own.inv());
        assert(self.cursors[id].inv_region(self.regions));
        assert(self.cursors[id].list_own.relate_region(self.regions));
        assert(self.loose[lid].inv());
        assert(self.loose[lid].global_inv(self.regions));
        assert(self.loose[lid].frame_link_inv(self.regions));
        assert(self.regions.slot_owners[fidx].inner_perms.in_list.value() == 0);
        assert(0 <= n <= self.cursors[id].list_own.list.len());

        let tracked cur = self.cursors.tracked_remove(id);
        let tracked CursorOwner { list_own: mut owner, index: _ } = cur;
        let tracked mut frame_own = self.loose.tracked_remove(lid);
        insert_before_at_embedded(&mut self.regions, &mut owner, &mut frame_own, n, used);
        let tracked cur2 = CursorOwner::tracked_cursor_mut_at_owner(owner, n + 1);
        self.cursors.tracked_insert(id, cur2);
        assert(self.loose =~= old_self.loose.remove(lid));
        assert(self.cursors =~= old_self.cursors.remove(id).insert(id, cur2));
        let ghost new_id = self.cursors[id].list_own.list_id;
        assert(self.cursors[id].list_own == owner);

        // `new_id` is distinct from every list id and every *other*
        // cursor id (minted outside `used`, or — when the cursor's list
        // already had an id — separated by the old uniqueness).
        assert forall|i: ListId|
            old_self.lists.dom().contains(i) && self.lists[i].list_id
                != 0 implies self.lists[i].list_id != new_id by {
            if old_self.cursors[id].list_own.list_id != 0 {
                assert(new_id == old_self.cursors[id].list_own.list_id);
                assert(old_self.cursors.dom().contains(id));
            } else {
                assert(used.contains(self.lists[i].list_id));
            }
        };
        assert forall|cid: CursorId|
            old_self.cursors.dom().contains(cid) && cid != id
                && old_self.cursors[cid].list_own.list_id
                != 0 implies old_self.cursors[cid].list_own.list_id != new_id by {
            if old_self.cursors[id].list_own.list_id != 0 {
                assert(new_id == old_self.cursors[id].list_own.list_id);
            } else {
                assert(used.contains(old_self.cursors[cid].list_own.list_id));
            }
        };

        // --- per-list: every list is preserved (none is operating) ---
        assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
            &&& self.lists[i].inv()
            &&& self.lists[i].relate_region(self.regions)
        } by {
            assert(old_self.lists.dom().contains(i));
            assert(old_self.lists[i] == self.lists[i]);
            assert(old_self.lists[i].relate_region(old_regions));
            assert(self.lists[i].list_id != new_id);
            assert(self.lists[i].relate_region(self.regions));
        };

        // --- per-loose: `lid` removed; others at `!= fidx` preserved ---
        assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
            &&& self.loose[lid2].inv()
            &&& self.loose[lid2].global_inv(self.regions)
            &&& self.loose[lid2].frame_link_inv(self.regions)
            &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0
        } by {
            assert(lid2 != lid);
            assert(old_self.loose.dom().contains(lid2));
            assert(old_self.loose[lid2] == self.loose[lid2]);
            assert(old_self.loose[lid2].global_inv(old_regions));
            assert(old_self.loose[lid2].frame_link_inv(old_regions));
            assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                == 0);
            assert(self.loose[lid2].slot_index != fidx);
        };

        // --- disjointness (list/cursor domains unchanged) ---
        assert(self.lists.dom() =~= old_self.lists.dom());
        assert(self.cursors.dom() =~= old_self.cursors.dom());
        assert(self.lists.dom().disjoint(self.cursors.dom()));

        // --- per-cursor: operating cursor rebuilt; others preserved ---
        assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
            &&& self.cursors[cid].list_own.inv()
            &&& self.cursors[cid].inv_region(self.regions)
        } by {
            if cid == id {
                assert(self.cursors[id].list_own == owner);
                assert(self.cursors[id].index == n + 1);
                assert(owner.list.len() == old_self.cursors[id].list_own.list.len() + 1);
            } else {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.cursors[cid] == self.cursors[cid]);
                assert(old_self.cursors[cid].list_own.inv());
                assert(old_self.cursors[cid].inv_region(old_regions));
                assert(self.cursors[cid].list_own.relate_region(old_regions));
                assert(self.cursors[cid].list_own.list_id != new_id);
                assert(self.cursors[cid].list_own.relate_region(self.regions));
            }
        };

        // --- cross list/cursor uniqueness ---
        assert forall|id2: ListId, cid: CursorId|
            self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                && self.lists[id2].list_id != 0 implies false by {
            assert(old_self.lists.dom().contains(id2));
            assert(old_self.lists[id2] == self.lists[id2]);
            if cid == id {
                assert(self.cursors[id].list_own.list_id == new_id);
                assert(self.lists[id2].list_id != new_id);
            } else {
                assert(old_self.cursors.dom().contains(cid));
                assert(old_self.cursors[cid] == self.cursors[cid]);
            }
        };

        // --- cursor×cursor uniqueness ---
        assert forall|cid1: CursorId, cid2: CursorId|
            self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
            if cid1 == id && cid2 != id {
                assert(self.cursors[id].list_own.list_id == new_id);
                assert(old_self.cursors.dom().contains(cid2));
                assert(old_self.cursors[cid2] == self.cursors[cid2]);
                assert(self.cursors[cid2].list_own.list_id != new_id);
            } else if cid2 == id && cid1 != id {
                assert(self.cursors[id].list_own.list_id == new_id);
                assert(old_self.cursors.dom().contains(cid1));
                assert(old_self.cursors[cid1] == self.cursors[cid1]);
                assert(self.cursors[cid1].list_own.list_id != new_id);
            } else if cid1 != id && cid2 != id {
                assert(old_self.cursors.dom().contains(cid1));
                assert(old_self.cursors.dom().contains(cid2));
            }
        };
    }

    /// `CursorMut::take_current`: through the checked-out cursor `id`,
    /// pop the link the cursor is on (index `n`, requires the cursor be
    /// on an element) back into the loose pool, leaving the cursor at the
    /// same index (now on the following link). The general
    /// [`Self::step_take_at`] on a cursored list. Returns the fresh loose
    /// id.
    pub proof fn step_cursor_take_current(tracked &mut self, id: CursorId) -> (res: Option<LooseId>)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(id),
        ensures
            final(self).inv(),
            !(0 <= old(self).cursors[id].index < old(self).cursors[id].length()) ==> res is None
                && *final(self) == *old(self),
            0 <= old(self).cursors[id].index < old(self).cursors[id].length() ==> res is Some,
    {
        if !(0 <= self.cursors[id].index < self.cursors[id].length()) {
            // Exec `CursorMut::take_current` returns `None` when the
            // cursor is not on an element; the store is unchanged.
            Option::None
        } else {
            let ghost old_self = *self;
            let ghost old_regions = self.regions;
            let ghost n = self.cursors[id].index;
            let ghost old_list_id = self.cursors[id].list_own.list_id;
            let ghost popped_idx = self.cursors[id].list_own.slot_index_at(n);
            assert(self.cursors[id].list_own.inv());
            assert(self.cursors[id].list_own.relate_region(self.regions));
            assert(0 <= n < self.cursors[id].list_own.list.len());
            // A non-empty list carries a nonzero id (`LinkedListOwner::inv`).
            assert(old_list_id != 0);

            let tracked cur = self.cursors.tracked_remove(id);
            let tracked CursorOwner { list_own: mut owner, index: _ } = cur;
            let tracked frame_own = take_at_embedded(&mut self.regions, &mut owner, n);
            let tracked cur2 = CursorOwner::tracked_cursor_mut_at_owner(owner, n);
            self.cursors.tracked_insert(id, cur2);
            let ghost new_loose = fresh_loose_id(self.loose);
            axiom_fresh_loose_id_not_in_dom(self.loose);
            self.loose.tracked_insert(new_loose, frame_own);

            assert(self.cursors =~= old_self.cursors.remove(id).insert(id, cur2));
            assert(self.loose =~= old_self.loose.insert(new_loose, frame_own));
            assert(self.cursors[id].list_own.list_id == old_list_id);
            assert(self.cursors[id].list_own == owner);
            assert(frame_own.slot_index == popped_idx);

            // --- per-list: every list preserved (operating is a cursor) ---
            assert forall|i: ListId| #[trigger] self.lists.dom().contains(i) implies {
                &&& self.lists[i].inv()
                &&& self.lists[i].relate_region(self.regions)
            } by {
                assert(old_self.lists.dom().contains(i));
                assert(old_self.lists[i] == self.lists[i]);
                assert(old_self.lists[i].relate_region(old_regions));
                assert(old_self.cursors.dom().contains(id));
                assert(self.lists[i].list_id != old_list_id);
                assert(self.lists[i].relate_region(self.regions));
            };

            // --- per-loose: new entry from the axiom; others preserved;
            // the popped slot is disjoint from every loose slot ---
            assert forall|lid2: LooseId| #[trigger] self.loose.dom().contains(lid2) implies {
                &&& self.loose[lid2].inv()
                &&& self.loose[lid2].global_inv(self.regions)
                &&& self.loose[lid2].frame_link_inv(self.regions)
                &&& self.regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                    == 0
            } by {
                if lid2 != new_loose {
                    assert(old_self.loose.dom().contains(lid2));
                    assert(old_self.loose[lid2] == self.loose[lid2]);
                    assert(old_self.loose[lid2].global_inv(old_regions));
                    assert(old_self.loose[lid2].frame_link_inv(old_regions));
                    assert(old_regions.slot_owners[self.loose[lid2].slot_index].inner_perms.in_list.value()
                        == 0);
                }
            };

            // --- disjointness ---
            assert(self.lists.dom() =~= old_self.lists.dom());
            assert(self.cursors.dom() =~= old_self.cursors.dom());
            assert(self.lists.dom().disjoint(self.cursors.dom()));

            // --- per-cursor: operating cursor rebuilt; others preserved ---
            assert forall|cid: CursorId| #[trigger] self.cursors.dom().contains(cid) implies {
                &&& self.cursors[cid].list_own.inv()
                &&& self.cursors[cid].inv_region(self.regions)
            } by {
                if cid == id {
                    assert(self.cursors[id].list_own == owner);
                    assert(self.cursors[id].index == n);
                    assert(owner.list.len() == old_self.cursors[id].list_own.list.len() - 1);
                } else {
                    assert(old_self.cursors.dom().contains(cid));
                    assert(old_self.cursors[cid] == self.cursors[cid]);
                    assert(old_self.cursors[cid].list_own.inv());
                    assert(old_self.cursors[cid].inv_region(old_regions));
                    assert(self.cursors[cid].list_own.relate_region(old_regions));
                    assert(self.cursors[cid].list_own.list_id != old_list_id);
                    assert(self.cursors[cid].list_own.relate_region(self.regions));
                }
            };

            // --- cross list/cursor uniqueness ---
            assert forall|id2: ListId, cid: CursorId|
                self.lists.dom().contains(id2) && self.cursors.dom().contains(cid)
                    && self.lists[id2].list_id == self.cursors[cid].list_own.list_id
                    && self.lists[id2].list_id != 0 implies false by {
                assert(old_self.lists.dom().contains(id2));
                assert(old_self.lists[id2] == self.lists[id2]);
                if cid == id {
                    assert(self.cursors[id].list_own.list_id == old_list_id);
                    assert(self.lists[id2].list_id != old_list_id);
                } else {
                    assert(old_self.cursors.dom().contains(cid));
                    assert(old_self.cursors[cid] == self.cursors[cid]);
                }
            };

            // --- cursor×cursor uniqueness ---
            assert forall|cid1: CursorId, cid2: CursorId|
                self.cursors.dom().contains(cid1) && self.cursors.dom().contains(cid2)
                    && self.cursors[cid1].list_own.list_id == self.cursors[cid2].list_own.list_id
                    && self.cursors[cid1].list_own.list_id != 0 implies cid1 == cid2 by {
                assert(old_self.cursors.dom().contains(cid1));
                assert(old_self.cursors.dom().contains(cid2));
                assert(self.cursors[cid1].list_own.list_id
                    == old_self.cursors[cid1].list_own.list_id);
                assert(self.cursors[cid2].list_own.list_id
                    == old_self.cursors[cid2].list_own.list_id);
            };

            // --- loose-internal slot disjointness ---
            assert forall|l1: LooseId, l2: LooseId|
                self.loose.dom().contains(l1) && self.loose.dom().contains(l2)
                    && self.loose[l1].slot_index == self.loose[l2].slot_index implies l1 == l2 by {
                if l1 == new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l2));
                    assert(self.loose[l2].slot_index != popped_idx);
                } else if l2 == new_loose && l1 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(self.loose[l1].slot_index != popped_idx);
                } else if l1 != new_loose && l2 != new_loose {
                    assert(old_self.loose.dom().contains(l1));
                    assert(old_self.loose.dom().contains(l2));
                }
            };
            Option::Some(new_loose)
        }
    }
}

} // verus!
