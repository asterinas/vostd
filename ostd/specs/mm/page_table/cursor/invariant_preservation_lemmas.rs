/// CursorOwner-level preservation lemmas for transient `MetaRegionOwners`
/// updates that affect at most one slot. Phase 3b of the `paths_in_pt`
/// refactor, where map/unmap operations insert or remove a single tree path
/// from a single frame slot and must show that the global
/// `Cursor::invariants` survives the edit.
///
/// Both directions are now proven: `metaregion_preserved_under_path_insert`
/// (used by `map`, the huge-page split) and
/// `metaregion_preserved_under_path_remove` (the foundational lemma the
/// `unmap` `paths_in_pt.remove` rewrite — Phase 3b stages 2–4 — will use;
/// the exec/postcondition rewrites that wire it in are still pending).
///
/// Each lemma here lifts [`EntryOwner`]-level preservation facts (from
/// `entry_owners.rs`) over the full cursor tree.
use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::REF_COUNT_UNUSED;
use crate::mm::page_size;
use crate::mm::page_table::*;
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_owners::PageUsage;
use crate::specs::mm::frame::{mapping::frame_to_index, meta_region_owners::MetaRegionOwners};
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::cursor::owners::{CursorContinuation, CursorOwner};
use crate::specs::mm::page_table::node::entry_owners::EntryOwner;
use crate::specs::mm::page_table::owners::{OwnerSubtree, PageTableOwner, vaddr_of};

verus! {

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// Tree-wide predicate: no page-table node in either the cursor's tree
    /// children or its continuation path has metadata slot index `idx`.
    /// Used as the "sanity" precondition of the path-insert preservation
    /// lemma: the only kind of entry it can touch with the new path is a
    /// frame. Callers satisfy it by observing that page-table node metadata
    /// lives in `FRAME_METADATA_RANGE`, which is disjoint from any data-frame
    /// paddr (where `paths_in_pt` inserts happen).
    pub open spec fn no_node_at_idx(self, idx: usize) -> bool {
        &&& self.map_full_tree(
            |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
                e.is_node() && e.meta_slot_paddr() is Some ==> frame_to_index(
                    e.meta_slot_paddr()->0,
                ) != idx,
        )
        &&& forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> {
                let e = self.continuations[i].entry_own;
                e.is_node() && e.meta_slot_paddr() is Some ==> frame_to_index(
                    e.meta_slot_paddr()->0,
                ) != idx
            }
    }

    /// Pointwise conjunction of two tree-wide predicates: if `self.map_full_tree(f)`
    /// and `self.map_full_tree(guard)` hold, then `self.map_full_tree(f && guard)`
    /// holds. A thin wrapper around `OwnerSubtree::lemma_map_implies_and` applied per
    /// continuation + per child; extracted so callers don't have to re-derive
    /// the same nested `assert forall ... by { lemma_map_implies_and(...) }` block.
    pub proof fn and_map_full_tree(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        guard: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            self.inv(),
            self.map_full_tree(f),
            self.map_full_tree(guard),
        ensures
            self.map_full_tree(|e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f(e, p) && guard(e, p)),
    {
        let combined = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f(e, p) && guard(e, p);
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(
            combined,
        ) by {
            let cont = self.continuations[i];
            reveal(CursorContinuation::inv_children);
            assert forall|j: int|
                #![trigger cont.children[j]]
                0 <= j < cont.children.len()
                    && cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
            cont.path().push_tail(j as usize), combined) by {
                cont.inv_children_unroll(j);
                OwnerSubtree::lemma_map_implies_and(
                    cont.children[j].unwrap(),
                    cont.path().push_tail(j as usize),
                    f,
                    guard,
                    combined,
                );
            };
        };
    }

    /// Discharge `no_node_at_idx(changed_idx)` from the observation that
    /// `changed_idx` is not a page-table slot. Active node entries always
    /// occupy metadata slots whose usage is `PageTable`, so any node in the
    /// cursor tree must have a different slot index than `changed_idx`.
    ///
    /// Callers doing a `paths_in_pt.insert` at a frame's data-slot
    /// (e.g., `map` and the huge-page split) use this helper to
    /// satisfy the precondition of
    /// [`Self::metaregion_preserved_under_path_insert`].
    pub proof fn no_node_at_idx_from_slot_key(self, regions: MetaRegionOwners, changed_idx: usize)
        requires
            self.inv(),
            regions.inv(),
            self.metaregion_sound(regions),
            regions.slots.contains_key(changed_idx),
            regions.slot_owners[changed_idx].usage != PageUsage::PageTable,
        ensures
            self.no_node_at_idx(changed_idx),
    {
        let msp = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let target = |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            e.is_node() && e.meta_slot_paddr() is Some ==> frame_to_index(
                e.meta_slot_paddr().unwrap(),
            ) != changed_idx;

        self.map_children_implies(msp, target);

        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies {
            let e = self.continuations[i].entry_own;
            e.is_node() && e.meta_slot_paddr() is Some ==> frame_to_index(
                e.meta_slot_paddr().unwrap(),
            ) != changed_idx
        } by {
            let entry = self.continuations[i].entry_own;
            if entry.is_node() && entry.meta_slot_paddr() is Some {
                let idx = frame_to_index(entry.meta_slot_paddr().unwrap());
                if idx == changed_idx {
                    assert(false);
                }
            }
        };
    }

    /// Preservation of the cursor-level metaregion invariants when the only
    /// change to `regions` is the **insertion** of a new path into the
    /// `paths_in_pt` set at a single slot.
    pub proof fn metaregion_preserved_under_path_insert(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        changed_idx: usize,
        new_path: TreePath<NR_ENTRIES>,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.inv(),
            regions0.slot_owners.contains_key(changed_idx),
            regions1.slots == regions0.slots,
            regions1.slot_owners.dom() =~= regions0.slot_owners.dom(),
            forall|i: usize|
                #![trigger regions1.slot_owners[i]]
                i != changed_idx ==> regions0.slot_owners[i] == regions1.slot_owners[i],
            regions1.slot_owners[changed_idx].inner_perms
                == regions0.slot_owners[changed_idx].inner_perms,
            regions1.slot_owners[changed_idx].slot_vaddr
                == regions0.slot_owners[changed_idx].slot_vaddr,
            regions1.slot_owners[changed_idx].usage == regions0.slot_owners[changed_idx].usage,
            regions1.slot_owners[changed_idx].paths_in_pt
                == regions0.slot_owners[changed_idx].paths_in_pt.insert(new_path),
            self.no_node_at_idx(changed_idx),
        ensures
            self.metaregion_sound(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        let guard = |entry: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            entry.is_node() && entry.meta_slot_paddr() is Some ==> frame_to_index(
                entry.meta_slot_paddr().unwrap(),
            ) != changed_idx;
        let f_strong = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            f(entry, path) && guard(entry, path);

        self.and_map_full_tree(f, guard);
        self.map_children_implies(f_strong, g);

        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i
                < NR_LEVELS implies self.continuations[i].entry_own.metaregion_sound(regions1) by {
            let cont_entry = self.continuations[i].entry_own;
            if cont_entry.meta_slot_paddr() is Some {
                // Same sub-page bridge as above (continuations branch).
                cont_entry.metaregion_sound_one_slot_changed(regions0, regions1, changed_idx);
            }
        };
    }

    /// Tree-wide guard for the **removal** of `removed_path` from
    /// `paths_in_pt[changed_idx]`. Mirror of [`Self::no_node_at_idx`] but
    /// also rules out any *frame* entry that still maps `changed_idx`
    /// through exactly `removed_path` — removing that path would break
    /// such an entry's `metaregion_sound` (`paths_in_pt.contains(path)`).
    /// A node at `changed_idx` is also excluded (its `paths_in_pt` is a
    /// singleton, so removal would falsify `== set![path]`). Callers
    /// (the `unmap` site) satisfy this because the entry whose path is
    /// being removed has just left the cursor tree.
    pub open spec fn path_removable_at_idx(
        self,
        idx: usize,
        removed_path: TreePath<NR_ENTRIES>,
    ) -> bool {
        &&& self.map_full_tree(
            |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
                e.meta_slot_paddr() is Some && frame_to_index(e.meta_slot_paddr()->0) == idx
                    ==> !e.is_node() && (e.is_frame() ==> e.path != removed_path),
        )
        &&& forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> {
                let e = self.continuations[i].entry_own;
                e.meta_slot_paddr() is Some && frame_to_index(e.meta_slot_paddr()->0) == idx
                    ==> !e.is_node() && (e.is_frame() ==> e.path != removed_path)
            }
    }

    /// Tree-wide predicate: no *frame* entry in the cursor tree has
    /// tree path exactly `removed_path`. After `unmap`'s
    /// `replace_cur_entry(Child::None)`, the entry at the cursor path
    /// (`== removed_path`) is absent, so by tree-path correctness no
    /// frame entry can carry that path. This is the one structural
    /// residual of the `paths_in_pt`-removal refactor.
    pub open spec fn no_frame_with_path(self, removed_path: TreePath<NR_ENTRIES>) -> bool {
        &&& self.map_full_tree(
            |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>| e.is_frame() ==> e.path != removed_path,
        )
        &&& forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> {
                let e = self.continuations[i].entry_own;
                e.is_frame() ==> e.path != removed_path
            }
    }

    /// Establishes [`Self::no_frame_with_path`] from the observation that
    /// **no current view mapping starts at `vaddr_of(removed_path)`**.
    ///
    /// This is the standalone "lift `path_correct_pred` + uniqueness over
    /// the cursor tree" lemma the `unmap` site needs. Each continuation
    /// child subtree is `pt_inv` + path-correct (via
    /// [`PageTableOwner::pt_inv_implies_path_correct`]), and its mappings
    /// all bubble up into `self@.mappings`; so by
    /// [`PageTableOwner::no_frame_with_path_rec`] a frame entry carrying
    /// `removed_path` would force a mapping starting at
    /// `vaddr_of(removed_path)` into `self@.mappings` — exactly what the
    /// hypothesis forbids. Continuation *entries* are nodes, so the
    /// continuations conjunct is vacuous.
    pub proof fn no_frame_with_path_from_no_view_mapping(self, removed_path: TreePath<NR_ENTRIES>)
        requires
            self.inv(),
            forall|m: Mapping|
                #![trigger self@.mappings.contains(m)]
                self@.mappings.contains(m) ==> m.va_range.start != vaddr_of::<C>(removed_path),
        ensures
            self.no_frame_with_path(removed_path),
    {
        broadcast use CursorContinuation::group_lemmas;

        let g = |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            e.is_frame() ==> e.path != removed_path;

        // map_full_tree(g): each continuation child subtree is pt_inv,
        // path-correct, and its mappings sit inside self@.mappings.
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(g) by {
            self.inv_continuation(i);
            let cont = self.continuations[i];
            reveal(CursorContinuation::inv_children);
            assert forall|j: int|
                #![trigger cont.children[j]]
                0 <= j < cont.children.len()
                    && cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
            cont.path().push_tail(j as usize), g) by {
                cont.inv_children_unroll(j);
                cont.pt_inv_children_unroll(j);
                cont.inv_children_rel_unroll(j);
                let child = cont.children[j].unwrap();
                let child_path = cont.path().push_tail(j as usize);
                // child.value.path == child_path (inv_children_rel) and
                // child.value.path.inv() (EntryOwner::inv_base).
                // L1: pt_inv ⟹ tree-wide path correctness.
                PageTableOwner::<C>::pt_inv_implies_path_correct(child, child_path);
                // Every mapping of this child subtree is in self@.mappings.
                assert forall|m: Mapping|
                    #![trigger self@.mappings.contains(m)]
                    PageTableOwner(child).view_rec(child_path).contains(
                        m,
                    ) implies self@.mappings.contains(m) by {
                    self.lemma_view_mappings_intro(m, i);
                };
                // L-rec: no frame entry in this subtree carries removed_path.
                PageTableOwner(child).no_frame_with_path_rec(
                    child_path,
                    removed_path,
                    self@.mappings,
                );
            };
        };

        // Continuation entries are page-table nodes ⟹ not frames.
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies {
            let e = self.continuations[i].entry_own;
            e.is_frame() ==> e.path != removed_path
        } by {
            self.inv_continuation(i);
        };
    }

    /// Bridge: `path_removable_at_idx` follows from the (mechanically
    /// dischargeable) no-node-at-idx fact plus the structural
    /// no-frame-with-`removed_path` fact. Per entry mapping `idx`:
    /// `no_node_at_idx` forces `!is_node`, and `no_frame_with_path`
    /// forces `is_frame ==> path != removed_path` — exactly the
    /// `path_removable_at_idx` conjunction.
    pub proof fn path_removable_from_no_node_and_no_frame_path(
        self,
        idx: usize,
        removed_path: TreePath<NR_ENTRIES>,
    )
        requires
            self.inv(),
            self.no_node_at_idx(idx),
            self.no_frame_with_path(removed_path),
        ensures
            self.path_removable_at_idx(idx, removed_path),
    {
        let nn = |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            e.is_node() && e.meta_slot_paddr() is Some ==> frame_to_index(
                e.meta_slot_paddr().unwrap(),
            ) != idx;
        let nf = |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            e.is_frame() ==> e.path != removed_path;
        let r = |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            e.meta_slot_paddr() is Some && frame_to_index(e.meta_slot_paddr().unwrap()) == idx
                ==> !e.is_node() && (e.is_frame() ==> e.path != removed_path);

        // Pointwise: nn(e) && nf(e) ==> r(e).
        // map_full_tree halves -> combined -> r.
        self.and_map_full_tree(nn, nf);
        self.map_children_implies(
            |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| nn(e, p) && nf(e, p),
            r,
        );

        // Continuation-entry halves combine directly.
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies {
            let e = self.continuations[i].entry_own;
            e.meta_slot_paddr() is Some && frame_to_index(e.meta_slot_paddr().unwrap()) == idx
                ==> !e.is_node() && (e.is_frame() ==> e.path != removed_path)
        } by {
            let e = self.continuations[i].entry_own;
        }
    }

    /// Preservation of the cursor-level metaregion invariants when the
    /// only change to `regions` is the **removal** of `removed_path`
    /// from the `paths_in_pt` set at a single slot. Dual of
    /// [`Self::metaregion_preserved_under_path_insert`]; the missing
    /// half of the deferred `paths_in_pt` refactor that `unmap` needs.
    ///
    /// Removal is *not* monotone (unlike insert): the guard
    /// [`Self::path_removable_at_idx`] is what makes it sound — no live
    /// tree entry still needs `removed_path` at `changed_idx`.
    pub proof fn metaregion_preserved_under_path_remove(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        changed_idx: usize,
        removed_path: TreePath<NR_ENTRIES>,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.inv(),
            regions0.slot_owners.contains_key(changed_idx),
            regions1.slots == regions0.slots,
            regions1.slot_owners.dom() =~= regions0.slot_owners.dom(),
            forall|i: usize|
                #![trigger regions1.slot_owners[i]]
                i != changed_idx ==> regions0.slot_owners[i] == regions1.slot_owners[i],
            regions1.slot_owners[changed_idx].inner_perms
                == regions0.slot_owners[changed_idx].inner_perms,
            regions1.slot_owners[changed_idx].slot_vaddr
                == regions0.slot_owners[changed_idx].slot_vaddr,
            regions1.slot_owners[changed_idx].usage == regions0.slot_owners[changed_idx].usage,
            regions1.slot_owners[changed_idx].paths_in_pt
                == regions0.slot_owners[changed_idx].paths_in_pt.remove(removed_path),
            self.path_removable_at_idx(changed_idx, removed_path),
        ensures
            self.metaregion_sound(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        let guard = |entry: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            entry.meta_slot_paddr() is Some && frame_to_index(entry.meta_slot_paddr().unwrap())
                == changed_idx ==> !entry.is_node() && (entry.is_frame() ==> entry.path
                != removed_path);
        let f_strong = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            f(entry, path) && guard(entry, path);

        self.and_map_full_tree(f, guard);
        self.map_children_implies(f_strong, g);

        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i
                < NR_LEVELS implies self.continuations[i].entry_own.metaregion_sound(regions1) by {
            let cont_entry = self.continuations[i].entry_own;
            if cont_entry.meta_slot_paddr() is Some {
                let eidx = frame_to_index(cont_entry.meta_slot_paddr().unwrap());
                if eidx != changed_idx {
                    cont_entry.metaregion_sound_one_slot_changed(regions0, regions1, changed_idx);
                } else {
                    if cont_entry.is_frame() {
                        cont_entry.frame_sub_pages_valid_preserved_at_own_slot(regions0, regions1);
                    }
                }
            }
        };
    }

    /// Packages the `take_next` frame-unmap preservation proof after
    /// `paths_in_pt` removes the unmapped frame path from one metadata slot.
    pub proof fn take_next_remove_path_preserves_metaregion(
        self,
        owner_before_replace: Self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        removed_idx: usize,
        removed_path: TreePath<NR_ENTRIES>,
        target: Mapping,
    )
        requires
            self.inv(),
            owner_before_replace.inv(),
            owner_before_replace.in_locked_range(),
            self.metaregion_sound(regions0),
            regions0.inv(),
            regions0.slot_owners.contains_key(removed_idx),
            regions0.slots.contains_key(removed_idx),
            regions0.slot_owners[removed_idx].usage != PageUsage::PageTable,
            self@.mappings == owner_before_replace@.mappings - PageTableOwner(
                owner_before_replace.cur_subtree(),
            )@.mappings,
            PageTableOwner(owner_before_replace.cur_subtree())@.mappings == set![target],
            owner_before_replace.cur_subtree().value().path == removed_path,
            regions1.slots == regions0.slots,
            regions1.slot_owners.dom() =~= regions0.slot_owners.dom(),
            forall|i: usize|
                #![trigger regions1.slot_owners[i]]
                i != removed_idx ==> regions0.slot_owners[i] == regions1.slot_owners[i],
            regions1.slot_owners[removed_idx].inner_perms
                == regions0.slot_owners[removed_idx].inner_perms,
            regions1.slot_owners[removed_idx].slot_vaddr
                == regions0.slot_owners[removed_idx].slot_vaddr,
            regions1.slot_owners[removed_idx].usage == regions0.slot_owners[removed_idx].usage,
            regions1.slot_owners[removed_idx].paths_in_pt
                == regions0.slot_owners[removed_idx].paths_in_pt.remove(removed_path),
        ensures
            self.metaregion_sound(regions1),
    {
        self.no_node_at_idx_from_slot_key(regions0, removed_idx);

        owner_before_replace.cur_subtree_eq_filtered_mappings_path();

        let ghost sv = vaddr_of::<C>(removed_path) as int;
        let ghost sz = page_size(owner_before_replace.level) as int;
        assert(sz > 0) by {
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                owner_before_replace.level,
            );
        };
        assert forall|mm: Mapping| #[trigger] self@.mappings.contains(mm) implies mm.va_range.start
            != sv by {};

        self.no_frame_with_path_from_no_view_mapping(removed_path);
        self.path_removable_from_no_node_and_no_frame_path(removed_idx, removed_path);
        self.metaregion_preserved_under_path_remove(regions0, regions1, removed_idx, removed_path);
    }
}

} // verus!
