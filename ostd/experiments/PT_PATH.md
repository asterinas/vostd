# The `pt_path` protocol, for `mm` developers

*Audience: you know `MetaRegionOwners`, `paths_in_pt`, `accounting_inv`. You have
not written a state machine or a PCM. This maps the experiment in
[`pt_path_tsm.rs`](pt_path_tsm.rs) onto machinery you already use.*

---

## 1. The one thing to understand first

Today, "this PTE holds a reference to frame *X*" is recorded as **ghost data
describing the world**: a path is inserted into `MetaSlotOwner.paths_in_pt`, and
a separate invariant asserts that the description matches the hardware:

```rust
// embedding/mod.rs, accounting_inv
rc == handle_count(frames, idx) + so.paths_in_pt.len()
    + segment_cover_count(segments, index_to_frame(idx))
```

The set and the count are two independent facts, held in agreement by a proof
obligation that every operation must re-discharge.

In the token protocol, the same statement is recorded as **a linear object the
PTE owns**. An installed entry physically holds one `FrameRc::reader` token. The
token cannot be copied, forged, or dropped silently — so the count and the set of
holders cannot drift apart, and there is nothing to re-discharge.

Everything below follows from that one substitution: *a ghost description of who
holds a reference becomes an object that the holder holds.*

---

## 2. Correspondence table

| today (sequential) | `pt_path` protocol |
|---|---|
| `so.paths_in_pt: Set<TreePath<NR_ENTRIES>>` | one `FrameRc::reader` token per installed entry, held *in* the entry — a reference, **not** a path |
| `paths_in_pt.len()` — the `P` in `rc == H + P + cover` | the number of those tokens; never computed, never needed |
| `rc == H + P + cover` (`accounting_inv` clause) | `counter == \|reader\|`, one clause of `FrameRc`'s invariant |
| `paths_in_pt.insert(new_path)` in a cursor lemma | `PtNode::install` — the token *moves into* the entry |
| `paths_in_pt.remove(removed_path)` | `PtNode::uninstall` — the token *moves out* |
| `UNUSED ⟹ paths_in_pt.is_empty()` (guard clause) | `no_readers_outside_shared` — an invariant of `FrameRc` |
| "active head": some user ⟹ `rc` in valid range | `reader_implies_shared` — a *property* you invoke, holding a token |
| `Tracked(regions): &mut MetaRegionOwners` threaded through every op | a per-slot `AtomicInvariant`, opened for one slot at a time |
| `Child::into_pte` consuming a `Frame<M>` handle | `FrameRc::do_clone` mints a reference; `PtNode::install` takes custody |

The right-hand column has no analogue of
[`invariant_preservation_lemmas.rs`](../specs/mm/page_table/cursor/invariant_preservation_lemmas.rs)
— the `paths_in_pt.insert` / `.remove` rewrite lemmas exist to keep the
description in step with the count, and there is no description to keep in step.

---

## 3. What an installed entry actually is

```rust
tokenized_state_machine!(PtNode {
    fields {
        #[sharding(constant)]       rc_instance: InstanceId,
        #[sharding(variable)]       ref_view: Option<FrameRc::reader<()>>,
        #[sharding(storage_option)] ref_held: Option<FrameRc::reader<()>>,
    }
    #[invariant] fn view_matches_held(&self) -> bool { self.ref_view == self.ref_held }
    ...
})
```

**The token is not a path.** This is the one place the analogy with
`paths_in_pt` misleads, so it is worth stating flatly: `paths_in_pt` is a set of
`TreePath`s and each element says *where*; the token carries no location at all.
It says only "a reference to that frame is held **here**". Where *here* is stays
implicit in which `PtNode` instance you are holding, and is deliberately not
modelled.

("PtPath" in `TOKENIZATION_PLAN.md` names the *kind* of reference — one held by a
page table, as against a `Frame` handle or a `Segment` cover. It does not name a
path value. The file is called `pt_path_tsm.rs` for that reason.)

So the two fields are: **`ref_held` is the reference itself; `ref_view` is a ghost
note recording which reference it is.** The invariant ties them together.

Why two fields for one thing? Because you cannot *borrow* something you cannot
name. Reaching a fact about the frame requires borrowing the reference out of the
entry, and the borrowing rule demands the caller name what it is borrowing.
`ref_view` is what lets it.

`rc_instance` says *which frame* the reference belongs to — the same job the
enclosing slot index does for a `paths_in_pt` entry.

---

## 4. `map`, step by step

`probe_map_step` is `cursor::map` in miniature:

```rust
if let Some(tok) = tsm_try_inc_ref_count(slot, idx, rc, handle) {   // CAS n → n+1
    proof { pt_inst.install(t, ref_view, t); }                        // entry takes custody
}
```

Two moves, and it is worth being clear about which needs to be atomic:

- the **refcount bump** touches a cell other CPUs are also touching, so it is a
  CAS inside `open_atomic_invariant!` — the token analogue of "the refcount is
  shared, so `&mut` on `inner_perms.ref_count` was always a fiction";
- the **entry install** touches node memory you hold the node lock for, so it
  needs no atomicity at all. That is why `ref_view` is passed `&mut`: exclusive
  access *is* the lock.

Compare today's version, where `&mut MetaRegionOwners` grants exclusive access to
*the entire region* for both moves. The protocol splits that single fiction into
one genuinely-shared cell and one genuinely-exclusive one.

---

## 5. The one real behavioural difference: the in-flight window

Between the CAS and the install, the caller holds a reference that no registry
owns. Another CPU reading `ref_count` sees `n+1` while only `n` users exist.

*(The CAS is specific to the example, which clones a reference. The real `map`
transfers one instead and touches no atomic — see §8. The window itself is real
either way: in `map` it sits between `item_into_raw` and the PTE write, and the
current proof already names it `frame_obligations`.)*

This is not a flaw introduced by the protocol — it is what the hardware has
always done, and the sequential proof simply could not see it, because `&mut
MetaRegionOwners` meant no other thread existed. Making the sharing honest makes
the window visible.

During that window:

- `FrameRc`'s `counter == |reader|` — **still exact.** A token in a thread's hand
  is still a token.
- `PtNode`'s `ref_view == ref_held` — **still exact.** Both are still `None`.
- `rc == H + P + cover` — **transiently false.** The reference is in a hand, and
  `H`, `P` and `cover` only count references sitting in registries.

**Consequence for anyone touching `accounting_inv` or its successor:** the
accounting equation is a *quiescent-boundary* property, not a running invariant.
It can be asserted where operations begin and end; it cannot be asserted as
something true at every instant, because it isn't. A concurrent version needs
either that scoping made explicit, or a fourth term counting in-flight
references.

What makes the window harmless is conservation: the reference is *somewhere* at
every instant. Linearity is what guarantees that, and it is the same guarantee
`frame_obligations` was hand-built to provide.

---

## 6. What this does not change

- **`in_scope`, `OwnerSubtree::inv`, and the cursor tree-level proofs** are
  untouched. They are about page-table *structure* (which node is settled, which
  subtree a cursor owns), not about reference accounting.
- **`paths_in_pt` as a source of path identity.** The token records *that* a
  reference exists, not *where in the tree* it lives. Anything needing the actual
  `TreePath` still needs a path — the token deliberately does not carry one.
- **`Segment` covers and `Frame` handles.** Only the PT-path leg is modelled
  here; `H` and `cover` would get the same treatment (a token per handle, a token
  per cover), which is Phases 5–6 of `TOKENIZATION_PLAN.md`.

---

## 7. The costs, honestly

Two taxes, both small but recurring, both paid per *protocol boundary* rather
than per operation:

1. **A ghost copy per consumer.** The entry must carry `ref_view` alongside the
   reference it holds, because a borrow must be nameable.
2. **An explicit re-export per crossing.** A machine's invariants are invisible
   to callers — only what a transition or property `assert`s becomes a
   postcondition. Both `path_guard` and `uninstall` needed their own
   `assert(tok.instance_id() == pre.rc_instance)`; without it the token comes out
   anonymous and the frame machine refuses it.

Against that: `install`/`uninstall` have no proof obligations at all, and the
cross-layer fact — *this entry's presence implies the frame's count includes it*
— is three lines, where today it is an `accounting_inv` clause re-discharged by
every `step_*` proof.

---

## 8. How this would fit into the real `map`

`probe_map_step` is deliberately a two-line example. Mapping it onto
[`VmSpace::map`](../src/mm/vm_space.rs) turns up one thing the example gets
*wrong about `map` specifically*, and it is worth knowing before anyone
generalises from it.

### The example clones; the real `map` transfers

`probe_map_step` mints a fresh reference off a borrowed handle
(`tsm_try_inc_ref_count`, i.e. `do_clone`) and installs it. The real `map` does
not clone anything. Follow the ownership:

```rust
pub fn map(&mut self, frame: UFrame, prop: PageProperty)   // frame taken BY VALUE
```

1. the caller's `Frame` handle is consumed by `C::item_into_raw` — documented as
   *"the item will be forgotten after this function is called"*, so the reference
   it held survives as a bare `Paddr`, recorded meanwhile in
   `regions.frame_obligations`;
2. `Child::Frame(paddr, level, prop)` carries only that address — no handle;
3. [`Child::into_pte`](../src/mm/page_table/node/child.rs) builds the PTE (for
   the `PageTable` arm, `ManuallyDrop::new(node)` does the same forgetting);
4. [`Entry::replace`](../src/mm/page_table/node/entry.rs) writes `self.pte` and
   the caller inserts the path into `paths_in_pt`.

Net effect on the newly-mapped frame: `H − 1`, `P + 1`, and **`ref_count` is
never touched.** There is no atomic, because nothing was created — one
reference simply changed hands.

In token terms that is *simpler* than the example: move the `FrameRc::reader`
token out of the `Frame` handle and into the entry. One `PtNode::install`, and
**no `FrameRc` transition at all**.

So `probe_map_step`'s shape belongs to the paths that genuinely duplicate a
reference — `clone_item` on the fork/COW path, and `get_from_in_use` — not to
`map`.

### Where `map`'s refcount atomic actually is

On the **evicted** mapping. `map` is really replace: `Entry::replace` hands back
the old `Child`, `VmSpace::map` matches it as `PageTableFrag::Mapped { va, item }`,
issues the TLB flush, and drops it. That drop is the `fetch_sub` — so the
transitions `map` fires are `PtNode::uninstall` (old reference out),
`PtNode::install` (new reference in), and `dec_basic`/`dec_to_zero` on the old
frame *after the flush*.

The ordering matters and is already load-bearing in the exec code: the reference
must outlive the TLB flush, which is exactly why the old item is returned to the
caller rather than dropped inside `replace`.

### `frame_obligations` is the in-flight window, already named

Step 1 above leaves a reference owned by nobody — held as a raw `Paddr` between
`item_into_raw` and the PTE write. That is precisely the in-flight window of §5,
and the current proof already tracks it: `frame_obligations` exists to record
"a reference is out there, unowned, and must be redeemed."

In the token model the token *is* that record, so `frame_obligations` has nothing
left to do — which is what Phase 6 of `TOKENIZATION_PLAN.md` means by "the
`frame_obligations` field + its 3 axioms are subsumed by the reader multiset."

### Plumbing that the example skips

- **One entry vs 512.** `PtNode` models a single entry. A real node would carry
  `#[sharding(storage_map)] refs: Map<usize, FrameRc::reader<..>>` keyed by entry
  index — one instance per *node*, not per entry — so it lines up with `Entry`'s
  `self.idx`.
- **What justifies `&mut`.** The example passes `ref_view` as `&mut`, standing in
  for exclusive access. In the real cursor that is the node lock, tracked today
  by `owner.nodes_locked(*guards)` and destined to become a real lock token under
  Stage C.
- **Where the deposit goes.** The natural site is the `proof` block inside
  `Entry::replace` that today performs `new_meta_slot.paths_in_pt =
  set![new_owner.path]` — the token deposit replaces that assignment.
- **Levels and huge pages.** A `Child` may be a page table node or a huge frame,
  and `replace` is also reached from the huge-page split path. Each of those is a
  reference movement too, and each needs its own `install`/`uninstall` pairing;
  the example covers only the base-page frame case.
