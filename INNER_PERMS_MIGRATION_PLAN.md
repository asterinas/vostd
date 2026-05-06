# Migration plan: removing `MetadataInnerPerms` dual-presence

## Problem statement

`MetadataInnerPerms` is currently held *simultaneously* in two tracked locations whenever a frame is "forgotten" into a `SegmentOwner` / `UniqueFrameOwner`:

- `regions.slot_owners[idx].inner_perms` (in [`MetaRegionOwners`](ostd/specs/mm/frame/meta_region_owners.rs#L50-L53)), with spec value forced into sync via [`MetaSlotOwner::sync_inner`](ostd/specs/mm/frame/meta_owners.rs#L352-L353).
- The owner's perm structure (`MetaPerm<M> = cast_ptr::PointsTo<MetaSlot, Metadata<M>>` for segments, `meta_perm: PointsTo<MetaSlot, Metadata<M>>` for unique frames), constructed by [`MetaSlot::cast_perm`](ostd/src/mm/frame/meta.rs#L357).

Both holders have `MetadataInnerPerms` with matching atomic ids. Verus's resource logic treats this as a duplication once `tracked_remove` exposes both — bodies operating on `(SegmentOwner, MetaRegionOwners)` pairs verify vacuously rather than soundly. The [`take_inner_perms`](ostd/specs/mm/frame/meta_owners.rs#L344-L350) / [`sync_inner`](ostd/specs/mm/frame/meta_owners.rs#L352-L353) axioms paper over the gap; they're effectively unsoundness escape hatches.

The fix is to pick **one** holder for `inner_perms` and have the other reference it (by id only, in spec). This plan picks `regions.slot_owners[idx].inner_perms` as the canonical home.

## Target invariant

For any forgotten frame at index `idx`:
- `regions.slot_owners[idx].inner_perms` holds the **unique** tracked `MetadataInnerPerms`.
- The forgetter (`SegmentOwner`, `UniqueFrameOwner`) holds **only** the slot pointer permission `simple_pptr::PointsTo<MetaSlot>` — no `inner_perms`.
- Atomic-modifying operations access `inner_perms` through `regions.slot_owners[idx]`, never via the forgetter.

## Phase 1 — `meta.rs` foundations

**Goal:** retire the `take_inner_perms` / `sync_inner` axiom dance in favor of real tracked moves.

### 1.1 Add a typed slot-pointer permission

Introduce `pub type SlotPerm<M> = (simple_pptr::PointsTo<MetaSlot>, PhantomData<M>)` (or a small wrapper struct) so `M`-tagging survives without `cast_ptr`'s `inner_perms` baggage.

### 1.2 Refactor `MetaSlot::get_from_unused`

Current signature ([meta.rs:289](ostd/src/mm/frame/meta.rs#L289)):
```rust
fn get_from_unused(...) -> Result<(PPtr<Self>, Tracked<PointsTo<MetaSlot, Metadata<M>>>), GetFrameError>
```

New signature:
```rust
fn get_from_unused(...) -> Result<(PPtr<Self>, Tracked<simple_pptr::PointsTo<MetaSlot>>), GetFrameError>
```

Body change: drop the [`take_inner_perms`](ostd/src/mm/frame/meta.rs#L304) / [`sync_inner`](ostd/src/mm/frame/meta.rs#L353) sandwich entirely. Modify the atomic via `&mut regions.slot_owners[idx].inner_perms.ref_count` directly. The local `inner_perms` variable disappears. `cast_perm` is no longer called here.

`get_from_unused_perm_spec` is updated to assert only the `simple_pptr` properties; it stops claiming `wf(perm.inner_perms)`.

### 1.3 Retire `take_inner_perms` and `sync_inner`

Once all callers are migrated (Phases 2–3), delete these axioms. They're the source of the dual-presence — keeping them invites regression.

### 1.4 New helper: `with_slot_inner_perms`

For operations that need `&mut MetadataInnerPerms` to perform atomic ops, introduce:
```rust
proof fn with_slot_inner_perms_mut<F, R>(
    tracked regions: &mut MetaRegionOwners,
    idx: usize,
    f: F,
) -> R
    where F: FnOnce(Tracked<&mut MetadataInnerPerms>) -> R
```

Or, more pragmatically given Verus's experimental `&mut`: a take/swap-out idiom where the caller `tracked_remove`s the `MetaSlotOwner`, mutates `slot_own.inner_perms` directly, and `tracked_insert`s it back. No spec axiom required because the move is real.

## Phase 2 — `Frame` (in `mod.rs`)

**Goal:** propagate the typed slot perm through `Frame::from_raw`, `borrow`, `borrow_perm`, and `Frame::TrackDrop`.

### 2.1 `Frame::from_raw`

Current signature uses `Tracked(perm): Tracked<&MetaPerm<M>>` ([mod.rs:590](ostd/src/mm/frame/mod.rs#L590)).

New: `Tracked(perm): Tracked<&simple_pptr::PointsTo<MetaSlot>>`. The function still needs `inner_perms` to verify (e.g., the `wf(slot_owners[idx])` precondition); that comes from `regions.slot_owners[idx].inner_perms` directly, which the body already has (`regions: &mut MetaRegionOwners`).

Update preconditions: the `perm.points_to.value().wf(slot_owner)` clause becomes `perm.value().wf(slot_owner)`. The `perm.points_to.is_init()` becomes `perm.is_init()`.

### 2.2 `Frame::TrackDrop` impl

[`Frame`'s constructor_spec / drop_tracked](ostd/src/mm/frame/mod.rs#L115-L183) bumps/decrements `slot_owners[idx].raw_count`. Already operates on `regions.slot_owners[idx]` exclusively — no change needed beyond updating any signatures that reference the old perm type.

### 2.3 `Frame::borrow*`, `Frame::inc_ref_count`

Audit every function that takes `Tracked<&MetaPerm<M>>` or `Tracked<&mut MetaPerm<M>>`; convert to the simple_pptr variant.

## Phase 3 — `SegmentOwner` (in `segment.rs`)

**Goal:** complete the in-place refactor we attempted, now that the `inner_perms` problem is solved at the source.

### 3.1 Type change

```rust
pub tracked struct SegmentOwner<M: AnyFrameMeta + ?Sized> {
    pub ghost range: Range<Paddr>,
    pub perms: Seq<simple_pptr::PointsTo<MetaSlot>>,
    pub _marker: PhantomData<M>,
}
```

### 3.2 `SegmentOwner::inv`

Drop `self.perms[i].wf(&self.perms[i].inner_perms)` ([line 136](ostd/src/mm/frame/segment.rs#L136)). The perm no longer has an `inner_perms` field.

### 3.3 `Segment::wf` and `relate_regions`

`relate_regions`'s `self.perms[i].points_to.value().wf(...)` becomes `self.perms[i].value().wf(...)`. **No more duplication contradiction.** The vacuous-bodies caveat doc comment ([line 152-181](ostd/src/mm/frame/segment.rs#L152-L181)) gets deleted.

### 3.4 Construction sites

- [`from_unused`](ostd/src/mm/frame/segment.rs#L660): `perms.tracked_push(frame_perm)` becomes a clean push of the now-typed `simple_pptr::PointsTo<MetaSlot>` returned by the new `get_from_unused`. No `MetaPerm` destructuring, no `inner_perms` to dispose of.
- [`split`](ostd/src/mm/frame/segment.rs#L815-L818), [`slice_ensures`](ostd/src/mm/frame/segment.rs#L572-L583): Seq subrange/split operates the same; just add the `_marker` field.

### 3.5 Body updates

- **`next`** ([line 948](ostd/src/mm/frame/segment.rs#L948)): the call to `Frame::from_raw` now passes the simple_pptr perm; `Frame::from_raw` uses `regions.slot_owners[idx].inner_perms` internally (Phase 2.1).
- **`drop`** ([line 897](ostd/src/mm/frame/segment.rs#L897)): the body calls `slot.ref_count.fetch_sub(Tracked(&mut slot_own.inner_perms.ref_count), 1)` — which already works on `slot_own = regions.slot_owners.tracked_remove(cur_idx)`. Once `slot_own.inner_perms` is the canonical holder, the `slot_perm.value().wf(slot_own)` assertion ([line 1069](ostd/src/mm/frame/segment.rs#L1069)) follows from `relate_regions` non-vacuously, and the `assert(slot_own.raw_count == 0)` branch in the if becomes reachable.
- The body needs to **decrement `raw_count`** before `drop_last_in_place` (the bug we identified). With the contradictions gone, this becomes a real verification obligation that has to be discharged by an actual tracked operation:
  ```rust
  proof {
      slot_own.raw_count = (slot_own.raw_count - 1) as usize;
  }
  ```
  inserted before [line 1078](ostd/src/mm/frame/segment.rs#L1078). The pre-existing assertion `slot_own.raw_count == 0` ([line 1060](ostd/src/mm/frame/segment.rs#L1060)) becomes correct.

## Phase 4 — `UniqueFrameOwner` (in `specs/mm/frame/unique.rs` and `src/mm/frame/unique.rs`)

**Goal:** apply the same treatment to the single-frame case.

### 4.1 Type change

```rust
pub tracked struct UniqueFrameOwner<M> {
    pub meta_own: M::Owner,
    pub meta_perm: simple_pptr::PointsTo<MetaSlot>,  // was PointsTo<MetaSlot, Metadata<M>>
    pub ghost slot_index: usize,
}
```

### 4.2 `UniqueFrameOwner::inv` and `global_inv`

`inv` drops the `meta_perm.wf(...)` self-clause. `global_inv` ([line 80-85](ostd/specs/mm/frame/unique.rs#L80-L85)) keeps the spec equality `regions.slot_owners[self.slot_index].inner_perms == self.meta_perm.inner_perms` *deleted* — because `meta_perm` no longer has `inner_perms`. The link to `regions` is via `slot_index` and the slot-pointer permission only.

### 4.3 Operations

- [`UniqueFrame::from_raw`](ostd/src/mm/frame/unique.rs#L411): tracked args drop `meta_perm: PointsTo<MetaSlot, Metadata<M>>`, pick up `slot_perm: simple_pptr::PointsTo<MetaSlot>` instead. `meta_own: M::Owner` stays.
- [`UniqueFrame::into_raw`](ostd/src/mm/frame/unique.rs#L390), [`reset_as_unused`](ostd/src/mm/frame/unique.rs#L352), [`drop`](ostd/src/mm/frame/unique.rs#L489): same treatment as segment's bodies — atomic ops go through `regions.slot_owners[idx]`.

### 4.4 `UniqueFrameOwner::from_raw_owner` and `from_unused_owner_spec`

Constructors get the new field signature.

## Phase 5 — call-site cleanup

After Phases 1–4, audit:
- [`heap/slot.rs`](ostd/src/mm/heap/slot.rs) — currently unverified, but consumes `Segment::from_raw`. Sees no perm types directly, should be unaffected.
- [`page_table/`](ostd/specs/mm/page_table/) — `PageTablePageMeta` and friends use the same patterns. [`page_table/node/owners.rs`](ostd/specs/mm/page_table/node/owners.rs) likely has a similar `meta_perm` field and would benefit from the same treatment, though it's a separate (PageTable-specific) refactor.
- Any `cast_ptr::PointsTo<MetaSlot, ...>` callers outside the migration scope.

## Migration strategy

Two viable approaches:

**(A) Parallel-path migration.** Introduce `get_from_unused_v2`, `Frame::from_raw_v2`, etc., alongside the existing functions. Migrate `SegmentOwner` first using v2. Then `UniqueFrameOwner`. Then delete v1. Pros: each step is small and stays green. Cons: temporary code duplication.

**(B) Big-bang per-phase.** Change `get_from_unused` in place, fix every caller in the same change. Each phase is a single PR that touches many files. Pros: no temporary duplication. Cons: large PRs, harder to bisect if something breaks.

Recommend **(A)** for Phase 1 (since `get_from_unused` has many indirect users) and **(B)** for Phases 2–4 (where the change set is bounded).

## Estimated scope

| Phase | Files | New / changed lines (rough) |
|---|---|---|
| 1 | `meta.rs`, `meta_owners.rs`, `meta_specs.rs` | ~150 |
| 2 | `mod.rs`, `frame_specs.rs` | ~200 |
| 3 | `segment.rs` | ~80 (most of which is reverting current vacuous-body workarounds) |
| 4 | `unique.rs` (both src and specs) | ~150 |
| 5 | audit + small fixes | ~50 |

Total ~600 lines of focused change. Each phase should land independently with green verification — no phase introduces vacuous bodies that the next phase fixes.

## Validation

For each phase:
1. `cargo dv verify --targets ostd -- -V new-mut-ref` passes.
2. As a regression check after Phase 3: re-run the probe sequence we used (insert `assert(false)` after `owner.perms.tracked_remove(0)` in `drop`'s loop body) — it should now **fail** rather than pass, confirming the duplication is gone and bodies verify non-vacuously.
3. After all phases: re-add the explicit `slot_own.raw_count = (slot_own.raw_count - 1) as usize` decrement in `drop`. Verify the `drop_last_in_place` precondition `raw_count == 0` is now genuinely satisfied (not vacuously).
