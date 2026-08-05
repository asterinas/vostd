# Tokenizing `ostd/src/mm`: from sequential exclusive-token proofs to VerusSync state machines

**Status:** Phases 0–1 complete + a Phase 2/3 binding spike landed (all green); Stage C or Stage P next (Phase 2 proper is gated on Stage C — see §4).
**Baseline:** ostd verifies at **1570/0** (`cargo dv verify --targets ostd`, 231 s, measured 2026-08-04). *Not comparable to earlier figures in this doc:* `experiments/tmp_region.rs` was an orphan file (declared in no `mod.rs`, so never compiled or verified) until it was wired in on 2026-07-31. The earlier **1970/0** figure in this doc was measured against a different version and does not describe this tree; treat 1508 as the number to diff against. [`experiments/rc_tsm.rs`](../../experiments/rc_tsm.rs) is green, including the Phase 0 per-slot-namespace de-risk (`phase0_touch_slot`/`phase0_touch_two`, marked scratch, delete at Phase 2) and the Phase 1 `lifecycle_smoke_test`.

> **Counting caveat.** `--verify-only-module experiments::rc_tsm` checks only the *module-level* fns (5 of them); every macro-generated inductive/transition proof lives in the nested `FrameRc` module, which that filter silently skips, and the `dv` cache then returns the stale pass in ~0.3 s. Ground truth for this module is the full `cargo dv verify --targets ostd` run only.

> **Repo-state note (re-ported 2026-07-26).** This plan was authored in `../certik-vostd-broken` and re-established in the current upstream-synced tree, which has drifted since. Reconciled: baseline is now **1970/0** (was 1478/0); the Phase-0 scaffold + `verus_state_machines_macros` dep were re-added. Upstream changes that touch the plan text: **`Metadata` was removed (#668)** — the storage cast is now `Repr<MetaSlotStorage>` + vtable dispatch, not `Metadata<M>` (Stage M updated below); minor renames (`has_safe_slot`→`valid_frame_paddr` #667, `ReprPtr::Perm`→`ReprPtr::ReprPerm` #668, `TrackDrop` redesign #658) touch the accounting/embedding phases' identifiers but not their structure. **Open setup item:** the vendored Verus copied from `broken` (2026-06-14) predates #619, so `vstd_extra` (which now uses `vstd::std_specs::nonzero`) does not compile against it — a newer vstd is needed for a fully green `cargo dv verify`; `ostd` itself is unaffected.

---

## 1. Motivation

Today `ostd/src/mm` is verified under a **sequential, exclusive-ownership** ghost model: the shared per-frame `ref_count` (`PAtomicU64`) and per-node `lock` (`PAtomicU8`) are governed by permissions threaded as exclusive `&mut` out of a monolithic [`MetaRegionOwners`](frame/meta_region_owners.rs) / `Guards`. There are **no VerusSync atomic invariants anywhere in `mm`** — they exist only in `ostd/src/sync/`. As a result:

- Function-call-granularity claims about shared state are *value-level* (`ref_count.value() == n`), which are **not interference-stable** — sound only under a "giant lock" assumption that is never discharged.
- The soundness of the whole subsystem rests on a handful of `external_body` token-minting bridges (`node.lock`, the `MetaRegionOwners` source, `tlb.rs`) and, for the page-table locking, an outright `assume(...)` in [`cursor/locking.rs`](../../src/mm/page_table/cursor/locking.rs).

**Goal:** replace the exclusive-token model with real per-slot tokenized state machines, so that each shared-state claim is a *linear token* (interference-stable) backed by an `AtomicInvariant` opened around a single hardware atomic — exactly how `sync/` already governs its locks.

### The reframing that makes this tractable

Three mechanisms in the codebase are **the same fact stated three times**:

| mechanism | where | statement |
|---|---|---|
| exclusive `PermissionU64` value | `MetaSlotOwner.inner_perms.ref_count` | "`rc` equals _n_" |
| `frame_obligations` ledger | `MetaRegionOwners.frame_obligations: Multiset<usize>` | "_n_ outstanding obligations at this slot" |
| embedding `accounting_inv` | `VmStore` ([embedding/mod.rs `rc == H + P + cover_count`](embedding/mod.rs)) | "`rc == handles + pt_paths + segment_covers`" |

A per-slot refcount TSM collapses all three into **one linear resource**: `counter == |reader|`, where the `reader` multiset is partitioned by *kind* — Handle (H), PtPath (P), SegCover (cover). Each outstanding owner object physically holds one kind-tagged reader token. Token linearity then maintains the accounting equation for free, with no sequential re-derivation.

---

## 2. The two state machines

Two orthogonal tokenizations, over **two independent atomic cells per page-table node**:

- **`FrameRc` (this plan):** governs `ref_count: PAtomicU64`. Per-slot; states UNUSED / UNDER_CONSTRUCTION(0) / SHARED(n) / UNIQUE, mirroring the existing [`MetaSlotStatus`/`MetaSlotModel`](frame/meta_owners.rs). Built in [`experiments/rc_tsm.rs`](../../experiments/rc_tsm.rs).
- **CortenMM (Stage C):** governs `lock: PAtomicU8` and the cursor lock-coupling / RCU protocol. This is the **SOSP'25 best-paper concurrency proof** (separate artifact, `func-correct` branch / TELOS-syslab repo), which this repo's README states is a planned-but-unstarted merge. It discharges the `assume` in `cursor/locking.rs` and the `node.lock` `external_body`.

Because `ref_count` and `lock` are **different cells**, the two invariants never share a namespace mask — a cursor can hold a node's CortenMM lock token while opening that node's `FrameRc` invariant. This orthogonality is why the two efforts can be sequenced independently.

**Both sit on a third, foundational axis — the memory-layout model (Stage M).** Today `MetaSlot`'s four fields (`storage: pcell_maybe_uninit::PCell<MetaSlotStorage>`, `ref_count: PAtomicU64`, `vtable_ptr: PPtr<usize>`, `in_list: PAtomicU64`) are modeled as independent abstract cells with opaque `id()`s. Stage M reproduces the **VerusBelt** theoretical model — an axiomatization giving interior-mutable **cells an address** — plus custom `#[repr(C)]` layout axioms pinning `MetaSlot`'s field offsets, so each cell of a slot at `meta_addr(i)` has address `meta_addr(i) + offset`, *derived* rather than assumed. This grounds the `*const MetaSlot → *const AnyFrameMeta` cast (storage at offset 0), cell non-aliasing within the 64-byte slot, and the frame↔meta bijection at the byte level — especially for the interior-mutable `MetaSlotStorage`, inside whose `PTNode` variant the CortenMM `lock` physically lives. *The 2026-07 spike found CortenMM already implements this model (`vstd::raw_ptr::PointsTo`), so Stage M adopts + extends it rather than reproducing it standalone — see §3 Stage M.*

---

## 3. Phases

### FrameRc track

- **Phase 0 — De-risk per-slot dynamic-ns invariants** *(isolated test)*. Prove two `AtomicInvariant`s at namespaces `= slot index` can be opened independently and fire a transition. Everything rests on this; `AtomicInvariant::new(k, v, ns: int)` takes a runtime `int` ns, so it should be legal. Delete the test after.
- **Phase 1 — Full-state `FrameRc`** *(isolated, in `refcount_tsm.rs`)* — ✅ **done, green (2026-07-27).** Delivered:
  - **`RcState`** ghost enum replaces the scaffold's `counter: nat` — `Unused` / `Claimed` / `Shared(nat)` / `Unique`, one variant per physical band; `sentinel_of` maps it to the `u64` and `state_in_band` is the bound (`1 ≤ n < REF_COUNT_MAX`) that makes that map injective. `FrameRcGhost::wf` now covers all four bands.
  - **Two exclusive-window tokens**, both `Option`-sharded so single-ownership is a linearity theorem: `permit: Option<()>` (the transient physical-`0` window) and `unique: Option<()>` (the UNIQUE band). Payload is `()`, not the perm — the metadata is mutated inside the window, so any perm recorded at entry would be stale at exit (same choice as `rwlock.rs`'s `writer`).
  - **Storage custody across all four bands:** parked in `Unused`/`Shared`, withdrawn in `Claimed`/`Unique` — exactly the bands where one thread has exclusive metadata access (`write_meta` / `drop_meta_in_place`, `meta_mut`). `claim` uses `birds_eye` to withdraw the parked perm.
  - **Ten transitions**, each with a discharged `#[inductive]` proof: claim / publish_shared / publish_unique / do_clone / dec_basic / dec_to_zero / recycle / to_unique / from_unique, **plus `release_unique`** — the `UniqueFrame::drop` + `reset_as_unused` `store(0)` edge (UNIQUE → 0), which the original transition list above omitted but the exec code performs.
  - **Six invariants**, the load-bearing ones being `shared_band_wf` (`reader.count(storage) == n` ∧ `1 ≤ n < MAX`) and `no_readers_outside_shared`.
  - **Five properties** — `reader_guard`, `reader_match`, `reader_implies_shared`, `permit_implies_claimed`, `unique_implies_unique_band` — so a held token alone pins the band, which is the Phase-3 exec bridge; `lemma_state_from_value` is its numeric half (one atomic read ⇒ the band).
  - **`lifecycle_smoke_test`** drives one slot around both lifecycles (shared ⇄ unique, both back to free) firing every transition once. It pins down the generated call shapes before exec depends on them, and it caught the real API detail that `reader_implies_shared` needs the `state` token passed alongside the reader.
- **Phase 2 — Mirror into `MetaRegionOwners`** *(on CortenMM structures)*. Add per-slot `Instance` + `Shared<AtomicInvariant>` + a coherence conjunct tying token state to the existing `inner_perms.ref_count`. No exec change. Heavy proof plumbing; the coherence fact likely lives in a `*_sound` side predicate, not `inv()` (cf. the nr_children precedent).
- **Phase 3 — Migrate the 6 exec ops** onto `open_atomic_invariant!` + transitions. **Order revised by the 2026-07-27 spike (below): CAS ops first** — `get_from_in_use` (load-check-CAS) → `get_from_unused` (two blocks, transient-0 honest) → `Frame::drop` + `drop_last_in_place` → the `unique.rs` trio → **`inc_ref_count` last, as a design decision rather than a migration**. **Stop-point: ops token-driven.**
- **Phase 4 — Retire the exclusive `PermissionU64`**. Provide a spec bridge `MetaRegionOwners::ref_count(i)` reading the token value so most sites compile unchanged; audit each; delete the mirror; reconcile the region-fabricating bridges (`Tracked::assume_new` at meta.rs, embedding axioms). **Measured 2026-07-27:** the bridge [`MetaRegionOwners::ref_count(i)`](frame/meta_region_owners.rs) already exists but is used at only **4** sites, while **599** reach through `.inner_perms.ref_count` directly. So Phase 4 has an unbudgeted mechanical precursor — route those 599 through the bridge *first*, while both representations still agree. That precursor is zero-risk, AI-assistable, and independent of Stage C. **Stop-point: `ref_count` is a real tokenized atomic.**

#### Phase 2/3 spike results (2026-07-27, green at 1509/0)

`tsm_try_inc_ref_count` in [`experiments/rc_tsm.rs`](../../experiments/rc_tsm.rs) binds the machine to a **real** `MetaSlot.ref_count` and runs a real bump as a transition, with the token bundle passed as parameters (no `MetaRegionOwners` surgery). Vacuity-probed. Four findings, two of which change the plan:

1. **The op ordering above was backwards.** `inc_ref_count` increments *blind* and checks after, so inside the invariant the cell is already out of band and the token must move before the invariant can be re-established. An `Overflow` state was tried and **rejected**: (a) admitting readers in it destroys the "reader token ⟹ `Shared`" implication that six transitions and one property depend on (6 full-run errors), and (b) a single saturation state does not close — re-entering bumps the cell past `REF_COUNT_MAX` with nothing to absorb it, so a faithful model must reproduce the whole `REF_COUNT_MAX..REF_COUNT_UNIQUE` guard band as live states. Escaping by diverging inside the block is also unavailable: `open_atomic_invariant!` must restore the invariant and the body must stay atomic, so an exec `panic_diverge()` cannot live there. **Load-check-CAS has none of this** — the CAS only succeeds if the value is still the checked one, so the cell never leaves `1..REF_COUNT_MAX` and no extra state is needed. *Do not re-attempt the `Overflow` band.*
2. **`inc_ref_count` needs a decision, not a migration:** either model the guard band as real states, or re-implement it as a CAS loop (it is the only op that bumps blind). Deferred to the end of Phase 3.
3. **The "derive old `ensures` via a bridge lemma so consumers are untouched" premise is false for value-shaped contracts.** `final(rc_perm).value() == old(rc_perm).value() + 1` is not merely hard to re-derive — it is *not expressible* once the cell is genuinely shared, because no pre- or post-value of it is stable under interference. What survives is the linear claim (*the caller holds one more reader token*), with `counter == |reader|` carrying the accounting. Consumers of that postcondition must move to tokens; Phase 3's cost should be re-priced accordingly.
4. **Saturation guards degrade the same way.** `old(rc_perm).value() >= REF_COUNT_MAX ==> may_panic()` names the current value of a shared cell, so it collapses to the unconditional `may_panic()` (the Arc-style convention already used in this repo).

**Drop path bound too (same session, green at 1511/0).** `tsm_dec_ref_count` binds `Frame::drop`'s blind `fetch_sub` to `dec_basic` / `dec_to_zero`, and `tsm_recycle` binds `drop_last_in_place`'s closing `store(REF_COUNT_UNUSED)` to `recycle`. Four of the ten transitions now run against a real cell. Three further findings:

5. **The `inc_ref_count` obstacle is not "blind RMW" — it is "blind RMW into a non-band."** `fetch_sub` is equally unchecked, yet trivial to bind, because *every landing site is a legal band*: `Shared(n-1)` for `n >= 2`, and physical `0` for `n == 1`, which is `Claimed` — a real state with real meaning. `fetch_add` off `Shared(REF_COUNT_MAX - 1)` lands on `REF_COUNT_MAX`, which is not a band at all. The machine absorbs an unchecked decrement for free and cannot absorb an unchecked increment without modelling the guard band.
6. **Underflow needs no exec check**: `fetch_sub`'s `value >= 1` precondition comes straight from the reader token pinning `Shared(n), n >= 1`. Note the asymmetry with the overflow side, where *no* token can supply the corresponding fact — that is the same gap as finding 1, seen from the other end.
7. **`dec_to_zero` returns the storage permission *and* the permit together**, so "this was the last reference" and "you may run `drop_last_in_place`" become one object rather than the unenforced `if last_ref_cnt == 1` branch the exec code uses today. Consuming the reader token makes double-drop unrepresentable rather than merely incorrect.

**Custody groundwork landed (same session, green at 1512/0) — and it needs NO axiom.** This was scoped as an `external_body` mint from `&mut MetaRegionOwners`; it turned out not to need one. `tracked_bind_slot` is an ordinary verified proof fn that builds a slot's `FrameRcSlot` bundle (instance + per-slot `AtomicInvariant`) from its `PermissionU64` + storage perm. Three more findings:

8. **Bind at boot, and the adoption axiom disappears.** `AtomicInvariant::new`'s precondition `Pred::inv(k, v)` is discharged straight from `rc_perm.value() == REF_COUNT_UNUSED` — exactly what `sentinel_of` maps the `Unused` band to — and `alloc_meta_frames` already leaves every slot's cell at `REF_COUNT_UNUSED`. So the machine is born in the state the hardware is already in. Adopting a *live* slot (already `Shared(n)`) would need an extra `init!` for that band or a real axiom; binding all slots up front avoids the question.
9. **The invariant constant must hold *ids*, not objects:** `(InstanceId, AtomicCellId)`. `Instance::clone` is exec-mode and uncallable from proof code, and `PAtomicU64` is `external_body` so it cannot go in a constant at all (`arc.rs` works around that with a `Ghost<PAtomicU64>`; ids are cleaner). The predicate only ever uses `.id()`, so nothing needs duplicating.
**ALL TEN TRANSITIONS NOW BOUND to a real `MetaSlot.ref_count` (green at 1518/0).** Added `tsm_try_claim` / `tsm_publish_shared` / `tsm_publish_unique` / `tsm_try_to_unique` / `tsm_from_unique` / `tsm_release_unique` alongside the earlier four. Every op in the Phase 3 list therefore has a proven binding pattern ready to drop in when the permission split lands. Two more findings:

11. **`get_from_unused`'s two-block window models honestly**, with no giant-lock assumption: `tsm_try_claim` then a publish. Between the two the cell physically reads `0`, and the caller is provably the sole party able to touch the metadata because it holds the only permit — the plan's "transient-0 honest" requirement, discharged.
12. **The CAS ops need no incoming token — the hardware supplies the precondition.** `tsm_try_claim` takes *nothing*: CAS success means the cell read `REF_COUNT_UNUSED`, which decodes to the `Unused` band. Likewise `try_to_unique`'s CAS success is what *proves* this reader was the only one, rather than that being assumed. Acquisition-from-nothing is exactly where a token-based model might have looked stuck, and doesn't.

**PoC REGION LANDED** — [`experiments/tmp_region.rs`](../../experiments/tmp_region.rs), a self-contained local stand-in for `MetaRegionOwners` written against the *split* permission layout upstream is currently building. It proves the whole chain now rather than waiting: split perms → `tracked_bind_all` → `TmpRegionOwners` → `tracked_borrow(idx)` → `FrameRcSlot` → `tsm_*` op on a real cell. Contents: the region + its invariant, the recursive **axiom-free** `tracked_bind_all` over all slots, and `tsm_region_acquire` / `tsm_region_release` (= `get_from_unused` and `Frame::drop` in miniature, driven through the region by slot *index*). Findings:

13. **Region-scale binding needs no new soundness machinery** — `tracked_bind_all` is a plain recursive proof fn over `tracked_bind_slot`; the only cost is the recursion. The per-slot namespace discipline (Phase 0) lifts to the region invariant unchanged: `namespace == slot index`, so distinct slots stay independently openable.
14. **The teardown branch cannot be got wrong by a caller.** In `tsm_region_release` the `if` is not a check: `dec_to_zero` is what *produces* the permit + storage permission, so the branch is reachable only when this really was the last reference — replacing the exec code's unenforced `if last_ref_cnt == 1`.
15. **Verus mechanics worth remembering** (all cost a cycle here): `Tracked(..)` is not a valid `match`/`if let` pattern (bind the pair, use `.get()`); `proof { }` blocks are rejected *inside* a proof fn; and a region invariant of the form `0 <= i < n <==> dom().contains(i)` triggers on its own conclusion — split it and trigger the forward direction on `dom().contains(i)`, plus `broadcast use group_map_lemmas` and one bridging `assert forall` to carry the recursive result across the `remove`/`insert` back to the entry map.

**`Shared<AtomicInvariant>` refinement done (green at 1525/0).** `FrameRcSlot.inv` is now a `Shared<AtomicInvariant<..>>` and `FrameRcSlot::share()` duplicates a slot's governing bundle; all ten `tsm_*` ops open via `rc.inv.borrow()`. In the region, `tracked_slot_handle` + `tsm_region_acquire_owned` show a caller walking away from a region borrow holding **both** a reader token and its own bundle — the shape a real `Frame<M>` has, which was previously inexpressible (the bundle could only be borrowed). Findings:

16. **This duplicates *access*, not *authority*.** A shared bundle opens nothing by itself: every op still demands a `reader` / `permit` / `unique` token, and those stay linear. Every handle may look; only a token holder may act. That is the split the frame layer needs — a `Frame<M>` must reach its slot's cell from anywhere, while the right to move the count stays accounted for.
17. **`Instance::clone` IS proof-mode** — the macro emits a proof-mode inherent `clone` (plus a trap `Clone` impl that is `unimplemented!()`). The earlier failure during the custody work was calling it in a **spec** position (`AtomicInvariant::new`'s `k` is not tracked), not a mode conflict. Holding ids in the constant is still right (`PAtomicU64` cannot go in a constant at all), but the diagnosis was wrong — and this is why `share()` can be a proof fn rather than exec.

**Reworked 2026-07-31 (green at 1551/0), two changes:**

18. **No storage permission.** The planned upstream split separates **only** `ref_count`; `storage` stays in `MetaSlotOwner.inner_perms`. So the machine is instantiated at `NoStorage = ()` and `tracked_bind_all` takes only `Map<int, PermissionU64>`. Be clear on what this narrows: the bands, the count equation and the linearity of `reader`/`permit`/`unique` are untouched (they never depended on `Perm`), but the *metadata-access* half degenerates — with `()` parked, the permission `claim` withdraws and `publish_shared` returns conveys nothing, `reader_guard` becomes vacuous, and `Claimed`/`Unique` mark exclusivity without conferring the right that exclusivity is *for*. Recovering it needs `Perm` = the real `MetaSlotStorage` permission, i.e. a split that is not planned.
19. **Shaped like the real region.** The first cut invented structure `MetaRegionOwners` does not have — an `n_slots` field and a parallel `cell_ids: Map<int, AtomicCellId>` ghost map. Reshaped to carry `slots: Map<int, &PointsTo<MetaSlot>>` verbatim, index by `max_meta_slots()`, and `impl Inv` mirroring the real invariant clause for clause (`slots ⊇ rc_slots`, `slots[i].is_init()`, `slots[i].addr() == index_to_meta(i)`). `rc_slots` now sits exactly where `slot_owners` sits, and where the real region says `slots[i].value().wf(slot_owners[i])` this says `rc_slots[i].wf(slots[i].value().ref_count.id(), i)` — **cell identity is derived, not carried**, as it will be in the real region. Migration becomes a substitution rather than a redesign.
20. **That collapsed the connection too.** Because the region carries the slot pointers itself, `tsm_acquire_frame(paddr, region)` takes **one region and one physical address** — the same shape as `get_from_unused(paddr)` — instead of threading a real *and* a PoC region related by a hand-written `coherent_with` predicate (now deleted). Coherence is internal to `inv()`, which is where Phase 2 will put it.
21. **Watch for preconditions that are really theorems.** `frame_to_meta(paddr) == index_to_meta(frame_to_index(paddr))` and `paddr / PAGE_SIZE == frame_to_index(paddr)` were initially written as `requires` on `tsm_acquire_frame`; both are derivable, and dropping them still verifies. A precondition that is a theorem is a hidden assumption dressed as an interface.

19. **Actually connected.** Two gaps were closed: the module was declared in no `mod.rs` (orphan — never compiled or verified), and its ops were driven by a caller-conjured `&MetaSlot`. `tsm_acquire_frame(paddr, regions, region)` now takes a `Paddr` and the **real** `MetaRegionOwners`, calls `inv_implies_correct_addr`, borrows the actual `PointsTo<MetaSlot>` from `regions.slots`, computes the address with the production `frame_to_meta`, and CASes that slot's own `ref_count`. Only the *governance* of the cell comes from the PoC region. The tie is a new `TmpRegionOwners::coherent_with` — the stand-in for the conjunct Phase 2 adds to `MetaRegionOwners::inv()`. It relates the regions by **cell identity alone** and deliberately says nothing about who holds the permission: `tracked_bind_all` consumes the `PermissionU64`s, so a `TmpRegionOwners` for these cells cannot coexist with a `MetaRegionOwners` still holding them. Linearity rules out the bad combination with nothing here checking for it. *Limit:* the preconditions are satisfiable (vacuity-probed), but a running program cannot supply both regions until the split actually hands the permissions over — what this buys now is that the call shape, address computation and coherence statement are fixed and verified, so the landing is a wiring change.

**`experiments/tmp_region.rs` is destined to be PORTED, not deleted** — its contents move into the real `MetaRegionOwners` when the upstream `ref_count` split lands.

### TSM vs raw resource logic — measured 2026-08-04

`tokenized_state_machine!` is a *front end* for the resource logic: it generates a PCM, token types, and the frame-preserving-update lemmas. The alternative is hand-writing the PCM on `vstd::resource::pcm::Resource`, as `vstd_extra`'s `count.rs` already does. [`experiments/rc_pcm.rs`](../../experiments/rc_pcm.rs) prices it by encoding the carrier and proving **`do_clone`** both ways (green, delete once the question is settled).

**Cost** (non-comment lines, same transition): TSM transition + `#[inductive]` = **13**; PCM `lemma_do_clone_frame_preserving` = **52**; one-time carrier + `valid`/`op` + trait obligations = 78. ≈4× per transition, on the *easiest* transition (no storage withdraw/deposit, no multiset removal). `#[inductive]` proves `inv(pre) ∧ step ⟹ inv(post)` for a fixed pre/post; frame preservation is `∀c. valid(a·c) ⟹ valid(b·c)` — quantified over arbitrary frames, so you case-split the frame and redo the arithmetic under each. Surprises: the algebraic obligations (`associative`/`commutative`/`valid_op`/`op_unit`/`unit_valid`) all discharged with **empty bodies**; and `Invalid` is **not** optional — a `bad: bool` poison flag that keeps the other fields breaks associativity when three authorities compose (the bracketings retain different `auth`), which is why `count.rs` has an `Invalid` variant.

**The blocking finding: validity cannot state the count equation.** `ResourceAlgebra::valid_op` requires validity to be downward-closed (`op(a,b).valid() ==> a.valid()`), so every clause must be an inequality — the authority composed with only *some* fragments genuinely has fewer readers than the band records. Verified by experiment: flipping `readers <= n` to `readers == n` fails `valid_op`'s postcondition. **This hits the centrepiece of this plan** — `counter == |reader|`, the equation that makes the accounting theorem free and that Phases 5–7's kind-tagged Handle/PtPath/SegCover story rests on, is what the TSM gives directly and raw PCM cannot state. Recovering it requires the remainder encoding (`count.rs`'s `frac`: the authority also holds the not-yet-handed-out shares).

**Composition — the reason this question is live.** TSMs *do* compose by token passing: a larger machine can hold a smaller machine's tokens in `storage_option`/`multiset` fields and `guard` them out. But (i) **no nesting** — `transition!` bodies are a closed DSL with no call, so a larger machine cannot perform a smaller machine's transition as part of its own step ("cursor `map` atomically mints a PtPath reference on the frame" is not one transition; it becomes exec glue that is not verified *as a protocol*); and (ii) **no cross-machine invariants** — a machine's invariant ranges over its own fields, and relating PT structure to frame refcounts would need the refcount `state` token, which is `#[sharding(variable)]`, exclusive, and lives inside the frame's `AtomicInvariant`. Neither limit bites for one closed protocol over fixed cells (why the refcount machine went smoothly); both bite constantly for "the whole of `mm`", whose entire point is invariants relating per-slot refcounts, per-node locks, PT structure and TLB, with atomic steps touching several at once. vstd itself splits this way — `Shared<T>` is a TSM (small, closed), `count.rs` is raw PCM (a building block others consume).

**RESOLVED 2026-08-04 — the composition experiment was run, and it came out the OTHER WAY: TSM composition works.** [`experiments/pt_path_tsm.rs`](../../experiments/pt_path_tsm.rs) (green, vacuity-probed) builds a *second* TSM — `PtNode`, a page-table entry that holds a `FrameRc::reader` token while installed — and proves Phase 6's property across the two machines: **from "this entry is installed", conclude the frame's physical `ref_count` is in `1..MAX`**. Chain: `PtNode::path_guard` borrows the reference out of the entry → `FrameRc::reader_implies_shared` pins the band → `lemma_state_from_value` decodes it (step 2 inside `open_atomic_invariant!`, where a real op lives anyway).

**Correction to finding "no cross-machine invariants" above.** That statement is literally true — `PtNode` cannot mention `FrameRc`'s band in its `#[invariant]` — but the conclusion drawn from it ("composed steps degrade into exec glue that is not verified as a protocol") was WRONG. You do not need cross-machine invariants; you need cross-machine *facts at the point of use*, and token-passing delivers them. The relation is carried by the token: holding a `FrameRc::reader` **is** the proof that the count includes you, so it never needs restating in the consumer's invariant.

Two mechanical constraints that will recur in every consumer:

22. **`guard` cannot sit under a `birds_eye`** — "a guard value must be a deterministic function of the local inputs". The consumer must be able to *name* the token it borrows, so it needs a `#[sharding(variable)] entry: Option<FrameRc::reader<..>>` ghost copy of *which* reference it holds; a bare `present: bool` cannot name it. Small standing tax per consumer.
23. **Invariants do not leak.** `PtNode`'s `path_belongs` is invisible to callers — only what a transition/property `assert`s becomes an `ensures`. Without an explicit `assert(tok.instance_id() == pre.rc_instance)` inside `path_guard`, the borrowed token is anonymous and `FrameRc` rejects it. Every cross-machine fact must be deliberately re-exported.

**The composed step was tested too — it also works.** `probe_map_step` / `probe_unmap_step` in the same file (green, vacuity-probed) mint a PtPath reference off an existing handle and install it, and the reverse (falling correctly into teardown-and-recycle when it was the last reference).

24. **"Atomic across both machines" is the wrong requirement.** The two moves cannot be one hardware atomic and should not be: the refcount is a shared cell needing a CAS under `open_atomic_invariant!`, while the entry is protected by the node lock, so its token is held exclusively (`&mut`). Only the first needs atomicity against other threads.
25. **⚠ The accounting equation is a QUIESCENT-BOUNDARY property, not a running invariant — this affects Phase 7.** Between the CAS and the install there is an **in-flight window**: the caller holds a reference no registry owns, and another thread reading `ref_count` sees the bump before any entry justifies it. During that window `FrameRc`'s `counter == |reader|` is *never* violated (an in-flight token is still a token) and `PtNode`'s `entry == path` is *never* violated (both still `None`) — but the **decomposition by registry**, `rc == H + P + cover`, is transiently false. Phase 7 must therefore either scope `accounting_inv`'s replacement to quiescent points or carry an explicit in-flight term. Token linearity is what makes the transient benign: a reference in flight is conserved, not lost.
26. **The re-export tax is systematic, one per crossing.** `uninstall` failed exactly as `path_guard` had — the *withdrawn* token was anonymous and `FrameRc` refused it — until given its own `assert(tok.instance_id() == pre.rc_instance)`. Budget one such `assert` per transition/property that hands a token across a machine boundary.

**Relocated 2026-08-04.** The whole refcount track moved out of `specs/` into [`ostd/experiments/`](../../experiments/mod.rs), wired in `lib.rs` beside `specs`; the dependency points one way only (experiments → specs), and nothing in `src/`/`specs/` holds any of these tokens. Contents, with **two different dispositions**:

| file | was | disposition |
|---|---|---|
| `rc_tsm.rs` | `specs/mm/frame/refcount_tsm.rs` | **port** — becomes load-bearing at Phase 2/3 |
| `tmp_region.rs` | `specs/mm/frame/tmp_region.rs` | **port** — contents move into the real `MetaRegionOwners` |
| `rc_pcm.rs`, `pt_path_tsm.rs`, `pt_path_pcm.rs` | (new) | **delete** — they only price the TSM-vs-PCM question |

"Experiments" reads as "throwaway"; two of the five are not. Keep that distinction visible.

27. **The same composition was then built BOTH ways** (`pt_path_tsm.rs` vs `pt_path_pcm.rs`, both green), and the result is sharper than "the TSM wins" — the two costs sit on **different axes** and neither approach dominates:

| | TSM | PCM |
|---|---|---|
| the entry is | a second machine: 3 fields, 2 invariants, 2 transitions, 1 property, 3 inductive proofs | a struct holding one `Resource<RcCarrier>` |
| install / uninstall | `deposit`/`withdraw` transitions, each with a proof | move the value in / out — **nothing to prove** |
| the cross-fact | `path_guard` → borrow → `reader_implies_shared` → decode, inside `open_atomic_invariant!` | one `validate_2` |
| identity plumbing | an `assert` **per crossing** (invariants do not leak) | none — a fragment carries its own `loc` |
| composition proof | ~15 lines on top of the machine | 1 line |

**The trade, stated properly: the TSM makes each protocol cheap and the accounting free, but charges a fixed fee per protocol *boundary*; the PCM makes boundaries free but charges ~4× per *step* and turns the accounting equation into a construction.**

**⇒ Current recommendation: do NOT rewrite onto raw resource logic** — but for a *quantitative* reason, not the structural one originally claimed. `mm` has a bounded, small number of protocol boundaries (frames, page-table paths, segments) against a large number of transitions and heavy reliance on exact accounting, so the per-crossing fee is paid a few times, not a few hundred. **If the boundary count were the thing that scaled, the answer would flip.**

**Superseded next step:** not more refcount work. Take the smallest *real* composition — one page-table entry owner holding a PtPath reference — and try to state "this entry's presence implies the frame's count includes it" both ways. If TSM token-passing expresses it, the TSM survives contact with a consumer; if it needs the PT machine's invariant to mention frame state, it does not. **Complication:** CortenMM (Stage C) is itself TSM-based (spinlock = `tokenized_state_machine!` + `atomic_with_ghost`), so choosing raw resources for `mm` means carrying both idioms or reworking theirs.



10. **What actually blocks in-place wiring is structural, not axiomatic.** `rc_perm`/`storage` sit in `MetaSlotOwner.inner_perms` as plain fields threaded by `&mut`; the region must *give them up*, and with one permission per cell it cannot keep a copy. Fabricating a second with `external_body` would not be staging convenience but unsoundness (two permissions for one cell), so it is deliberately not done. Changing `MetaSlotOwner`'s shape is Phase 2 proper.

### Embedding-accounting track (supplants the sequential `VmStore`/`step` accounting)

- **Phase 5 — Kind-tagged readers.** `reader: Multiset<(RefKind, Perm)>` with `RefKind ∈ {Handle, PtPath, SegCover}`; transitions take a kind arg.
- **Phase 6 — Attach readers to registries; merge `frame_obligations`.** `FrameEntry` / `EntryOwner`(PtPath) / `SegmentEntry` each own a kind-tagged reader; `handle_count` / `paths_in_pt.len()` / `segment_cover_count` become token multiplicities. The `frame_obligations` field + its 3 axioms are subsumed by the reader multiset. **PtPath readers are minted by cursor `map` under a CortenMM-held lock** — the confluence point.
- **Phase 7 — Replace `accounting_inv` with the TSM invariant.** The `rc == H + P + cover` clause becomes a theorem (`counter == reader.len()` + Phase-6 bridges); `accounting_inv` shrinks to token custody. The UNUSED-guard / active-head clauses become consequences of the TSM state invariant. **Stop-point: accounting = token custody.**
- **Phase 8 — Dissolve the sequential accounting machinery.** The refcount `_embedded` **axioms become theorems** (delete axiom, keep proof fn with same ensures); the accounting `op_pre` residuals and `step_*` accounting-preservation proofs are discharged by linearity. **Stop-point: accounting axioms → theorems.**

### Stage C — Merge CortenMM (structural / locking layer)

Import CortenMM's locking TSM; discharge `node.lock` (`external_body`) and the `assume` + ~10 `external_body`/`assume` across `cursor/locking.rs` (2+7), `cursor/mod.rs` (1+2), `node/mod.rs` (2); reconcile this repo's `Guards.lock_held(addr)` with CortenMM's structured lock tokens (the load-bearing merge lemma); refine the sequential `cursor_steps.rs` model into CortenMM's concurrent transitions. **This absorbs the old "Phase 9 structural frontier"**: with the locking layer tokenized, the sequential `Seq<Op>` model retires for structure as well as accounting, yielding a fully token-driven `mm`.

### Stage M — Realistic `MetaSlot` memory model (VerusBelt reproduction)

Reproduce the **VerusBelt** theoretical model — an axiomatization giving interior-mutable **cells an address** (today `PCell`/`PAtomic` expose only an opaque `id()`) — plus custom `#[repr(C)]` layout axioms pinning `MetaSlot`'s field offsets. Each field cell of a slot at `meta_addr(i)` then has address `meta_addr(i) + offset`, *derived* not assumed. Grounds: the `*const MetaSlot → *const AnyFrameMeta` cast (storage at offset 0), cell non-aliasing inside the 64-byte slot, and the frame↔meta bijection at the byte level — decisively for the interior-mutable `MetaSlotStorage`.

**Stage M is a third, orthogonal hardening axis (memory-layout realism) that sits *under* both TSMs**, because it redefines the exact cells they bind:

| binder | cell it binds | why Stage M touches it |
|---|---|---|
| FrameRc | `ref_count: PAtomicU64` | becomes a cell at a slot offset, not an opaque id |
| FrameRc | `storage: Option<Perm>` payload | `Perm` *is* the `MetaSlotStorage` permission Stage M redefines |
| CortenMM | node `lock: PAtomicU8` | lives *inside* `MetaSlotStorage::PTNode` — buried in the storage Stage M remodels |
| Phase 2 | `MetaRegionOwners.slots: Map<usize, PointsTo<MetaSlot>>` | slot-perm shape changes |

**Ordering — RESOLVED by the CortenMM spike (2026-07).** The spike (see below) found CortenMM's `lock-protocol-rcu` *already* uses an address-carrying model (`vstd::raw_ptr::PointsTo` with `.addr()`; `MetaSlotPerm.relate` pins `frame_paddr == meta_to_frame(meta_vaddr)`; the spinlock ties `perms.addr() == paddr_to_vaddr(paddr)`) — effectively the VerusBelt model already. So:

- **Do NOT reproduce VerusBelt standalone before Stage C** — that would build a second address model only to merge it away (the double-reconciliation risk, now confirmed real).
- **Stage M has an easy adoptable part and a hard novel core.**
  - *Adoptable from CortenMM (easy):* the slot-*pointer* address model — `raw_ptr::PointsTo<MetaSlot>` with real `.addr()` and the `frame_paddr ↔ meta_vaddr` bijection.
  - *This repo's to solve (the real Stage M):* the **live, initialized, dynamically-typed storage-as-metadata cast** `*const MetaSlot → *mut M` (`M: AnyFrameMeta`), realized by `as_meta_ptr`/`dyn_meta_ptr` via the `vstd_extra::cast_ptr::Repr<MetaSlotStorage>` trait (assoc perm `ReprPerm`) + the `vtable_ptr` `DynMetadata` dispatch. *(The intermediate `Metadata<M>` newtype was removed upstream in #668 — the cast now goes storage→`M` directly through `Repr`; `ReprPtr::Perm` was renamed `ReprPerm`.)* `raw_ptr` does **not** give this — its `PointsToRaw`/`split`/`into_typed` are (i) **uninit-only** (`into_raw` requires `is_uninit`), (ii) require you to *supply* the field offsets (Verus derives no `#[repr(C)]` layout — the "custom C-layout axioms" are still yours to write), and (iii) monomorphic (`into_typed::<V>` takes a fixed `V`, but the metadata is `dyn AnyFrameMeta` chosen at runtime via `vtable_ptr`). CortenMM gives nothing here — its `MetaSlot = { usage, Option<PageTablePageMeta> }` uses a plain typed field and *sidesteps* the type-pun (no untyped frames / dyn metadata). So Stage M must **re-found `vstd_extra::cast_ptr::PointsTo<R,T>` / `Repr` on real addresses**, adding `#[repr(C)]` offset/size/align axioms + `Repr`/vtable dispatch + an *init-preserving* reinterpretation, and in doing so retire the current `external_body` cast (whose `borrow_mut` is flagged `FIXME[SOUNDNESS]: unsound`).
- **Stage M is orthogonal to the refcount TSM, not a prerequisite for Phase 2.** `FrameRc`'s `AtomicInvariant` binds `ref_count` by `.id()` (as `arc.rs` binds a `PAtomicU64`); it needs no address. Stage M is *realism* hardening entangled mainly with **CortenMM** (shared `raw_ptr` model). Its real cost is a `simple_pptr`/`PCell` → `raw_ptr` migration of this repo's frame model (620+ sites) to match CortenMM.

**Bonus from the spike:** CortenMM's spinlock is itself a `tokenized_state_machine!` (`SpinInstance`/`SpinFlagToken`) bound to an `atomic_with_ghost` `AtomicBool` keyed on `(InstanceId, NodeId, Paddr, PagingLevel, CellId)` — a working template of the exact TSM+atomic-with-ghost+address architecture `FrameRc` targets, de-risking Phase 2's binding.

### Stage P — Simple per-CPU model & `tlb.rs` verification

**A fourth, largely-orthogonal axis: SMP / TLB shootdown.** Distinct from the frame-refcount, PT-locking, and memory-layout axes, but it underlies the cursor's map/unmap (which issue TLB flushes) and `VmSpace::activate`.

**Current gap (all axiomatized):**
- `TlbModel` ([specs/mm/tlb.rs](tlb.rs)) is a **single-CPU** ghost `{ pending: Seq<TlbFlushOp>, mappings: Set<Mapping> }`; its transitions (`tracked_update`/`tracked_flush`/`tracked_issue_tlb_flush`/`dispatch_tlb_flush_spec`) are `axiom fn`.
- `AtomicCpuSet` ([specs/mm/cpu.rs](cpu.rs)) is an **empty stub** (`struct AtomicCpuSet;`), though the exec `cpu/set.rs` uses real per-word `AtomicU64` `fetch_or`/`fetch_and`.
- Every `TlbFlusher` op (`issue_tlb_flush{,_with}`, `dispatch_tlb_flush`, `sync_tlb_flush`, `perform_on_current`) is `#[verifier::external_body]`; the real cross-CPU dispatch (per-CPU `FLUSH_OPS: SpinLock` queue + `ACK_REMOTE_FLUSH: AtomicBool` + `smp::inter_processor_call` IPI) is unmodeled.

**The simple per-CPU model to build:**
- `PerCpu<T> ≈ Map<CpuId, T>` with a tracked "current CPU"; give `AtomicCpuSet` real bitset-over-CPUs semantics tied to the exec `fetch_or`/`fetch_and`.
- Per-CPU TLB state: each CPU carries a `Set<Mapping>` TLB plus its `FLUSH_OPS` pending-queue and `ACK_REMOTE_FLUSH` flag as ghost per-CPU state.
- Model `inter_processor_call` **abstractly and synchronously**: `dispatch` enqueues the flush ops onto each *target* CPU's per-CPU state and clears its ack; `sync_tlb_flush` blocks until every target has acked, which in the model *removes the stale mappings* from those CPUs' TLBs. This over-approximates the async handshake soundly (the real ack barrier guarantees completion before proceeding) and keeps the model "simple" — the ack tokens can later become a small TSM if the handshake itself is to be *proven* rather than abstracted.

**Correctness target:** **TLB-shootdown consistency** — after `dispatch`+`sync` for an unmapped range, no target CPU's TLB retains a flushed mapping; invariant "every CPU's TLB ⊆ its active page table ∪ its pending flushes." This is exactly the property [`CursorMut::unmap`](../../src/mm/vm_space.rs)'s doc flags as an open TODO ("proving that this function preserves TLB consistency"). Deliverable: the five `TlbFlusher` ops become verified, and the `TlbModel` transition axioms become theorems over the per-CPU model.

**Coupling & ordering:** **Parallelizable** — a good independent / second-engineer workstream, since it shares almost nothing with the refcount or memory-cast work. It *intersects* the cursor (the `Tracked(tlb_model)` threaded through `map`/`unmap`) and `VmSpace` (`AtomicCpuSet` + the currently-`unimplemented!` `activate`). It is a **prerequisite for claiming `CursorMut::map`/`unmap` are axiom-free** (their flush calls), so it should land before the embedding phases assert that. No dependency on Stage M or CortenMM at the model level; a light spec-level touchpoint with the PT view (`TlbModel::consistent_with_pt(PageTableView)`).

---

## 4. Ordering decision: where CortenMM sits vs. the full-state TSM

"The full-state TSM" is two things with opposite rework exposure:

- **As an artifact** (Phases 0–1, isolated in `refcount_tsm.rs`): touches nothing CortenMM reshapes → **zero rework exposure**, and the ideal low-risk vehicle to prove the `verus_state_machines_macros` toolchain in-repo. → **before CortenMM.**
- **Its integration** (Phases 2–4): restructures the very owner types CortenMM rewrites → **do after CortenMM**, so it builds on the settled structural shape rather than being reworked.

**Decision:** *build the full-state TSM first (isolated); merge CortenMM next; then integrate the refcount TSM on CortenMM's structures; then the embedding-accounting phases.* CortenMM slots **after the full-state TSM artifact (Phase 1), before its integration (Phase 2).**

| force | pulls toward | satisfied by the split because |
|---|---|---|
| toolchain / risk laddering | TSM-first | Phases 0–1 isolated; prove tooling on the small thing |
| owner-structure stability | CortenMM-before-integration | Phases 2–4 build on CortenMM's final shapes |
| foundational depth | CortenMM-early | lands before anything integrates against structure |
| merge stability | no overlapping migrations | refcount integration and CortenMM don't churn `MetaRegionOwners` at once |

### Master sequence

```
0.  De-risk per-slot dynamic-ns AtomicInvariant     [isolated]     S   ✅ done
1.  Full-state FrameRc TSM                           [isolated]     M   ✅ done (2026-07-27)
P.  Simple per-CPU model & tlb.rs verification       [∥ orthogonal] M    (SMP/TLB axis; independent workstream)
──────────────────────────────────────────────────────────────────────
C.  MERGE CortenMM (locking TSM; brings raw_ptr address model)  [foundational] XL
M.  Extend CortenMM's raw_ptr model to storage/ref_count/in_list  [on C]  L   (was "reproduce VerusBelt"; spike → adopt CortenMM's)
──────────────────────────────────────────────────────────────────────
2.  Mirror FrameRc into MetaRegionOwners (binds ref_count by id) [on C]  L
3.  Migrate 6 refcount exec ops                      incremental    M×6   ✅ ops token-driven
4.  Retire exclusive PermissionU64 (~620 sites)      mechanical     L     ✅ rc a real atomic
5.  Kind-tagged readers                              additive       S–M
6.  Attach readers; merge frame_obligations          [refcount⋈C]   L
7.  Replace accounting_inv with TSM invariant        central        L     ✅ accounting = custody
8.  Dissolve accounting step/op_pre/_embedded        subtractive    M–L   ✅ axioms → theorems
```

---

## 5. Risks & practical notes

- **`--verify-only-module` does not reach macro-generated proofs.** `tokenized_state_machine!` emits its inductive/transition lemmas into a nested module (`…::refcount_tsm::FrameRc`), so filtering on the *parent* module reports only the hand-written module-level fns and says nothing about the machine itself. Naming the nested module directly just hits the cache. Only the full run is evidence.
- **`dv --focus` cache is unreliable on ghost / `#[inductive]` edits** (hits cache at ~0.3s and skips re-check). Trust only full `cargo dv verify --targets ostd` (~400s) for ground truth after ghost changes. Without `--focus` the `--verify-only-module` filter wrongly applies to `vstd`.
- **Per-slot invariant namespace = slot index** confirmed legal (runtime `int` ns, `vstd/invariant.rs`).
- **Coherence-in-`inv()` hazard:** mid-transition a token is briefly in flight, so the coherence fact may need a `*_sound` side predicate rather than the top-level `inv()` (nr_children precedent).
- **Stage C is the XL item** — larger than the entire refcount track, because it imports a full external concurrency proof ("first at the spec level, then the code"). Treat its scheduling as gating.
- **Region-fabricating bridges** (`Tracked::assume_new::<&mut MetaRegionOwners>`, embedding axioms) remain boundary axioms until Phase 4.

## 6. Scope & sequencing estimate

Effort ranges for **one engineer already fluent in this codebase and Verus**. These are proof-engineering estimates — a 2–3× spread is normal and dead-ends happen (cf. the reverted `in_scope` removal). "Intervention" = share of hands-on expert proof-discovery vs. mechanical / AI-assistable / delegable work.

| Stage | Effort (1 expert) | Intervention | Dominant driver / risk |
|---|---|---|---|
| 0. De-risk ns | ✅ done (~1 hr) | — | Complete, green. |
| 1. Full-state `FrameRc` | ✅ done | — | Complete, green. Landed in one session; the `arc.rs`/`rwlock.rs` templates carried the inductive proofs with only `broadcast use group_multiset_axioms` + two `assert forall` bodies. |
| P. Per-CPU model & `tlb.rs` | 3–5 wks | Med–High (~40%) | Build `PerCpu`/`AtomicCpuSet` bitset + per-CPU TLB state; verify 5 `TlbFlusher` ops + turn `TlbModel` axioms into theorems; prove TLB-shootdown consistency (the open `unmap` TODO). Design crux = the synchronous IPI abstraction. **Orthogonal — parallelizable / second-engineer track.** |
| M. Realistic `MetaSlot` memory | **5–9 wks** | **High** (~20%) | **Spike-corrected:** adopting CortenMM's slot-pointer `raw_ptr` model is easy; the hard core is re-founding the **live, dyn-typed storage-as-`Meta` cast** (`cast_ptr`/`Repr`) on real addresses — raw_ptr's `into_typed` is uninit-only + monomorphic + offset-less, so this needs `#[repr(C)]` layout axioms + vtable dispatch + an init-preserving reinterpret, *and* retires the current `external_body`/FIXME-unsound cast. Novel; CortenMM sidesteps it. 620+ `simple_pptr`/`PCell` sites migrate. |
| C. Merge CortenMM | **8–16 wks** | **Very High** (~15%) | XL. Import external SOSP proof; `Guards ↔ CortenMM token` reconciliation lemma is novel; discharge ~10 `assume`/`external_body`; re-thread every cursor method. Likely needs CortenMM-author involvement. **Dominates the program.** |
| 2. Mirror into `MetaRegionOwners` | 2–4 wks | High (~25%) | Core-invariant surgery + `AtomicInvariant`-in-a-tracked-`Map` + thread through every region helper; cascade + "coherence-broken-mid-op → side predicate" risk. |
| 3. Migrate 6 exec ops | 2–3 wks | Med–High (~50%) | Pattern set by `arc.rs`; ~2–4 days/op, accelerating. `get_from_unused` (two-block) + `drop` last-ref awkward. |
| 4. Retire exclusive perm (~620 sites) | 2–4 wks | Med (~65%, voluminous) | `ref_count(i)` bridge keeps most sites unchanged; bulk is classify-and-audit (AI-assistable); hard 20% is `assume_new`/embedding-axiom reconciliation. |
| 5. Kind-tagged readers | 0.5–1 wk | Med (~60%) | Small, local re-threading. |
| 6. Attach readers; merge `frame_obligations` | 3–5 wks | High (~30%) | Broad `Frame`/`Segment`/`EntryOwner` ghost-rep change; **cascades into `PageTableConfig` trait methods**; depends on Stage C for PtPath-under-lock provenance. |
| 7. Replace `accounting_inv` | 3–5 wks | Very High (~20%) | Embedding's central invariant (11k-line module); every `step_*` re-proven vs. custody; the "fragile SMT chain" the code already laments. |
| 8. Dissolve accounting machinery | 2–3 wks | Med (~45%) | Mostly subtractive once 7 lands, but each `_embedded`-axiom→theorem is real proof work. |

**Totals (one engineer):** refcount track (1–5) ≈ 7–13 wks; Stage M ≈ 5–9 wks (rides with/after Stage C); Stage P ≈ 3–5 wks (orthogonal — off the critical path with a 2nd engineer); embedding track (6–8) ≈ 8–13 wks; Stage C ≈ 8–16 wks. **Whole program ≈ 31–56 wks (~7–13 months) for one engineer; Stage P is the cleanest slice to parallelize.**

**Sequencing levers:**
- *Two engineers ≈ 40% calendar compression, not 50%* — Stage C is orthogonal to Phase 1 and can run in parallel from day one, but Phases 2→3→4→6→7→8 are a strict invariant chain. Natural split: one owns Stage C, the other drives the refcount/embedding chain.
- *AI assistance compresses volume, not discovery* — helps 1/3/4/5 (templated transitions, 620-site classification, boilerplate bridges); barely helps 2/7/C (novel invariant + cross-codebase reconciliation). Intervention-weighted cost concentrates in **C + 2 + 7 + 6**.
- Carry **+30–50% buffer** on 2, 6, 7, and C specifically.

## 7. Delivery milestones (each full-crate green)

End of **Phase 3** (ops token-driven, transient-0 honest) · **Phase 4** (`ref_count` a real atomic — closes the frame half of the concurrency gap) · **Stage C** (locking axioms discharged) · **Phase 8** (embedding accounting rests on token linearity, not `_embedded` axioms + sequential dispatch).
