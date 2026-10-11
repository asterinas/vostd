# OSTD specification optimization review

Assessment: all **95 Rust files / 55,680 lines** in `ostd/specs` and `ostd/src/mm` were read at HEAD `b761ce631`. This is a static, read-only review. No source changes, compilation, verifier runs, controlled removal experiments, or performance measurements were performed. The findings distinguish two trusted-contract correctness risks from equivalent simplifications, model-scope decisions, and optional presentation cleanup.

The root reviewer checked coverage and source hashes, audited exact evidence ranges, rechecked core invariant/constructor premises, and consumed an independent refutation pass for PT-01 through PT-26. PT-27 and PT-28 received root review. Reported logical redundancy does not establish that removing a fact preserves SMT proof success; cached facts, opacity, and triggers can matter.

Exclusions honored: `into_pte_owner_spec` / `from_pte_owner_spec`; manually expanded level clauses in `Cursor::wf`; the three accepted `mappings_*` free functions. No `Set<Mapping>` extension trait is proposed. Physical alias policies remain distinct; shared-page models must not inherit legacy physical uniqueness merely to share predicates.

## Suggested fix order

1. Repair P01 / PT-01 and PT-28 as trusted-contract correctness work. Decide metadata slot-domain semantics before applying P17/P18.
2. Remove exact duplicate calls/clauses and tautologies: P02–P06, P13, P15; M1, M4, M8, M12, M17–M18; PT-05–PT-08, PT-16–PT-20. Keep any separately meaningful frame/resource postconditions.
3. Consolidate repeated models and proven helpers: P08, P12, P14, P23; M5–M7, M11; PT-02–PT-04, PT-10–PT-14, PT-21–PT-24. Verify the smallest affected module after each coherent change.
4. Handle opaque/derived invariants (P09–P11, P16–P18, PT-09/PT-15) with checked implication lemmas and trigger review. Decide model/API intent separately for P19–P22. Leave optional layout work last.

## Finding index

| ID | Priority | Finding |
| --- | --- | --- |
| [P01](#p01) | High | Root allocation contracts contradict the total metadata-slot domain (merged P01 / PT-01) |
| [P02](#p02) | Low | Delete duplicate broadcast lemma |
| [P03](#p03) | Low | Remove unused tautological preservation lemma |
| [P04](#p04) | Low | Remove repeated frame-drop frame clause |
| [P05](#p05) | Low | Remove transitive bound from VirtPtr invariant |
| [P06](#p06) | Low | Remove copy preconditions already supplied by pointer invariants |
| [P07](#p07) | Low | Remove writer-removal presence requirement implied by invariant |
| [P08](#p08) | Medium | Reuse the established mapping-set disjointness predicate |
| [P09](#p09) | Medium | Remove global-accounting conjunct implied by complement equivalence |
| [P10](#p10) | Medium | Derive TLB disjointness from PT disjointness and subset |
| [P11](#p11) | Low | Remaining-view disjointness follows total-view disjointness and subset |
| [P12](#p12) | Medium | Replace recursive pointwise view model with Seq::map_values |
| [P13](#p13) | Low | Collapse equal cursor-transition branches |
| [P14](#p14) | Medium | Share the identical metadata-pointer validity model |
| [P15](#p15) | Low | Eliminate in-list facts already included in frame_link_inv |
| [P16](#p16) | Medium | Use the stronger region relation instead of threading duplicate list invariants |
| [P17](#p17) | Low | Drop valid-address membership checks implied by region validity |
| [P18](#p18) | Low | Drop slot-owner domain preservation implied by old/final invariants |
| [P19](#p19) | Medium | Eliminate the one-call wrapper duplicating an entire trusted contract |
| [P20](#p20) | Low | Delete unconsumed aliases and unused owner helpers |
| [P21](#p21) | Medium | Remove unused per-op adapters after reconciling incomplete dispatcher behavior |
| [P22](#p22) | Low | Remove unused redundant precondition facade and dormant API helpers |
| [P23](#p23) | Medium | Factor repeated read/write memory-view properties |
| [P24](#p24) | Medium | Consolidate duplicated owner-splitting proof |
| [M1](#m1) | Medium | Delete duplicated architecture arithmetic lemma calls |
| [M2](#m2) | Low | Remove the unused CPU-local covers alias |
| [M3](#m3) | Low | Remove unused same-CPU authority lemma |
| [M4](#m4) | Medium | Erase the always-true DMA address predicate |
| [M5](#m5) | Medium | Reuse constructor memory views instead of minting them twice |
| [M6](#m6) | Medium | Delete dormant VmIoOnce policy hooks |
| [M7](#m7) | Medium | Collapse duplicate success/error byte-count contracts |
| [M8](#m8) | Low | Remove duplicate dereferenced-owner assertions |
| [M9](#m9) | Medium | Remove a vacuous implementation postcondition inherited from VmIo |
| [M10](#m10) | Medium | Remove duplicate Frame::meta pointer precondition |
| [M11](#m11) | Medium | Replace the affine address history with its formula |
| [M12](#m12) | Low | Delete the repeated segment loop bound |
| [M13](#m13) | Low | Inline a one-conjunct Segment invariant alias |
| [M14](#m14) | Low | Drop the duplicate exact Segment::size contract |
| [M15](#m15) | Low | Remove tautological PhantomData equality |
| [M16](#m16) | Medium | Remove an unused erased owner argument |
| [M17](#m17) | Low | Remove duplicated external_body annotation |
| [M18](#m18) | Medium | Delete equivalent LinkedList drop membership quantifier |
| [M19](#m19) | Medium | Delete duplicate KVirtArea proof calls |
| [M20](#m20) | Medium | Drop the overflow bound already implied by bounds policy |
| [M21](#m21) | Medium | Reuse the StrayPageTable disjoint-cardinality proof |
| [M22](#m22) | Low | Use returns for exact getters and omit unused binders |
| [M23](#m23) | Low | Keep the single-use stride proof inside its caller |
| [PT-02](#pt-02) | Low | A complete legacy model family is unused by the current page-table proof. |
| [PT-03](#pt-03) | Low | map_full_tree and map_only_children define exactly the same predicate. |
| [PT-04](#pt-04) | Low | CursorView duplicates common mapping-set well-formedness and disjointness predicates. |
| [PT-05](#pt-05) | Low | NodeOwner repeats the child counter bound already carried by its metadata owner invariant. |
| [PT-06](#pt-06) | Low | metaregion_sound_node repeats the metadata cell identity supplied by wf. |
| [PT-07](#pt-07) | Low | relate_guard repeats its guard pointer equality. |
| [PT-08](#pt-08) | Low | Entry::wf repeats the PTE address validity already in match_pte. |
| [PT-09](#pt-09) | Medium | PageTableOwner::inv stores a path-correctness property already derivable from its tree invariant. |
| [PT-10](#pt-10) | Low | Unused not_in_scope predicate and recursive proof remain in the tree API. |
| [PT-11](#pt-11) | Low | User-specific view bound proof duplicates the generic view-range proof. |
| [PT-12](#pt-12) | Low | Unused kernel-specific view-range proof duplicates the generic result. |
| [PT-13](#pt-13) | Low | CursorOwner::map_children_implies reimplements continuation predicate lifting. |
| [PT-14](#pt-14) | Low | max_steps_partial_inv duplicates the recursive equality lemma immediately above it. |
| [PT-15](#pt-15) | Low | An inv-unfolding helper takes unnecessary range/pop premises for a bound already in inv. |
| [PT-16](#pt-16) | Low | empty_with_owner repeats node and lock-preservation guarantees. |
| [PT-17](#pt-17) | Low | Replacement contracts repeat weak slots preservation beneath exact map equality. |
| [PT-18](#pt-18) | Low | find_next_impl loop contains duplicate and derived invariants. |
| [PT-19](#pt-19) | Low | cur_entry spells out consequences of its existing reborrow equalities. |
| [PT-20](#pt-20) | Low | move_forward separately guarantees a field of already preserved slot owners. |
| [PT-21](#pt-21) | Low | Huge split repeatedly proves the same pure arithmetic witness in one iteration. |
| [PT-22](#pt-22) | Low | The count-equality helper carries an irrelevant idx parameter through recursion. |
| [PT-23](#pt-23) | Medium | Two branches duplicate the same long proof that skipping an empty slot extends the scanned-empty range. |
| [PT-24](#pt-24) | Medium | Many split lemmas repeat query_mapping filtered-set choice reasoning. |
| [PT-25](#pt-25) | Low | Several exact-result equalities use ensures instead of returns. |
| [PT-26](#pt-26) | Low | Historical helper debt documentation is now attached to PageTableFrag and describes obsolete raw_count accounting. |
| [PT-27](#pt-27) | Low | take_next and replacement postconditions repeatedly project the same Option/enum payload. |
| [PT-28](#pt-28) | High | Trusted DFS return count is equated to an unconstrained caller-chosen nat, making an oversized choice impossible for a successful usize return. |

## High findings

<a id="p01"></a>
### P01 — Root allocation contracts contradict the total metadata-slot domain (merged P01 / PT-01)

**Evidence / premise.** old.contains(root) and old.inv place root in [0,max_meta_slots). final.inv gives root in final.slot_owners and final.slots, contradicting Map::remove at root. Underlying empty_with_owner already promises old.contains(root), !final.contains(root), final.inv.

**Suggested change.** Reconcile root allocation with current total parked-slot invariant, updating both trusted executable front door and mirrored embedding. Preserve validity; do not merely delete final.inv.

**Root qualification.** Choose a consistent total-domain or partial-domain resource model before changing these contracts. Do not simply delete final(regions).inv(). Successful verification against a trusted inconsistent contract would not establish soundness.

**Guideline / confidence.** complete-external-contracts; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/meta_region_owners.rs:42, ostd/specs/mm/frame/meta_region_owners.rs:65, ostd/src/mm/page_table/mod.rs:1302, ostd/src/mm/page_table/mod.rs:1320, ostd/specs/mm/embedding/mod.rs:1128.

[ostd/specs/mm/embedding/vm_space.rs:57](ostd/specs/mm/embedding/vm_space.rs#L57) (lines 57–69)

```rust
57:         final(regions).slots == old(regions).slots.remove(vm_space_root_idx(res)),
58:         final(regions).slot_owners[vm_space_root_idx(res)].usage is PageTable,
59:         final(regions).ref_count(vm_space_root_idx(res)) != REF_COUNT_UNUSED,
60:         forall|i: int|
61:             #![trigger final(regions).slot_owners[i]]
62:             final(regions).slot_owners[i].in_list_perm == old(regions).slot_owners[i].in_list_perm,
63:         forall|i: int|
64:             #![trigger final(regions).slot_owners[i]]
65:             final(regions).slot_owners[i] != old(regions).slot_owners[i] ==> {
66:                 &&& old(regions).ref_count(i) == REF_COUNT_UNUSED
67:                 &&& final(regions).ref_count(i) != REF_COUNT_UNUSED
68:                 &&& final(regions).slot_owners[i].usage is PageTable
69:             },
```

[ostd/src/mm/page_table/mod.rs:1301](ostd/src/mm/page_table/mod.rs#L1301) (lines 1301–1323)

```rust
1301:         requires
1302:             old(regions).inv(),
1303:         ensures
1304:             final(owner)@ is Some,
1305:             final(owner)@->0.inv(),
1306:             (final(owner)@->0).0.value().is_node(),
1307:             (final(owner)@->0).0.value().is_node(),
1308:             r.root.ptr.addr() == (final(owner)@->0).0.value().node().slot_vaddr(),
1309:             (final(owner)@->0).0.value().metaregion_sound(*final(regions)),
1310:             final(regions).inv(),
1311:             final(guards).unlocked((final(owner)@->0).0.value().node().slot_vaddr()),
1312:             // Allocating a fresh node does not change the lock set, so any node
1313:             // that was (un)locked before remains so.
1314:             final(guards).guards == old(guards).guards,
1315:             // The newly allocated slot was in the free pool before the call.
1316:             old(regions).contains(
1317:                 crate::specs::mm::frame::mapping::frame_to_index(
1318:                     (final(owner)@->0).0.value().meta_slot_paddr()->0)),
1319:             // After the alloc, the slot is removed from the free pool (now owned
1320:             // by the new pt's NodeOwner).
1321:             !final(regions).contains(
1322:                 crate::specs::mm::frame::mapping::frame_to_index(
1323:                     (final(owner)@->0).0.value().meta_slot_paddr()->0)),
```

[ostd/specs/mm/frame/meta_region_owners.rs:38](ostd/specs/mm/frame/meta_region_owners.rs#L38) (lines 38–68)

```rust
38:     open spec fn inv(self) -> bool {
39:         &&& {
40:             // Keep the map-membership trigger: callers frequently expose a
41:             // slot-owner lookup without mentioning the `contains` wrapper.
42:             forall|i: int|
43:                 0 <= i < max_meta_slots() <==> #[trigger] self.slot_owners.contains_key(i)
44:         }
45:         &&& {
46:             forall|i: int| #[trigger]
47:                 self.slot_owners.contains_key(i) ==> self.slots.contains_key(i)
48:         }
49:         &&& { forall|i: int| #[trigger] self.slots.contains_key(i) ==> 0 <= i < max_meta_slots() }
50:         &&& {
51:             forall|i: int| #[trigger]
52:                 self.slots.contains_key(i) ==> {
53:                     &&& self.slot_owners[i].inv()
54:                     &&& self.slots[i].is_init()
55:                     &&& self.slots[i].addr() == index_to_meta(i)
56:                     &&& self.slots[i].value().wf(self.slot_owners[i])
57:                     &&& self.slot_owners[i].slot_vaddr == self.slots[i].addr()
58:                 }
59:         }
60:     }
61: }
62:
63: impl MetaRegionOwners {
64:     /// Returns whether the slot permission and its corresponding owner are both present.
65:     pub open spec fn contains(self, index: int) -> bool {
66:         &&& self.slot_owners.contains_key(index)
67:         &&& self.slots.contains_key(index)
68:     }
```

<a id="pt-28"></a>
### PT-28 — Trusted DFS return count is equated to an unconstrained caller-chosen nat, making an oversized choice impossible for a successful usize return.

**Evidence / premise.** The only requires are owner.inv632 and a guard lock634. Ghost subtree_mappings_count630 is never related to sub_tree or owner. Choosing usize::MAX+1 yields res as nat == usize::MAX+1 while res:usize, contradiction. Source caller cursor/mod.rs3768-3771 passes an actual ghost-view cardinality, but this does not constrain other callers or the trusted generic contract.

**Suggested change.** Require the supplied count to equal a proved cardinality of the actual removed subtree and require representability, or derive the model count within the contract from a related subtree owner. Preserve all lock, mutation and ownership framing guarantees.

**Root qualification.** Root independently read the full contract and external_body marker. For any state satisfying the two requires, the nat argument remains unconstrained. A successful usize return cannot equal usize::MAX+1. Current caller choices do not repair the generic contract.

**Guideline / confidence.** complete-external-contracts; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/cursor/locking.rs:630](ostd/src/mm/page_table/cursor/locking.rs#L630) (lines 630–638)

```rust
630:         Ghost(subtree_mappings_count): Ghost<nat>
631:     requires
632:         old(owner).inv(),
633:         // The locked_addr must be the address that was locked (held in guards)
634:         old(guards).lock_held(locked_addr),
635:     ensures
636:         // The return value equals the number of mappings in the subtree.
637:         // This connects the physical DFS frame count to the ghost view_rec mappings count.
638:         res as nat == subtree_mappings_count,
```

## Medium findings

<a id="p08"></a>
### P08 — Reuse the established mapping-set disjointness predicate

**Evidence / premise.** This definition and its membership triggers are exactly mappings_disjoint_vaddrs(self.mappings), which unfolds Mapping::disjoint_vaddrs to the same VA-end comparison. No PA disjointness should be added.

**Suggested change.** Keep this useful method as an alias to mappings_disjoint_vaddrs(self.mappings), or migrate callers to the existing free function.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/page_table/view.rs:39, ostd/specs/mm/page_table/view.rs:76.

[ostd/specs/mm/virt_mem.rs:232](ostd/specs/mm/virt_mem.rs#L232) (lines 232–244)

```rust
232:     pub open spec fn mappings_are_disjoint(self) -> bool {
233:         forall|m1: Mapping, m2: Mapping|
234:             #![trigger self.mappings.contains(m1), self.mappings.contains(m2)]
235:             self.mappings.contains(m1) && self.mappings.contains(m2) && m1 != m2 ==> {
236:                 m1.va_range.end <= m2.va_range.start || m2.va_range.end <= m1.va_range.start
237:             }
238:     }
239:
240:     /// Specification for splitting this view at `split_end = vaddr + len`.
241:     ///
242:     /// Returns `(left, right)` where:
243:     /// - `left` covers `[vaddr, split_end)`, i.e. all mappings overlapping that range.
244:     /// - `right` covers addresses `>= split_end`.
```

<a id="p09"></a>
### P09 — Remove global-accounting conjunct implied by complement equivalence

**Evidence / premise.** unmapped_correct states forall pa, is_mapped(pa) <==> !unmapped_pas.contains(pa). Classical excluded middle then implies is_mapped(pa)||unmapped_pas.contains(pa), including the narrower 0<=pa<MAX_PADDR domain.

**Suggested change.** Remove all_pas_accounted_for from inv; retain the complement equivalence. Since no other consumers exist, delete helper if the dormant global-view model remains.

**Root qualification.**  Logical entailment is a candidate for proof reuse, not evidence that deleting the conjunct will verify or improve performance.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/virt_mem.rs:1089, ostd/specs/mm/virt_mem.rs:1103.

[ostd/specs/mm/virt_mem.rs:1065](ostd/specs/mm/virt_mem.rs#L1065) (lines 1065–1077)

```rust
1065:         &&& self.all_pas_accounted_for()
1066:         &&& self.pas_uniquely_mapped()
1067:         &&& self.unmapped_correct()
1068:     }
1069: }
1070:
1071: impl GlobalMemView {
1072:     pub open spec fn addr_transl(self, va: usize) -> Option<(usize, usize)> {
1073:         let mappings = self.tlb_mappings.filter(
1074:             |m: Mapping| m.va_range.start <= va < m.va_range.end,
1075:         );
1076:         if 0 < mappings.len() {
1077:             let m = mappings.choose();  // In a well-formed TLB there will only be one, but if malformed this is non-deterministic!
```

<a id="p10"></a>
### P10 — Derive TLB disjointness from PT disjointness and subset

**Evidence / premise.** GlobalMemView::inv already requires PT VA and PA disjointness. The TLB subset clause transports both properties; its explicit TLB VA quantifier and pas_uniquely_mapped call repeat them. Shared PA aliases elsewhere are irrelevant: this older model explicitly assumes PT PA disjointness.

**Suggested change.** Keep subset plus PT disjointness; derive or expose TLB disjointness by a reuse lemma where needed. Do not impose this older PA uniqueness policy on other models.

**Root qualification.**  Logical entailment is a candidate for proof reuse, not evidence that deleting the conjunct will verify or improve performance.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/virt_mem.rs:1047, ostd/specs/mm/virt_mem.rs:1051, ostd/specs/mm/virt_mem.rs:1055, ostd/specs/mm/virt_mem.rs:1095.

[ostd/specs/mm/virt_mem.rs:1059](ostd/specs/mm/virt_mem.rs#L1059) (lines 1059–1071)

```rust
1059:         &&& forall|m: Mapping|
1060:             forall|n: Mapping|
1061:                 #![auto]
1062:                 self.tlb_mappings.contains(m) ==> self.tlb_mappings.contains(n) ==> m != n
1063:                     ==> #[trigger] m.va_range.end <= n.va_range.start || n.va_range.end
1064:                     <= m.va_range.start
1065:         &&& self.all_pas_accounted_for()
1066:         &&& self.pas_uniquely_mapped()
1067:         &&& self.unmapped_correct()
1068:     }
1069: }
1070:
1071: impl GlobalMemView {
```

<a id="p12"></a>
### P12 — Replace recursive pointwise view model with Seq::map_values

**Evidence / premise.** Full recursive definition maps each owner to owner.view, preserving sequence length/order. Vendored Seq::map_values is Seq::new(self.len(), |i| f(self[i])). Local recursive length/index lemmas exist solely to recover these canonical properties.

**Suggested change.** Define view_helper as owners.map_values(|owner: LinkOwner| owner@), then replace length/index scaffolding with standard facts and retain insertion bridge only if current callers need it.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: tools/verus/source/vstd/seq_lib.rs:30, ostd/specs/mm/frame/linked_list/linked_list_owners.rs:920, ostd/specs/mm/frame/linked_list/linked_list_owners.rs:931, ostd/src/mm/frame/linked_list.rs:220, ostd/specs/mm/frame/linked_list/linked_list_specs.rs:93.

[ostd/specs/mm/frame/linked_list/linked_list_owners.rs:910](ostd/specs/mm/frame/linked_list/linked_list_owners.rs#L910) (lines 910–922)

```rust
910:     pub open spec fn view_helper(owners: Seq<LinkOwner>) -> Seq<LinkModel>
911:         decreases owners.len(),
912:     {
913:         if owners.len() == 0 {
914:             Seq::<LinkModel>::empty()
915:         } else {
916:             seq![owners[0].view()].add(Self::view_helper(owners.remove(0)))
917:         }
918:     }
919:
920:     pub proof fn lemma_view_preserves_len(owners: Seq<LinkOwner>)
921:         ensures
922:             Self::view_helper(owners).len() == owners.len(),
```

<a id="p14"></a>
### P14 — Share the identical metadata-pointer validity model

**Evidence / premise.** UniqueFrame::start_paddr_spec is meta_to_frame(self.ptr.addr()). Its first three ptr_inv clauses are exactly valid_slot_vaddr(self.ptr.addr()), already used by Frame::ptr_inv. Permission-pointer equality and initialization are also identical.

**Suggested change.** Use valid_slot_vaddr(self.ptr.addr()) in UniqueFrame::ptr_inv; retain the owning frame types' distinct resource invariants.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/frame_specs.rs:32, ostd/specs/mm/frame/frame_specs.rs:100, ostd/specs/mm/frame/unique.rs:30.

[ostd/specs/mm/frame/unique.rs:50](ostd/specs/mm/frame/unique.rs#L50) (lines 50–62)

```rust
50:     pub open spec fn ptr_inv(self) -> bool {
51:         &&& valid_frame_paddr(self.start_paddr_spec())
52:         &&& self.ptr.addr() % META_SLOT_SIZE == 0
53:         &&& FRAME_METADATA_RANGE.start <= self.ptr.addr() < FRAME_METADATA_RANGE.start
54:             + MAX_NR_PAGES * META_SLOT_SIZE
55:         &&& self.slot_perm().pptr() == self.ptr
56:         &&& self.slot_perm().is_init()
57:     }
58: }
59:
60: impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrame<M> {
61:     open spec fn inv(self) -> bool {
62:         &&& self.ptr_inv()
```

<a id="p16"></a>
### P16 — Use the stronger region relation instead of threading duplicate list invariants

**Evidence / premise.** relate_region supplies both permission lengths and nonempty=>nonzero id; each relate_region_at supplies list[i].in_list==list_id and list[i].inv. These are exactly all LinkedListOwner::inv clauses. Thus list.inv adds no semantics at these combined sites.

**Suggested change.** Introduce a reusable relate_region-implies-inv lemma, then consider removing duplicate inv at combined sites only after checking opaque-predicate instantiation and proof performance; retain inv for independent APIs.

**Root qualification.** relate_region is opaque: first prove the implication as a checked helper. Do not blanket-reveal or remove cached facts without measuring proof behavior.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/linked_list/linked_list_owners.rs:245, ostd/specs/mm/frame/linked_list/linked_list_owners.rs:315, ostd/specs/mm/frame/linked_list/linked_list_owners.rs:324, ostd/specs/mm/embedding/list_store.rs:253.

[ostd/specs/mm/embedding/list_store.rs:133](ostd/specs/mm/embedding/list_store.rs#L133) (lines 133–145)

```rust
133:             self.lists.dom().contains(id) ==> {
134:                 &&& self.lists[id].inv()
135:                 &&& self.lists[id].relate_region(self.regions)
136:             }
137:         &&& forall|lid: LooseId| #[trigger]
138:             self.loose.dom().contains(lid) ==> {
139:                 &&& self.loose[lid].inv()
140:                 &&& self.loose[lid].global_inv(self.regions)
141:                 &&& self.loose[lid].frame_link_inv(self.regions)
142:                 &&& self.regions.slot_owners[self.loose[lid].slot_index].in_list_perm.value() == 0
143:             }
144:             // Distinct lists carry distinct *nonzero* ids.
145:         &&& forall|id1: ListId, id2: ListId|
```

<a id="p19"></a>
### P19 — Eliminate the one-call wrapper duplicating an entire trusted contract

**Evidence / premise.** new_vm_space_step has one direct caller at embedding/mod.rs:1128; body is precisely the axiom call and full requires/ensures are copied without adaptation. No documented separate opacity boundary.

**Suggested change.** After correcting root-allocation contract, call vm_space_new_embedded directly and delete the duplicate wrapper.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/embedding/mod.rs:1128, ostd/specs/mm/embedding/vm_space.rs:37.

[ostd/specs/mm/embedding/vm_space.rs:82](ostd/specs/mm/embedding/vm_space.rs#L82) (lines 82–94)

```rust
82: pub(super) proof fn new_vm_space_step<'a>(tracked regions: &mut MetaRegionOwners) -> (tracked res:
83:     VmSpaceOwner)
84:     requires
85:         old(regions).inv(),
86:     ensures
87:         final(regions).inv(),
88:         res.inv(),
89:         // `VmSpace::new` (`create_user_page_table` → `empty_with_owner`)
90:         // allocates a fresh PT root and PERMANENTLY extracts its slot
91:         // perm from `regions.slots` (the root is owned by the page table,
92:         // not parked in the free pool). Every OTHER slot perm is
93:         // preserved. The extracted root slot is an active page-table node
94:         // (`usage == PageTable`, `rc != UNUSED`) — exactly the
```

<a id="p21"></a>
### P21 — Remove unused per-op adapters after reconciling incomplete dispatcher behavior

**Evidence / premise.** Declaration-only search also finds cursor_find_next_step, cursor_jump_step, cursor_protect_next_step, cursor_mut_regions_step; dispatchers for find/jump/protect/unmap currently only extract entries, without calling adapters/reinserting. Removing the adapters silently would obscure an incomplete embedding.

**Suggested change.** First decide whether these transitions are required to model the named executable API; wire the existing adapters and restore entries if so. Otherwise explicitly document reduced theorem scope and delete unused adapter cluster. Do not count the no-op/extraction proof as equivalent operational behavior.

**Root qualification.** Model-coverage decision, not a demonstrated semantics-preserving deletion. The invariant-preservation theorem may hold while the dispatcher fails to model the named operation. Confirm intended refinement scope.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/embedding/mod.rs:1286, ostd/specs/mm/embedding/mod.rs:1298, ostd/specs/mm/embedding/mod.rs:1310, ostd/specs/mm/embedding/mod.rs:1447.

[ostd/specs/mm/embedding/cursor.rs:551](ostd/specs/mm/embedding/cursor.rs#L551) (lines 551–563)

```rust
551: pub(super) proof fn drop_cursor_step<'rcu>(tracked _entry: CursorEntry<'rcu>) {
552: }
553:
554: pub(super) proof fn cursor_query_step<'rcu>(
555:     tracked entry: &mut CursorEntry<'rcu>,
556:     tracked regions: &mut MetaRegionOwners,
557: ) -> (res: Option<Paddr>)
558:     requires
559:         old(entry).inv(),
560:         old(regions).inv(),
561:         old(entry).owner.metaregion_sound(*old(regions)),
562:     ensures
563:         final(entry).vm_space == old(entry).vm_space,
```

<a id="p23"></a>
### P23 — Factor repeated read/write memory-view properties

**Evidence / premise.** VmIoOwner::inv repeats identical mapping-disjointness/coverage formulas for both variants; disjoint repeats the same lmv.mappings.disjoint(rmv.mappings) for all four variant combinations. Variant distinction is meaningful for access, but irrelevant to these predicates.

**Suggested change.** Expose a single spec projection of VmIoMemView to its underlying MemView and use it for invariant/overlap properties; keep has_read/has_write/read_initialized variant checks.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/io.rs:118, ostd/specs/mm/io.rs:125, ostd/specs/mm/io.rs:196.

[ostd/specs/mm/io.rs:137](ostd/specs/mm/io.rs#L137) (lines 137–149)

```rust
137:
138: impl VmIoOwner {
139:     /// Whether this owner carries a read memory view.
140:     #[verifier::inline]
141:     pub open spec fn has_read_view(self) -> bool {
142:         self.mem_view matches Some(VmIoMemView::ReadView(_))
143:     }
144:
145:     /// Whether this owner carries a write memory view.
146:     #[verifier::inline]
147:     pub open spec fn has_write_view(self) -> bool {
148:         self.mem_view matches Some(VmIoMemView::WriteView(_))
149:     }
```

<a id="p24"></a>
### P24 — Consolidate duplicated owner-splitting proof

**Evidence / premise.** advance and split repeat tracked_split, translation, disjointness, and initialized-read proofs over identical left/right MemViews. Only wrapping left into VmIoOwner differs; advance currently lacks left-half facts required by split.

**Suggested change.** Strengthen advance's result contract with the already proved left-half coverage/kind/initialization facts, then implement split through advance plus owner construction. Keep all current guarantees and reverify before deleting proof assertions. Preserve advance's byte-preservation guarantees even where split currently promises less.

**Root qualification.** advance additionally guarantees byte preservation. Any shared split primitive must preserve that guarantee and strengthen the appropriate output contract; this is not a mechanical duplicate deletion.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: medium. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/io.rs:256, ostd/specs/mm/io.rs:294, ostd/specs/mm/io.rs:413.

[ostd/specs/mm/io.rs:374](ostd/specs/mm/io.rs#L374) (lines 374–386)

```rust
374:     /// - If the original was an initialized read view, both sides remain initialized.
375:     pub proof fn split(tracked &mut self, nbytes: usize) -> (tracked r: VmIoOwner)
376:         requires
377:             old(self).inv(),
378:             old(self).mem_view is Some,
379:             nbytes <= old(self).range.end - old(self).range.start,
380:         ensures
381:             r.inv(),
382:             r.range.start == old(self).range.start,
383:             r.range.end == old(self).range.start + nbytes,
384:             r.is_fallible == old(self).is_fallible,
385:             r.is_kernel == old(self).is_kernel,
386:             r.mem_view is Some,
```

<a id="m1"></a>
### M1 — Delete duplicated architecture arithmetic lemma calls

**Evidence / premise.** The same two pure lemmas are called consecutively with identical constants, with no intervening state changes.

**Suggested change.** Keep the first calls for12 and9 and delete the second pair.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/arch/x86/mod.rs:133](ostd/specs/arch/x86/mod.rs#L133) (lines 133–136)

```rust
133:     lemma_usize_pow2_ilog2(12);
134:     lemma_usize_pow2_ilog2(9);
135:     lemma_usize_pow2_ilog2(12);
136:     lemma_usize_pow2_ilog2(9);
```

<a id="m4"></a>
### M4 — Erase the always-true DMA address predicate

**Evidence / premise.** is_valid_daddr is literally true for every Daddr. Its only executable-module uses are DmaCoherentInner::inv and DmaStreamInner::inv conjuncts; these constrain nothing.

**Suggested change.** Delete is_valid_daddr and the two conjuncts/imports, or supply a real hardware-address validity model with an actual consumer rather than this placeholder.

**Guideline / confidence.** avoid-unused-spec-helpers, canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/dma/mod.rs:100](ostd/src/mm/dma/mod.rs#L100) (lines 100–103)

```rust
100: #[verifier::inline]
101: pub open spec fn is_valid_daddr(d: Daddr) -> bool {
102:     true
103: }
```

[ostd/src/mm/dma/dma_coherent.rs:88](ostd/src/mm/dma/dma_coherent.rs#L88) (lines 88–94)

```rust
88:
89: impl<M: AnyUFrameMeta + ?Sized> Inv for DmaCoherentInner<M> {
90:     open spec fn inv(self) -> bool {
91:         &&& self.segment.inv()
92:         &&& is_valid_daddr(self.start_daddr)
93:     }
94: }
```

[ostd/src/mm/dma/dma_stream.rs:689](ostd/src/mm/dma/dma_stream.rs#L689) (lines 689–695)

```rust
689:
690: impl<M: AnyUFrameMeta + ?Sized> Inv for DmaStreamInner<M> {
691:     open spec fn inv(self) -> bool {
692:         &&& self.segment.inv()
693:         &&& is_valid_daddr(self.start_daddr)
694:     }
695: }
```

<a id="m5"></a>
### M5 — Reuse constructor memory views instead of minting them twice

**Evidence / premise.** VmReader::from_kernel_space and VmWriter::from_kernel_space already call axiom_kernel_mem_view and initialize owner.mem_view when the kernel-range obligations hold. These DMA wrappers prove those same obligations and then mint a second view, overwriting the first. The same pattern occurs in six reader/writer paths.

**Suggested change.** Use the constructor guarantees and remove the six second axiom_kernel_mem_view calls and owner.mem_view assignments. Keep all address/range obligations. Confirm the stronger DMA reader/writer invariant from the constructor result.

**Root qualification.** Constructor contracts already supply the resulting view invariant and wf when pointer/kernel-range premises hold. Check those premises at all six sites before removing the second mint; no variant was verified.

**Guideline / confidence.** reuse-existing-specifications, centralize-trusted-boundaries; static premise confidence: medium. All implementation and solver outcomes remain unverified.

[ostd/src/mm/dma/dma_coherent.rs:286](ostd/src/mm/dma/dma_coherent.rs#L286) (lines 286–295)

```rust
286:
287:         let reader = unsafe {
288:             proof_with!(Ghost(id) => Tracked(reader_owner));
289:             VmReader::from_kernel_space(ptr, len)
290:         };
291:         proof {
292:             let tracked mem_view = axiom_kernel_mem_view(range);
293:             reader_owner.mem_view = Some(VmIoMemView::ReadView(mem_view));
294:         }
295:         proof_with!(|= Tracked(reader_owner));
```

[ostd/src/mm/io.rs:274](ostd/src/mm/io.rs#L274) (lines 274–299)

```rust
274:             !fallible && ptr.inv() && ptr.range@.start == ptr.vaddr
275:                 && len == ptr.range@.end - ptr.range@.start
276:                 && (len == 0 || KERNEL_BASE_VADDR <= ptr.vaddr)
277:                 && (len == 0 || ptr.vaddr + len <= KERNEL_END_VADDR) ==> {
278:                 &&& r.inv()
279:                 &&& owner@.inv()
280:                 &&& r.wf(owner@)
281:                 &&& owner@.has_write_view()
282:             },
283:     )]
284:     pub unsafe fn from_kernel_space(ptr: VirtPtr, len: usize) -> Self {
285:         let ghost range: Range<usize> = ptr.vaddr..(ptr.vaddr + len) as usize;
286:         let tracked mem_view: Option<VmIoMemView> = if fallible {
287:             None
288:         } else {
289:             let tracked mv = axiom_kernel_mem_view(range);
290:             Some(VmIoMemView::WriteView(mv))
291:         };
292:         let tracked owner = VmIoOwner {
293:             id,
294:             range: ptr.vaddr..(ptr.vaddr + len) as usize,
295:             is_fallible: fallible,
296:             is_kernel: true,
297:             mem_view,
298:         };
299:
```

[ostd/src/mm/io.rs:692](ostd/src/mm/io.rs#L692) (lines 692–727)

```rust
692:     /// `ptr` must be [valid] for reads of `len` bytes during the entire lifetime `a`.
693:     ///
694:     /// [valid]: crate::mm::io#safety
695:     #[verus_spec(r =>
696:         with
697:             Ghost(id): Ghost<nat>,
698:             -> owner: Tracked<VmIoOwner>,
699:         ensures
700:             r.inv_wf(),
701:             owner@.id == id,
702:             owner@.is_kernel,
703:             r.cursor == ptr,
704:             r.end == ptr.wrapping_add_spec(len),
705:             r.cursor.range@ == ptr.range@,
706:             r.end.range@ == ptr.range@,
707:             ptr.inv() && ptr.range@.start == ptr.vaddr
708:                 && len == ptr.range@.end - ptr.range@.start
709:                 && (len == 0 || KERNEL_BASE_VADDR <= ptr.vaddr)
710:                 && (len == 0 || ptr.vaddr + len <= KERNEL_END_VADDR) ==> {
711:                 &&& r.inv()
712:                 &&& owner@.inv()
713:                 &&& r.wf(owner@)
714:                 &&& owner@.read_view_initialized()
715:             },
716:     )]
717:     pub unsafe fn from_kernel_space(ptr: VirtPtr, len: usize) -> Self {
718:         let ghost range: Range<usize> = ptr.vaddr..(ptr.vaddr + len) as usize;
719:         let tracked mv = axiom_kernel_mem_view(range);
720:         let tracked owner = VmIoOwner {
721:             id,
722:             range,
723:             is_fallible: false,
724:             is_kernel: true,
725:             mem_view: Some(VmIoMemView::ReadView(mv)),
726:         };
727:
```

[ostd/src/mm/dma/dma_coherent.rs:338](ostd/src/mm/dma/dma_coherent.rs#L338) (lines 338–345)

```rust
338:         let writer = unsafe {
339:             proof_with!(Ghost(id), Tracked(false) => Tracked(writer_owner));
340:             VmWriter::from_kernel_space(ptr, len)
341:         };
342:         proof {
343:             let tracked mem_view = axiom_kernel_mem_view(range);
344:             writer_owner.mem_view = Some(VmIoMemView::WriteView(mem_view));
345:         }
```

[ostd/src/mm/dma/dma_stream.rs:246](ostd/src/mm/dma/dma_stream.rs#L246) (lines 246–254)

```rust
246:                                 let reader = unsafe {
247:                                     proof_with!(Ghost(id) => Tracked(reader_perm));
248:                                     VmReader::from_kernel_space(ptr, self.len)
249:                                 };
250:                                 proof {
251:                                     let tracked mem_view = axiom_kernel_mem_view(range);
252:                                     reader_perm.mem_view = Some(VmIoMemView::ReadView(mem_view));
253:                                 }
254:                                 proof_with!(|= Tracked(Some(reader_perm)));
```

[ostd/src/mm/dma/dma_stream.rs:333](ostd/src/mm/dma/dma_stream.rs#L333) (lines 333–341)

```rust
333:                                 let writer = unsafe {
334:                                     proof_with!(Ghost(id), Tracked(false) => Tracked(writer_perm));
335:                                     VmWriter::from_kernel_space(ptr, self.len)
336:                                 };
337:                                 proof {
338:                                     let tracked mem_view = axiom_kernel_mem_view(range);
339:                                     writer_perm.mem_view = Some(VmIoMemView::WriteView(mem_view));
340:                                 }
341:                                 proof_with!(|= Tracked(Some(writer_perm)));
```

[ostd/src/mm/dma/dma_stream.rs:618](ostd/src/mm/dma/dma_stream.rs#L618) (lines 618–626)

```rust
618:         let reader = unsafe {
619:             proof_with!(Ghost(id) => Tracked(reader_owner));
620:             VmReader::from_kernel_space(ptr, len)
621:         };
622:         proof {
623:             let tracked mem_view = axiom_kernel_mem_view(range);
624:             reader_owner.mem_view = Some(VmIoMemView::ReadView(mem_view));
625:         }
626:         proof_with!(|= Tracked(reader_owner));
```

[ostd/src/mm/dma/dma_stream.rs:677](ostd/src/mm/dma/dma_stream.rs#L677) (lines 677–685)

```rust
677:         let writer = unsafe {
678:             proof_with!(Ghost(id), Tracked(false) => Tracked(writer_owner));
679:             VmWriter::from_kernel_space(ptr, len)
680:         };
681:         proof {
682:             let tracked mem_view = axiom_kernel_mem_view(range);
683:             writer_owner.mem_view = Some(VmIoMemView::WriteView(mem_view));
684:         }
685:         proof_with!(|= Tracked(writer_owner));
```

<a id="m6"></a>
### M6 — Delete dormant VmIoOnce policy hooks

**Evidence / premise.** Each of these four hook names occurs repo-wide only in this trait declaration and the DmaCoherent override. Neither read_once nor write_once contracts consult them; no macro, broadcast, or spec redirection uses them.

**Suggested change.** Remove the four trait declarations and four constant-true DmaCoherent overrides. If they were meant to gate contracts, that is separate substantive contract work and these current hooks have no effect.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/io.rs:1498](ostd/src/mm/io.rs#L1498) (lines 1498–1504)

```rust
1498:     spec fn obeys_vmio_once_read_requires() -> bool;
1499:
1500:     spec fn obeys_vmio_once_write_requires() -> bool;
1501:
1502:     spec fn obeys_vmio_once_read_ensures() -> bool;
1503:
1504:     spec fn obeys_vmio_once_write_ensures() -> bool;
```

[ostd/src/mm/dma/dma_coherent.rs:801](ostd/src/mm/dma/dma_coherent.rs#L801) (lines 801–815)

```rust
801:     closed spec fn obeys_vmio_once_read_requires() -> bool {
802:         true
803:     }
804:
805:     closed spec fn obeys_vmio_once_write_requires() -> bool {
806:         true
807:     }
808:
809:     closed spec fn obeys_vmio_once_read_ensures() -> bool {
810:         true
811:     }
812:
813:     closed spec fn obeys_vmio_once_write_ensures() -> bool {
814:         true
815:     }
```

<a id="m7"></a>
### M7 — Collapse duplicate success/error byte-count contracts

**Evidence / premise.** fill_zeros has identical predicates in both Result arms after renaming n. The two fallible-copy macros repeat the same four facts in both Result arms, so a later contract correction must be copied six ways after expansion.

**Suggested change.** Bind one ghost count with let n=match r {Ok(n)=>n,Err((_,n))=>n}; state the common predicates once. Apply in fill_zeros and both macro contracts without introducing a new public helper.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/io.rs:1880](ostd/src/mm/io.rs#L1880) (lines 1880–1892)

```rust
1880:             final(self).cursor.vaddr <= old(self).end.vaddr,
1881:             match r {
1882:                 Ok(n) => {
1883:                     &&& n <= len
1884:                     &&& n <= old(self).avail_spec()
1885:                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
1886:                 },
1887:                 Err((_, n)) => {
1888:                     &&& n <= len
1889:                     &&& n <= old(self).avail_spec()
1890:                     &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
1891:                 },
1892:             }
```

[ostd/src/mm/io.rs:2087](ostd/src/mm/io.rs#L2087) (lines 2087–2100)

```rust
2087:                     match r {
2088:                         Ok(n) => {
2089:                             &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
2090:                             &&& final(writer).cursor.vaddr == old(writer).cursor.vaddr + n
2091:                             &&& n <= old(self).remain_spec()
2092:                             &&& n <= old(writer).avail_spec()
2093:                         },
2094:                         Err((_, copied_len)) => {
2095:                             &&& final(self).cursor.vaddr == old(self).cursor.vaddr + copied_len
2096:                             &&& final(writer).cursor.vaddr == old(writer).cursor.vaddr + copied_len
2097:                             &&& copied_len <= old(self).remain_spec()
2098:                             &&& copied_len <= old(writer).avail_spec()
2099:                         },
2100:                     }
```

[ostd/src/mm/io.rs:2148](ostd/src/mm/io.rs#L2148) (lines 2148–2161)

```rust
2148:                     match r {
2149:                         Ok(n) => {
2150:                             &&& final(self).cursor.vaddr == old(self).cursor.vaddr + n
2151:                             &&& final(reader).cursor.vaddr == old(reader).cursor.vaddr + n
2152:                             &&& n <= old(self).avail_spec()
2153:                             &&& n <= old(reader).remain_spec()
2154:                         },
2155:                         Err((_, copied_len)) => {
2156:                             &&& final(self).cursor.vaddr == old(self).cursor.vaddr + copied_len
2157:                             &&& final(reader).cursor.vaddr == old(reader).cursor.vaddr + copied_len
2158:                             &&& copied_len <= old(self).avail_spec()
2159:                             &&& copied_len <= old(reader).remain_spec()
2160:                         },
2161:                     }
```

<a id="m9"></a>
### M9 — Remove a vacuous implementation postcondition inherited from VmIo

**Evidence / premise.** DmaStreamSlice::obeys_vmio_write_spec returns false, making this entire implication true; the trait method already carries the identical gated postcondition.

**Suggested change.** Remove this redundant implementation-level ensures clause; keep the trait-required write_spec method and the inherited trait contract.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/dma/dma_stream.rs:1518](ostd/src/mm/dma/dma_stream.rs#L1518) (lines 1518–1539)

```rust
1518:     #[verus_spec()]
1519:     fn write(
1520:         &self,
1521:         offset: usize,
1522:         reader: &mut VmReader,
1523:         Tracked(reader_own): Tracked<&mut VmIoOwner>,
1524:         Tracked(owner): Tracked<&mut ()>,
1525:     ) -> (r: core::result::Result<(), Error>)
1526:         ensures
1527:             Self::obeys_vmio_write_spec() ==> Self::write_spec(
1528:                 *self,
1529:                 offset,
1530:                 *old(reader),
1531:                 *final(reader),
1532:                 *old(reader_own),
1533:                 *final(reader_own),
1534:                 *old(owner),
1535:                 *final(owner),
1536:                 r,
1537:             ),
1538:     {
1539:         proof {
```

[ostd/src/mm/dma/dma_stream.rs:1348](ostd/src/mm/dma/dma_stream.rs#L1348) (lines 1348–1350)

```rust
1348:     closed spec fn obeys_vmio_write_spec() -> bool {
1349:         false
1350:     }
```

[ostd/src/mm/io.rs:1298](ostd/src/mm/io.rs#L1298) (lines 1298–1310)

```rust
1298:             Self::obeys_vmio_write_spec() ==> Self::write_spec(
1299:                 *self,
1300:                 offset,
1301:                 *old(reader),
1302:                 *final(reader),
1303:                 *old(writer_own),
1304:                 *final(writer_own),
1305:                 *old(owner),
1306:                 *final(owner),
1307:                 r,
1308:             ),
1309:     ;
1310:
```

<a id="m10"></a>
### M10 — Remove duplicate Frame::meta pointer precondition

**Evidence / premise.** Both alternatives in the second precondition entail ptr_inv: Frame::inv includes it, and external_meta_wf includes it. Hence the preceding standalone self.ptr_inv is logically redundant.

**Suggested change.** Keep the disjunction expressing the two valid ownership modes and remove its standalone ptr_inv precondition.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/mod.rs:259](ostd/src/mm/frame/mod.rs#L259) (lines 259–267)

```rust
259:         requires
260:             self.ptr_inv(),
261:             {
262:                 self.inv() && metadata_perm is None
263:                 && typed_meta_wf::<M>(self.slot_perm(), self.metadata_perm(), *repr_perm) ||
264:                 metadata_perm is Some
265:                 && self.external_meta_wf(*metadata_perm->0, *repr_perm)
266:             },
267:         ensures
```

[ostd/specs/mm/frame/frame_specs.rs:116](ostd/specs/mm/frame/frame_specs.rs#L116) (lines 116–135)

```rust
116:     /// Relates an externally stored metadata permission to this frame's slot permission.
117:     pub open spec fn external_meta_wf(
118:         self,
119:         metadata_perm: MetadataPerm,
120:         repr_perm: M::ReprPerm,
121:     ) -> bool {
122:         &&& self.ptr_inv()
123:         &&& self.tracked_metadata_perm@ is None
124:         &&& typed_meta_wf::<M>(self.slot_perm(), metadata_perm, repr_perm)
125:     }
126: }
127:
128: impl<M: ?Sized> Inv for Frame<M> {
129:     open spec fn inv(self) -> bool {
130:         &&& self.ptr_inv()
131:         &&& self.tracked_metadata_perm@ is Some
132:         &&& self.frac_metadata_perm().frac() == 1
133:         &&& MetaSlot::perms_related(self.slot_perm(), self.metadata_perm())
134:     }
135: }
```

<a id="m11"></a>
### M11 — Replace the affine address history with its formula

**Evidence / premise.** The tracked addrs sequence stores no linear permissions. Its invariant fixes every addrs[j] to range.start+j*PAGE_SIZE, and its length is i; segment.tracked_perms already tracks permission length. All addresses are therefore derivable.

**Suggested change.** Remove addrs, its tracked_empty/push operations and length/equality bookkeeping. Quantify over0<=j<i and compute the physical address from range.start+j*PAGE_SIZE. Keep raw_perms tracked and preserve executable loop/rollback behavior.

**Root qualification.** Retain rollback and actual permission bookkeeping. Only the formula-reconstructible address sequence is a candidate for removal.

**Guideline / confidence.** canonical-spec-models, avoid-redundant-mode-markers; static premise confidence: medium. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/segment.rs:280](ostd/src/mm/frame/segment.rs#L280) (lines 280–283)

```rust
280:         proof_decl! {
281:             let tracked mut addrs = Seq::<usize>::tracked_empty();
282:             let tracked raw_perms = Seq::<FrameRawPerms>::tracked_empty();
283:         }
```

[ostd/src/mm/frame/segment.rs:306](ostd/src/mm/frame/segment.rs#L306) (lines 306–342)

```rust
306:             invariant
307:                 segment.tracked_perms@ is Some,
308:                 i <= addr_len,
309:                 i == addrs.len(),
310:                 i == segment.tracked_perms@->0.len(),
311:                 range.start <= range.start + i * PAGE_SIZE <= range.end,
312:                 range.end == range.start + addr_len * PAGE_SIZE,
313:                 addr_len == (range.end - range.start) / PAGE_SIZE as int,
314:                 i <= addr_len,
315:                 forall|paddr_in: Paddr|
316:                     (range.start + i * PAGE_SIZE <= paddr_in < range.end && paddr_in % PAGE_SIZE
317:                         == 0) ==> {
318:                         &&& metadata_fn.requires((paddr_in,))
319:                     },
320:                 forall|paddr_in: Paddr, paddr_out: Paddr, m: M|
321:                     range.start + i * PAGE_SIZE <= paddr_in < range.end && paddr_in % PAGE_SIZE == 0
322:                         && metadata_fn.ensures((paddr_in,), (paddr_out, m)) ==> paddr_in
323:                         == paddr_out,
324:                 forall|j: int|
325:                     #![trigger addrs[j]]
326:                     0 <= j < addrs.len() ==> {
327:                         let idx = frame_to_index(addrs[j]);
328:                         &&& regions.contains(idx)
329:                         &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
330:                         &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
331:                         &&& segment.tracked_perms@->0[j].inv()
332:                         &&& segment.tracked_perms@->0[j].slot_perm == regions.slots[idx]
333:                         &&& segment.tracked_perms@->0[j].metadata_perm.id()
334:                             == regions.slot_owners[idx].metadata_perm.id()
335:                         &&& regions.slot_owners[idx].paths_in_pt.is_empty()
336:                         &&& regions.slot_owners[idx].usage is Frame
337:                         &&& addrs[j] % PAGE_SIZE == 0
338:                         &&& addrs[j] < MAX_PADDR
339:                         &&& addrs[j] == range.start + (j as u64) * PAGE_SIZE
340:                     },
341:                 regions.inv(),
342:                 regions.slot_owners.dom() == old(regions).slot_owners.dom(),
```

<a id="m16"></a>
### M16 — Remove an unused erased owner argument

**Evidence / premise.** The UniqueFrameOwner reference appears only in the with signature, never in the requires, ensures, or body. The actual returned MetadataPerm is taken from self.

**Suggested change.** Remove this erased owner parameter and matching proof arguments at callers; preserve the executable into_raw signature and tracked metadata output.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: medium. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/unique.rs:415](ostd/src/mm/frame/unique.rs#L415) (lines 415–432)

```rust
415:     /// Converts this frame into a raw physical address.
416:     #[verus_spec(r =>
417:         with
418:             Tracked(owner): Tracked<&UniqueFrameOwner<M>>,
419:                 -> metadata_perms: Tracked<MetadataPerm>,
420:         requires
421:             self.inv(),
422:         ensures
423:             metadata_perms@ == self.metadata_perm(),
424:             r == meta_to_frame(self.ptr.addr()),
425:     )]
426:     pub(crate) fn into_raw(mut self) -> Paddr {
427:         let tracked metadata_perms = self.tracked_metadata_perm.tracked_take();
428:         let this = ManuallyDrop::new(self);
429:
430:         proof_with!(|= Tracked(metadata_perms));
431:         this.start_paddr()
432:     }
```

<a id="m18"></a>
### M18 — Delete equivalent LinkedList drop membership quantifier

**Evidence / premise.** These two forall clauses have identical bounds and triggers. The second only let-binds meta_to_index before asserting the same contains fact.

**Suggested change.** Delete one quantified conjunct. Also consider grouping the remaining per-link facts under one forall only if trigger behavior remains satisfactory.

**Guideline / confidence.** canonical-spec-models, quantifiers-and-triggers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/linked_list.rs:1476](ostd/src/mm/frame/linked_list.rs#L1476) (lines 1476–1486)

```rust
1476:         &&& s.0.inv()
1477:         &&& s.1.inv()
1478:         &&& forall|i: int|
1479:             #![trigger s.0.list[i]]
1480:             0 <= i < s.0.list.len() ==> s.1.contains(meta_to_index(s.0.list[i].paddr))
1481:         &&& forall|i: int|
1482:             #![trigger s.0.list[i]]
1483:             0 <= i < s.0.list.len() ==> {
1484:                 let idx = meta_to_index(s.0.list[i].paddr);
1485:                 s.1.contains(idx)
1486:             }
```

<a id="m19"></a>
### M19 — Delete duplicate KVirtArea proof calls

**Evidence / premise.** Two adjacent lemma_nat_align_down_sound calls use exactly the same arguments. Earlier in the same iteration, extend_right/mono are repeated with unchanged iterator sequence and pos.

**Suggested change.** Delete the second adjacent align_down call and second pre-map extend_right/mono pair. Do not remove the post-map bridge until checking cursor-owner changes.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/kspace/kvirt_area.rs:947](ostd/src/mm/kspace/kvirt_area.rs#L947) (lines 947–955)

```rust
947:                     vstd_extra::arithmetic::lemma_nat_align_down_sound(
948:                         old_cursor_owner_va as nat,
949:                         page_size::<PagingConsts>(level_raw) as nat,
950:                     );
951:                     vstd_extra::arithmetic::lemma_nat_align_down_sound(
952:                         old_cursor_owner_va as nat,
953:                         page_size::<PagingConsts>(level_raw) as nat,
954:                     );
955:
```

[ostd/src/mm/kspace/kvirt_area.rs:885](ostd/src/mm/kspace/kvirt_area.rs#L885) (lines 885–886)

```rust
885:                     sum_page_sizes_extend_right(it.seq(), 0, pos@);
886:                     sum_page_sizes_mono(it.seq(), 0, pos@ + 1, it.seq().len() as int);
```

[ostd/src/mm/kspace/kvirt_area.rs:906](ostd/src/mm/kspace/kvirt_area.rs#L906) (lines 906–907)

```rust
906:                     sum_page_sizes_extend_right(it.seq(), 0, pos@);
907:                     sum_page_sizes_mono(it.seq(), 0, pos@ + 1, it.seq().len() as int);
```

<a id="m20"></a>
### M20 — Drop the overflow bound already implied by bounds policy

**Evidence / premise.** The negated bounds_panic_condition requires map_offset+range_len<=area_size; area_size is usize. This directly implies the standalone <=usize::MAX clause.

**Suggested change.** Remove the standalone overflow precondition and retain the bounds-panic policy.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/kspace/kvirt_area.rs:758](ostd/src/mm/kspace/kvirt_area.rs#L758) (lines 758–767)

```rust
758:     // provable; OOM uses the implication form.
759:
760:             !Self::map_untracked_frames_bounds_panic_condition(area_size, map_offset, &pa_range),
761:             kvirt_alloc_oom_condition(area_size) ==> may_panic(),
762:             old(regions).inv(),
763:             owner.inv(),
764:             owner.pt_owner.metaregion_sound(*old(regions)),
765:             owner.pt_owner.0.value().node().relate_guard(root_guard),
766:             Self::untracked_range_slots_in_regions(&pa_range, *old(regions)),
767:             map_offset + usize::range_len(pa_range.start, pa_range.end) <= usize::MAX,
```

[ostd/src/mm/kspace/kvirt_area.rs:690](ostd/src/mm/kspace/kvirt_area.rs#L690) (lines 690–701)

```rust
690:     /// offset misalignment, plus the top-level capacity assert.
691:     pub open spec fn map_untracked_frames_bounds_panic_condition(
692:         area_size: usize,
693:         map_offset: usize,
694:         pa_range: &Range<Paddr>,
695:     ) -> bool {
696:         ||| pa_range.start % PAGE_SIZE != 0
697:         ||| pa_range.end % PAGE_SIZE != 0
698:         ||| area_size % PAGE_SIZE != 0
699:         ||| map_offset % PAGE_SIZE != 0
700:         ||| map_offset + usize::range_len(pa_range.start, pa_range.end) > area_size
701:     }
```

<a id="m21"></a>
### M21 — Reuse the StrayPageTable disjoint-cardinality proof

**Evidence / premise.** The StrayPageTable arm proves old_removed disjoint from the filtered subtree and invokes lemma_set_disjoint_lens before the runtime count increment; later the same branch proves and invokes it again, with subtree bound to that exact filter. old_removed and prev_mappings are unchanged.

**Suggested change.** Retain the first disjoint/cardinality fact for the runtime overflow proof and reuse it in the later ghost update instead of reproving/calling the lemma again.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: medium. All implementation and solver outcomes remain unverified.

[ostd/src/mm/vm_space.rs:1123](ostd/src/mm/vm_space.rs#L1123) (lines 1123–1149)

```rust
1123:                         assert(old_removed.disjoint(
1124:                             prev_mappings.filter(
1125:                                 |m2: Mapping|
1126:                                     frag_ghost->StrayPageTable_va <= m2.va_range.start
1127:                                         < frag_ghost->StrayPageTable_va
1128:                                         + frag_ghost->StrayPageTable_len,
1129:                             ),
1130:                         )) by {
1131:                             assert forall|m: Mapping|
1132:                                 old_removed.contains(m) implies !prev_mappings.filter(
1133:                                 |m2: Mapping|
1134:                                     frag_ghost->StrayPageTable_va <= m2.va_range.start
1135:                                         < frag_ghost->StrayPageTable_va
1136:                                         + frag_ghost->StrayPageTable_len,
1137:                             ).contains(m) by {
1138:                                 assert(!prev_mappings.contains(m));
1139:                             };
1140:                         };
1141:                         vstd::set_lib::lemma_set_disjoint_lens(
1142:                             old_removed,
1143:                             prev_mappings.filter(
1144:                                 |m2: Mapping|
1145:                                     frag_ghost->StrayPageTable_va <= m2.va_range.start
1146:                                         < frag_ghost->StrayPageTable_va
1147:                                         + frag_ghost->StrayPageTable_len,
1148:                             ),
1149:                         );
```

[ostd/src/mm/vm_space.rs:1232](ostd/src/mm/vm_space.rs#L1232) (lines 1232–1240)

```rust
1232:                 match frag_ghost {
1233:                     PageTableFrag::StrayPageTable { .. } => {
1234:                         assert(old_removed.disjoint(subtree)) by {
1235:                             assert forall|e: Mapping|
1236:                                 old_removed.contains(e) implies !subtree.contains(e) by {};
1237:                         };
1238:                         vstd::set_lib::lemma_set_disjoint_lens(old_removed, subtree);
1239:                         assert(removed == old_removed + subtree);
1240:                     },
```

<a id="pt-09"></a>
### PT-09 — PageTableOwner::inv stores a path-correctness property already derivable from its tree invariant.

**Evidence / premise.** pt_inv630-633 equals self.0.inv && pt_inv_at_depth. Existing pt_inv_implies_path_correct1004-1031 proves subtree_satisfies(path,path_correct_pred) from that predicate and root path equality; inv1871-1872 already supplies pt_inv.

**Suggested change.** Consider removing redundant subtree_satisfies clause1879 and invoke the existing path-correctness lemma where consumers need it. Preserve all pt_inv clauses.

**Root qualification.**  Logical entailment is a candidate for proof reuse, not evidence that deleting the conjunct will verify or improve performance.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/owners.rs:1869](ostd/specs/mm/page_table/owners.rs#L1869) (lines 1869–1881)

```rust
1869: impl<C: PageTableConfig> Inv for PageTableOwner<C> {
1870:     open spec fn inv(self) -> bool {
1871:         &&& self.0.inv()
1872:         &&& self.pt_inv_at_depth((INC_LEVELS - self.0.level()) as nat)
1873:         &&& self.0.value().is_node()
1874:         &&& self.0.value().path.len() <= INC_LEVELS - 1
1875:         &&& self.0.value().path.inv()
1876:         &&& self.0.value().path.len() == self.0.level()
1877:         &&& self.0.value().parent_level == (INC_LEVELS - self.0.level()) as PagingLevel
1878:         &&& self.0.value().node().tree_level == self.0.value().path.len()
1879:         &&& self.0.subtree_satisfies(self.0.value().path, Self::path_correct_pred())
1880:     }
1881: }
```

<a id="pt-23"></a>
### PT-23 — Two branches duplicate the same long proof that skipping an empty slot extends the scanned-empty range.

**Evidence / premise.** Empty-node branch1095-1151 and absent branch1172-1223 use identical mapping-preservation, aligned slot emptiness, VA step bounds and filter decomposition; only the final absent-vs-empty-node lemma differs.

**Suggested change.** Extract a mathematical set/range lemma proving union of the previous empty scanned range and current empty slot is empty, call it from both branches, and keep branch-specific subtree emptiness lemmas. Preserve exec branching and lock release.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/cursor/mod.rs:1095](ostd/src/mm/page_table/cursor/mod.rs#L1095) (lines 1095–1151)

```rust
1095:                         proof {
1096:                             assert(*owner == owner_before_move.move_forward_owner_spec());
1097:                             owner_before_move.move_forward_owner_preserves_mappings();
1098:                             if !split_happened {
1099:                                 assert(owner@.mappings == old(owner)@.mappings);
1100:                                 let ghost aligned_start = nat_align_down(
1101:                                     va_before_move as nat,
1102:                                     cur_slot_size as nat,
1103:                                 ) as Vaddr;
1104:                                 assert(old(owner)@.mappings.filter(
1105:                                     |m: Mapping|
1106:                                         aligned_start <= m.va_range.start < aligned_start
1107:                                             + cur_slot_size as usize,
1108:                                 ) == Set::<Mapping>::empty());
1109:                                 lemma_nat_align_down_sound(
1110:                                     va_before_move as nat,
1111:                                     cur_slot_size as nat,
1112:                                 );
1113:                                 owner_before_move.lemma_va_plus_page_size_no_overflow(
1114:                                     owner_before_move.level,
1115:                                 );
1116:                                 assert(self.va == (nat_align_down(
1117:                                     va_before_move as nat,
1118:                                     cur_slot_size as nat,
1119:                                 ) + cur_slot_size as nat) as Vaddr);
1120:                                 assert(self.va <= aligned_start + cur_slot_size as usize);
1121:
1122:                                 assert(owner@.mappings.filter(
1123:                                     |m: Mapping| old(self).va <= m.va_range.start < self.va,
1124:                                 ) == Set::<Mapping>::empty()) by {
1125:                                     assert forall|m: Mapping|
1126:                                         !(#[trigger] old(owner)@.mappings.contains(m) && old(
1127:                                             self,
1128:                                         ).va <= m.va_range.start && m.va_range.start < self.va) by {
1129:                                         if old(owner)@.mappings.contains(m) && old(self).va
1130:                                             <= m.va_range.start && m.va_range.start < self.va {
1131:                                             if m.va_range.start < va_before_move {
1132:                                                 assert(old(owner)@.mappings.filter(
1133:                                                     |m2: Mapping|
1134:                                                         old(self).va <= m2.va_range.start
1135:                                                             < va_before_move,
1136:                                                 ).contains(m));
1137:                                             } else {
1138:                                                 assert(old(owner)@.mappings.filter(
1139:                                                     |m2: Mapping|
1140:                                                         aligned_start <= m2.va_range.start
1141:                                                             < aligned_start
1142:                                                             + cur_slot_size as usize,
1143:                                                 ).contains(m));
1144:                                             }
1145:                                         }
1146:                                     };
1147:                                 };
1148:                                 if va_before_move as usize == old(self).va as usize {
1149:                                     owner_before_move.lemma_cur_subtree_empty_not_present();
1150:                                 }
1151:                             }
```

<a id="pt-24"></a>
### PT-24 — Many split lemmas repeat query_mapping filtered-set choice reasoning.

**Evidence / premise.** Repeated filtered covering-set/lemma_set_choose_len/m.inv blocks occur73-79,145-150,198-205,257-261,296-300,338-342,367-371,471-475,522-526,563-567,641-646. CursorView::present/query_mapping36-46 use this same covering filter; repository query-lemma name search found no shared characterization lemma.

**Suggested change.** Add a reusable proved query characterization under CursorView.inv and present that establishes membership, covers(cur_va), and mapping inv; use it at actual repeated call sites. Preserve set finiteness/uniqueness and trigger control.

**Root qualification.** The existing lemma_set_choose_len requires nonzero set length; present already supplies it. Do not introduce unnecessary new finite/unique preconditions. Inv supplies validity of the chosen mapping.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: medium. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/split_while_huge_lemmas.rs:73](ostd/specs/mm/page_table/cursor/split_while_huge_lemmas.rs#L73) (lines 73–79)

```rust
73:         assert(v.mappings.contains(m) && m.va_range.start <= cur_va && cur_va < m.va_range.end) by {
74:             let f = v.mappings.filter(
75:                 |m2: Mapping| m2.va_range.start <= v.cur_va < m2.va_range.end,
76:             );
77:             vstd::set::lemma_set_choose_len(f);
78:         };
79:         assert(m.inv());
```

## Low findings

<a id="p02"></a>
### P02 — Delete duplicate broadcast lemma

**Evidence / premise.** Its requires and ensures are identical to lemma_meta_to_frame_soundness at 89-98, including trigger. Both are listed in group_page_meta, but only soundness has direct callers.

**Suggested change.** Remove alignment and its broadcast-group entry; retain soundness.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/mapping.rs:89, ostd/specs/mm/frame/mapping.rs:125, ostd/specs/arch/x86/mod.rs:106.

[ostd/specs/mm/frame/mapping.rs:110](ostd/specs/mm/frame/mapping.rs#L110) (lines 110–122)

```rust
110: pub broadcast proof fn lemma_meta_to_frame_alignment(meta: Vaddr)
111:     requires
112:         meta % META_SLOT_SIZE == 0,
113:         FRAME_METADATA_RANGE.start <= meta && meta < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
114:             * META_SLOT_SIZE,
115:     ensures
116:         #[trigger] meta_to_frame(meta) % PAGE_SIZE == 0,
117:         meta_to_frame(meta) < MAX_PADDR,
118: {
119: }
120:
121: pub broadcast group group_page_meta {
122:     lemma_index_to_frame_biinjective,
```

<a id="p03"></a>
### P03 — Remove unused tautological preservation lemma

**Evidence / premise.** The entire result is already an explicit prerequisite, and exhaustive name search finds only its declaration.

**Suggested change.** Delete lemma_consistent_with_pt_implies_inv; do not replace it with an invalid inference from PT consistency alone.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/tlb.rs:86](ostd/specs/mm/tlb.rs#L86) (lines 86–98)

```rust
86:     pub proof fn lemma_consistent_with_pt_implies_inv(self, pt: PageTableView)
87:         requires
88:             self.inv(),
89:             self.consistent_with_pt(pt),
90:             pt.inv(),
91:         ensures
92:             self.inv(),
93:     {
94:     }
95:
96:     pub open spec fn issue_tlb_flush(self, op: TlbFlushOp) -> Self {
97:         TlbModel { pending: self.pending.push(op), mappings: self.mappings }
98:     }
```

<a id="p04"></a>
### P04 — Remove repeated frame-drop frame clause

**Evidence / premise.** The exact same equality is immediately preceding at 131-133.

**Suggested change.** Keep one equality.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/embedding/frame.rs:131.

[ostd/specs/mm/embedding/frame.rs:134](ostd/specs/mm/embedding/frame.rs#L134) (lines 134–146)

```rust
134:         final(regions).slot_owner(paddr).in_list_perm == old(regions).slot_owner(
135:             paddr,
136:         ).in_list_perm,
137:         final(regions).slot_owner(paddr).in_list_perm == old(regions).slot_owner(
138:             paddr,
139:         ).in_list_perm,
140:         old(regions).slot_owner(paddr).ref_count() == 1 ==> final(regions).slot_owner(
141:             paddr,
142:         ).ref_count() == REF_COUNT_UNUSED,
143:         old(regions).slot_owner(paddr).ref_count() > 1 ==> final(regions).slot_owner(
144:             paddr,
145:         ).ref_count() == (old(regions).slot_owner(paddr).ref_count() - 1) as u64,
146:         old(regions).slot_owner(paddr).ref_count() > 1 ==> final(regions).slot_owner(
```

<a id="p05"></a>
### P05 — Remove transitive bound from VirtPtr invariant

**Evidence / premise.** Previous conjunct is range.start <= vaddr <= range.end, which implies the quoted ordering for all values.

**Suggested change.** Retain the chained bound only.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/virt_mem.rs:484.

[ostd/specs/mm/virt_mem.rs:485](ostd/specs/mm/virt_mem.rs#L485) (lines 485–497)

```rust
485:         &&& self.range@.end >= self.range@.start
486:     }
487: }
488:
489: impl Clone for VirtPtr {
490:     fn clone(&self) -> (res: Self)
491:         ensures
492:             res == self,
493:     {
494:         Self { vaddr: self.vaddr, range: Ghost(self.range@) }
495:     }
496: }
497:
```

<a id="p06"></a>
### P06 — Remove copy preconditions already supplied by pointer invariants

**Evidence / premise.** src.inv and dst.inv imply each range.start<=vaddr by VirtPtr::inv. The extra destination conjunct is at 911. End/length, initialized-byte, and translation conditions are independent and must remain.

**Suggested change.** Remove only src/dst lower-bound repetitions.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/virt_mem.rs:898, ostd/specs/mm/virt_mem.rs:911, ostd/specs/mm/virt_mem.rs:484.

[ostd/specs/mm/virt_mem.rs:900](ostd/specs/mm/virt_mem.rs#L900) (lines 900–912)

```rust
900:             src.range@.start <= src.vaddr,
901:             src.vaddr + n <= src.range@.end,
902:             forall|i: usize|
903:                 #![trigger mem_src.addr_transl(i)]
904:                 src.vaddr <= i < src.vaddr + n ==> {
905:                     &&& mem_src.addr_transl(i) is Some
906:                     &&& mem_src.memory.contains_key((mem_src.addr_transl(i)->0).0)
907:                     &&& mem_src.memory[(mem_src.addr_transl(i)->0).0].contents[(mem_src.addr_transl(
908:                         i,
909:                     )->0).1 as int] is Init
910:                 },
911:             dst.range@.start <= dst.vaddr,
912:             dst.vaddr + n <= dst.range@.end,
```

<a id="p07"></a>
### P07 — Remove writer-removal presence requirement implied by invariant

**Evidence / premise.** old(self).inv + old(self).active imply mem_view_wf, whose first conjunct is mem_view is Some <==> mv_range is Some; previous requires already supplies mem_view is Some.

**Suggested change.** Drop only the mv_range presence conjunct.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/vm_space.rs:122, ostd/specs/mm/vm_space.rs:182, ostd/specs/mm/vm_space.rs:491.

[ostd/specs/mm/vm_space.rs:492](ostd/specs/mm/vm_space.rs#L492) (lines 492–504)

```rust
492:             old(self).mv_range is Some,
493:             0 <= idx < old(self).writers.len(),
494:         ensures
495:             final(self).inv(),
496:             final(self).active == old(self).active,
497:             final(self).shared_reader == old(self).shared_reader,
498:             final(self).writers == old(self).writers.remove(idx as int),
499:     {
500:         let tracked writer = self.writers.tracked_remove(idx as int);
501:
502:         let tracked mv = match writer.mem_view {
503:             Some(VmIoMemView::WriteView(mv)) => mv,
504:             _ => { proof_from_false() },
```

<a id="p11"></a>
### P11 — Remaining-view disjointness follows total-view disjointness and subset

**Evidence / premise.** Next conjunct requires total_view.mappings_are_disjoint; remaining_view.mappings.subset_of(total_view.mappings) follows in same implication. Pairwise disjointness is hereditary under subsets.

**Suggested change.** Keep total-view disjointness and subset, and remove repeated remaining-view predicate after checking trigger behavior.

**Root qualification.**  Logical entailment is a candidate for proof reuse, not evidence that deleting the conjunct will verify or improve performance.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/vm_space.rs:191, ostd/specs/mm/vm_space.rs:195.

[ostd/specs/mm/vm_space.rs:190](ostd/specs/mm/vm_space.rs#L190) (lines 190–202)

```rust
190:             &&& remaining_view.mappings_are_disjoint()
191:             &&& total_view.mappings_are_disjoint()
192:             // ======================
193:             // Remaining Consistency
194:             // ======================
195:             &&& remaining_view.mappings.subset_of(total_view.mappings)
196:             &&& remaining_view.memory.dom().subset_of(
197:                 total_view.memory.dom(),
198:             )
199:             // =====================
200:             // Total View Consistency
201:             // =====================
202:             &&& forall|va: usize|
```

<a id="p13"></a>
### P13 — Collapse equal cursor-transition branches

**Evidence / premise.** Both final branches in move_next_owner_spec are identical for every input. In move_prev_owner_spec, the index==length branch is identical to final else once the empty case has returned.

**Suggested change.** Remove equal move-next branch; order move-prev as empty, index==0, otherwise index-1.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/linked_list/linked_list_specs.rs:203, ostd/src/mm/frame/linked_list.rs:678, ostd/specs/mm/embedding/list_store.rs:1002.

[ostd/specs/mm/frame/linked_list/linked_list_specs.rs:193](ostd/specs/mm/frame/linked_list/linked_list_specs.rs#L193) (lines 193–205)

```rust
193:         } else if self.index == self.length() - 1 {
194:             Self { list_own: self.list_own, index: self.index + 1 }
195:         } else {
196:             Self { list_own: self.list_own, index: self.index + 1 }
197:         }
198:     }
199:
200:     pub open spec fn move_prev_owner_spec(self) -> Self {
201:         if self.length() == 0 {
202:             self
203:         } else if self.index == self.length() {
204:             Self { list_own: self.list_own, index: self.index - 1 }
205:         } else if self.index == 0 {
```

<a id="p15"></a>
### P15 — Eliminate in-list facts already included in frame_link_inv

**Evidence / premise.** Immediately preceding frame_link_inv(self.regions) unfolds to this exact equality. The same explicit repetition appears in insertion preconditions and loose-frame preservation antecedents/results throughout this file.

**Suggested change.** Remove the repeated equality wherever frame_link_inv on the same owner and region is already required or promised.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/linked_list/linked_list_owners.rs:1280, ostd/specs/mm/frame/linked_list/linked_list_owners.rs:1284, ostd/specs/mm/embedding/list_store.rs:261, ostd/specs/mm/embedding/list_store.rs:503.

[ostd/specs/mm/embedding/list_store.rs:142](ostd/specs/mm/embedding/list_store.rs#L142) (lines 142–154)

```rust
142:                 &&& self.regions.slot_owners[self.loose[lid].slot_index].in_list_perm.value() == 0
143:             }
144:             // Distinct lists carry distinct *nonzero* ids.
145:         &&& forall|id1: ListId, id2: ListId|
146:             #![trigger self.lists.dom().contains(id1), self.lists.dom().contains(id2)]
147:             self.lists.dom().contains(id1) && self.lists.dom().contains(id2)
148:                 && self.lists[id1].list_id == self.lists[id2].list_id && self.lists[id1].list_id
149:                 != 0 ==> id1
150:                 == id2
151:             // Distinct loose handles occupy distinct slots (a UNIQUE frame
152:             // is held in at most one place).
153:         &&& forall|lid1: LooseId, lid2: LooseId|
154:             #![trigger self.loose.dom().contains(lid1), self.loose.dom().contains(lid2)]
```

<a id="p17"></a>
### P17 — Drop valid-address membership checks implied by region validity

**Evidence / premise.** All four occurrences (two axioms and two per-op wrappers) also require old(regions).inv. Existing lemma_contains_valid_frame_paddr proves exactly this implication. Same redundant direct contains check appears with valid_frame_paddr+regions.inv in unique_from_unused and segment_next.

**Suggested change.** Remove these explicit membership prerequisites, using existing lemma at proof call sites if needed. Keep membership conditions when address validity is absent.

**Root qualification.** Depends on retaining the current total-domain invariant. Re-audit after the P01 model decision.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/meta_region_owners.rs:93, ostd/specs/mm/embedding/frame.rs:89, ostd/specs/mm/embedding/frame.rs:175, ostd/specs/mm/embedding/frame.rs:203, ostd/specs/mm/embedding/unique.rs:90, ostd/specs/mm/embedding/segment.rs:267.

[ostd/specs/mm/embedding/frame.rs:63](ostd/specs/mm/embedding/frame.rs#L63) (lines 63–75)

```rust
63:     ensures
64:         final(regions).inv(),
65:         !valid_frame_paddr(paddr) ==> res is None,
66:         res is Some ==> MetaSlot::get_from_unused_region_spec(
67:             paddr,
68:             false,
69:             *old(regions),
70:             *final(regions),
71:         ),
72:         res is Some ==> MetaSlot::slot_perm_reparked_spec(paddr, *old(regions), *final(regions)),
73:         // Non-interference: failure leaves `regions` unchanged.
74:         res is None ==> *final(regions) == *old(regions),
75:         forall|c: CursorOwner<'_, UserPtConfig>|
```

<a id="p18"></a>
### P18 — Drop slot-owner domain preservation implied by old/final invariants

**Evidence / premise.** Both region invariants characterize slot_owners keys by exactly 0<=i<max_meta_slots(). Hence domains coincide independently of this axiom's transition clauses.

**Suggested change.** Remove this duplicated equality or expose a single reusable region-domain lemma if clients need an explicit instantiation.

**Root qualification.** Depends on retaining the current total-domain invariant. Re-audit after the P01 model decision.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/frame/meta_region_owners.rs:42, ostd/specs/mm/embedding/frame.rs:112, ostd/specs/mm/embedding/frame.rs:123.

[ostd/specs/mm/embedding/frame.rs:127](ostd/specs/mm/embedding/frame.rs#L127) (lines 127–139)

```rust
127:         final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
128:         final(regions).slot_owner(paddr).slot_vaddr == old(regions).slot_owner(paddr).slot_vaddr,
129:         final(regions).slot_owner(paddr).usage == old(regions).slot_owner(paddr).usage,
130:         final(regions).slot_owner(paddr).paths_in_pt == old(regions).slot_owner(paddr).paths_in_pt,
131:         old(regions).slot_owner(paddr).ref_count() == 1 ==> final(regions).slot_owner(
132:             paddr,
133:         ).paths_in_pt.is_empty(),
134:         final(regions).slot_owner(paddr).in_list_perm == old(regions).slot_owner(
135:             paddr,
136:         ).in_list_perm,
137:         final(regions).slot_owner(paddr).in_list_perm == old(regions).slot_owner(
138:             paddr,
139:         ).in_list_perm,
```

<a id="p20"></a>
### P20 — Delete unconsumed aliases and unused owner helpers

**Evidence / premise.** Cross-root search finds can_read, can_write, params_eq, change_fallible only at declarations; aliases duplicate has_read_view/has_write_view and helpers have no documented current external consumer.

**Suggested change.** Delete can_read/can_write/params_eq/change_fallible until a proof needs them. If change_fallible is retained for a consumer, is_fallible!=fallible is unnecessary for a plain assignment preserving inv.

**Root qualification.**  No in-repository consumers were found for the identified unused items; check public API intent before removing externally visible declarations.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/io.rs:153](ostd/specs/mm/io.rs#L153) (lines 153–165)

```rust
153:     pub open spec fn can_read(self) -> bool {
154:         self.has_read_view()
155:     }
156:
157:     /// Whether this owner is ready to serve as the writable side of a copy.
158:     #[verifier::inline]
159:     pub open spec fn can_write(self) -> bool {
160:         self.has_write_view()
161:     }
162:
163:     /// Whether the read view initializes the entire owner range.
164:     #[verifier::inline]
165:     pub open spec fn read_view_initialized(self) -> bool {
```

<a id="p22"></a>
### P22 — Remove unused redundant precondition facade and dormant API helpers

**Evidence / premise.** writer_requires ignores self/vaddr/len and has no calls. VmIoPermission, query_success_requires, query_success_ensures, map_cursor_requires also have no code consumers (some only stale rustdoc links).

**Suggested change.** Delete unused helpers and repair stale documentation links; do not re-add a duplicate invariant facade for symmetry.

**Root qualification.**  No in-repository consumers were found for the identified unused items; check public API intent before removing externally visible declarations.

**Guideline / confidence.** proof-engineering / canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

Supporting locations: ostd/specs/mm/vm_space.rs:38, ostd/specs/mm/vm_space.rs:692, ostd/specs/mm/vm_space.rs:696, ostd/specs/mm/vm_space.rs:713.

[ostd/specs/mm/vm_space.rs:676](ostd/specs/mm/vm_space.rs#L676) (lines 676–688)

```rust
676:     pub open spec fn writer_requires(
677:         &self,
678:         vm_owner: VmSpaceOwner,
679:         vaddr: Vaddr,
680:         len: usize,
681:     ) -> bool {
682:         &&& vm_owner.inv()
683:     }
684:
685:     pub open spec fn writer_success_cond(self, vaddr: Vaddr, len: usize) -> bool {
686:         &&& vaddr != 0 && len > 0 && vaddr + len <= MAX_USERSPACE_VADDR
687:         &&& current_page_table_paddr() == self.pt.root_paddr_spec()
688:     }
```

<a id="m2"></a>
### M2 — Remove the unused CPU-local covers alias

**Evidence / premise.** Repo-wide rg for covers over ostd and verified_libs finds this as the only code occurrence; it is not a trait method, broadcast lemma, or when_used_as_spec target. No external consumer is documented.

**Suggested change.** Remove covers and use the already exposed cpus()==cpus expression if a future caller needs it.

**Root qualification.**  No in-repository consumers were found for the identified unused items; check public API intent before removing externally visible declarations.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/task/cpu_local.rs:124](ostd/specs/task/cpu_local.rs#L124) (lines 124–127)

```rust
124:     /// Whether this authority contains exactly the configured CPU set.
125:     pub open spec fn covers(&self, cpus: Set<CpuId>) -> bool {
126:         self.cpus() == cpus
127:     }
```

<a id="m3"></a>
### M3 — Remove unused same-CPU authority lemma

**Evidence / premise.** Repo-wide rg finds only this definition; unlike the following smoke test this is a public convenience lemma without a regression-test role or documented external consumer.

**Suggested change.** Remove until a proof needs this derived fact; retain the separate regression smoke test.

**Root qualification.** Optional public API decision. Lack of an in-repository caller does not prove that a public fact has no intended external consumers.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: medium. All implementation and solver outcomes remain unverified.

[ostd/specs/task/cpu_local.rs:239](ostd/specs/task/cpu_local.rs#L239) (lines 239–257)

```rust
239:     /// Two live points-to resources for the same CPU cannot belong to the same
240:     /// CPU-local authority.
241:     pub proof fn lemma_same_cpu_has_distinct_auth(
242:         tracked &mut self,
243:         tracked other: &CpuLocalPointsTo<V>,
244:     )
245:         requires
246:             old(self).cpu() == other.cpu(),
247:         ensures
248:             final(self).id() == old(self).id(),
249:             final(self).cpu() == old(self).cpu(),
250:             final(self).value() == old(self).value(),
251:             final(self).id() != other.id(),
252:     {
253:         if self.id() == other.id() {
254:             self.points_to.disjoint(&other.points_to);
255:         }
256:     }
257: }
```

<a id="m8"></a>
### M8 — Remove duplicate dereferenced-owner assertions

**Evidence / premise.** writer_own is a reference; Rust/Verus method autoderef makes writer_own.inv() and (*writer_own).inv() the same predicate. The two mem_view assertions likewise denote the same field.

**Suggested change.** Keep one inv assertion and one Read/WriteView assertion; delete their explicit-deref copies.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/dma/dma_stream.rs:1239](ostd/src/mm/dma/dma_stream.rs#L1239) (lines 1239–1243)

```rust
1239:             assert(writer_own.inv());
1240:             assert((*writer_own).inv());
1241:             assert(writer_own.mem_view matches Some(VmIoMemView::WriteView(_)));
1242:             assert((*writer_own).mem_view matches Some(VmIoMemView::WriteView(_)));
1243:             assert(reader_own.mem_view matches Some(VmIoMemView::ReadView(_)));
```

<a id="m12"></a>
### M12 — Delete the repeated segment loop bound

**Evidence / premise.** i<=addr_len occurs twice in the same invariant list with no difference.

**Suggested change.** Delete either duplicate.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/segment.rs:306](ostd/src/mm/frame/segment.rs#L306) (lines 306–314)

```rust
306:             invariant
307:                 segment.tracked_perms@ is Some,
308:                 i <= addr_len,
309:                 i == addrs.len(),
310:                 i == segment.tracked_perms@->0.len(),
311:                 range.start <= range.start + i * PAGE_SIZE <= range.end,
312:                 range.end == range.start + addr_len * PAGE_SIZE,
313:                 addr_len == (range.end - range.start) / PAGE_SIZE as int,
314:                 i <= addr_len,
```

<a id="m13"></a>
### M13 — Inline a one-conjunct Segment invariant alias

**Evidence / premise.** Repo-wide rg finds only its definition and one invocation in Segment::inv. The body is simply tracked_perms is Some, with no independent abstraction or other consumer.

**Suggested change.** Replace the inv invocation with self.tracked_perms@ is Some and remove this public closed helper.

**Guideline / confidence.** avoid-unused-spec-helpers, keep-internal-spec-helpers-closed; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/segment.rs:558](ostd/src/mm/frame/segment.rs#L558) (lines 558–560)

```rust
558:     pub closed spec fn inner_perm_inv(&self) -> bool {
559:         self.tracked_perms@ is Some
560:     }
```

[ostd/src/mm/frame/segment.rs:1163](ostd/src/mm/frame/segment.rs#L1163) (lines 1163–1167)

```rust
1163:         &&& self.end_paddr() % PAGE_SIZE == 0
1164:         &&& self.start_paddr() <= self.end_paddr() <= MAX_PADDR
1165:         &&& self.inner_perm_inv()
1166:         &&& self.raw_perms().len() == self.len()
1167:         &&& forall|i: int|
```

<a id="m14"></a>
### M14 — Drop the duplicate exact Segment::size contract

**Evidence / premise.** The dual_spec body is range.end-range.start; getters return those exact fields. returns self.size already fixes the value, so the ensures clause restates the same equation.

**Suggested change.** Keep the self-referential returns self.size and remove the redundant ensures and now-unused r binder.

**Guideline / confidence.** use-returns-for-exact-results, pair-exec-helpers-with-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/segment.rs:526](ostd/src/mm/frame/segment.rs#L526) (lines 526–539)

```rust
526:
527:     /// Gets the length in bytes of the contiguous frames.
528:     #[verus_verify(dual_spec)]
529:     #[verus_spec(r =>
530:         requires
531:             self.inv(),
532:         ensures
533:             r == self.end_paddr() - self.start_paddr(),
534:         returns
535:             self.size()
536:     )]
537:     pub fn size(&self) -> usize {
538:         self.range.end - self.range.start
539:     }
```

<a id="m15"></a>
### M15 — Remove tautological PhantomData equality

**Evidence / premise.** PhantomData<M1> is a unit struct; every value of that exact type equals PhantomData::<M1>. The pointer/permission equations carry the actual transmute relation.

**Suggested change.** Delete the marker equality from transmute_spec.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/unique.rs:137](ostd/src/mm/frame/unique.rs#L137) (lines 137–143)

```rust
137:     pub open spec fn transmute_spec<M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
138:         self,
139:         transmuted: UniqueFrame<M1>,
140:     ) -> bool {
141:         &&& transmuted.ptr.addr() == self.ptr.addr()
142:         &&& transmuted._marker == PhantomData::<M1>
143:         &&& transmuted.tracked_slot_perm@ == self.tracked_slot_perm@
```

<a id="m17"></a>
### M17 — Remove duplicated external_body annotation

**Evidence / premise.** The same drop_meta_in_place item has verifier::external_body both above and below its verus_spec attribute.

**Suggested change.** Retain one external_body annotation. This does not remove the trusted boundary.

**Guideline / confidence.** avoid-redundant-mode-markers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/frame/meta.rs:860](ostd/src/mm/frame/meta.rs#L860) (lines 860–883)

```rust
860:     #[verifier::external_body]
861:     #[verus_spec(
862:         with
863:             Tracked(ref_count_perm): Tracked<&PermissionU64>,
864:             Tracked(in_list_perm): Tracked<&PermissionU64>,
865:             Tracked(metadata_perm): Tracked<&mut MetadataPerm>,
866:         requires
867:             self.ref_count.id() == ref_count_perm.id(),
868:             ref_count_perm.value() == 0 || ref_count_perm.value() == REF_COUNT_UNIQUE,
869:             self.in_list.id() == in_list_perm.id(),
870:             in_list_perm.value() == 0,
871:             old(metadata_perm).storage_perm.is_init(),
872:             old(metadata_perm).storage_perm.id() == self.storage.id(),
873:             old(metadata_perm).vtable_ptr_perm.is_init(),
874:             old(metadata_perm).vtable_ptr_perm.pptr() == self.vtable_ptr,
875:         ensures
876:             final(metadata_perm).storage_perm.is_uninit(),
877:             final(metadata_perm).storage_perm.id() == old(metadata_perm).storage_perm.id(),
878:             final(metadata_perm).vtable_ptr_perm.is_uninit(),
879:             final(metadata_perm).vtable_ptr_perm.pptr()
880:                 == old(metadata_perm).vtable_ptr_perm.pptr(),
881:     )]
882:     #[verifier::external_body]
883:     pub(super) unsafe fn drop_meta_in_place(&self) {
```

<a id="m22"></a>
### M22 — Use returns for exact getters and omit unused binders

**Evidence / premise.** nr_subpage_per_huge fixes the exact usize result using ensures. page_size likewise has one exact equality alongside other properties; remain/avail have exact usize equations; DmaCoherent::clone fixes r==self.

**Suggested change.** Use returns for the exact equations and keep non-exact ensures. Remove result binders made unused. Required narrowing casts remain.

**Guideline / confidence.** use-returns-for-exact-results; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/mod.rs:255](ostd/src/mm/mod.rs#L255) (lines 255–268)

```rust
255: pub open spec fn nr_subpage_per_huge_spec<C: PagingConstsTrait>() -> usize {
256:     C::BASE_PAGE_SIZE() / C::PTE_SIZE()
257: }
258:
259: /// The number of sub pages in a huge page.
260: #[verifier::when_used_as_spec(nr_subpage_per_huge_spec)]
261: pub fn nr_subpage_per_huge<C: PagingConstsTrait>() -> (res: usize)
262:     ensures
263:         res == nr_subpage_per_huge_spec::<C>(),
264: {
265:     proof {
266:         C::lemma_paging_consts_properties();
267:     }
268:     C::BASE_PAGE_SIZE() / C::PTE_SIZE()
```

[ostd/src/mm/mod.rs:223](ostd/src/mm/mod.rs#L223) (lines 223–230)

```rust
223: pub fn page_size<C: PagingConstsTrait>(level: PagingLevel) -> (ret: usize)
224:     requires
225:         1 <= level <= C::NR_LEVELS() + 1,
226:     ensures
227:         ret == page_size_spec::<C>(level),
228:         is_pow2(ret as int),
229:         ret >= C::BASE_PAGE_SIZE(),
230: {
```

[ostd/src/mm/io.rs:1574](ostd/src/mm/io.rs#L1574) (lines 1574–1583)

```rust
1574:     /// ## Postconditions
1575:     /// - The returned value equals [`Self::remain_spec`].
1576:     #[verus_spec(r =>
1577:         requires
1578:             self.inv(),
1579:         ensures
1580:             r == self.remain_spec(),
1581:     )]
1582:     #[verifier::when_used_as_spec(remain_spec)]
1583:     pub fn remain(&self) -> usize {
```

[ostd/src/mm/io.rs:1708](ostd/src/mm/io.rs#L1708) (lines 1708–1717)

```rust
1708:     /// - The returned value equals [`Self::avail_spec`].
1709:     #[inline]
1710:     #[verus_spec(r =>
1711:         requires
1712:             self.inv(),
1713:         ensures
1714:             r == self.avail_spec(),
1715:     )]
1716:     #[verifier::when_used_as_spec(avail_spec)]
1717:     pub fn avail(&self) -> usize {
```

[ostd/src/mm/dma/dma_coherent.rs:479](ostd/src/mm/dma/dma_coherent.rs#L479) (lines 479–485)

```rust
479: impl<M: AnyUFrameMeta + ?Sized> Clone for DmaCoherent<M> {
480:     #[verus_spec(r =>
481:         ensures
482:             r == self,
483:     )]
484:     fn clone(&self) -> Self {
485:         DmaCoherent { inner: self.inner.clone() }
```

<a id="m23"></a>
### M23 — Keep the single-use stride proof inside its caller

**Evidence / premise.** lemma_add_aligned_stride is private, nonrecursive, and has one actual call site (write_vals). Its ten-line arithmetic proof discharges that loop stride obligation rather than defining a caller-visible abstraction.

**Suggested change.** Inline the arithmetic proof at its sole call site; if stable solver context isolation is demonstrated later, document that reason for retaining it.

**Root qualification.** Optional proof-organization choice. A single caller does not itself make an arithmetic lemma redundant; context isolation may help the solver. Benefit is unverified.

**Guideline / confidence.** inline-single-use-proof-helpers, defer-auxiliary-proof-functions; static premise confidence: medium. All implementation and solver outcomes remain unverified.

[ostd/src/mm/io.rs:63](ostd/src/mm/io.rs#L63) (lines 63–81)

```rust
63: proof fn lemma_add_aligned_stride(start: usize, i: usize, len: usize, align: usize)
64:     requires
65:         align > 0,
66:         start % align == 0,
67:         len % align == 0,
68:     ensures
69:         (start + i * len) % align as int == 0,
70: {
71:     let a = align as int;
72:     let q_start = start as int / a;
73:     let q_len = len as int / a;
74:     vstd::arithmetic::div_mod::lemma_fundamental_div_mod(start as int, a);
75:     vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len as int, a);
76:     assert((q_start + i * q_len) * a == q_start * a + (i * q_len) * a) by (nonlinear_arith);
77:     assert((i * q_len) * a == i * (q_len * a)) by (nonlinear_arith);
78:     vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q_start + i * q_len, a);
79: }
80:
81: /// Verus spec stub for [`<*mut T>::is_aligned`]: returns whether the pointer's address is a
```

<a id="pt-02"></a>
### PT-02 — A complete legacy model family is unused by the current page-table proof.

**Evidence / premise.** Repository Rust reference search across ostd, verified_libs and vstd found LeafPageTableEntryView, IntermediatePageTableEntryView, address predicates, to_frame_view only within this file; FrameView appears additionally as unused import src/cursor/mod.rs46. No attached View implementation or broadcast group exists. Current models are Mapping, PageTableView, CursorView, EntryOwner.

**Suggested change.** Remove the unused 99-line entry_view module and its exports/imports as one dependency closure; retain current canonical ownership/mapping models.

**Root qualification.**  No in-repository consumers were found for the identified unused items; check public API intent before removing externally visible declarations.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/node/entry_view.rs:27](ostd/specs/mm/page_table/node/entry_view.rs#L27) (lines 27–50)

```rust
27: pub ghost struct LeafPageTableEntryView<C: PageTableConfig> {
28:     pub map_va: int,
29:     //    pub frame_pa: int,
30:     //    pub in_frame_index: int,
31:     pub map_to_pa: int,
32:     pub level: PagingLevel,
33:     pub prop: PageProperty,
34:     pub phantom: PhantomData<C>,
35: }
36:
37: impl<C: PageTableConfig> Inv for LeafPageTableEntryView<C> {
38:     open spec fn inv(self) -> bool {
39:         //        &&& pa_is_valid_pt_address(self.frame_pa)
40:         &&& pa_is_valid_kernel_address(
41:             self.map_to_pa,
42:         )
43:         // We assume that all level PTEs can be leaf. Thus they can map to huge pages.
44:         &&& 1 <= self.level
45:             <= NR_LEVELS
46:         // The corresponding virtual address must be aligned to the page size.
47:         &&& self.map_va % (page_size::<PagingConsts>(self.level) as int) == 0
48:     }
49: }
50:
```

<a id="pt-03"></a>
### PT-03 — map_full_tree and map_only_children define exactly the same predicate.

**Evidence / premise.** Both quantify self.level-1 <= i < NR_LEVELS and require self.continuations[i].map_children(f) with the same continuation trigger. map_only_children is used only by children_not_locked878 and only_current_locked894, plus explicit hide in source3129. map_full_tree is used by region/frame lemmas.

**Suggested change.** Retain one canonical definition, migrate the two predicate callers and associated hide/reveal directives. Do not alter the quantified level range or include continuation entry roots.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/owners.rs:859](ostd/specs/mm/page_table/cursor/owners.rs#L859) (lines 859–875)

```rust
859:     pub open spec fn map_full_tree(
860:         self,
861:         f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
862:     ) -> bool {
863:         forall|i: int|
864:             #![trigger self.continuations[i]]
865:             self.level - 1 <= i < NR_LEVELS ==> { self.continuations[i].map_children(f) }
866:     }
867:
868:     pub open spec fn map_only_children(
869:         self,
870:         f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
871:     ) -> bool {
872:         forall|i: int|
873:             #![trigger self.continuations[i]]
874:             self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].map_children(f)
875:     }
```

<a id="pt-04"></a>
### PT-04 — CursorView duplicates common mapping-set well-formedness and disjointness predicates.

**Evidence / premise.** Its per-mapping inv clause1817-1820 matches mappings_well_formed in view.rs71-73; non_overlapping1839-1843 matches mappings_disjoint_vaddrs76-79. These shared free functions already exist; trigger choices differ.

**Suggested change.** Use mappings_well_formed(self.mappings) and delegate non_overlapping to mappings_disjoint_vaddrs or migrate callers. Keep the accepted free-function API and evaluate trigger effects.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/owners.rs:1815](ostd/specs/mm/page_table/cursor/owners.rs#L1815) (lines 1815–1844)

```rust
1815: impl<C: PageTableConfig> Inv for CursorView<C> {
1816:     open spec fn inv(self) -> bool {
1817:         &&& forall|m: Mapping|
1818:             #![auto]
1819:             self.mappings.contains(m)
1820:                 ==> m.inv()
1821:         // Config-aware VA range: user page tables live in `[0, 2^47)`,
1822:         // kernel page tables in `[0xffff_8000_…, usize::MAX]`, etc.
1823:         // `vaddr_range_spec<C>` gives inclusive `(start, end_inclusive)`
1824:         // bounds derived from `LEADING_BITS_spec` + `TOP_LEVEL_INDEX_RANGE`,
1825:         // so `Mapping::inv` can stay config-agnostic.
1826:         &&& forall|m: Mapping|
1827:             #![auto]
1828:             self.mappings.contains(m) ==> {
1829:                 &&& vaddr_range_spec::<C>().start <= m.va_range.start
1830:                 &&& m.va_range.end <= vaddr_range_spec::<C>().end + 1
1831:             }
1832:         &&& self.non_overlapping()
1833:     }
1834: }
1835:
1836: impl<C: PageTableConfig> CursorView<C> {
1837:     /// Mappings in the view are non-overlapping. This is a consequence of the
1838:     /// page table tree structure: distinct paths map to disjoint VA ranges.
1839:     pub open spec fn non_overlapping(self) -> bool {
1840:         forall|m: Mapping, n: Mapping|
1841:             #![auto]
1842:             self.mappings.contains(m) ==> self.mappings.contains(n) ==> m != n ==> m.va_range.end
1843:                 <= n.va_range.start || n.va_range.end <= m.va_range.start
1844:     }
```

<a id="pt-05"></a>
### PT-05 — NodeOwner repeats the child counter bound already carried by its metadata owner invariant.

**Evidence / premise.** NodeOwner::inv includes self.meta_own.inv at211. PageMetaOwner::inv172-177 includes0<=nr_children.value()<=NR_ENTRIES.

**Suggested change.** Remove NodeOwner::inv counter-bound conjunct213; keep metadata initialization and other resource facts.

**Guideline / confidence.** implement-inv-for-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/node/owners.rs:209](ostd/specs/mm/page_table/node/owners.rs#L209) (lines 209–228)

```rust
209: impl<C: PageTableConfig> Inv for NodeOwner<C> {
210:     open spec fn inv(self) -> bool {
211:         &&& self.meta_own.inv()
212:         &&& self.frame_permission.frac() == 1
213:         &&& 0 <= self.meta_own.nr_children.value() <= NR_ENTRIES
214:         &&& 1 <= self.level() <= NR_LEVELS
215:         &&& self.children_perm.wf()
216:         &&& self.children_perm.is_init_all()
217:         &&& self.children_perm.addr() == paddr_to_vaddr(
218:             meta_to_frame(index_to_meta(self.slot_index)),
219:         )
220:         &&& self.tree_level == INC_LEVELS - self.level() - 1
221:         &&& 0 <= self.slot_index < max_meta_slots()
222:         &&& FRAME_METADATA_RANGE.start <= index_to_meta(self.slot_index) < FRAME_METADATA_RANGE.end
223:         &&& index_to_meta(self.slot_index) % META_SLOT_SIZE == 0
224:         &&& meta_to_frame(index_to_meta(self.slot_index)) < VMALLOC_BASE_VADDR
225:             - LINEAR_MAPPING_BASE_VADDR
226:         &&& meta_to_frame(index_to_meta(self.slot_index)) < MAX_PADDR
227:         &&& meta_to_frame(index_to_meta(self.slot_index)) == self.children_perm.addr()
228:     }
```

<a id="pt-06"></a>
### PT-06 — metaregion_sound_node repeats the metadata cell identity supplied by wf.

**Evidence / premise.** The preceding self.meta_value().wf(self.meta_own)277 unfolds PageTablePageMeta::wf183-187, whose184 is exactly the nr_children.id equality repeated278-279.

**Suggested change.** Remove the repeated nr_children identity conjunct; retain wf and count_consistent.

**Guideline / confidence.** implement-inv-for-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/node/owners.rs:272](ostd/specs/mm/page_table/node/owners.rs#L272) (lines 272–292)

```rust
272:     pub open spec fn metaregion_sound_node(self, regions: MetaRegionOwners) -> bool {
273:         let idx = self.slot_index;
274:         &&& regions.contains(idx)
275:         &&& self.frame_permission.id() == regions.slot_owners[idx].metadata_perm.id()
276:         &&& self.meta_wf(regions)
277:         &&& self.meta_value().wf(self.meta_own)
278:         &&& self.meta_own.nr_children.id()
279:             == self.meta_value().nr_children.id()
280:         // A page-table node's slot is tracked with `PageTable` usage (set at
281:         // allocation via `get_node_from_unused_spec`). This discriminates node
282:         // slots from data-frame slots (`Frame`/MMIO) by `usage` alone, so a
283:         // freshly-allocated node (whose slot was `UNUSED`) can't collide with an
284:         // existing live node — giving `alloc_if_none`/`split` the parent≠child
285:         // slot distinctness without a PointsTo-linearity axiom.
286:         &&& regions.slot_owners[self.slot_index].usage is PageTable
287:         // `nr_children` counts the present PTEs in `children_perm`. A settled-node
288:         // invariant (it is momentarily broken mid-`replace`/`alloc_if_none`, between
289:         // the PTE write and the counter update, which is why it lives here rather
290:         // than in `inv()`). Lets `nr_children_*_slot_bound` be proven, not axiomatized.
291:         &&& self.count_consistent()
292:     }
```

<a id="pt-07"></a>
### PT-07 — relate_guard repeats its guard pointer equality.

**Evidence / premise.** relate_guard339 requires guard.inner.inner@.wf(self); PageTableNode::wf348 states exactly self.ptr.addr()==owner.slot_vaddr, repeated338.

**Suggested change.** Remove explicit pointer equality338 from relate_guard, retaining wf and the remaining guard relation.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/node/owners.rs:335](ostd/specs/mm/page_table/node/owners.rs#L335) (lines 335–350)

```rust
335:
336: impl<'rcu, C: PageTableConfig> NodeOwner<C> {
337:     pub open spec fn relate_guard(self, guard: PageTableGuard<'rcu, C>) -> bool {
338:         &&& guard.inner.inner@.ptr.addr() == self.slot_vaddr()
339:         &&& guard.inner.inner@.wf(self)
340:         &&& guard.inner.inner@.external_meta_wf(self.frame_permission.resource(), ())
341:     }
342: }
343:
344: impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
345:     type Owner = NodeOwner<C>;
346:
347:     open spec fn wf(self, owner: Self::Owner) -> bool {
348:         &&& self.ptr.addr() == owner.slot_vaddr()
349:         &&& self.ptr_inv()
350:     }
```

<a id="pt-08"></a>
### PT-08 — Entry::wf repeats the PTE address validity already in match_pte.

**Evidence / premise.** wf778 requires owner.match_pte(self.pte,owner.parent_level). match_pte336-351 first conjunct337 is valid_frame_paddr(pte.paddr()).

**Suggested change.** Remove wf779, preserving match_pte and index/parent constraints.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/node/entry_owners.rs:773](ostd/specs/mm/page_table/node/entry_owners.rs#L773) (lines 773–781)

```rust
773: impl<'a, 'rcu, C: PageTableConfig> OwnerOf for Entry<'a, 'rcu, C> {
774:     type Owner = EntryOwner<C>;
775:
776:     open spec fn wf(self, owner: Self::Owner) -> bool {
777:         &&& self.idx < NR_ENTRIES
778:         &&& owner.match_pte(self.pte, owner.parent_level)
779:         &&& valid_frame_paddr(self.pte.paddr())
780:     }
781: }
```

<a id="pt-10"></a>
### PT-10 — Unused not_in_scope predicate and recursive proof remain in the tree API.

**Evidence / premise.** not_in_scope_pred returns constant true. Whole-repository Rust search found tree_not_in_scope only in its definition and self-recursion, and the predicate only in that pair; no broadcasts or traits expose calls.

**Suggested change.** Remove the unused predicate/proof pair.

**Root qualification.**  No in-repository consumers were found for the identified unused items; check public API intent before removing externally visible declarations.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/owners.rs:1710](ostd/specs/mm/page_table/owners.rs#L1710) (lines 1710–1731)

```rust
1710:     pub open spec fn not_in_scope_pred() -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool {
1711:         |entry: EntryOwner<C>, _path: TreePath<NR_ENTRIES>| true
1712:     }
1713:
1714:     /// `subtree_satisfies` for the trivial `not_in_scope_pred`.
1715:     pub proof fn tree_not_in_scope(subtree: OwnerSubtree<C>, path: TreePath<NR_ENTRIES>)
1716:         requires
1717:             subtree.inv(),
1718:         ensures
1719:             subtree.subtree_satisfies(path, Self::not_in_scope_pred()),
1720:         decreases INC_LEVELS - subtree.level(),
1721:     {
1722:         // `not_in_scope_pred` is trivially `true`; recurse to discharge it.
1723:         if subtree.level() < INC_LEVELS - 1 {
1724:             assert forall|i: int|
1725:                 0 <= i < subtree.children().len() && (
1726:                 #[trigger] subtree.children()[i]) is Some implies subtree.children()[i].unwrap().subtree_satisfies(
1727:             path.push_tail(i), Self::not_in_scope_pred()) by {
1728:                 Self::tree_not_in_scope(subtree.children()[i].unwrap(), path.push_tail(i));
1729:             };
1730:         }
1731:     }
```

<a id="pt-11"></a>
### PT-11 — User-specific view bound proof duplicates the generic view-range proof.

**Evidence / premise.** lemma_view_in_vaddr_range1849-1892 already proves the configured C::vaddr_range. User wrapper repeats two choose decompositions and view_rec_top_index_va_bound; its concrete bound can follow the existing user range lemma. The user wrapper is called by vm_space.rs1035.

**Suggested change.** Keep the useful concrete user contract but replace its body with the generic lemma and lemma_vaddr_range_spec_user; avoid duplicate decomposition reasoning.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/owners.rs:1902](ostd/specs/mm/page_table/cursor/owners.rs#L1902) (lines 1902–1932)

```rust
1902: pub proof fn lemma_view_in_vaddr_range_user<'rcu>(
1903:     owner: &CursorOwner<'rcu, crate::mm::vm_space::UserPtConfig>,
1904: )
1905:     requires
1906:         owner.inv(),
1907:     ensures
1908:         forall|m: Mapping|
1909:             #![auto]
1910:             owner.view_mappings().contains(m) ==> {
1911:                 &&& 0 <= m.va_range.start
1912:                 &&& m.va_range.end <= 0x8000_0000_0000int
1913:             },
1914: {
1915:     let end = crate::mm::vm_space::UserPtConfig::TOP_LEVEL_INDEX_RANGE().end as int;
1916:     assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
1917:         &&& 0 <= m.va_range.start
1918:         &&& m.va_range.end <= 0x8000_0000_0000int
1919:     } by {
1920:         let i = choose|i: int|
1921:             owner.level - 1 <= i < NR_LEVELS && (
1922:             #[trigger] owner.continuations[i]).view_mappings().contains(m);
1923:         let cont = owner.continuations[i];
1924:         let j = choose|j: int|
1925:             0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
1926:                 cont.children[j].unwrap(),
1927:             ).view_rec(cont.path().push_tail(j)).contains(m);
1928:         let child = PageTableOwner(cont.children[j].unwrap());
1929:         let p = cont.path().push_tail(j);
1930:         child.view_rec_top_index_va_bound(p, m, end);
1931:     }
1932: }
```

<a id="pt-12"></a>
### PT-12 — Unused kernel-specific view-range proof duplicates the generic result.

**Evidence / premise.** Repository search found lemma_view_in_vaddr_range_kernel only at its definition and a comment676. Its postcondition is the generic lemma instantiated at KernelPtConfig.

**Suggested change.** Remove the unused kernel wrapper; alternatively delegate to the generic lemma if maintaining this public API is intentional.

**Root qualification.**  No in-repository consumers were found for the identified unused items; check public API intent before removing externally visible declarations.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/owners.rs:1938](ostd/specs/mm/page_table/cursor/owners.rs#L1938) (lines 1938–1968)

```rust
1938: pub proof fn lemma_view_in_vaddr_range_kernel<'rcu>(owner: CursorOwner<'rcu, KernelPtConfig>)
1939:     requires
1940:         owner.inv(),
1941:     ensures
1942:         forall|m: Mapping|
1943:             #![auto]
1944:             owner.view_mappings().contains(m) ==> {
1945:                 &&& vaddr_range_spec::<KernelPtConfig>().start <= m.va_range.start
1946:                 &&& m.va_range.end <= vaddr_range_spec::<KernelPtConfig>().end + 1
1947:             },
1948: {
1949:     lemma_vaddr_range_spec_kernel();
1950:     let end = KernelPtConfig::TOP_LEVEL_INDEX_RANGE().end as int;
1951:     assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
1952:         &&& vaddr_range_spec::<KernelPtConfig>().start <= m.va_range.start
1953:         &&& m.va_range.end <= vaddr_range_spec::<KernelPtConfig>().end + 1
1954:     } by {
1955:         let i = choose|i: int|
1956:             owner.level - 1 <= i < NR_LEVELS && (
1957:             #[trigger] owner.continuations[i]).view_mappings().contains(m);
1958:         let cont = owner.continuations[i];
1959:         let j = choose|j: int|
1960:             0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
1961:                 cont.children[j].unwrap(),
1962:             ).view_rec(cont.path().push_tail(j)).contains(m);
1963:         let child = PageTableOwner(cont.children[j].unwrap());
1964:         let p = cont.path().push_tail(j);
1965:         child.view_rec_top_index_va_bound(p, m, end);
1966:         // m.start ≥ index(0)·2^39 + lb·2^48 ≥ start·2^39 + lb·2^48 = bound.0.
1967:     }
1968: }
```

<a id="pt-13"></a>
### PT-13 — CursorOwner::map_children_implies reimplements continuation predicate lifting.

**Evidence / premise.** CursorContinuation::map_children_lift27-55 already lifts exactly the same map_children f to g using OwnerSubtree::implies(f,g); map_children_implies repeats nested child/subtree quantifiers for each active continuation.

**Suggested change.** Within the active-continuation quantifier call self.continuations[i].map_children_lift(f,g), retaining all existing premises and postcondition.

**Root qualification.** Before delegating to the continuation lemma, establish the active continuation invariant, e.g. with lemma_inv_continuation(i).

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/tree_lemmas.rs:122](ostd/specs/mm/page_table/cursor/tree_lemmas.rs#L122) (lines 122–160)

```rust
122:     pub proof fn map_children_implies(
123:         self,
124:         f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
125:         g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
126:     )
127:         requires
128:             self.inv(),
129:             OwnerSubtree::implies(f, g),
130:             forall|i: int|
131:                 #![trigger self.continuations[i]]
132:                 self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].map_children(f),
133:         ensures
134:             forall|i: int|
135:                 #![trigger self.continuations[i]]
136:                 self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].map_children(g),
137:     {
138:         assert forall|i: int|
139:             #![trigger self.continuations[i]]
140:             self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(g) by {
141:             reveal(CursorContinuation::map_children);
142:             let cont = self.continuations[i];
143:             reveal(CursorContinuation::inv_children);
144:             assert forall|j: int|
145:                 #![trigger cont.children[j]]
146:                 0 <= j < cont.children.len()
147:                     && cont.children[j] is Some implies cont.children[j].unwrap().subtree_satisfies(
148:                 cont.path().push_tail(j),
149:                 g,
150:             ) by {
151:                 cont.lemma_inv_children_unroll(j);
152:                 OwnerSubtree::lemma_subtree_satisfies_implies(
153:                     cont.children[j].unwrap(),
154:                     cont.path().push_tail(j),
155:                     f,
156:                     g,
157:                 );
158:             }
159:         }
160:     }
```

<a id="pt-14"></a>
### PT-14 — max_steps_partial_inv duplicates the recursive equality lemma immediately above it.

**Evidence / premise.** max_steps_partial_eq153-166 needs the starting bound and matching continuation indices from start-1. The inv-specialized variant168-186 assumes both owners inv, equal levels and all active index equality, sufficient to discharge the general lemma. Only nonrecursive call is source cursor/mod.rs1311.

**Suggested change.** Delegate the specialized body to max_steps_partial_eq. Because it has one actual caller, consider replacing that call with the general lemma and removing the wrapper if no isolation role is needed.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/cursor_steps.rs:153](ostd/specs/mm/page_table/cursor/cursor_steps.rs#L153) (lines 153–186)

```rust
153:     pub proof fn max_steps_partial_eq(self, other: Self, start: usize)
154:         requires
155:             1 <= start <= NR_LEVELS + 1,
156:             forall|k: int|
157:                 start - 1 <= k < NR_LEVELS ==> #[trigger] self.continuations[k].idx
158:                     == other.continuations[k].idx,
159:         ensures
160:             self.max_steps_partial(start) == other.max_steps_partial(start),
161:         decreases NR_LEVELS + 1 - start,
162:     {
163:         if start <= NR_LEVELS {
164:             self.max_steps_partial_eq(other, (start + 1) as usize);
165:         }
166:     }
167:
168:     pub proof fn max_steps_partial_inv(self, other: Self, level: usize)
169:         requires
170:             self.inv(),
171:             other.inv(),
172:             self.level == other.level,
173:             self.level <= level <= NR_LEVELS + 1,
174:             forall|i: int|
175:                 #![trigger self.continuations[i].idx]
176:                 #![trigger other.continuations[i].idx]
177:                 self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].idx
178:                     == other.continuations[i].idx,
179:         ensures
180:             self.max_steps_partial(level) == other.max_steps_partial(level),
181:         decreases NR_LEVELS + 1 - level,
182:     {
183:         if level <= NR_LEVELS {
184:             self.max_steps_partial_inv(other, (level + 1) as usize);
185:         }
186:     }
```

<a id="pt-15"></a>
### PT-15 — An inv-unfolding helper takes unnecessary range/pop premises for a bound already in inv.

**Evidence / premise.** CursorOwner::inv642 includes level<=NR_LEVELS unconditionally. lemma_in_locked_range_level_le_nr_levels additionally requires in_locked_range and !popped_too_high but proves only the unconditional bound. Source callers919,979,1245 already retain owner.inv.

**Suggested change.** Prefer direct inv reasoning and delete the helper/calls, or at least drop the two redundant premises. Proof removal is unverified.

**Root qualification.**  Logical entailment is a candidate for proof reuse, not evidence that deleting the conjunct will verify or improve performance.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/cursor/owners.rs:1277](ostd/specs/mm/page_table/cursor/owners.rs#L1277) (lines 1277–1285)

```rust
1277:     pub proof fn lemma_in_locked_range_level_le_nr_levels(self)
1278:         requires
1279:             self.inv(),
1280:             self.in_locked_range(),
1281:             !self.popped_too_high,
1282:         ensures
1283:             self.level <= NR_LEVELS,
1284:     {
1285:     }
```

<a id="pt-16"></a>
### PT-16 — empty_with_owner repeats node and lock-preservation guarantees.

**Evidence / premise.** is_node1306 and1307 are identical; owner.inv1305 also requires root is_node. Guards equality1314 implies forall lock_held preservation1329 because Guards::lock_held is guards.contains (specs/node/mod.rs31).

**Suggested change.** After repairing PT-01, remove duplicate is_node1307 (and optionally both explicit is_node clauses under owner.inv) and derived lock_held1329.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/mod.rs:1304](ostd/src/mm/page_table/mod.rs#L1304) (lines 1304–1329)

```rust
1304:             final(owner)@ is Some,
1305:             final(owner)@->0.inv(),
1306:             (final(owner)@->0).0.value().is_node(),
1307:             (final(owner)@->0).0.value().is_node(),
1308:             r.root.ptr.addr() == (final(owner)@->0).0.value().node().slot_vaddr(),
1309:             (final(owner)@->0).0.value().metaregion_sound(*final(regions)),
1310:             final(regions).inv(),
1311:             final(guards).unlocked((final(owner)@->0).0.value().node().slot_vaddr()),
1312:             // Allocating a fresh node does not change the lock set, so any node
1313:             // that was (un)locked before remains so.
1314:             final(guards).guards == old(guards).guards,
1315:             // The newly allocated slot was in the free pool before the call.
1316:             old(regions).contains(
1317:                 crate::specs::mm::frame::mapping::frame_to_index(
1318:                     (final(owner)@->0).0.value().meta_slot_paddr()->0)),
1319:             // After the alloc, the slot is removed from the free pool (now owned
1320:             // by the new pt's NodeOwner).
1321:             !final(regions).contains(
1322:                 crate::specs::mm::frame::mapping::frame_to_index(
1323:                     (final(owner)@->0).0.value().meta_slot_paddr()->0)),
1324:             // Other slots and lock state are preserved.
1325:             forall |i: int| #![trigger final(regions).slot_owners[i]]
1326:                 i != crate::specs::mm::frame::mapping::frame_to_index(
1327:                     (final(owner)@->0).0.value().meta_slot_paddr()->0)
1328:                 ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
1329:             forall |a: usize| old(guards).lock_held(a) ==> final(guards).lock_held(a),
```

<a id="pt-17"></a>
### PT-17 — Replacement contracts repeat weak slots preservation beneath exact map equality.

**Evidence / premise.** Entry::replace333 ensures final(regions).slots==old(regions).slots. This implies key monotonicity319-322, repeated conditional equality336, and old-absent/nonnode conditional lookup equality344-346. Guard::replace_child repeats same structure1557-1580 with unconditional1569.

**Suggested change.** Retain unconditional slots equality and remove its weaker duplicate clauses in both APIs. Keep slot_owners preservation/refcounts/permissions, which describe distinct resources.

**Root qualification.** The secondary Guard::replace_child location is also in ostd/src/mm/page_table/node/entry.rs:1557-1580.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/node/entry.rs:319](ostd/src/mm/page_table/node/entry.rs#L319) (lines 319–346)

```rust
319:             forall|k: int|
320:                 old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(
321:                     k,
322:                 ),
323:             forall|idx: int|
324:                 #![trigger final(regions).slot_owners[idx].ref_count()]
325:                 final(regions).ref_count(idx) == old(
326:                     regions,
327:                 ).ref_count(idx),
328:             forall|idx: int|
329:                 #![trigger final(regions).slot_owners[idx].ref_count_perm]
330:                 final(regions).slot_owners[idx].same_permissions(
331:                     old(regions).slot_owners[idx],
332:                 ),
333:             final(regions).slots == old(regions).slots,
334:             // When both old and new are not nodes: from_pte/into_pte are identity.
335:             (!old(owner).is_node() && !final(new_owner).is_node()) ==> {
336:                 &&& final(regions).slots == old(regions).slots
337:                 &&& forall|i: int|
338:                     #![trigger final(regions).slot_owners[i]]
339:                     final(regions).slot_owners[i] == old(
340:                         regions,
341:                     ).slot_owners[i]
342:             },
343:             // When old child is absent and new child is not a node: slots values unchanged.
344:             (old(owner).is_absent() && !final(new_owner).is_node()) ==> forall|k: int|
345:                 old(regions).slots.contains_key(k) ==> old(regions).slots[k]
346:                     == #[trigger] final(regions).slots[k],
```

<a id="pt-18"></a>
### PT-18 — find_next_impl loop contains duplicate and derived invariants.

**Evidence / premise.** self.inv appears875 and878 exactly. !split_happened mappings equality896 plus unconditional old-map empty scanned range900-901 imply the conditional current-map empty scanned range897-899.

**Suggested change.** Remove duplicate self.inv878 and consider removing derived conditional range-empty897-899, retaining the equality and unconditional accumulator.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/cursor/mod.rs:872](ostd/src/mm/page_table/cursor/mod.rs#L872) (lines 872–901)

```rust
872:         while self.va < end
873:             invariant
874:                 owner.inv(),
875:                 self.inv(),
876:                 self.wf(*owner),
877:                 regions.inv(),
878:                 self.inv(),
879:                 old(owner)@.inv(),
880:                 owner.in_locked_range() || self.va >= end,
881:                 self.va >= old(self).va,
882:                 end == old(self).va + len,
883:                 end % PAGE_SIZE == 0,
884:                 end <= self.barrier_va.end,
885:                 !old(self).find_next_panic_condition(len),
886:                 self.barrier_va == barrier_va,
887:                 barrier_va == old(self).barrier_va,
888:                 self.guard_level == old(self).guard_level,
889:                 owner.children_not_locked(*guards),
890:                 owner.nodes_locked(*guards),
891:                 owner.metaregion_sound(*regions),
892:                 !owner.popped_too_high,
893:                 old_owner_cur_va == old(owner)@.cur_va,
894:                 old_owner_cur_va == old(self).va,
895:                 // Mapping preservation: if no split happened, mappings are unchanged.
896:                 !split_happened ==> owner@.mappings == old(owner)@.mappings,
897:                 !split_happened ==> owner@.mappings.filter(
898:                     |m: Mapping| old(self).va <= m.va_range.start < self.va,
899:                 ) == Set::<Mapping>::empty(),
900:                 old(owner)@.mappings.filter(|m: Mapping| old(self).va <= m.va_range.start < self.va)
901:                     == Set::<Mapping>::empty(),
```

<a id="pt-19"></a>
### PT-19 — cur_entry spells out consequences of its existing reborrow equalities.

**Evidence / premise.** 1847 equates final path payload with final res.node. Substitution immediately proves1848-1852. Entry-state1845 identifies res.node with old path payload, so wf implication1855 has the same antecedent as1853-1854.

**Suggested change.** Remove derived equality implications1848-1852 and one equivalent wf implication1855; retain1845-1847,1853-1854, other-path preservation, and owner equality.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/cursor/mod.rs:1845](ostd/src/mm/page_table/cursor/mod.rs#L1845) (lines 1845–1859)

```rust
1845:             *res.node == old(self).path[old(self).level - 1]->0,
1846:             final(self).path[old(self).level - 1] is Some,
1847:             final(self).path[old(self).level - 1]->0 == *final(res.node),
1848:             *final(res.node) == old(self).path[old(self).level - 1]->0
1849:                 ==> final(self).path[old(self).level - 1]->0
1850:                     == old(self).path[old(self).level - 1]->0,
1851:             *final(res.node) == *res.node ==> final(self).path[old(self).level - 1]->0
1852:                 == *res.node,
1853:             *final(res.node) == old(self).path[old(self).level - 1]->0
1854:                 ==> final(self).wf(*final(owner)),
1855:             *final(res.node) == *res.node ==> final(self).wf(*final(owner)),
1856:             forall|i: int|
1857:                 0 <= i < NR_LEVELS && i != old(self).level - 1 ==> #[trigger] final(self).path[i]
1858:                     == old(self).path[i],
1859:             *final(owner) == *old(owner),
```

<a id="pt-20"></a>
### PT-20 — move_forward separately guarantees a field of already preserved slot owners.

**Evidence / premise.** 1536-1540 says every final slot owner paths_in_pt equals old;1543-1545 guarantees entire slot owner equality at every index. pop_level also guarantees entire regions equality1710 while repeating regions.inv1693 under old.inv1679.

**Suggested change.** Remove move_forward paths-only quantified clause; optionally trim pop_level final regions.inv using exact region preservation. Preserve guards and mapping changes.

**Guideline / confidence.** canonical-spec-models; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/cursor/mod.rs:1535](ostd/src/mm/page_table/cursor/mod.rs#L1535) (lines 1535–1545)

```rust
1535:             // move_forward only calls pop_level, which does not touch regions.
1536:             forall|idx: int|
1537:                 #![trigger final(regions).slot_owners[idx].paths_in_pt]
1538:                 final(regions).slot_owners[idx].paths_in_pt == old(
1539:                     regions,
1540:                 ).slot_owners[idx].paths_in_pt,
1541:             // Slots and slot_owners fully unchanged (pop_level is purely cursor manipulation).
1542:             final(regions).slots == old(regions).slots,
1543:             forall|idx: int|
1544:                 #![trigger final(regions).slot_owners[idx]]
1545:                 final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
```

<a id="pt-21"></a>
### PT-21 — Huge split repeatedly proves the same pure arithmetic witness in one iteration.

**Evidence / premise.** lemma_split_sub_page_big_j(pa,level,i) is called1118-1122,1199-1201,1214-1217. pa/level/i are unchanged; helper's proof result is arithmetic, independent of mutation to regions.paths_in_pt1208-1209.

**Suggested change.** Bind the nonzero-i witness once and reuse it in subsequent proof blocks. Keep the i==0 branch and all mutation framing. Remove empty level-1>1 block1211-1212 as trivial scaffolding.

**Root qualification.** Hoist a witness into the enclosing ghost scope. A branch-local binder cannot simply be reused outside that scope.

**Guideline / confidence.** reuse-existing-specifications; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/node/entry.rs:1116](ostd/src/mm/page_table/node/entry.rs#L1116) (lines 1116–1122)

```rust
1116:             proof {
1117:                 let idx = frame_to_index(small_pa);
1118:                 if i != 0 {
1119:                     let ghost big_j =
1120:                         crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_split_sub_page_big_j(
1121:                     pa, level, i);
1122:                 }
```

<a id="pt-22"></a>
### PT-22 — The count-equality helper carries an irrelevant idx parameter through recursion.

**Evidence / premise.** lemma_count_present_upto_unchanged uses idx only in0<=n<=idx; its inductive count equality requires nonnegative n and pointwise equality below n. idx is forwarded unchanged163. Only nonrecursive call is lemma_count_present_upto_update126.

**Suggested change.** Remove idx from the helper and retain0<=n plus pointwise equality. Do not remove the caller's actual update index bounds.

**Guideline / confidence.** avoid-unused-spec-helpers; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/node/owners.rs:149](ostd/specs/mm/page_table/node/owners.rs#L149) (lines 149–165)

```rust
149: pub proof fn lemma_count_present_upto_unchanged<E: PageTableEntryTrait>(
150:     s: Seq<E>,
151:     s2: Seq<E>,
152:     n: int,
153:     idx: int,
154: )
155:     requires
156:         0 <= n <= idx,
157:         forall|k: int| 0 <= k < n ==> s[k] == s2[k],
158:     ensures
159:         count_present_upto(s2, n) == count_present_upto(s, n),
160:     decreases n,
161: {
162:     if n > 0 {
163:         lemma_count_present_upto_unchanged(s, s2, n - 1, idx);
164:     }
165: }
```

<a id="pt-25"></a>
### PT-25 — Several exact-result equalities use ensures instead of returns.

**Evidence / premise.** PageTablePageMeta::into93-94 and StoredPageTablePageMeta::into118-119 return exactly into_spec. PageTableGuard::read_pte source node/mod.rs536-537 is also exact result. Cursor::cur_va_range1930 is exact owner range plus separate bounds.

**Suggested change.** Use returns for these exact result clauses while preserving other ensures and casts required by differing types.

**Guideline / confidence.** use-returns-for-exact-results; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/specs/mm/page_table/node/mod.rs:90](ostd/specs/mm/page_table/node/mod.rs#L90) (lines 90–102)

```rust
90:
91:     #[verifier::when_used_as_spec(into_spec)]
92:     pub fn into(self) -> (res: StoredPageTablePageMeta)
93:         ensures
94:             res == self.into_spec(),
95:     {
96:         StoredPageTablePageMeta {
97:             nr_children: self.nr_children,
98:             stray: self.stray,
99:             level: self.level,
100:             lock: self.lock,
101:         }
102:     }
```

<a id="pt-26"></a>
### PT-26 — Historical helper debt documentation is now attached to PageTableFrag and describes obsolete raw_count accounting.

**Evidence / premise.** The comment starts Borrows a live PageTableNode and proposes a fix, but the following item160 is an enum. Active subtree branch3737 uses borrow_with_permission; EntryOwner into/from wrappers are identity and retained by user instruction.

**Suggested change.** Delete or relocate the obsolete helper comment. Also correct stale Axiom wording in specs/cursor/owners1071-1084 for checked proof1111-1122 and outdated unmap-pending statement invariant_preservation_lemmas1-11; retain real documented assumptions.

**Root qualification.** Correct stale comments only. Checked clone reasoning still consumes existing axioms; this does not eliminate its trusted dependencies.

**Guideline / confidence.** document-real-proof-debt; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/cursor/mod.rs:139](ostd/src/mm/page_table/cursor/mod.rs#L139) (lines 139–159)

```rust
139: /// Borrows a live `PageTableNode` as a `PageTableNodeRef` without requiring
140: /// `raw_count == 1`.
141: ///
142: /// ## Justification
143: /// `Child::from_pte` (called inside `Entry::replace`) invokes `PageTableNode::from_raw`,
144: /// which sets `regions.slot_owners[idx].raw_count = 0`.  Consequently `metaregion_sound`
145: /// reports `raw_count == 0`, but
146: /// `Frame::borrow` / `FrameRef::borrow_paddr` require `raw_count == 1`.
147: ///
148: /// This function bridges that gap: we have unique ownership of the live frame `pt`
149: /// (just returned from `Entry::replace`), so borrowing it as a `PageTableNodeRef`
150: /// is semantically sound.  The `raw_count == 1` requirement in `borrow_paddr` is an
151: /// accounting invariant designed for *forgotten* frames stored in PTEs; it does not
152: /// apply to live frames held directly.
153: ///
154: /// ## Fix path
155: /// The proper fix is:
156: ///   1. Add `ensures old(owner).is_node() ==> regions.contains(...)` to
157: ///      `Entry::replace`.
158: ///   2. Replace this call with `pt.into_raw()` + `PageTableNodeRef::borrow_paddr()`.
159: /// A fragment of a page table that can be taken out of the page table.
```

<a id="pt-27"></a>
### PT-27 — take_next and replacement postconditions repeatedly project the same Option/enum payload.

**Evidence / premise.** take_next3058-3116 repeatedly uses res is Some && res->0 is Mapped/StrayPageTable followed by res->0->Variant_field. replace_cur_entry3434-3448 repeats the same pattern. Payload binding changes presentation only; mapping removal, split and count properties remain distinct.

**Suggested change.** Use matches Some(PageTableFrag::Mapped { va, item }) and the analogous StrayPageTable binding for each meaningful postcondition group; preserve every existing semantic clause and trigger.

**Guideline / confidence.** bind-option-payloads; static premise confidence: high. All implementation and solver outcomes remain unverified.

[ostd/src/mm/page_table/cursor/mod.rs:3058](ostd/src/mm/page_table/cursor/mod.rs#L3058) (lines 3058–3076)

```rust
3058:             res is Some && res->0 is Mapped ==>
3059:                 old(owner)@.mappings.filter(|m: Mapping|
3060:                     old(self).0.va <= m.va_range.start < res->0->Mapped_va)
3061:                     == Set::<Mapping>::empty(),
3062:             res is Some && res->0 is StrayPageTable ==>
3063:                 old(owner)@.mappings.filter(|m: Mapping|
3064:                     old(self).0.va <= m.va_range.start < res->0->StrayPageTable_va)
3065:                     == Set::<Mapping>::empty(),
3066:             res is Some && res->0 is Mapped ==> {
3067:                 let m = CursorView::<C>::item_into_mapping(
3068:                     res->0->Mapped_va, res->0->Mapped_item);
3069:                 final(owner)@.mappings.filter(|m2: Mapping|
3070:                     res->0->Mapped_va <= m2.va_range.start < final(self).0.va)
3071:                     == Set::<Mapping>::empty()
3072:             },
3073:             res is Some && res->0 is StrayPageTable ==>
3074:                 final(owner)@.mappings.filter(|m2: Mapping|
3075:                     res->0->StrayPageTable_va <= m2.va_range.start < final(self).0.va)
3076:                     == Set::<Mapping>::empty(),
```

## Retracted or deliberately unsupported claims

- `0 < ref_count` does not exclude `REF_COUNT_UNUSED = u64::MAX`; no contradiction is claimed solely from that comparison.
- A broadcast lemma is not unused merely because there are no named call sites. P02 concerns an exact duplicated proposition and trigger, not generic broadcast removal.
- The dispatcher observations in P21 establish a model-scope question, not a proven runtime bug or permission to delete the model.
- Public helpers with no internal consumers and one-caller arithmetic lemmas remain API/proof-organization choices. No verifier speedup is claimed.
- No blanket PA-disjointness rule is imposed on shared mappings. No trusted boundary is removed or newly introduced by this review.

## Guideline coverage and bounded compliance

The following are localized observations, not a claim that an entire module satisfies a rule. Full rules: [coding guidelines](docs/coding-guidelines/README.md), [maintainability](docs/coding-guidelines/maintainability.md), [proof engineering](docs/coding-guidelines/proof-engineering.md). Workflow checks on changed rlimit caps or new standard-library external specs are not applicable: this review does not change those sources.

| Review area | Rule | Status | Observation |
| --- | --- | --- | --- |
| spec/proof | complete-external-contracts | finding | P01 contradicts the resource invariant at an internal trusted allocation front door; report isolates correction from simplification. No claim that current empty proof bodies establish runtime behavior. |
| spec/proof | centralize-trusted-boundaries | finding | P19 duplicates an entire internal trusted contract through an unadapted one-call wrapper. External bodies and embedding axioms were read together with front-door contracts. |
| spec/proof | restrict-generic-trusted-models | checked | No proposal to invent a generic trusted model or strengthen arbitrary metadata; typed metadata invariants and ownership roles retained. |
| spec/proof | distinguish-spec-and-exec-indexing | checked | Sequence/map ghost accesses reviewed; bound and permission preconditions retained except precisely implied facts. No indexing requirement removed merely because spec indexing is total. |
| spec/proof | reuse-existing-specifications | finding | P08 reuses accepted mappings_disjoint_vaddrs; P12 uses vendored Seq::map_values; P14 reuses valid_slot_vaddr; P17 uses existing region-valid-address lemma. |
| spec/proof | canonical-spec-models | finding | P08,P12,P14,P23 consolidate equivalent models; P21 flags incomplete operational modeling separately. Do not collapse distinct owning resources or PA-alias policies. |
| spec/proof | quantifiers-and-triggers | checked_with_caveat | P02 exact trigger duplicate; P10/P11/P16 require proof-instantiation/performance validation before removing cached quantified facts. No removable solver-hint claim. |
| spec/proof | implement-inv-for-models | guideline_gap; no semantic redundancy claimed | KVmStore (embedding/kvirt_store.rs:82), ListStore (embedding/list_store.rs:128), VmIoEntry/ CursorEntry/ VmStore (embedding/mod.rs:255/300/323) define intrinsic inherent inv without implementing Inv. Move unchanged definitions to Inv if these models are retained; do not automatically inject type_invariant across temporarily extracted ownership states. |
| spec/proof | separate-verus-modes | checked | Spec/proof items predominantly reside in verus blocks. Layout-only changes excluded from actionable optimization findings. |
| spec/proof | use-chained-comparisons | finding | P05 removes range ordering already carried by chained bounds; other cosmetic chaining opportunities not promoted as substantive optimizations. |
| spec/proof | use-returns-for-exact-results | checked | Exact-result clauses inspected; no wholesale ensures conversion without retaining relational state guarantees. |
| spec/proof | avoid-redundant-as-int-casts | checked_with_caveat | Casts reviewed as proof syntax; no broad removal recommended without compiler checks. |
| spec/proof | seq-range-slicing | checked | Sequence operations inspected; P12 targets semantic model duplication rather than equivalent slicing spelling. |
| spec/proof | organize-proof-imports | checked_with_caveat | No reveal/open-function fuel deletion recommended without verification; import layout excluded from substantive redundancy report. |
| spec/proof | group-imports-by-crate | checked | Import organization reviewed; no source edits or style-only findings produced. |
| spec/proof | bind-option-payloads | checked | Option relationships traced for P07/P23; retain meaningful variant/read-write checks. |
| spec/proof | preserve-exec-code | compliant_for_review | Read-only review; all suggested equivalent simplifications target spec/proof code. P01 runtime-front-door correction requires a separate reviewed change. |
| spec/proof | name-proof-roles | checked | Roles and naming examined; no bulk rename recommendation in a redundancy audit. |
| spec/proof | avoid-unused-spec-helpers | finding | P03,P20,P22 have declaration-only evidence; P21 deliberately separates incomplete operational coverage from safe unused-helper deletion. |
| spec/proof | inline-single-use-proof-helpers | finding | P19 is exact full-contract passthrough with one caller; no claim all one-caller helpers lack valuable opacity. |
| spec/proof | defer-auxiliary-proof-functions | checked | Auxiliary proof placement reviewed; no layout-only rewrite proposed. |
| spec/proof | avoid-redundant-mode-markers | checked | Ghost/tracked boundaries reviewed; linear ownership markers retained. |
| spec/proof | prefer-ghost-model-structs | checked | Frame, list, cursor and IO resources carry tracked authority; no conversion to ghost on superficial all-ghost fields. |
| spec/proof | keep-internal-spec-helpers-closed | checked_with_caveat | Opacity preserved for relate_region P16; propose implication lemma rather than broad reveal to force optimization. |
| spec/proof | document-verified-apis | finding | P21 missing operational coverage and P22 stale consumer links should be reflected accurately in documentation. |
| spec/proof | narrow-lint-suppressions | checked | No new suppressions or lint-driven source changes; existing allowances not treated as semantic redundancy. |
| spec/proof | right-size-spec-placement | checked | Substantial shared ownership/subsystem models justify specs tree; no relocation merely from a single size threshold. |
| spec/proof | document-real-proof-debt | finding | P01/P21 current concrete contradictions/transition gaps must be documented accurately; no speculative tool-limit warnings. |
| spec/proof | qualified-verus-spec-calls | not_applicable_to_change | No modified executable verus_spec call; relevant front-door spec attachment read as dependency context. |
| spec/proof | pair-exec-helpers-with-spec-models | checked | Address conversion and front-door bindings traced; no changed executable model formula or duplicate exec rewrite proposed. |
| source/other specs | separate-verus-modes | grouped-low-impact | Adjacent verus blocks can merge; mode groups elsewhere generally distinguish proof_decl/proof from exec. Grouped layout follow-up, not a substantive optimization. |
| source/other specs | use-chained-comparisons | grouped-low-impact | fill_zeros cursor lower/upper bounds can form one chain. Do not strengthen unrelated bounds. |
| source/other specs | use-returns-for-exact-results | finding | See linked concrete findings; no blanket compliance assertion. |
| source/other specs | avoid-redundant-as-int-casts | bounded-compliance | Division/modulo calls take int and require casts here. Other arithmetic casts may be removable only with type checking; no blind cast-removal finding. |
| source/other specs | seq-range-slicing | bounded-compliance | Reviewed sequence invariants and slice/drop paths; no actionable spec-only range rewrite isolated in primary files. Method-like runtime slice operations are not ghost subrange calls. |
| source/other specs | organize-proof-imports | grouped-low-impact | Repeated mapping_set_lemmas qualified paths should use explicit proof imports; no open-function reveals proposed for removal without verification. |
| source/other specs | group-imports-by-crate | grouped-low-impact | Verification/core crate imports split across several same-crate statements. Group proof imports while preserving inherited executable import separation. |
| source/other specs | bind-option-payloads | grouped-low-impact | pop_front/pop_back/take_current repeatedly project Some tuple payloads. Bind once with matches Some((frame,frame_owner)) and keep conditions identical. |
| source/other specs | preserve-exec-code | limited-history-audit | Snapshot contains commented original migration macro; current marker format is not the required adjacent Origin Rust block. This review made no exec edits; exhaustive upstream executable equivalence was not audited, so no global compliance claim. |
| source/other specs | name-proof-roles | bounded-compliance | Reusable arithmetic/region lemmas have lemma_ names; tracked owners state authority role. Proof-context-isolation helper is intentionally documented. |
| source/other specs | avoid-unused-spec-helpers | finding | See linked concrete findings; no blanket compliance assertion. |
| source/other specs | inline-single-use-proof-helpers | finding | See linked concrete findings; no blanket compliance assertion. |
| source/other specs | defer-auxiliary-proof-functions | finding | See linked concrete findings; no blanket compliance assertion. |
| source/other specs | avoid-redundant-mode-markers | finding | Tracked address-only history can disappear; retain actual permission tokens. |
| source/other specs | prefer-ghost-model-structs | bounded-compliance | RcuPublishedObject is ghost; RcuRootGhost carries a linear domain authority and appropriately remains tracked. DMA zero-state owner modes are candidates only after mode verification. |
| source/other specs | keep-internal-spec-helpers-closed | finding | Single-use internal predicate can inline instead of retaining pub closed exposure. |
| source/other specs | document-verified-apis | grouped-low-impact | Several proof docs repeat Preconditions/Postconditions prose disallowed by live rule; verified runtime sections often order fields differently. Group documentation cleanup, preserve functional/trust claims and useful summaries. |
| source/other specs | narrow-lint-suppressions | grouped-low-impact | Broad module lint allows should narrow to triggering items; no spec-semantic reduction from changing lint scope. |
| source/other specs | right-size-spec-placement | bounded-compliance | Substantial shared VM-space model already located in specs and imported by path. Small implementation-specific adapters may stay local; do not force extension traits for accepted mappings functions. |
| source/other specs | document-real-proof-debt | grouped-low-impact | Historical AI-generation note does not explain current proof debt; remove it. Keep actual trust/overflow/RCU debt notes and avoid claims stronger than contracts. |
| source/other specs | qualified-verus-spec-calls | bounded-compliance | Attributed get_slot uses qualified crate path; do not import merely to alter Verus attribute resolution. |
| source/other specs | pair-exec-helpers-with-spec-models | finding | size already uses dual_spec self-referential returns; exact relation duplicate removable. page-size helpers have when_used_as_spec twins. |
| page table | centralize-trusted-boundaries | complies | Atomic PTE load is localized behind a permission-aware trusted wrapper. This localized compliance does not override PT-01. |
| page table | restrict-generic-trusted-models | complies | Generic PageTableEntryTrait exposes abstract new_page_req instead of globally asserting concrete architecture bit behavior. |
| page table | distinguish-spec-and-exec-indexing | complies | Executable index is bounded by idx<NR_ENTRIES and the proof uses explicit spec indexing into the permission value. |
| page table | quantifiers-and-triggers | complies | Named per-cursor coverage predicate and instantiation lemma explain why the forall is exposed explicitly. |
| page table | separate-verus-modes | complies | Executable API specifications are attached through verus_spec; separately located spec modules hold model definitions. |
| page table | use-chained-comparisons | complies | Range and alignment requirements use chained lower/upper comparisons. |
| page table | organize-proof-imports | complies | Arithmetic proof-only imports are local to proof blocks rather than scattered into executable logic. |
| page table | group-imports-by-crate | complies | vstd, vstd_extra and crate imports are grouped. This is a localized positive example, not a claim all imports need no cleanup. |
| page table | name-proof-roles | complies | pt_inv_implies_path_correct names the proposition established by the proof. |
| page table | inline-single-use-proof-helpers | complies | Single-use set-arithmetic proof explicitly localizes a spinoff prover obligation; retaining this isolation role is justified. |
| page table | defer-auxiliary-proof-functions | complies | Existing coverage helper documents a concrete trigger-instantiation purpose; proposed shared helpers PT-23/24 have multiple actual repeated sites. |
| page table | avoid-redundant-mode-markers | complies | Tracked ownership wrapper marks its struct mode once; it holds the resource tree rather than repeating per-field mode annotations. |
| page table | prefer-ghost-model-structs | complies | Legacy model uses ghost struct as appropriate for specification-only data (its removal is independently recommended by PT-02). |
| page table | right-size-spec-placement | complies | Implementation attaches child and entry specification modules from ostd/specs, separating substantial model logic. |
| page table | pair-exec-helpers-with-spec-models | complies | dfs_get_idx_range contract refers to named idx_range_spec; arithmetic execution and model are linked. |

## Per-file coverage ledger

Every listed file was read in full, including executable bodies, spec definitions, proof bodies, contracts, imports and module declarations. A file without a finding is recorded as reviewed, rather than treated as automatically removable. SHA-256 values bind this report to the inspected source. The requested `ostd/mm` path resolves to this repository's `ostd/src/mm`.

| File | Read interval | Lines | SHA-256 | Module conclusion |
| --- | --- | --- | --- | --- |
| [ostd/specs/arch/x86/mod.rs](ostd/specs/arch/x86/mod.rs) | 1–140 | 140 | `97383e12aec6f87ea5a3264e41131184f815435dee33e12bbfa8032e5ed5b187` | Read constants and broadcast lemmas; found repeated constant-instantiation calls; retained broadcast facts despite absent named callers. |
| [ostd/specs/mm/embedding/cursor.rs](ostd/specs/mm/embedding/cursor.rs) | 1–826 | 826 | `443046f0d9db6c8d09f559cb43e883eb6f012a325dae00e73490c68a08a9a1ff` | Full cursor-owner adapters and trusted contracts inspected; dormant adapters linked to incomplete dispatcher semantics (P21), not presumed safe deletion. |
| [ostd/specs/mm/embedding/frame.rs](ostd/specs/mm/embedding/frame.rs) | 1–274 | 274 | `3735b54fc26a9617d5f6ef98d2e6f954b4646b180bbfdeec825ee5c850da9cd7` | Frame authority and region preservation checked against total metadata domain; exact duplicate in-list clause and conditional domain redundancies (P04,P17,P18). |
| [ostd/specs/mm/embedding/io.rs](ostd/specs/mm/embedding/io.rs) | 1–355 | 355 | `64263a938a806636c8e44a64e332fbd5f658685c46ac5fa7ea0440e0248b0df0` | Read/write, limit/skip, and method adapter contracts read; ownership/read initialization retained; dispatcher connectivity reviewed. |
| [ostd/specs/mm/embedding/kvirt_store.rs](ostd/specs/mm/embedding/kvirt_store.rs) | 1–108 | 108 | `0fcd003836f36eeb8cec1e845c551294d7d14f7ade2d209825f12846fdea25d9` | Kernel-virtual ownership and region-store relation inspected; no equivalent simplification established. |
| [ostd/specs/mm/embedding/list_store.rs](ostd/specs/mm/embedding/list_store.rs) | 1–1133 | 1133 | `1cb3fb7d8c467ec813b0a439882c3ee8d79e5166b08c488f8115259781748966` | List and loose-frame models, all operation frames, and quantified preservation read; relation implies list invariant and frame-link relation implies in-list zero (P15,P16). |
| [ostd/specs/mm/embedding/mod.rs](ostd/specs/mm/embedding/mod.rs) | 1–3205 | 3205 | `95a49b903721e4018d014486bf9925d86b6e57561dc4a6f21ce73cf231cf788a` | All 3205 lines of stores, dispatcher, events, fresh IDs and embedding proof read; inactive/no-op transition concerns separated from optimization (P21). |
| [ostd/specs/mm/embedding/segment.rs](ostd/specs/mm/embedding/segment.rs) | 1–469 | 469 | `9e5fac3cf41646a738ef4a73b62cfe5eb01005d1d813cff8c10c40714b6af471` | Full segment adapters read; independent bounds/permission relations retained; membership redundancy conditional on total region model (P17). |
| [ostd/specs/mm/embedding/trace.rs](ostd/specs/mm/embedding/trace.rs) | 1–53 | 53 | `baa9785fddaad826059303ad89de657d502932051b4ee234af2ae5e6414c3e66` | Event/trace model fully read; no duplicate semantic abstraction established. |
| [ostd/specs/mm/embedding/unique.rs](ostd/specs/mm/embedding/unique.rs) | 1–232 | 232 | `0823d64e8b76847e65b84901871031c41a3288ea55fea7489ff5bb8f7bcd8755` | Full unique-owner transition contracts read; resource distinctions retained; membership condition evaluated under region invariant (P17). |
| [ostd/specs/mm/embedding/vm_space.rs](ostd/specs/mm/embedding/vm_space.rs) | 1–125 | 125 | `8fed9404885cfbf9042d271cafbc2c3030b4d195de0a7377ef1999f299c311ff` | Allocation contract, root-index model, and single-use adapter read; incompatible total-region removal isolated as correctness issue (P01,P19). |
| [ostd/specs/mm/frame/frame_specs.rs](ostd/specs/mm/frame/frame_specs.rs) | 1–202 | 202 | `8d7e606fb04f958c2f18100daa370c24662e7e70dae41b90129cd9d95a0601ae` | Frame pointer validity, OwnerOf and global owner relations read; used as canonical validity predicate for P14. |
| [ostd/specs/mm/frame/linked_list/linked_list_owners.rs](ostd/specs/mm/frame/linked_list/linked_list_owners.rs) | 1–1301 | 1301 | `9e448ad5daa391348993eef0f05d885e8c2159e8bcf48fdd799f8c4c9b644e03` | All 1301 lines of list/link owners and recursive/quantified bridge proofs read; canonical map_values and implication candidates (P12,P15,P16). |
| [ostd/specs/mm/frame/linked_list/linked_list_specs.rs](ostd/specs/mm/frame/linked_list/linked_list_specs.rs) | 1–213 | 213 | `ec1da7a0030bc153cc51caa7461e6ee2382e48bc56c2934de234621c1fe7c459` | Frame list and cursor transition models read; equal branches confirmed with actual executable/embedding callers (P13). |
| [ostd/specs/mm/frame/linked_list/mod.rs](ostd/specs/mm/frame/linked_list/mod.rs) | 1–4 | 4 | `8bee8a760bd6bbb690b2e5a5a278c52fd8a8f3a22c807676543ef370194fd379` | Module declarations fully read; no contracts or independent predicates. |
| [ostd/specs/mm/frame/mapping.rs](ostd/specs/mm/frame/mapping.rs) | 1–130 | 130 | `306775b7cbb98217411e54d7cf163b5652f24b05094b4f482c2031a70f6c4a69` | Address conversion arithmetic and all broadcast declarations read; duplicate lemma and trigger checked (P02). |
| [ostd/specs/mm/frame/meta_owners.rs](ostd/specs/mm/frame/meta_owners.rs) | 1–341 | 341 | `e4fcd876279bdf38424ddf69945b2553f74ee65a59fd640fe67720c5f2c5ac98` | Metadata state machine, typed metadata wiring and owner invariants read; REF_COUNT_UNUSED preserved as u64::MAX. |
| [ostd/specs/mm/frame/meta_region_owners.rs](ostd/specs/mm/frame/meta_region_owners.rs) | 1–168 | 168 | `4a09e15850bf2815cb5d10088bb04839ad05a85cc1c910413afc9ce71fd38dba` | Total parked-slot domain, slot ownership, contains, and valid-address lemmas read; authority for P01/P17/P18. |
| [ostd/specs/mm/frame/meta_specs.rs](ostd/specs/mm/frame/meta_specs.rs) | 1–189 | 189 | `992ef1ab860a67efc6eb870327b026db9adc2223b30c77430331eade6039b64d` | Slot pointer/type metadata and permission relations read; initialization/type invariants not treated as removable mere bounds. |
| [ostd/specs/mm/frame/mod.rs](ostd/specs/mm/frame/mod.rs) | 1–8 | 8 | `004265e3e30d343951b19a7cfd5e69622c2cfd4b7abb2f5b4de96922633d49b3` | All model-module declarations read; no contracts or independent predicates. |
| [ostd/specs/mm/frame/segment.rs](ostd/specs/mm/frame/segment.rs) | 1–63 | 63 | `9b8627a7bedd20bc225a360669004ddcb82b6f98cbfc62c9577c9d8cb71e7077` | Segment ownership, range and containment invariant read; meaningful contiguous-resource conditions retained. |
| [ostd/specs/mm/frame/unique.rs](ostd/specs/mm/frame/unique.rs) | 1–193 | 193 | `655e8bd0b8b4abadab439f6ee1042f2f93f4aa330b1732e4c1786c799210f668` | Unique frame validity and typed metadata ownership read; pointer-validity predicate matches canonical Frame predicate (P14). |
| [ostd/specs/mm/io.rs](ostd/specs/mm/io.rs) | 1–640 | 640 | `6dad7cb72d5f6aa63151985c3b30d2b71725ce26aa849810af7980f9e4a9e2c2` | All owner variants, byte initialization, split/advance and executable contracts read; duplicate projections and unused aliases found (P20,P23,P24). |
| [ostd/specs/mm/mod.rs](ostd/specs/mm/mod.rs) | 1–124 | 124 | `b67a295cedc3ddbe0bd31678c30ff1472e46698b864e29f339d5ec6978d0ee82` | Memory ranges and constants/models read; arithmetic and address conversion dependencies checked. |
| [ostd/specs/mm/page_table/cursor/cursor_fn_lemmas.rs](ostd/specs/mm/page_table/cursor/cursor_fn_lemmas.rs) | 1–313 | 313 | `ef330f35b2668490b5820f6548cdbc81e4e7426a5c21a64ac7c1481bc9725aaf` | Cursor compatibility and local executable/owner bridges read; retain arithmetic and panic-specific bounds; no independent additional deletion established. |
| [ostd/specs/mm/page_table/cursor/cursor_fn_specs.rs](ostd/specs/mm/page_table/cursor/cursor_fn_specs.rs) | 1–303 | 303 | `07e1393ffd934adf20fef016e5c58cbcd31fc895d1ba229be5606805f246a225` | Operation pre/post predicates read; resource and panic roles checked; no blanket merging of distinct operation semantics proposed. |
| [ostd/specs/mm/page_table/cursor/cursor_steps.rs](ostd/specs/mm/page_table/cursor/cursor_steps.rs) | 1–930 | 930 | `569b99b67a6888e87cb1fa949e640ba9803a24c22e49d968d198d396af44eaa0` | Termination and index arithmetic read; specialized equality duplicates reusable recursion (PT-14). |
| [ostd/specs/mm/page_table/cursor/invariant_preservation_lemmas.rs](ostd/specs/mm/page_table/cursor/invariant_preservation_lemmas.rs) | 1–544 | 544 | `237b8e0a57a405acb5bdf7f6082cf145fa65652e9d16af31efb3a2b40d6483d5` | Frame preservation and predicate lifting read; keep distinct region-change hypotheses and explicit triggers; stale unmap debt wording (PT-26). |
| [ostd/specs/mm/page_table/cursor/mapping_set_lemmas.rs](ostd/specs/mm/page_table/cursor/mapping_set_lemmas.rs) | 1–745 | 745 | `aa9af47dba0fd3f199f854f22bc8bccbe47d12851cd7687e7902aed8174e7844` | Tree-view mapping proofs read; set membership/emptiness and region transport roles retained; no speculative reveal removal endorsed. |
| [ostd/specs/mm/page_table/cursor/mod.rs](ostd/specs/mm/page_table/cursor/mod.rs) | 1–23 | 23 | `a56c1287a3a1b840ec69efe97f6794f821ec6c9acc22f009bcd20ce638147134` | Specification module wiring and proof-module separation read; no independent optimization. |
| [ostd/specs/mm/page_table/cursor/owners.rs](ostd/specs/mm/page_table/cursor/owners.rs) | 1–2082 | 2082 | `55f06db542d7e2c8368fa052ad71358adcf1f420ec7f6431fd6590d0c9eb87fc` | All ownership, continuation, ghost-view and VA lemmas read; canonical duplicates and unused/generic wrappers identified (PT-03/04/11/12/15/26). |
| [ostd/specs/mm/page_table/cursor/page_size_lemmas.rs](ostd/specs/mm/page_table/cursor/page_size_lemmas.rs) | 1–269 | 269 | `568aa4db055fa101e0995b594b014e8bbcc3b79746d2faf9ba8f11fb9b694242` | All arithmetic and split witness proofs read; witness can be reused at caller (PT-21), no weakening of overflow/cast bounds proposed. |
| [ostd/specs/mm/page_table/cursor/page_table_cursor_specs.rs](ostd/specs/mm/page_table/cursor/page_table_cursor_specs.rs) | 1–234 | 234 | `ee03350af3c614474c615b09a3532e4fedec240621ce54c55e76a99098437cad` | Complete manually expanded wf and intrinsic inv read; user-requested per-level checks retained. |
| [ostd/specs/mm/page_table/cursor/split_while_huge_lemmas.rs](ostd/specs/mm/page_table/cursor/split_while_huge_lemmas.rs) | 1–798 | 798 | `06e007490bdcb4fe51320304e039b80b970226bc29f1b18bb6ae2598ecf045e9` | All recursive split model proofs read; repeated covering-choice scaffolding candidate (PT-24); no measured solver-removal claims. |
| [ostd/specs/mm/page_table/cursor/tree_lemmas.rs](ostd/specs/mm/page_table/cursor/tree_lemmas.rs) | 1–216 | 216 | `8d80db796d3f4f9ea83583b46df7ef14bf9ebf51721aa0106abc47229946ec50` | Complete predicate lifting/frame proofs read; reuse continuation lift (PT-13). |
| [ostd/specs/mm/page_table/cursor/va_lemmas.rs](ostd/specs/mm/page_table/cursor/va_lemmas.rs) | 1–295 | 295 | `fb93079cccda552b029151b44f1e4ca1acf3feb66bf2f5d8979144c9b5cc279e` | All range/index/overflow lemmas read; generic page-size and locked-range constraints retained. |
| [ostd/specs/mm/page_table/mapping_set_lemmas.rs](ostd/specs/mm/page_table/mapping_set_lemmas.rs) | 1–185 | 185 | `a39518bf693a2a28fc93a068bd7113f7d78078e6d5070cfd8485fd922f59cbb9` | All common mapping-set arithmetic proofs read; no extension trait proposed; shared free functions retained. |
| [ostd/specs/mm/page_table/mod.rs](ostd/specs/mm/page_table/mod.rs) | 1–571 | 571 | `46edc5e70b050de647eb07188146e93146a526c62e4f9ef88802bca6914bd72d` | All tree construction, freshness and path rebasing definitions read; preserve allocated child path/level invariants. |
| [ostd/specs/mm/page_table/node/child.rs](ostd/specs/mm/page_table/node/child.rs) | 1–117 | 117 | `b699419ca970ce93e7a46e4c09ac0609c74e518c7173b86a26a0d970bf584b80` | Child/ChildRef wf, ownership and region predicates read; user-protected owner transformations retained. |
| [ostd/specs/mm/page_table/node/entry.rs](ostd/specs/mm/page_table/node/entry.rs) | 1–179 | 179 | `6ffa758032701536fc2029b77d7f0dc4ecc34aa8a36640bc08647e3440df3e3a` | Entry invariants, node matching and preservation predicates read; distinct parent resource/frame semantics retained. |
| [ostd/specs/mm/page_table/node/entry_owners.rs](ostd/specs/mm/page_table/node/entry_owners.rs) | 1–783 | 783 | `ec5379c572a89905615d14c81f260beb7af338070e6a53db505a2e02cf3ffdf7` | All variant/region/permission/PTE relations read; redundant paddr validity (PT-08), identity conversion wrappers retained. |
| [ostd/specs/mm/page_table/node/entry_view.rs](ostd/specs/mm/page_table/node/entry_view.rs) | 1–99 | 99 | `be094e223ed922ca14aa73b1f94e6374a1b4a1af9b2686d987990b41fabeb88d` | Entire legacy unused model family and references checked (PT-02). |
| [ostd/specs/mm/page_table/node/mod.rs](ostd/specs/mm/page_table/node/mod.rs) | 1–192 | 192 | `b76c3b5f9eeac43a500d9b6d45f5e74ca611697d48a2041c5075a1da73d8852b` | All Guards and tracked/Stored conversion specs read; centralized lock relation and exact-result cleanup (PT-25). |
| [ostd/specs/mm/page_table/node/owners.rs](ostd/specs/mm/page_table/node/owners.rs) | 1–360 | 360 | `56af9756db7a2ce66ccd3812fb5fb5dd318b61216351a9d0655267b9deb5b727` | All counter and node metadata/guard invariants read; counter/id/pointer duplicates and irrelevant helper parameter (PT-05/06/07/22). |
| [ostd/specs/mm/page_table/owners.rs](ostd/specs/mm/page_table/owners.rs) | 1–1892 | 1892 | `d2457987e27e72b4e0aaf1dbf190ca84f5134a353844e31689cfadcd967eb44b` | All recursive page-table invariants and view proofs read; derived path property and dead scope predicate (PT-09/10). |
| [ostd/specs/mm/page_table/vaddr_range_proofs.rs](ostd/specs/mm/page_table/vaddr_range_proofs.rs) | 1–170 | 170 | `02171421fc12d29e25144b0d64171f0dac210cf61945b304a5b0b70b358b5652` | All canonical-address and signed-range arithmetic read; offset assumptions retained; repeated requires-as-ensures are low-impact optional cleanup. |
| [ostd/specs/mm/page_table/view.rs](ostd/specs/mm/page_table/view.rs) | 1–98 | 98 | `5ee279cb58c0b8992929ed5d63c5630402c759a519ff0566ea1b3ce20fbf42d8` | Mapping and common mapping-set predicates read; existing slim Mapping invariant not re-reported; existing free functions reused in PT-04. |
| [ostd/specs/mm/tlb.rs](ostd/specs/mm/tlb.rs) | 1–124 | 124 | `6a869a0f62cf42636680726c43ed0ff4780dca109c0f619428cda01b25d50891` | TLB model and trusted operations read; unused lemma exactly repeats premise (P03); meaningful consistency condition retained. |
| [ostd/specs/mm/virt_mem.rs](ostd/specs/mm/virt_mem.rs) | 1–1295 | 1295 | `777b1ea8b4ed2b4c7de7a8d4eac2ee969fa54542cd4f541da9bafb4432d604f4` | All 1295 lines, including byte/mapping proofs and dormant GlobalMemView read; subset/complement direction and alias policy checked (P05,P06,P08-P10). |
| [ostd/specs/mm/vm_space.rs](ostd/specs/mm/vm_space.rs) | 1–762 | 762 | `9a5c10ae8aab812912885bbff1d7b37dd2ff8062f262712e401cb1a229ed7c34` | All owner lifecycle/view/reader/writer/query contracts read; Option relation, subset disjointness and dormant helpers checked (P07,P11,P22). |
| [ostd/specs/mod.rs](ostd/specs/mod.rs) | 1–18 | 18 | `d72364fe1e635fb566b3a4939a4f43660559aa6dcc723feb87721691e69a6c27` | Read module declarations and lint allowances; these declarations do not duplicate mathematical models. |
| [ostd/specs/sync/examples/abstract_lock_tla.rs](ostd/specs/sync/examples/abstract_lock_tla.rs) | 1–771 | 771 | `167403d1aba4506f1943c77e2a72a27301cbbc5abb8302d809472b0ad722aa44` | Read all temporal safety/liveness proofs; intentionally disabled study model. Proof cases are distinct; no bulk deletion based on missing callers. Local closure/filter repetition exists but abstraction would need proof-context evidence. |
| [ostd/specs/sync/examples/mod.rs](ostd/specs/sync/examples/mod.rs) | 1–5 | 5 | `6b06b65b84e3141ca5a10dca0e9f903696683c6480bd58b60ad4b1966cf8c6c0` | Read declarations; examples module is disabled by parent; lint covers lowercase example labels. |
| [ostd/specs/sync/examples/mutex_tla.rs](ostd/specs/sync/examples/mutex_tla.rs) | 1–387 | 387 | `ed91380e49eb381ca24b03f269b91ec7e2416ba41c9893bd6081c0419e10d678` | Read all manual Action transitions and liveness formulas; shares algorithm with state-machine example for comparison, not duplicate active kernel contracts. |
| [ostd/specs/sync/examples/mutex_verussync.rs](ostd/specs/sync/examples/mutex_verussync.rs) | 1–224 | 224 | `6cdf4c561372220b0ee4ccdcd1e3d60c411d0cacdd96ae581910803cc4c445b5` | Read every macro transition; count and queue length intentionally separate during enqueue two-step transitions, so cannot unify them. |
| [ostd/specs/sync/mod.rs](ostd/specs/sync/mod.rs) | 1–2 | 2 | `60be0381aa3c07c70bcf903ac650ae7c207a0373b153bcd4fb478e4ab9307a31` | Read active rcu declaration and commented examples declaration. |
| [ostd/specs/sync/rcu/mod.rs](ostd/specs/sync/rcu/mod.rs) | 1–4 | 4 | `0bbf104d191dedc36be6c34665842beeefd407375af99c4d192919835264cfb2` | Read IRC11 feature-gated root declaration. |
| [ostd/specs/sync/rcu/root.rs](ostd/specs/sync/rcu/root.rs) | 1–408 | 408 | `b3f59284f66b3e6b9334fc62cf36a3cd9391caebdce0b02694f760a5a4723330` | Read complete publication identity protocol, fresh/registered updates and regression proofs. Domain authority is linear; objects/publications/timestamps encode different identities and should remain separate. Repeated update proof body not blindly abstracted. |
| [ostd/specs/task/cpu_core.rs](ostd/specs/task/cpu_core.rs) | 1–300 | 300 | `77f6b3a51f0966370985bd3d1d2fa1517808e265fbcb4a0dc03a28a569887fe5` | Read full authority/points-to threading and regression proof; tracked tokens preserve ownership identity. No removal of smoke proof. |
| [ostd/specs/task/cpu_local.rs](ostd/specs/task/cpu_local.rs) | 1–287 | 287 | `60992f733812629cfd49ee1c66aff9c7d3ae9647144c0992ad4dd7981254c651` | Read full local authority split/update/return protocol; two unused convenience APIs flagged with repo-wide occurrence checks; regression proof retained. |
| [ostd/specs/task/mod.rs](ostd/specs/task/mod.rs) | 1–19 | 19 | `505cccea13acaf78f0047e1a284b7519e0ed447eaeefd47c198eae5d4fc48976` | Read atomic guard stub; consumer exists in VmSpace creation and trait-bound contexts. |
| [ostd/src/mm/dma/dma_coherent.rs](ostd/src/mm/dma/dma_coherent.rs) | 1–831 | 831 | `3a8b207b57feac60b18cd13d7c98a20db726d44ca6fdac8889692dbb43ac1729` | Read all contracts and implementation; duplicate kernel-view minting and dormant VmIoOnce hooks; trait-specific read/write requirements remain meaningful. |
| [ostd/src/mm/dma/dma_stream.rs](ostd/src/mm/dma/dma_stream.rs) | 1–1625 | 1625 | `bc62899999112eb245c25d5c4fa4fb158434ca66f86a77a584f917e19ce79988` | Read all stream/slice paths; duplicate view minting/assertions and vacuous inherited ensures; direction-specific requirements intentionally retained. |
| [ostd/src/mm/dma/mod.rs](ostd/src/mm/dma/mod.rs) | 1–222 | 222 | `69c5777cfb03f2917e560499889cf1653550bc499bbcfab347e50cf3e4fee42d` | Read mapping-set resource and runtime trust boundary; always-true address predicate adds no restriction. |
| [ostd/src/mm/dma/test.rs](ostd/src/mm/dma/test.rs) | 1–392 | 392 | `7fbbcbcad103d5a64acb55f862788903ed88cdeaefb5b2ec51a9c86016d95217` | Read all runtime DMA tests; no Verus contracts/spec helpers. Test behavior assertions are not redundant specification scaffolding. |
| [ostd/src/mm/frame/allocator.rs](ostd/src/mm/frame/allocator.rs) | 1–371 | 371 | `afeb083c392b21795047020b0f97612f79ae8adcacc6f3805fbfd263c018e895` | Read allocator implementation and commented upstream block; active allocation entry uses external_body without substantive model to reduce. |
| [ostd/src/mm/frame/frame_ref.rs](ostd/src/mm/frame/frame_ref.rs) | 1–231 | 231 | `1a029cfa0143c034f186945f218492b78b3f7e4d15538847769ab1138e46a105` | Read NonNullPtr/borrow plumbing; trait-mandated spec methods retained; exact dereference reference result is not blindly converted to value returns. |
| [ostd/src/mm/frame/linked_list.rs](ostd/src/mm/frame/linked_list.rs) | 1–1741 | 1741 | `423666022e803bb37c3b2ce094616c417dd8a0b7003f6b79315432a4e47b4442` | Read insertion/removal/cursor/drop proofs in full; duplicate membership quantifier; spinoff helper has documented quantifier-isolation reason and retained. |
| [ostd/src/mm/frame/meta.rs](ostd/src/mm/frame/meta.rs) | 1–1118 | 1118 | `e41139975bb291ee39386eedbbe84312589e12e4b9b99e33037734e67193c90e` | Read metadata slot/refcount/resource operations in full; duplicate external_body annotation; explicit ref-count states and payload lifetimes retain linear meaning. |
| [ostd/src/mm/frame/mod.rs](ostd/src/mm/frame/mod.rs) | 1–875 | 875 | `5626bfc6e6c948e24f6bc24c5d8ada549567ff5efeb27bba86010abf4614f2d5` | Read frame construction/clone/drop/borrow/conversion in full; duplicate ptr_inv precondition. REF_COUNT_UNUSED=u64MAX so >0 does not subsume !=UNUSED. |
| [ostd/src/mm/frame/segment.rs](ostd/src/mm/frame/segment.rs) | 1–1177 | 1177 | `355954ea95f4c00eb5abb086123339425d392e58624588f3652950d930800c16` | Read full construction/rollback/drop/slice/clone proofs; derivable affine address log, duplicate bound and exact size relation; tracked permissions remain linear. |
| [ostd/src/mm/frame/test.rs](ostd/src/mm/frame/test.rs) | 1–529 | 529 | `ae97308493f2b8bc2e8a89432b87f0e72ebe3379f31e6176b5a069361589f8ab` | Read all frame/list/segment/runtime tests; no Verus contracts or spec helper definitions. |
| [ostd/src/mm/frame/unique.rs](ostd/src/mm/frame/unique.rs) | 1–672 | 672 | `a134ec34ffef9a400ab0b8c454ef586fb51ca17d70887abb97d55dfc301088e1` | Read full unique ownership conversion/drop model; PhantomData tautology and unused erased owner argument. Region/representation ownership facts retained. |
| [ostd/src/mm/frame/untyped.rs](ostd/src/mm/frame/untyped.rs) | 1–243 | 243 | `042a1715f5d1256df598bcf250804061ea7580b406a457676f60f7850be5d88f` | Read segment reader/writer proofs and commented macro; current constructors already provide kernel views without DMA reminting. |
| [ostd/src/mm/heap/mod.rs](ostd/src/mm/heap/mod.rs) | 1–149 | 149 | `a73831a87b724511ecc45e41a299406f022cc898438e3eac8e1100e5bfc299dd` | Read disabled heap entry/runtime code; no Verus contract/model to reduce. |
| [ostd/src/mm/heap/slab.rs](ostd/src/mm/heap/slab.rs) | 1–132 | 132 | `5d5a695d691fbbb769f254a5f11b3656096f8c79a9accf21ffc0b81ecd086310` | Read slab runtime implementation; no Verus specification or proof helpers. |
| [ostd/src/mm/heap/slot.rs](ostd/src/mm/heap/slot.rs) | 1–155 | 155 | `60b5edf57923ceb1b2a3662ccf0fe46b02fe970121ecccab13a6502c30026609` | Read slot allocator runtime implementation; no Verus specification or proof helpers. |
| [ostd/src/mm/heap/slot_list.rs](ostd/src/mm/heap/slot_list.rs) | 1–91 | 91 | `e290012cf44022b115189c3bbbf8050fc33a85218623a53e5fb2d015d186610b` | Read slot linked runtime implementation; no Verus specification or proof helpers. |
| [ostd/src/mm/io.rs](ostd/src/mm/io.rs) | 1–2254 | 2254 | `27742c992662e928c7c11ad0d95de838f259963079cadcd8550a97431fd00292` | Read every constructor/memory operation/trait/macro; duplicate Result contracts and dead VmIoOnce gates; retained linear split/consume outputs and required layout obligations. |
| [ostd/src/mm/kspace/kvirt_area.rs](ostd/src/mm/kspace/kvirt_area.rs) | 1–988 | 988 | `2e22999a5daaf45b8b5ad78ae98a6af5f441f74b3dfbb097ff20794c90e57389` | Read full frame/untracked mappings, allocation and iterator proofs; duplicate arithmetic calls and implied overflow bound. |
| [ostd/src/mm/kspace/mod.rs](ostd/src/mm/kspace/mod.rs) | 1–659 | 659 | `5f54ba9e26b73ac1d42a5e01bb522c45ca78877853f49ae7d92450d972a962bb` | Read full kernel config encoding/decoding/permission proofs; tracked tag disjunction distinguishes raw MMIO and owned frame representations. |
| [ostd/src/mm/kspace/test.rs](ostd/src/mm/kspace/test.rs) | 1–105 | 105 | `a566e972d59eb539f28c0df44410789ad2c7f3827d46b05b706f2c3819aaa843` | Read all runtime KVirtArea tests; no Verus specifications or proof definitions. |
| [ostd/src/mm/mod.rs](ostd/src/mm/mod.rs) | 1–301 | 301 | `4c25fcaf83390471ea276d679dd345865a3da788cbc53f607cff0691a60b2215` | Read memory address/page-size traits and helpers; exact-result clauses eligible for returns; constants themselves remain runtime behavior. |
| [ostd/src/mm/page_prop.rs](ostd/src/mm/page_prop.rs) | 1–210 | 210 | `b7166f8377f4a404f25c9f14b67083ea6bc2dce9d499cf9deb59ae457818f7d0` | Read all bitflags/property definitions and contract bridges; dual-spec constructors already paired; tagged bits and available bits have distinct roles. |
| [ostd/src/mm/page_table/boot_pt.rs](ostd/src/mm/page_table/boot_pt.rs) | 1–338 | 338 | `d6d393e31040c6611a83c0fbf8ac1147e564bd024efbe48dfa4ae51c191696d5` | Entire boot implementation read; disabled parent module and runtime mapping/panic paths noted; no active spec simplification. |
| [ostd/src/mm/page_table/cursor/locking.rs](ostd/src/mm/page_table/cursor/locking.rs) | 1–876 | 876 | `4848968bec52ea93ca8610d1c0e94c4d6ee7b59d26923ef5647f54c704182393` | Entire locking traversal/DFS/spec contracts read; trust/admitted boundaries recognized; no claim these contracts are checked proofs. |
| [ostd/src/mm/page_table/cursor/mod.rs](ostd/src/mm/page_table/cursor/mod.rs) | 1–3872 | 3872 | `766259758996a1d7af24d9b50e0f810bc08d37e28e11d26f1a0207b40511789b` | All3872lines read, including traversal/map/query/take/protect and commented originals; contract, loop and repeated-body candidates PT-18/19/20/23/27; manually expanded wf unchanged. |
| [ostd/src/mm/page_table/mod.rs](ostd/src/mm/page_table/mod.rs) | 1–1869 | 1869 | `a9c5f596c3a29cbb03c23056a22606dcc78330f8dad38949f7b6920cb40b93b1` | All traits/configuration/allocation/API and load/store specs read; contradictory trusted constructor PT-01, duplicates PT-16 and exact-result API PT-25. |
| [ostd/src/mm/page_table/node/child.rs](ostd/src/mm/page_table/node/child.rs) | 1–217 | 217 | `44d7e9a86b2fb0284d758d3e9a3fda3fc23654c58f2cf32d3014e26578a2dc66` | All conversions and owner transitions read; no removal or change to protected into/from owner spec wrappers. |
| [ostd/src/mm/page_table/node/entry.rs](ostd/src/mm/page_table/node/entry.rs) | 1–2076 | 2076 | `e55701be9fbf6d91ee72cca630980e0f25d5ec630bf700e117c09f09076048b2` | All2076lines read, including PTE replacement/allocation/huge split/counter proofs; resource framing kept; duplicate slots clauses PT-17 and witness reuse PT-21. |
| [ostd/src/mm/page_table/node/mod.rs](ostd/src/mm/page_table/node/mod.rs) | 1–787 | 787 | `908c521e865a7befb8dd3be1f0cb81145e432d7e7d4c38b2ad3e2b8240f1c7e0` | Entire node metadata/destructor/lock/guard implementation read; trusted destructor not claimed verified; source exact result candidate PT-25. |
| [ostd/src/mm/page_table/test.rs](ostd/src/mm/page_table/test.rs) | 1–982 | 982 | `cecd34ce2d51df439c18d61e8e68eaf97e9ee95f3a55a89e9f9a815597fec49b` | All982lines read; ordinary ktest scenarios and legacy APIs are not proof contracts; no test rewrite or test-run claim. |
| [ostd/src/mm/test.rs](ostd/src/mm/test.rs) | 1–884 | 884 | `97d6cdd8c229ea9ca124c682f4eadc5f22db646d4bc7d28ae996a81c9e1e2832` | Read all runtime IO/VM-space tests; no Verus contracts/spec helpers. Runtime asserts retained. |
| [ostd/src/mm/tlb.rs](ostd/src/mm/tlb.rs) | 1–351 | 351 | `24e8a04767fc4be88e4ba0ee20e22d78c41a91b838fa6626eed40d2b7682eab9` | Read full TLB stub/trusted interface; model invariant and consistency are different facts; no speculative deletion of ownership/drop boundary. |
| [ostd/src/mm/vm_space.rs](ostd/src/mm/vm_space.rs) | 1–1857 | 1857 | `72f82340c1ea16bfc61ae93673350accd73e8a82c55cfe0495820aaad592e99b` | Read full VM construction, IO wrappers, cursor and unmap proof; repeated subtree disjoint/cardinality proof; wrapper contracts kept where public API shape is original. |

## Evidence and validation record

Coverage union: 95 distinct files, 55,680 lines; no missing or overlapping assignments. Source SHA-256 values matched the immutable snapshot at report generation. 74 distinct observations are indexed; P01 and PT-01 are merged as one issue. Observation count includes optional cleanup and model/API decisions and is not a count of independently proven defects.

Verification performed: **none**. This report itself is the only repository artifact created. For implementation, use `cargo dv focus --targets ostd -- --verify-only-module <module_path>` during iteration and the repository-required full `make` before submitting proof-sensitive changes. Preserve executable behavior and all existing meaningful resource/byte-preservation guarantees.
