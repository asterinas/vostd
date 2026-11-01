# VOSTD Proof Patterns

These examples record proof shapes that recur in VOSTD. They support the coding
guidelines but are not mandatory project-wide rules. Prefer a simpler local
proof when one is available, and re-check each pattern against the active Verus
and `vstd` versions before reusing it.

## Recursive finite set models

The page-table owner model builds mapping sets from finite recursive unions. The
recursive definition is paired with two directions of bridge reasoning:

- An elimination lemma turns membership in the combined set into a structural
  witness identifying a child that contains the element.
- An introduction lemma turns membership in a selected child into membership in
  the combined set.

Call the elimination lemma before choosing a witness, and call the introduction
lemma when lifting a child's fact into the parent. Keep both lemmas with the
model so callers do not unfold the recursive representation independently.

See [`CursorContinuation::lemma_view_mappings_contains`](../../ostd/specs/mm/page_table/cursor/owners.rs#L376)
and [`CursorContinuation::lemma_view_mappings_intro`](../../ostd/specs/mm/page_table/cursor/owners.rs#L412).

## Set replacement equalities

For equalities that combine difference and union, such as replacing one
subtree's mapping set with another, prove extensional equality by showing both
membership directions. Within each direction, split on membership in the added
set and use the model's introduction and elimination lemmas to move between the
combined set and its structural components.

Use contradiction when a subset relation implies membership in a set already
known not to contain the element. Keep the proof at element level instead of
adding a project-wide axiom for the whole set expression.

See [`view_mappings_replace_lowest`](../../ostd/specs/mm/page_table/cursor/mapping_set_lemmas.rs#L557).

## Unmodeled representation mappings

When a value and its external representation — raw bytes is the
common layout, hardware-structure headers another — need a spec
bridge, but the representation's layout is not modeled (endianness,
padding, domain rules), do not pretend the conversion is definable or
provable in both directions. Build the model from three parts:

- One **uninterpreted** spec function is the mapping itself —
  `pub uninterp spec fn pod_bytes<T>(val: T) -> Seq<u8>;` —
  with no body, so nothing claims more than the
  unmodeled layout permits.
- The decoder is the `choose` of its preimage, defined against a
  generic model helper rather than a type- or trait-specific
  wrapper:

  ```rust
  pub open spec fn decode_pod<T>(bytes: Seq<u8>) -> T {
      choose|val: T| pod_bytes::<T>(val) == bytes
  }
  ```

  A `choose` definition is total (arbitrary when no preimage
  exists), so callers obtain the existence fact from a checked
  conversion rather than from the decoder itself. Defining the
  decoder in the model's vocabulary keeps the uninterpreted leaf
  the only extra function and avoids wrapper → trait → wrapper
  dependency cycles.
- Nothing can prove an uninterpreted function injective, so
  byte-level equality alone never recovers the value. Contracts
  whose callers need the *value* — not the representation —
  pin the value identity directly at the boundary
  (`returns from_bytes_spec::<Self>(bytes@)`,
  `*final(self) == decode_pod::<Self>(final(r)@)` in the Pod
  case), instead of relying on `repr(val) == bytes` to imply an
  equality of values. Keep `external_body` on the minimal
  primitives the composition is proved against — the copying
  body of `from_bytes` verifies against them.

See [`pod_bytes`](../../ostd/libs/ostd-pod/src/lib.rs#L95), PR
[#789](https://github.com/asterinas/vostd/pull/789#issuecomment-5862940573),
[#789](https://github.com/asterinas/vostd/pull/789#discussion_r4129275716),
[#789](https://github.com/asterinas/vostd/pull/789#discussion_r4129277023),
[#789](https://github.com/asterinas/vostd/pull/789#discussion_r4130560586), and
[#789](https://github.com/asterinas/vostd/pull/789#discussion_r4131142127).
