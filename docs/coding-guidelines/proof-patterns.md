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
