// SPDX-License-Identifier: MPL-2.0
//! Abstract models for ISA IRQ override selection, collection, and empty-list fallback.
use vstd::prelude::*;

verus! {

pub(crate) type IsaOverrideMapping = (u8, u32);

/// A decoded MADT override's bus, source and target, or a different entry kind.
pub(crate) type MadtOverrideEntry = Option<(u8, u8, u32)>;

/// The first override for an ISA source wins; an absent source maps to itself.
pub(crate) open spec fn isa_mapping_correct(
    overrides: Seq<IsaOverrideMapping>,
    isa: u8,
    gsi: u32,
) -> bool {
    &&& (forall|i: int| 0 <= i < overrides.len() ==> #[trigger] overrides[i].0 != isa) ==> gsi
        == isa as u32
    &&& (exists|i: int| 0 <= i < overrides.len() && #[trigger] overrides[i].0 == isa) ==> (exists|
        i: int,
    |
        0 <= i < overrides.len() && #[trigger] overrides[i].0 == isa && (forall|j: int|
            0 <= j < i ==> #[trigger] overrides[j].0 != isa) && gsi == overrides[i].1)
}

/// Retain the source and target of an ISA interrupt-source override.
pub(crate) open spec fn isa_override_entry(entry: MadtOverrideEntry) -> Option<IsaOverrideMapping> {
    match entry {
        Some((bus, source, target)) if bus == 0 => Some((source, target)),
        _ => None,
    }
}

/// Collect ISA overrides in MADT traversal order, preserving duplicates.
pub(crate) open spec fn collect_isa_overrides(entries: Seq<MadtOverrideEntry>) -> Seq<
    IsaOverrideMapping,
> {
    entries.filter_map(|entry: MadtOverrideEntry| isa_override_entry(entry))
}

/// Insert the PIT override only if the whole collected list is empty.
pub(crate) open spec fn isa_overrides_with_fallback(overrides: Seq<IsaOverrideMapping>) -> Seq<
    IsaOverrideMapping,
> {
    if overrides.len() == 0 {
        seq![(0u8, 2u32)]
    } else {
        overrides
    }
}

/// Processing one more entry appends exactly its ISA mapping, if it has one.
pub(crate) proof fn lemma_collect_isa_override_push(
    entries: Seq<MadtOverrideEntry>,
    entry: MadtOverrideEntry,
)
    ensures
        collect_isa_overrides(entries.push(entry)) == match isa_override_entry(entry) {
            Some(mapping) => collect_isa_overrides(entries).push(mapping),
            None => collect_isa_overrides(entries),
        },
{
    let next = entries.push(entry);
    assert(next[..entries.len()] == entries);
    next.lemma_filter_map_take_succ(
        |e: MadtOverrideEntry| isa_override_entry(e),
        entries.len() as int,
    );
}

} // verus!
