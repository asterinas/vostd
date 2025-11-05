use std::ops::Range;

use vstd::prelude::*;

use common::mm::{Vaddr, PagingLevel, MAX_USERSPACE_VADDR};
use common::mm::page_table::{PageTableConfig, PagingConstsTrait, pte_index_spec};
use common::spec::{common::*, node_helper::self};

verus! {

pub open spec fn va_range_wf<C: PageTableConfig>(va: Range<Vaddr>) -> bool {
    &&& valid_va_range::<C>(va)
    &&& va.start < va.end < MAX_USERSPACE_VADDR
    &&& vaddr_is_aligned::<C>(va.start)
    &&& vaddr_is_aligned::<C>(va.end)
}

pub open spec fn va_range_get_guard_level_rec<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
) -> PagingLevel
    recommends
        va_range_wf::<C>(va),
        1 <= level <= C::NR_LEVELS_SPEC(),
    decreases level,
    when 1 <= level <= C::NR_LEVELS_SPEC()
{
    if level == 1 {
        1
    } else {
        let st = va.start;
        let en = (va.end - 1) as usize;

        if pte_index_spec::<C>(st, level) == pte_index_spec::<C>(en, level) {
            va_range_get_guard_level_rec::<C>(va, (level - 1) as PagingLevel)
        } else {
            level
        }
    }
}

pub open spec fn va_range_get_guard_level<C: PageTableConfig>(va: Range<Vaddr>) -> PagingLevel
    recommends
        va_range_wf::<C>(va),
{
    va_range_get_guard_level_rec::<C>(va, C::NR_LEVELS_SPEC())
}

pub proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= level <= C::NR_LEVELS_SPEC(),
        forall|l|
            level < l <= C::NR_LEVELS_SPEC() ==> pte_index_spec::<C>(va.start, l)
                == pte_index_spec::<C>((va.end - 1) as usize, l),
        level == 1 || pte_index_spec::<C>(va.start, level) != pte_index_spec::<C>(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level::<C>(va),
{
    lemma_va_range_get_guard_level_implied_by_offsets_equal_induction::<C>(
        va,
        level,
        C::NR_LEVELS_SPEC(),
    );
}

proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal_induction<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
    top_level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= level <= top_level <= C::NR_LEVELS_SPEC(),
        forall|l|
            level < l <= top_level ==> pte_index_spec::<C>(va.start, l) == pte_index_spec::<
                C,
            >((va.end - 1) as usize, l),
        level == 1 || pte_index_spec::<C>(va.start, level) != pte_index_spec::<C>(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level_rec::<C>(va, top_level),
    decreases top_level,
{
    if (top_level == 1) {
    } else {
        if pte_index_spec::<C>(va.start, top_level) == pte_index_spec::<C>(
            (va.end - 1) as usize,
            top_level,
        ) {
            lemma_va_range_get_guard_level_implied_by_offsets_equal_induction::<C>(
                va,
                level,
                (top_level - 1) as PagingLevel,
            );
        }
    }
}

pub proof fn lemma_va_range_get_guard_level_implies_offsets_equal<C: PageTableConfig>(
    va: Range<Vaddr>,
)
    requires
        va_range_wf::<C>(va),
    ensures
        forall|l: PagingLevel| #[trigger]
            va_range_get_guard_level::<C>(va) < l <= C::NR_LEVELS_SPEC() ==> pte_index_spec::<
                C,
            >(va.start, l) == pte_index_spec::<C>((va.end - 1) as usize, l),
        va_range_get_guard_level::<C>(va) == 1 || pte_index_spec::<C>(
            va.start,
            va_range_get_guard_level::<C>(va),
        ) != pte_index_spec::<C>((va.end - 1) as usize, va_range_get_guard_level::<C>(va)),
{
    C::lemma_consts_properties();
    lemma_va_range_get_guard_level_implies_offsets_equal_induction::<C>(va, C::NR_LEVELS_SPEC());
}

proof fn lemma_va_range_get_guard_level_implies_offsets_equal_induction<C: PageTableConfig>(
    va: Range<Vaddr>,
    top_level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= top_level <= C::NR_LEVELS_SPEC(),
    ensures
        forall|l: PagingLevel| #[trigger]
            va_range_get_guard_level_rec::<C>(va, top_level) < l <= top_level
                ==> pte_index_spec::<C>(va.start, l) == pte_index_spec::<C>(
                (va.end - 1) as usize,
                l,
            ),
        va_range_get_guard_level_rec::<C>(va, top_level) == 1 || pte_index_spec::<C>(
            va.start,
            va_range_get_guard_level_rec::<C>(va, top_level),
        ) != pte_index_spec::<C>(
            (va.end - 1) as usize,
            va_range_get_guard_level_rec::<C>(va, top_level),
        ),
    decreases top_level,
{
    if top_level == 1 {
    } else {
        if pte_index_spec::<C>(va.start, top_level) == pte_index_spec::<C>(
            (va.end - 1) as usize,
            top_level,
        ) {
            lemma_va_range_get_guard_level_implies_offsets_equal_induction::<C>(
                va,
                (top_level - 1) as PagingLevel,
            );
        }
    }
}

pub proof fn lemma_va_range_get_guard_level_rec<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= level <= C::NR_LEVELS_SPEC(),
    ensures
        1 <= va_range_get_guard_level_rec::<C>(va, level) <= level,
    decreases level,
{
    if level > 1 {
        let st = va.start;
        let en = (va.end - 1) as usize;
        if pte_index_spec::<C>(st, level) == pte_index_spec::<C>(en, level) {
            lemma_va_range_get_guard_level_rec::<C>(va, (level - 1) as PagingLevel);
        }
    }
}

pub proof fn lemma_va_range_get_guard_level<C: PageTableConfig>(va: Range<Vaddr>)
    requires
        va_range_wf::<C>(va),
    ensures
        1 <= va_range_get_guard_level::<C>(va) <= C::NR_LEVELS_SPEC(),
{
    C::lemma_consts_properties();
    lemma_va_range_get_guard_level_rec::<C>(va, C::NR_LEVELS_SPEC());
}

pub open spec fn va_range_get_tree_path<C: PageTableConfig>(va: Range<Vaddr>) -> Seq<NodeId>
    recommends
        va_range_wf::<C>(va),
{
    Seq::new(
        (C::NR_LEVELS_SPEC() + 1 - va_range_get_guard_level::<C>(va)) as nat,
        |i| va_level_to_nid::<C>(va.start, (C::NR_LEVELS_SPEC() - i) as PagingLevel),
    )
}

pub proof fn lemma_va_range_get_tree_path<C: PageTableConfig>(va: Range<Vaddr>)
    requires
        va_range_wf::<C>(va),
    ensures
        va_range_get_tree_path::<C>(va).all(|nid| node_helper::valid_nid::<C>(nid)),
        va_range_get_tree_path::<C>(va).len() == C::NR_LEVELS_SPEC() + 1
            - va_range_get_guard_level::<C>(va),
{
    lemma_va_range_get_guard_level::<C>(va);
    assert forall|i: int| 0 <= i < va_range_get_tree_path::<C>(va).len() implies {
        #[trigger] node_helper::valid_nid::<C>(va_range_get_tree_path::<C>(va)[i])
    } by {
        lemma_va_level_to_nid_valid::<C>(va.start, (C::NR_LEVELS_SPEC() - i) as PagingLevel);
    }
}

} // verus!
