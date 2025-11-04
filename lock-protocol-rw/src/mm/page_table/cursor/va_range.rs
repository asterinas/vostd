use std::ops::Range;

use vstd::prelude::*;

use common::mm::{Vaddr, PagingLevel};
use common::mm::page_table::PageTableConfig;
use common::spec::{common::*, node_helper::self};

verus! {

pub open spec fn va_range_wf<C: PageTableConfig>(va: Range<Vaddr>) -> bool {
    &&& valid_va_range::<C>(va)
    &&& va.start < va.end
    &&& vaddr_is_aligned::<C>(va.start)
    &&& vaddr_is_aligned::<C>(va.end)
}

pub open spec fn va_range_get_guard_level_rec<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
) -> PagingLevel
    recommends
        va_range_wf::<C>(va),
        1 <= level <= 4,
    decreases level,
    when 1 <= level <= 4
{
    if level == 1 {
        1
    } else {
        let st = va.start;
        let en = (va.end - 1) as usize;

        if va_level_to_offset::<C>(st, level) == va_level_to_offset::<C>(en, level) {
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
    va_range_get_guard_level_rec::<C>(va, 4)
}

pub proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= level <= 4,
        forall|l|
            level < l <= 4 ==> va_level_to_offset::<C>(va.start, l) == va_level_to_offset::<C>(
                (va.end - 1) as usize,
                l,
            ),
        level == 1 || va_level_to_offset::<C>(va.start, level) != va_level_to_offset::<C>(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level::<C>(va),
{
    lemma_va_range_get_guard_level_implied_by_offsets_equal_induction::<C>(va, level, 4);
}

proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal_induction<C: PageTableConfig>(
    va: Range<Vaddr>,
    level: PagingLevel,
    top_level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= level <= top_level <= 4,
        forall|l|
            level < l <= top_level ==> va_level_to_offset::<C>(va.start, l) == va_level_to_offset::<
                C,
            >((va.end - 1) as usize, l),
        level == 1 || va_level_to_offset::<C>(va.start, level) != va_level_to_offset::<C>(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level_rec::<C>(va, top_level),
    decreases top_level,
{
    if (top_level == 1) {
    } else {
        if va_level_to_offset::<C>(va.start, top_level) == va_level_to_offset::<C>(
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
            va_range_get_guard_level::<C>(va) < l <= 4 ==> va_level_to_offset::<C>(va.start, l)
                == va_level_to_offset::<C>((va.end - 1) as usize, l),
        va_range_get_guard_level::<C>(va) == 1 || va_level_to_offset::<C>(
            va.start,
            va_range_get_guard_level::<C>(va),
        ) != va_level_to_offset::<C>((va.end - 1) as usize, va_range_get_guard_level::<C>(va)),
{
    lemma_va_range_get_guard_level_implies_offsets_equal_induction::<C>(va, 4);
}

proof fn lemma_va_range_get_guard_level_implies_offsets_equal_induction<C: PageTableConfig>(
    va: Range<Vaddr>,
    top_level: PagingLevel,
)
    requires
        va_range_wf::<C>(va),
        1 <= top_level <= 4,
    ensures
        forall|l: PagingLevel| #[trigger]
            va_range_get_guard_level_rec::<C>(va, top_level) < l <= top_level
                ==> va_level_to_offset::<C>(va.start, l) == va_level_to_offset::<C>(
                (va.end - 1) as usize,
                l,
            ),
        va_range_get_guard_level_rec::<C>(va, top_level) == 1 || va_level_to_offset::<C>(
            va.start,
            va_range_get_guard_level_rec::<C>(va, top_level),
        ) != va_level_to_offset::<C>(
            (va.end - 1) as usize,
            va_range_get_guard_level_rec::<C>(va, top_level),
        ),
    decreases top_level,
{
    if top_level == 1 {
    } else {
        if va_level_to_offset::<C>(va.start, top_level) == va_level_to_offset::<C>(
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
        1 <= level <= 4,
    ensures
        1 <= va_range_get_guard_level_rec::<C>(va, level) <= level,
    decreases level,
{
    if level > 1 {
        let st = va.start;
        let en = (va.end - 1) as usize;
        if va_level_to_offset::<C>(st, level) == va_level_to_offset::<C>(en, level) {
            lemma_va_range_get_guard_level_rec::<C>(va, (level - 1) as PagingLevel);
        }
    }
}

pub proof fn lemma_va_range_get_guard_level<C: PageTableConfig>(va: Range<Vaddr>)
    requires
        va_range_wf::<C>(va),
    ensures
        1 <= va_range_get_guard_level::<C>(va) <= 4,
{
    lemma_va_range_get_guard_level_rec::<C>(va, 4);
}

pub open spec fn va_range_get_tree_path<C: PageTableConfig>(va: Range<Vaddr>) -> Seq<NodeId>
    recommends
        va_range_wf::<C>(va),
{
    Seq::new(
        (5 - va_range_get_guard_level::<C>(va)) as nat,
        |i| va_level_to_nid::<C>(va.start, (4 - i) as PagingLevel),
    )
}

pub proof fn lemma_va_range_get_tree_path<C: PageTableConfig>(va: Range<Vaddr>)
    requires
        va_range_wf::<C>(va),
    ensures
        va_range_get_tree_path::<C>(va).all(|nid| node_helper::valid_nid::<C>(nid)),
        va_range_get_tree_path::<C>(va).len() == 5 - va_range_get_guard_level::<C>(va),
{
    lemma_va_range_get_guard_level::<C>(va);
    assert forall|i: int| 0 <= i < va_range_get_tree_path::<C>(va).len() implies {
        #[trigger] node_helper::valid_nid::<C>(va_range_get_tree_path::<C>(va)[i])
    } by {
        lemma_va_level_to_nid_valid::<C>(va.start, (4 - i) as PagingLevel);
    }
}

} // verus!
