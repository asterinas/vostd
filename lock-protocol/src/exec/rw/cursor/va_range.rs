use std::ops::Range;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::super::common::*;

verus! {

pub open spec fn va_range_wf(va: Range<Vaddr>) -> bool {
    &&& valid_va_range(va)
    &&& va.start < va.end
    &&& vaddr_is_aligned(va.start)
    &&& vaddr_is_aligned(va.end)
}

pub open spec fn va_range_get_guard_level_rec(va: Range<Vaddr>, level: PagingLevel) -> PagingLevel
    recommends
        va_range_wf(va),
        1 <= level <= 4,
    decreases level,
    when 1 <= level <= 4
{
    if level == 1 {
        1
    } else {
        let st = va.start;
        let en = (va.end - 1) as usize;

        if va_level_to_offset(st, level) == va_level_to_offset(en, level) {
            va_range_get_guard_level_rec(va, (level - 1) as PagingLevel)
        } else {
            level
        }
    }
}

pub open spec fn va_range_get_guard_level(va: Range<Vaddr>) -> PagingLevel
    recommends
        va_range_wf(va),
{
    va_range_get_guard_level_rec(va, 4)
}

pub proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal(
    va: Range<Vaddr>,
    level: PagingLevel,
)
    requires
        va_range_wf(va),
        1 <= level <= 4,
        forall|l|
            level < l <= 4 ==> va_level_to_offset(va.start, l) == va_level_to_offset(
                (va.end - 1) as usize,
                l,
            ),
        level == 1 || va_level_to_offset(va.start, level) != va_level_to_offset(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level(va),
{
    lemma_va_range_get_guard_level_implied_by_offsets_equal_induction(va, level, 4);
}

proof fn lemma_va_range_get_guard_level_implied_by_offsets_equal_induction(
    va: Range<Vaddr>,
    level: PagingLevel,
    top_level: PagingLevel,
)
    requires
        va_range_wf(va),
        1 <= level <= top_level <= 4,
        forall|l|
            level < l <= top_level ==> va_level_to_offset(va.start, l) == va_level_to_offset(
                (va.end - 1) as usize,
                l,
            ),
        level == 1 || va_level_to_offset(va.start, level) != va_level_to_offset(
            (va.end - 1) as usize,
            level,
        ),
    ensures
        level == va_range_get_guard_level_rec(va, top_level),
    decreases top_level,
{
    if (top_level == 1) {
    } else {
        if va_level_to_offset(va.start, top_level) == va_level_to_offset(
            (va.end - 1) as usize,
            top_level,
        ) {
            lemma_va_range_get_guard_level_implied_by_offsets_equal_induction(
                va,
                level,
                (top_level - 1) as PagingLevel,
            );
        }
    }
}

pub proof fn lemma_va_range_get_guard_level_implies_offsets_equal(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        forall|l: PagingLevel| #[trigger]
            va_range_get_guard_level(va) < l <= 4 ==> va_level_to_offset(va.start, l)
                == va_level_to_offset((va.end - 1) as usize, l),
        va_range_get_guard_level(va) == 1 || va_level_to_offset(
            va.start,
            va_range_get_guard_level(va),
        ) != va_level_to_offset((va.end - 1) as usize, va_range_get_guard_level(va)),
{
    lemma_va_range_get_guard_level_implies_offsets_equal_induction(va, 4);
}

proof fn lemma_va_range_get_guard_level_implies_offsets_equal_induction(
    va: Range<Vaddr>,
    top_level: PagingLevel,
)
    requires
        va_range_wf(va),
        1 <= top_level <= 4,
    ensures
        forall|l: PagingLevel| #[trigger]
            va_range_get_guard_level_rec(va, top_level) < l <= top_level ==> va_level_to_offset(
                va.start,
                l,
            ) == va_level_to_offset((va.end - 1) as usize, l),
        va_range_get_guard_level_rec(va, top_level) == 1 || va_level_to_offset(
            va.start,
            va_range_get_guard_level_rec(va, top_level),
        ) != va_level_to_offset((va.end - 1) as usize, va_range_get_guard_level_rec(va, top_level)),
    decreases top_level,
{
    if top_level == 1 {
    } else {
        if va_level_to_offset(va.start, top_level) == va_level_to_offset(
            (va.end - 1) as usize,
            top_level,
        ) {
            lemma_va_range_get_guard_level_implies_offsets_equal_induction(
                va,
                (top_level - 1) as PagingLevel,
            );
        }
    }
}

pub proof fn lemma_va_range_get_guard_level_rec(va: Range<Vaddr>, level: PagingLevel)
    requires
        va_range_wf(va),
        1 <= level <= 4,
    ensures
        1 <= va_range_get_guard_level_rec(va, level) <= level,
    decreases level,
{
    if level > 1 {
        let st = va.start;
        let en = (va.end - 1) as usize;
        if va_level_to_offset(st, level) == va_level_to_offset(en, level) {
            lemma_va_range_get_guard_level_rec(va, (level - 1) as PagingLevel);
        }
    }
}

pub proof fn lemma_va_range_get_guard_level(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        1 <= va_range_get_guard_level(va) <= 4,
{
    lemma_va_range_get_guard_level_rec(va, 4);
}

pub open spec fn va_range_get_tree_path(va: Range<Vaddr>) -> Seq<NodeId>
    recommends
        va_range_wf(va),
{
    Seq::new(
        (5 - va_range_get_guard_level(va)) as nat,
        |i| va_level_to_nid(va.start, (4 - i) as PagingLevel),
    )
}

pub proof fn lemma_va_range_get_tree_path(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        va_range_get_tree_path(va).all(|nid| NodeHelper::valid_nid(nid)),
        va_range_get_tree_path(va).len() == 5 - va_range_get_guard_level(va),
{
    lemma_va_range_get_guard_level(va);
    assert forall|i: int|
        0 <= i < va_range_get_tree_path(va).len() implies #[trigger] NodeHelper::valid_nid(
        va_range_get_tree_path(va)[i],
    ) by {
        lemma_va_level_to_nid_valid(va.start, (4 - i) as PagingLevel);
    }
}

} // verus!
