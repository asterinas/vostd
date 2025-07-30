use vstd::prelude::*;
use core::{num, ops::Range};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};

use crate::mm::entry::Entry;
use crate::mm::page_prop::{PageFlags, PageProperty, PrivilegedPageFlags};
use crate::mm::page_table::PageTableNode;

use crate::mm::vm_space::UntypedFrameMeta;
use crate::mm::{page_size, page_size_spec, pte_index, Paddr, PageTableGuard, NR_ENTRIES};
use crate::task::preempt;
use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTablePageMeta, PagingConsts, PagingConstsTrait,
        Vaddr, MAX_USERSPACE_VADDR, NR_LEVELS, PAGE_SIZE, PageTableConfig, PagingLevel,
        frame::allocator::AllocatorModel,
    },
    spec::sub_pt::{
        state_machine::{SubPageTableStateMachine, FrameView},
        SubPageTable,
    },
    task::{disable_preempt, DisabledPreemptGuard},
};
use vstd::simple_pptr::*;

use crate::exec::*;

verus! {

struct TestPtConfig;

unsafe impl PageTableConfig for TestPtConfig {
    type C = PagingConsts;
    type E = MockPageTableEntry;

    fn TOP_LEVEL_INDEX_RANGE() -> Range<usize> {
        0..256
    }

    open spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize> {
        0..256
    }

    fn TOP_LEVEL_CAN_UNMAP() -> bool {
        true
    }

    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool {
        true
    }

    type Item = TestPtItem;

    fn item_into_raw(item: Self::Item) -> (res: (Paddr, PagingLevel, PageProperty))
        ensures
            res == (item.paddr, item.level, item.prop),
    {
        (item.paddr, item.level, item.prop)
    }

    open spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        (item.paddr, item.level, item.prop)
    }

    unsafe fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty, Tracked(alloc_model): Tracked<&AllocatorModel<crate::mm::vm_space::UntypedFrameMeta>>) -> (res: Self::Item)
        ensures
            Self::item_into_raw_spec(res) == (paddr, level, prop),
    {
        TestPtItem {
            paddr,
            level,
            prop,
        }
    }
}

#[derive(Copy, Clone)]
pub struct TestPtItem {
    pub paddr: Paddr,
    pub level: PagingLevel,
    pub prop: PageProperty,
}

pub const ONE_GIG_VA: Vaddr = 0x40000000;

pub fn test(va: Vaddr, page_prop: page_prop::PageProperty)
requires
    0 <= va,
    va + page_size::<TestPtConfig>(1) <= ONE_GIG_VA,
    va % page_size::<TestPtConfig>(1) == 0,
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;

    let tracked mut alloc_model = AllocatorModel { meta_map: Map::tracked_empty() };

    let (p, Tracked(pt)) = alloc_page_table(3, Tracked(&mut alloc_model));

    assert(pt.mem_contents() != MemContents::<MockPageTablePage>::Uninit);
    assert(pt.value().ptes.len() == NR_ENTRIES);
    assert(pt.value().ptes[0].frame_pa == 0 as u64);

    let preempt_guard = disable_preempt();

    assert(0int % page_size_spec::<PagingConsts>(4) as int == 0) by { admit() };

    let ghost root = FrameView {
        map_va: 0,
        pa: p.start_paddr() as int,
        ancestor_chain: Map::empty(),
        level: 3, // To test a sub-tree rooted at level 3
        phantom: std::marker::PhantomData,
    };

    let tracked (
        Tracked(instance),
        Tracked(frame_tokens),
        Tracked(i_pte_tokens),
        Tracked(pte_tokens),
    ) = SubPageTableStateMachine::Instance::initialize(root);

    let tracked mut sub_page_table = SubPageTable {
        alloc_model,
        perms: {
            let tracked mut map = Map::tracked_empty();
            map.tracked_insert(p.start_paddr(), pt);
            map
        },
        root: Ghost(root),
        frames: frame_tokens,
        i_ptes: i_pte_tokens,
        ptes: pte_tokens,
        instance: instance.clone(),
    };

    assert(sub_page_table.wf());

    // TODO: use Cursor::new
    let mut cursor = {
        let path = [
            None, // level 1
            None, // level 2
            Some(p.borrow(Tracked(&sub_page_table.alloc_model)).make_guard_unchecked(&preempt_guard, Ghost(0))), // root
            None, // level 4
        ];
        CursorMut::<TestPtConfig> {
            0: Cursor::<TestPtConfig> {
                path,
                level: 3,
                guard_level: 3,
                va: va,
                barrier_va: 0..ONE_GIG_VA,
                preempt_guard: &preempt_guard,
                _phantom: std::marker::PhantomData,
            }
        }
    };

    assert(cursor.0.wf(&sub_page_table));

    let (mapped_frame_meta_ptr, Tracked(points_to)) = PPtr::new(UntypedFrameMeta);
    let tracked mut alloc_model = AllocatorModel::<UntypedFrameMeta> { meta_map:{
            let tracked mut map = Map::tracked_empty();
            map.tracked_insert(0, points_to);
            map
        }};
    let item = unsafe { TestPtConfig::item_from_raw(0, 1, page_prop, Tracked(&alloc_model)) };
    assert(TestPtConfig::item_into_raw_spec(item).1 == 1);
    assert(va + page_size::<TestPtConfig>(1) <= ONE_GIG_VA);
    cursor.map(
        item,
        Tracked(&mut sub_page_table),
    );

    assert(cursor.0.wf(&sub_page_table));
}

}
