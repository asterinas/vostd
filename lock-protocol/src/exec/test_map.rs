use vstd::prelude::*;
use core::{num, ops::Range};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};

use crate::mm::entry::Entry;
use crate::mm::page_prop::{PageFlags, PageProperty, PrivilegedPageFlags};
use crate::mm::page_table::PageTableNode;

use crate::mm::{pte_index, Paddr, PageTableGuard, NR_ENTRIES};
use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTablePageMeta, PagingConsts, PagingConstsTrait,
        Vaddr, MAX_USERSPACE_VADDR, NR_LEVELS, PAGE_SIZE, PageTableConfig, PagingLevel,
        frame::allocator::{alloc_page_table, AllocatorModel},
    },
    spec::sub_page_table,
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

    fn item_into_raw(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        (item.paddr, item.level, item.prop)
    }

    unsafe fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item {
        TestPtItem {
            paddr,
            level,
            prop,
        }
    }
}

#[derive(Copy, Clone)]
struct TestPtItem {
    paddr: Paddr,
    level: PagingLevel,
    prop: PageProperty,
}

pub fn test(va: Vaddr, frame: Frame, page_prop: page_prop::PageProperty)
requires
    0 <= va < MAX_USERSPACE_VADDR,
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;

    let tracked mut alloc_model = AllocatorModel { allocated_addrs: Set::empty() };

    let (p, Tracked(pt)) = alloc_page_table(Tracked(&mut alloc_model));
    let f = exec::create_new_frame(PHYSICAL_BASE_ADDRESS(), 4);
    assert(f.ptes[0].frame_pa == 0 as u64);
    p.write(Tracked(&mut pt), f);

    assert(pt.mem_contents() != MemContents::<MockPageTablePage>::Uninit);
    assert(pt.value().ptes.len() == NR_ENTRIES);
    assert(pt.value().ptes == f.ptes);
    assert(pt.value().ptes[0].frame_pa == 0 as u64);

    let tracked (
        Tracked(instance),
        Tracked(frame_tokens),
        Tracked(i_pte_tokens),
        Tracked(pte_tokens),
    ) = sub_page_table::SubPageTableStateMachine::Instance::initialize(crate::spec::sub_page_table::FrameView {
        pa: p.addr() as int,
        ancestor_chain: Map::empty(),
        level: 3, // To test a sub-tree rooted at level 3
    });

    let mut sub_page_table = SubPageTable {
        perms: HashMap::new(),
        frames: Tracked(frame_tokens),
        i_ptes: Tracked(i_pte_tokens),
        ptes: Tracked(pte_tokens),
        instance: Tracked(instance.clone()),
    };

    // assert(sub_page_table.wf());
    assume(sub_page_table.wf()); // FIXME!

    // TODO: use Cursor::new
    let mut cursor =
    CursorMut::<TestPtConfig> {
        0: Cursor::<TestPtConfig> {
            path: Vec::new(),
            level: 3,
            guard_level: NR_LEVELS as u8,
            va: va,
            barrier_va: 0..MAX_USERSPACE_VADDR + PAGE_SIZE(), // TODO: maybe cursor::new can solve this
            preempt_guard: disable_preempt(),
            _phantom: std::marker::PhantomData,
        }
    };
    assert(cursor.0.level == 3);

    cursor.0.path.push(None);
    cursor.0.path.push(None);
    cursor.0.path.push(Some(
        PageTableGuard::<TestPtConfig> {
            phantom: std::marker::PhantomData,
            level: 3,
            paddr: p.addr(),
        }
    )); // root

    // assert(cursor.0.path_wf(&sub_page_table));
    assume(cursor.0.path_wf(&sub_page_table)); // FIXME!

    cursor.map(frame, page_prop,
        &mut sub_page_table,
        Tracked(&mut alloc_model)
    );

    assert(sub_page_table.wf());

    assert(cursor.0.path.len() == NR_LEVELS as usize);
    assert(forall |i: usize| 1 < i <= NR_LEVELS as usize ==> #[trigger] cursor.0.path[i as int - 1].is_some());

    let level4_index = pte_index::<PagingConsts>(va, NR_LEVELS as u8);
    let level4_frame_addr = PHYSICAL_BASE_ADDRESS();
    let level4_pte = get_pte_from_addr(level4_frame_addr + level4_index * SIZEOF_PAGETABLEENTRY, &sub_page_table);

    // let level3_frame_addr = cursor.0.path[(NR_LEVELS as usize) - 2].as_ref().unwrap().paddr() as usize;
    // assert(level4_pte.frame_pa == level3_frame_addr as u64);
}

}
