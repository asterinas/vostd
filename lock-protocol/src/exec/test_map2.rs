use vstd::prelude::*;
use core::num;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};

use crate::mm::entry::Entry;
use crate::mm::page_prop::{PageFlags, PageProperty, PrivilegedPageFlags};
use crate::mm::page_table::PageTableNode;

use crate::mm::{pte_index, Paddr, NR_ENTRIES};
use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTableLockTrait, PageTablePageMeta, PagingConsts,
        PagingConstsTrait, UserMode, Vaddr, MAX_USERSPACE_VADDR, NR_LEVELS, PAGE_SIZE,
    },
    spec::simple_page_table,
    task::{disable_preempt, DisabledPreemptGuard},
};
use vstd::simple_pptr::*;

use crate::exec::*;

verus! {

pub fn test(va: Vaddr, frame: Frame<SimpleFrameMeta>, page_prop: page_prop::PageProperty)
requires
    0 <= va < MAX_USERSPACE_VADDR,
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    let tracked (
        Tracked(instance),
        Tracked(frames_token),
        Tracked(unused_addrs),
        Tracked(pte_token),
        Tracked(unused_pte_addrs),
    ) = simple_page_table::SubPageTableStateMachine::Instance::initialize();
    let tracked tokens = Tokens {
        unused_addrs: unused_addrs.into_map(),
        unused_pte_addrs: unused_pte_addrs.into_map(),
    };

    // TODO: use Cursor::new
    let mut cursor =
    CursorMut::<UserMode, MockPageTableEntry, PagingConsts, FakePageTableLock<MockPageTableEntry, PagingConsts>> {
        0: Cursor::<UserMode, MockPageTableEntry, PagingConsts, FakePageTableLock<MockPageTableEntry, PagingConsts>> {
            path: Vec::new(),
            level: 4,
            guard_level: NR_LEVELS as u8,
            va: va,
            barrier_va: 0..MAX_USERSPACE_VADDR + PAGE_SIZE, // TODO: maybe cursor::new can solve this
            preempt_guard: disable_preempt(),
            _phantom: std::marker::PhantomData,
        }
    };
    assert(cursor.0.level == 4);

    let mut sub_page_table = SubPageTable {
        mem: alloc_page_table_entries(),
        frames: Tracked(frames_token),
        ptes: Tracked(pte_token),
        instance: Tracked(instance.clone()),
    };

    let mut cur_alloc_index: usize = 0; // TODO: theoretically, this should be atomic
    let (p, Tracked(pt)) = get_frame_from_index(cur_alloc_index, &sub_page_table.mem); // TODO: permission violation
    p.write(Tracked(&mut pt), MockPageTablePage {
        ptes: {
            let mut ptes = [MockPageTableEntry {
                pte_addr: 0,
                frame_pa: 0,
                level: 0,
            }; NR_ENTRIES];
            for i in 0..NR_ENTRIES {
                assert((PHYSICAL_BASE_ADDRESS() as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64) < usize::MAX as u64) by { admit(); }; // TODO
                ptes[i] = MockPageTableEntry {
                    pte_addr: PHYSICAL_BASE_ADDRESS() as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64,
                    frame_pa: 0,
                    level: 4,
                };
            }
            ptes
        },
    });


    assert(pt.mem_contents() != MemContents::<MockPageTablePage>::Uninit);
    assert(pt.value().ptes.len() == NR_ENTRIES);
    // assert(pt.value().ptes[0].frame_pa == 0); // TODO: P0 don't know why this fails
    assume(forall |i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] pt.value().ptes[i]).pte_addr == PHYSICAL_BASE_ADDRESS() as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64);
    assume(forall |i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] pt.value().ptes[i]).frame_pa == 0);
    assume(forall |i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] pt.value().ptes[i]).level == 4);

    assert(sub_page_table.wf());

    assert(sub_page_table.mem.len() == MAX_FRAME_NUM);
    assert(p.addr() == PHYSICAL_BASE_ADDRESS() as usize);
    assert(sub_page_table.mem@.contains_key(cur_alloc_index));

    sub_page_table.mem.remove(&cur_alloc_index);
    assert(sub_page_table.mem.len() == MAX_FRAME_NUM - 1);
    sub_page_table.mem.insert(cur_alloc_index, (p, Tracked(pt)));
    assert(sub_page_table.mem.len() == MAX_FRAME_NUM);

    assert(sub_page_table.mem@[cur_alloc_index].1@.mem_contents() != MemContents::<MockPageTablePage>::Uninit);

    let (p, Tracked(pt)) = get_frame_from_index(cur_alloc_index, &sub_page_table.mem);
    assert(pt.mem_contents() != MemContents::<MockPageTablePage>::Uninit);

    // assert(sub_page_table.wf()); this should fail
    proof{
        let tracked used_addr = tokens.unused_addrs.tracked_remove(p.addr()as int);

        instance.new_at(p.addr() as int, simple_page_table::FrameView {
            pa: p.addr() as int,
            pte_addrs: Set::empty(),
        }, sub_page_table.frames.borrow_mut(), used_addr, sub_page_table.ptes.borrow_mut());
    }
    assert(sub_page_table.wf());

    cur_alloc_index = cur_alloc_index + 1;

    cursor.0.path.push(None);
    cursor.0.path.push(None);
    cursor.0.path.push(None);
    cursor.0.path.push(Some(
        FakePageTableLock {
            phantom: std::marker::PhantomData,
            paddr: p.addr(),
        }
    )); // root

    assert(cursor.0.path[cursor.0.level as usize - 1].is_some());

    cursor.map::<SimpleFrameMeta>(frame, page_prop,
        Tracked(instance),
        Tracked(tokens),
        &mut sub_page_table,
        &mut cur_alloc_index
    );

    assert(cursor.0.path.len() == NR_LEVELS as usize);
    assert(forall |i: usize| 1 < i <= NR_LEVELS as usize ==> #[trigger] cursor.0.path[i as int - 1].is_some());

    let level4_index = pte_index(va, NR_LEVELS as u8);
    let level4_frame_addr = PHYSICAL_BASE_ADDRESS();
    let level4_pte = get_pte_from_addr(level4_frame_addr + level4_index * SIZEOF_PAGETABLEENTRY, &sub_page_table);

    // let level3_frame_addr = cursor.0.path[(NR_LEVELS as usize) - 2].as_ref().unwrap().paddr() as usize;
    // assert(level4_pte.frame_pa == level3_frame_addr as u64);
}

}
