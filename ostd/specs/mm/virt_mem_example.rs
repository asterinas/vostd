use vstd::prelude::*;

use vstd::set::*;
use vstd::seq::*;
use vstd::map_lib;

use vstd_extra::ownership::*;

use super::*;
use crate::mm::{PagingLevel, PagingConstsTrait};
use crate::mm::vm_space::*;
use crate::specs::mm::page_table::{CursorOwner, Guards, EntryOwner};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::task::InAtomicMode;
use crate::mm::page_prop::PageProperty;
use crate::mm::frame::untyped::UFrame;
use crate::mm::page_table::{page_size, PageTableConfig};

verus! {

pub fn read_example(Tracked(gm): Tracked<&mut GlobalMemView>, va: Vaddr, pa: Paddr, mapping: Mapping)
    requires
        old(gm).inv(),
        old(gm).tlb_mappings.contains(mapping),
        mapping.va_range.start == va,
        mapping.pa_range.start == pa,
        mapping.page_size == 4096,
        old(gm).memory[pa].contents[0] is Init,
        old(gm).memory[pa].contents[0].value() == 42,
{
    let virt_ptr = VirtPtr::new(va, 16);

    assert(mapping.inv());

    let tracked Tracked(mem_view) = gm.take_view(va, 16);

    let ghost valid_mappings = mem_view.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
    assert(valid_mappings.contains(mapping));
    assert(mem_view.addr_transl(va) == Some((pa, 0usize)));

    let value = virt_ptr.read(Tracked(&mem_view));
    assert(value == 42);
}

pub fn write_example(Tracked(gm): Tracked<&mut GlobalMemView>, va: Vaddr, pa: Paddr, mapping: Mapping)
    requires
        old(gm).inv(),
        old(gm).tlb_mappings.contains(mapping),
        mapping.va_range.start == va,
        mapping.pa_range.start == pa,
        mapping.page_size == 4096,
{
    let virt_ptr = VirtPtr::new(va, 16);

    assert(mapping.inv());

    let tracked Tracked(mem_view) = gm.take_view(va, 16);

    let ghost valid_mappings = mem_view.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);

    assert(valid_mappings.contains(mapping));
    assert(mem_view.addr_transl(va) == Some((pa, 0usize)));

    let ghost old_frame = mem_view.memory[pa];

    virt_ptr.write(Tracked(&mut mem_view), 42u8);

    let value = virt_ptr.read(Tracked(&mem_view));
    assert(value == 42);
}

#[verus_spec(
    with Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
        Tracked(entry_owner): Tracked<EntryOwner<UserPtConfig>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
        Tracked(level): Tracked<PagingLevel>,
        Tracked(gm): Tracked<&mut GlobalMemView>
    requires
        old(cursor_owner).inv(),
        entry_owner.inv(),
        old(regions).inv(),
        old(gm).inv(),
        old(cursor).pt_cursor.inner.wf(*old(cursor_owner)),
        entry_owner.is_frame(),
        entry_owner.frame.unwrap().mapped_pa == pa,
        entry_owner.frame.unwrap().prop == prop,
        pa == UserPtConfig::item_into_raw_spec(MappedItem { frame: frame, prop: prop }).0,
        level == UserPtConfig::item_into_raw_spec(MappedItem { frame: frame, prop: prop }).1,
        prop == UserPtConfig::item_into_raw_spec(MappedItem { frame: frame, prop: prop }).2,
        old(cursor).pt_cursor.inner.level < old(cursor).pt_cursor.inner.guard_level,
        old(cursor).pt_cursor.inner.va % page_size(level) == 0,
        old(cursor).pt_cursor.inner.va + page_size(level) < old(cursor).pt_cursor.inner.barrier_va.end,
        old(cursor_owner).children_not_locked(*old(guards)),
        !old(cursor_owner).popped_too_high,
        old(cursor_owner).in_locked_range(),
        2 <= level <= UserPtConfig::HIGHEST_TRANSLATION_LEVEL(),
)]
pub fn map_example<'a, G: InAtomicMode>(cursor: &mut CursorMut<'a, G>,
                                        frame: UFrame, va: Vaddr, pa: Paddr, prop: PageProperty)
{
    #[verus_spec(with Tracked(cursor_owner), Tracked(entry_owner),
    Tracked(regions), Tracked(guards), Tracked(level), Ghost(pa), Ghost(prop))]
    cursor.map(frame, prop);
}

}