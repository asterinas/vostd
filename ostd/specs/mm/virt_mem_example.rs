use vstd::prelude::*;

use vstd::map_lib;
use vstd::seq::*;
use vstd::set::*;

use vstd_extra::ownership::*;

use super::*;
use crate::mm::frame::untyped::UFrame;
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::{page_size, PageTableConfig};
use crate::mm::vm_space::*;
use crate::mm::{PagingConstsTrait, PagingLevel};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::{CursorOwner, EntryOwner, Guards};
use crate::specs::task::InAtomicMode;
use crate::specs::mm::tlb::TlbModel;

verus! {

/// Example of reading from a virtual address.
/// This code assumes that `va` is mapped to `pa` in a page that contains an array of size 16.
/// The `GlobalMemView` object represents a global view of memory, including the page table and TLB;
/// from this we take a `MemView` of size 16, which is the argument to `read`.
/// Following this pattern we can prove that reading from the virtual address will return the value 42.
/// It takes some work to prove that the existence of the mapping implies the correct address translation;
/// in the future we will add more tooling to make this easier.
pub fn read_example(Tracked(gm): Tracked<&mut GlobalMemView>, va: Vaddr, pa: Paddr, Ghost(mapping): Ghost<Mapping>)
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

    let tracked mem_view = gm.take_view(va, 16);

    let ghost valid_mappings = mem_view.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
    // Specifically, the verifier needs to be told that to look for the mapping, at which point it can prove the address translation.
    assert(valid_mappings.contains(mapping));
    assert(mem_view.addr_transl(va) == Some((pa, 0usize)));

    let value = virt_ptr.read(Tracked(&mem_view));
    assert(value == 42);
}

/// Slightly more complex example showing the relationship between reads and writes.
/// In this case we only assume that the initial mapping exists, and the result of the read
/// follows from the write to the same location.
pub fn write_example(Tracked(gm): Tracked<&mut GlobalMemView>, va: Vaddr, pa: Paddr, Ghost(mapping): Ghost<Mapping>)
    requires
        old(gm).inv(),
        old(gm).tlb_mappings.contains(mapping),
        mapping.va_range.start == va,
        mapping.pa_range.start == pa,
        mapping.page_size == 4096,
{
    let virt_ptr = VirtPtr::new(va, 16);

    assert(mapping.inv());

    let tracked mem_view = gm.take_view(va, 16);

    let ghost valid_mappings = mem_view.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);

    assert(valid_mappings.contains(mapping));
    assert(mem_view.addr_transl(va) == Some((pa, 0usize)));

    let ghost old_frame = mem_view.memory[pa];

    virt_ptr.write(Tracked(&mut mem_view), 42u8);

    let value = virt_ptr.read(Tracked(&mem_view));
    assert(value == 42);
}

/// Example of mapping a page table entry (WIP). In this case there is more work to do connecting
/// the specification of the page table cursor to the `GlobalMemView` object. The payoff is that
/// we can prove the preconditions of examples 1 and 2.
#[verus_spec(
    with Tracked(cursor_owner): Tracked<&mut CursorOwner<'a, UserPtConfig>>,
        Tracked(entry_owner): Tracked<EntryOwner<UserPtConfig>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(guards): Tracked<&mut Guards<'a, UserPtConfig>>,
        Tracked(tlb_model): Tracked<&mut TlbModel>,
        Tracked(gm): Tracked<&mut GlobalMemView>
    requires
        old(cursor).map_cursor_requires(*old(cursor_owner)),
        old(cursor).map_cursor_inv(*old(cursor_owner), *old(guards), *old(regions)),
        old(cursor).map_item_requires(frame, prop, entry_owner),
        old(gm).inv(),
        old(tlb_model).inv(),
)]
pub fn map_example<'a, G: InAtomicMode>(cursor: &mut CursorMut<'a, G>,
                                        frame: UFrame, va: Vaddr, pa: Paddr, prop: PageProperty)
{
    let ghost cursor0 = *cursor;

    assert(cursor0.pt_cursor.inner.va == va) by { admit() };
    assert(page_size(1) == 4096) by { admit() };

    #[verus_spec(with Tracked(cursor_owner), Tracked(entry_owner), Tracked(regions), Tracked(guards), Tracked(tlb_model))]
    cursor.map(frame, prop);

    let ghost mapping = Mapping {
        va_range: cursor0.pt_cursor.inner.va..(cursor0.pt_cursor.inner.va + 4096) as usize,
        pa_range: pa..(pa + 4096) as usize,
        page_size: 4096,
        property: prop,
    };

    assert(gm.pt_mappings.contains(mapping)) by { admit() };

    proof {
        if gm.addr_transl(va) is None {
            gm.tlb_soft_fault(va);
            assert(gm.tlb_mappings.contains(mapping)) by { admit() };
        } else {
            assert(gm.tlb_mappings.contains(mapping)) by { admit() };
        }
    }

    write_example(Tracked(gm), va, pa, Ghost(mapping));

}

}
