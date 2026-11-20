// SPDX-License-Identifier: MPL-2.0
//! IDT gate operations from x86_64 0.15.5.
use vstd::prelude::*;

use crate::panic::allowed_to_panic_if;

use x86_64::{
    PrivilegeLevel, VirtAddr,
    instructions::tables::lidt,
    structures::{
        DescriptorTablePointer,
        idt::{Entry, EntryOptions},
    },
};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExVirtAddr(VirtAddr);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(F)]
pub struct ExEntry<F>(Entry<F>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExEntryOptions(EntryOptions);

#[verifier::external_type_specification]
pub struct ExPrivilegeLevel(PrivilegeLevel);

#[verifier::external_type_specification]
pub struct ExDescriptorTablePointer(DescriptorTablePointer);

pub ghost struct Gate {
    pub handler: u64,
    /// Raw IST, gate type, DPL and present bits, including the reserved bits.
    pub attributes: u16,
    pub selector: u16,
    pub reserved: u32,
}

pub uninterp spec fn gate<F>(entry: Entry<F>) -> Gate;

pub uninterp spec fn attributes(options: EntryOptions) -> u16;

pub uninterp spec fn selector(options: EntryOptions) -> u16;

pub uninterp spec fn address(addr: VirtAddr) -> u64;

/// Boot runs at CPL 0 with 48-bit canonical kernel addresses and a valid long-mode CS.
/// The selector read on the initializing CPU is usable on every CPU sharing the IDT.
pub uninterp spec fn idt_load_context() -> bool;

pub uninterp spec fn kernel_code_selector(cs: u16) -> bool;

pub open spec fn is_canonical(addr: u64) -> bool {
    addr < 0x0000_8000_0000_0000 || addr >= 0xffff_8000_0000_0000
}

/// The address is a valid interrupt handler with the signature required by F.
pub uninterp spec fn valid_handler<F>(addr: u64) -> bool;

/// A deliverable vector uses the interrupt stub's hardware stack convention,
/// including whether the processor pushes an error code for this vector.
pub uninterp spec fn valid_vector(handler: u64, vector: int) -> bool;

/// The base names permanently readable, immutable memory containing these gates.
pub uninterp spec fn static_idt_at(base: u64, entries: Seq<Entry<()>>) -> bool;

/// The selected TSS IST slot (1 through 7) provides a usable stack for
/// this vector on every CPU loading the table.
pub uninterp spec fn valid_ist_stack(slot: u16, vector: int) -> bool;

/// The handler supports software delivery of this vector from less privileged code.
pub uninterp spec fn software_interrupt_safe(handler: u64, vector: int) -> bool;

/// The handler tolerates delivery with IF preserved by a 64-bit trap gate.
pub uninterp spec fn trap_gate_safe(handler: u64, vector: int) -> bool;

pub open spec fn usable_gate(entry: Entry<()>, vector: int) -> bool {
    let g = gate(entry);
    let slot = g.attributes & 7;
    // Keep P, the gate type and the reserved bits. Check DPL and IST separately.
    let kind = g.attributes & 0x9ff8;
    &&& g.reserved == 0
    &&& kernel_code_selector(g.selector)
    &&& (kind == 0x8e00 || (kind == 0x8f00 && trap_gate_safe(g.handler, vector)))
    &&& (slot == 0 || valid_ist_stack(slot, vector))
    &&& (g.attributes & 0x6000 == 0 || software_interrupt_safe(g.handler, vector))
}

/// Descriptor and permanent table witnessed by a load on the executing CPU.
pub ghost struct LoadedIdt {
    pub base: u64,
    pub limit: u16,
    pub entries: Seq<Entry<()>>,
}

pub tracked struct IdtrLoad {
    ghost descriptor: Option<LoadedIdt>,
}

impl IdtrLoad {
    pub closed spec fn descriptor(self) -> Option<LoadedIdt> {
        self.descriptor
    }

    pub proof fn tracked_new() -> (tracked r: Self)
        ensures
            r.descriptor().is_none(),
    {
        IdtrLoad { descriptor: None }
    }
}

pub assume_specification<F>[ Entry::<F>::missing ]() -> (r: Entry<F>)
    ensures
        gate(r) == (Gate { handler: 0, attributes: 0x0e00, selector: 0, reserved: 0 }),
    opens_invariants none
    no_unwind
;

pub assume_specification[ VirtAddr::new ](addr: u64) -> (r: VirtAddr)
    requires
        allowed_to_panic_if(!is_canonical(addr)),
    ensures
        is_canonical(addr),
        address(r) == addr,
    opens_invariants none
    no_unwind when is_canonical(addr)
;

pub assume_specification<'a, F>[ Entry::<F>::set_handler_addr ](
    entry: &'a mut Entry<F>,
    addr: VirtAddr,
) -> (options: &'a mut EntryOptions)
    requires
        valid_handler::<F>(address(addr)),
    ensures
        attributes(*options) == 0x8e00,
        idt_load_context() ==> kernel_code_selector(selector(*options)),
        gate(*final(entry)) == (Gate {
            handler: address(addr),
            attributes: attributes(*final(options)),
            selector: selector(*final(options)),
            reserved: gate(*old(entry)).reserved,
        }),
    opens_invariants none
    no_unwind
;

pub assume_specification<'a>[ EntryOptions::set_privilege_level ](
    options: &'a mut EntryOptions,
    dpl: PrivilegeLevel,
) -> (r: &'a mut EntryOptions)
    ensures
        attributes(*r) == (attributes(*old(options)) & 0x9fff) | ((dpl as u16) << 13),
        selector(*r) == selector(*old(options)),
        *final(options) == *final(r),
    opens_invariants none
    no_unwind
;

} // verus!
/// # Safety
/// The current CPU must be privileged and all deliverable vectors must have
/// usable gates backed by permanently mapped memory.
#[verifier::external_body]
#[verus_spec(
    with Ghost(entries): Ghost<Seq<Entry<()>>>, Tracked(load): Tracked<&mut IdtrLoad>,
    requires
        idt_load_context(),
        is_canonical(address(idtr.base)),
        static_idt_at(address(idtr.base), entries),
        entries.len() == 256,
        idtr.limit + 1 == 16 * entries.len(),
        forall|i: int| 0 <= i < entries.len() ==> {
            let e = #[trigger] entries[i];
            &&& usable_gate(e, i)
            &&& is_canonical(gate(e).handler)
            &&& valid_handler::<()>(gate(e).handler)
            &&& valid_vector(gate(e).handler, i)
        },
    ensures
        final(load).descriptor() == Some(LoadedIdt {
            base: address(idtr.base), limit: idtr.limit, entries,
        }),
    opens_invariants none
    no_unwind
)]
#[inline]
pub unsafe fn load_idtr(idtr: &DescriptorTablePointer) {
    unsafe { lidt(idtr) };
}
