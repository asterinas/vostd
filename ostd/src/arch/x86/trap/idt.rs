// SPDX-License-Identifier: MPL-2.0
//! Configure the Interrupt Descriptor Table (IDT).
use vstd::prelude::*;
use vstd_extra::{
    external::x86::idt::{
        self, IdtrLoad, gate, idt_load_context, is_canonical, kernel_code_selector,
        lemma_idt_entry_layout, software_interrupt_safe, static_idt_at, usable_gate, valid_handler,
        valid_vector,
    },
    panic::allowed_to_panic_if,
};

use alloc::boxed::Box;
use core::arch::global_asm;

use spin::Once;
use x86_64::{
    PrivilegeLevel, VirtAddr,
    /* instructions::tables::lidt, */
    structures::{DescriptorTablePointer, idt::Entry},
};

global_asm!(include_str!("trap.S"));

#[verus_verify]
const NUM_INTERRUPTS: usize = 256;

#[verus_spec(ensures gate(MISSING_ENTRY).reserved == 0)]
const MISSING_ENTRY: Entry<()> = Entry::missing();

extern "C" {
    #[link_name = "trap_handler_table"]
    static VECTORS: [usize; NUM_INTERRUPTS];
}

/// # Safety
/// The linker must have relocated all 256 entries. The table must remain aligned,
/// readable and immutable for the lifetime of the kernel.
#[verifier::when_used_as_spec(vector_table_spec)]
#[verifier::external_body]
#[verus_spec(
    requires vectors_ready(),
    returns vector_table(),
    opens_invariants none
    no_unwind
)]
pub(super) unsafe fn vector_table() -> &'static [usize; NUM_INTERRUPTS] {
    unsafe { &VECTORS }
}

/* The cached slice needs a type invariant that also holds on cache hits.
 * Origin Rust: static GLOBAL_IDT: Once<&'static [Entry<()>]> = Once::new();
 */
#[verus_verify]
#[repr(transparent)]
struct Idt {
    entries: &'static [Entry<()>],
}

#[verifier::external_body]
#[verus_spec(result =>
    requires
        f.requires(()),
        idt_load_context(),
        allowed_to_panic_if(idt_once_may_observe_poison()),
    ensures
        result.1.addr() as u64 == published_idt_base(),
        is_canonical(result.1.addr() as u64),
        static_idt_at(result.1.addr() as u64, result.0.entries@),
)]
fn published_idt<F: FnOnce() -> Idt>(f: F) -> (&'static Idt, *const Entry<()>) {
    static GLOBAL_IDT: Once<Idt> = Once::new();
    let idt = GLOBAL_IDT.call_once(f);
    (idt, idt.entries.as_ptr())
}

/// Initializes and loads the IDT.
///
/// The caller should only call this method once in the boot context for each available processor.
/// This is not a safety requirement, however, because calling this method again will do nothing
/// more than load the same IDT.
///
/// The stubs for vectors 21, 29, and 30 require that the CPU deliver no error code.
#[verus_spec(
    with -> loaded: Tracked<IdtrLoad>,
    requires
        vectors_ready(),
        valid_vectors(vector_table()),
        idt_load_context(),
        allowed_to_panic_if(idt_once_may_observe_poison()),
    ensures
        loaded@.descriptor() matches Some(d) && {
            &&& d.base == published_idt_base()
            &&& d.limit == 4095
            &&& is_canonical(d.base)
            &&& static_idt_at(d.base, d.entries)
            &&& d.entries.len() == 256
            &&& forall|i: int| 0 <= i < d.entries.len() ==>
                entry_matches(#[trigger] d.entries[i], vector_table()@[i], i)
        },
)]
pub(super) fn init() {
    proof! {
        broadcast use lemma_idt_entry_layout;
    }
    /* Bind the pointer to the slice published by this Once, including on cache hits.
     * Origin Rust: let idt = *GLOBAL_IDT.call_once(|| {
     */
    let (idt, ptr) = published_idt(|| {
        /* Verus requires a named constant for this array repeat.
         * Origin Rust: let idt = Box::leak(Box::new([const { Entry::missing() }; NUM_INTERRUPTS]));
         */
        let idt = Box::leak(Box::new([MISSING_ENTRY; NUM_INTERRUPTS]));

        // SAFETY: The vector array is properly initialized, lives for `'static`, and will never be
        // mutated. So it's always fine to create an immutable borrow to it.
        /* Verus models the extern-static borrow through the accessor.
         * Origin Rust: let vectors = unsafe { &VECTORS };
         */
        let vectors = unsafe { vector_table() };

        // Initialize the IDT entries.
        #[verus_spec(iter =>
            invariant
                idt_load_context(),
                valid_vectors(vectors),
                forall|i: int| 0 <= i < iter.index() ==>
                    entry_matches(#[trigger] idt@[i], vectors@[i], i),
                forall|i: int| iter.index() <= i < NUM_INTERRUPTS ==>
                    gate(#[trigger] idt@[i]).reserved == 0,
        )]
        for (intr_no, &handler) in vectors.iter().enumerate() {
            let handler = VirtAddr::new(handler as u64);

            let entry = &mut idt[intr_no];
            // SAFETY: The handler defined in `trap.S` has a correct signature to handle the
            // corresponding exception or interrupt.
            let opt = unsafe { entry.set_handler_addr(handler) };

            // Enable `int3` and `into` in the userspace.
            if intr_no == 3 || intr_no == 4 {
                opt.set_privilege_level(PrivilegeLevel::Ring3);
                proof! {
                    assert((0x8e00u16 & 0x9fffu16) | (3u16 << 13) == 0xee00u16) by (bit_vector);
                }
            }
        }

        /* Carry the gate invariant with the published slice.
         * Origin Rust: idt
         */
        Idt { entries: idt }
    });
    proof! {
        use_type_invariant(idt);
        assert forall|i: int| 0 <= i < idt.entries.len() implies
            usable_gate(#[trigger] idt.entries@[i], i) by {
            let attrs = gate(idt.entries@[i]).attributes;
            assert(attrs & 0x9ff8 == 0x8e00 && attrs & 7 == 0
                && (attrs == 0xee00 || attrs & 0x6000 == 0)) by (bit_vector)
                requires attrs == 0x8e00 || attrs == 0xee00;
        }
    }

    let idtr = DescriptorTablePointer {
        /* Both fields describe the slice returned by the same Once.
         * Origin Rust:
         * limit: (core::mem::size_of_val(idt) - 1) as u16,
         * base: VirtAddr::new(idt.as_ptr().addr() as u64),
         */
        limit: (core::mem::size_of_val(idt.entries) - 1) as u16,
        base: VirtAddr::new(ptr.addr() as u64),
    };
    proof_decl! { let tracked mut load = IdtrLoad::tracked_new(); }
    // SAFETY: The IDT is valid to load because:
    //  - It lives for `'static`.
    //  - It contains correct entries at correct indexes: all handlers are defined in `trap.S` with
    //    correct handler signatures.
    /* The load returns an erased witness for this CPU.
     * Origin Rust: unsafe { lidt(&idtr) };
     */
    proof_with!(|= Tracked(load));
    unsafe {
        proof_with!(Ghost(idt.entries@), Tracked(&mut load));
        idt::load_idtr(&idtr)
    }
}

verus! {

impl Idt {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.entries@.len() == NUM_INTERRUPTS
        &&& forall|i: int|
            0 <= i < NUM_INTERRUPTS ==> entry_matches(
                #[trigger] self.entries@[i],
                vector_table()@[i],
                i,
            )
    }
}

/// Address of the slice published by `GLOBAL_IDT`.
pub(super) uninterp spec fn published_idt_base() -> u64;

/// An earlier or racing initializer of `GLOBAL_IDT` can unwind and poison the cell.
pub(super) uninterp spec fn idt_once_may_observe_poison() -> bool;

/// The relocated table is an aligned, initialized, immutable region of 256
/// `usize` entries that remains readable for the lifetime of the kernel.
pub(super) uninterp spec fn vectors_ready() -> bool;

pub(super) uninterp spec fn vector_table_spec() -> &'static [usize; NUM_INTERRUPTS];

pub(super) open spec fn valid_vectors(vectors: &[usize; NUM_INTERRUPTS]) -> bool {
    forall|i: int|
        0 <= i < vectors@.len() ==> {
            &&& is_canonical(#[trigger] vectors@[i] as u64)
            &&& valid_handler::<()>(vectors@[i] as u64)
            &&& valid_vector(vectors@[i] as u64, i)
            &&& (i == 3 || i == 4) ==> software_interrupt_safe(vectors@[i] as u64, i)
        }
}

pub(super) open spec fn entry_matches(entry: Entry<()>, handler: usize, vector: int) -> bool {
    let g = gate(entry);
    &&& g.handler == handler as u64
    &&& g.reserved == 0
    &&& kernel_code_selector(g.selector)
    &&& g.attributes == if vector == 3 || vector == 4 {
        0xee00u16
    } else {
        0x8e00u16
    }
}

} // verus!
