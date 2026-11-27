// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd_extra::external::volatile::{
    self as mmio, AccessLog, VolatileAccess, accesses, volatile_ref_addr,
};

/*use core::ptr::NonNull;*/

use bit_field::BitField;
/*use cfg_if::cfg_if;
use log::info;*/
use volatile::{
    VolatileRef,
    access::{ReadWrite, WriteOnly},
};

use crate::{
    Error,
    Result, /*arch::if_tdx_enabled, io::IoMemAllocatorBuilder, mm::paddr_to_vaddr,
           trap::irq::IrqLine,*/
};

/*cfg_if! {
    if #[cfg(feature = "cvm_guest")] {
        use crate::arch::tdx_guest;
    }
}*/

/// I/O Advanced Programmable Interrupt Controller (APIC).
///
/// It is used to distribute external interrupts in a more advanced manner than that of the
/// standard 8259 PIC. With the I/O APIC, interrupts can be distributed to physical or logical
/// (clusters of) processors and can be prioritized. Each I/O APIC typically handles 24 external
/// interrupts.
///
/// See also <https://wiki.osdev.org/IOAPIC>.
#[verus_verify]
pub(super) struct IoApic {
    access: IoApicAccess,
    interrupt_base: u32,
}

verus! {

impl IoApic {
    pub(super) closed spec fn mmio_addresses(&self) -> (usize, usize) {
        self.access.addresses()
    }
}

pub(super) open spec fn after_read(
    addresses: (usize, usize),
    previous: Seq<VolatileAccess>,
    register: u8,
    value: u32,
) -> Seq<VolatileAccess> {
    previous.push(VolatileAccess::Write { addr: addresses.0, value: register as u32 }).push(
        VolatileAccess::Read { addr: addresses.1, sample: value },
    )
}

pub(super) open spec fn after_write(
    addresses: (usize, usize),
    previous: Seq<VolatileAccess>,
    register: u8,
    value: u32,
) -> Seq<VolatileAccess> {
    previous.push(VolatileAccess::Write { addr: addresses.0, value: register as u32 }).push(
        VolatileAccess::Write { addr: addresses.1, value },
    )
}

} // verus!

#[verus_verify]
impl IoApic {
    const TABLE_REG_BASE: u8 = 0x10;

    /*/// # Safety
    ///
    /// The caller must ensure that the base address is a valid I/O APIC base address.
    pub(super) unsafe fn new(
        base_address: usize,
        base_interrupt: u32,
        io_mem_builder: &IoMemAllocatorBuilder,
    ) -> Self {
        let mut access = unsafe { IoApicAccess::new(base_address, io_mem_builder) };

        info!(
            "[IOAPIC]: Found at {:#x}, ID {}, version {}, interrupt base {}, interrupt count {}",
            base_address,
            access.id(),
            access.version(),
            base_interrupt,
            access.max_redirection_entry()
        );

        Self {
            access,
            interrupt_base: base_interrupt,
        }
    }

    /// Enables an entry.
    ///
    /// The caller should ensure that the IRQ line is not released before the entry is disabled.
    /// Otherwise, it will be considered a logical error.
    ///
    /// # Errors
    ///
    /// This method will fail if the index exceeds the I/O APIC's maximum redirection entry, or if
    /// the entry is in use.
    pub(super) fn enable(&mut self, index: u8, irq: &IrqLine) -> Result<()> {
        if index >= self.access.max_redirection_entry() {
            return Err(Error::InvalidArgs);
        }

        let value = self.access.read(Self::TABLE_REG_BASE + 2 * index);
        if value.get_bits(0..8) as u8 != 0 {
            return Err(Error::AccessDenied);
        }

        if let Some(remapping_index) = irq.remapping_index() {
            // Intel(R) Virtualization Technology for Directed I/O (Revision 5.0), Section 5.1.5.1
            // I/OxAPIC Programming says "Bit 48 in the I/OxAPIC RTE is Set to indicate the
            // Interrupt is in Remappable format."
            let mut value: u64 = irq.num() as u64 | 0x1_0000_0000_0000;

            // "The Interrupt_Index[14:0] is programmed in bits 63:49 of the I/OxAPIC RTE. The most
            // significant bit of the Interrupt_Index (Interrupt_Index[15]) is programmed in bit 11
            // of the I/OxAPIC RTE."
            value |= ((remapping_index & 0x8000) >> 4) as u64;
            value |= (remapping_index as u64 & 0x7FFF) << 49;

            self.access.write(
                Self::TABLE_REG_BASE + 2 * index,
                value.get_bits(0..32) as u32,
            );
            self.access.write(
                Self::TABLE_REG_BASE + 2 * index + 1,
                value.get_bits(32..64) as u32,
            );
        } else {
            self.access
                .write(Self::TABLE_REG_BASE + 2 * index, irq.num() as u32);
            self.access.write(Self::TABLE_REG_BASE + 2 * index + 1, 0);
        }

        Ok(())
    }*/

    /// Disables an entry.
    ///
    /// # Errors
    ///
    /// This method will fail if the index exceeds the I/O APIC's maximum redirection entry, or if
    /// the entry is not in use.
    #[verus_spec(ret =>
        with Tracked(log): Tracked<&mut Option<AccessLog>>
        requires index <= 119,
        ensures
            *final(self) == *old(self),
            ({
                let word = accesses(final(log))[accesses(old(log)).len() as int + 1]->sample;
                let reads = after_read(old(self).mmio_addresses(), accesses(old(log)), 1, word);
                let count = (((word >> 16) & 0xff) + 1) as u8;
                if index >= count {
                    ret == Err(Error::InvalidArgs) && accesses(final(log)) == reads
                } else {
                    let low = (0x10 + 2 * index) as u8;
                    let masked = after_write(old(self).mmio_addresses(), reads, low, 1u32 << 16);
                    ret == Ok(()) && accesses(final(log)) == after_write(old(self).mmio_addresses(), masked, (low + 1) as u8, 0)
                }
            }),
    )]
    pub(super) fn disable(&mut self, index: u8) -> Result<()> {
        if index
            >= (#[verus_spec(with Tracked(log))]
            self.access.max_redirection_entry())
        {
            return Err(Error::InvalidArgs);
        }

        // "Bit 16: Interrupt Mask - R/W. When this bit is 1, the interrupt signal is masked."
        #[verus_spec(with Tracked(log))]
        self.access.write(Self::TABLE_REG_BASE + 2 * index, 1 << 16);
        #[verus_spec(with Tracked(log))]
        self.access.write(Self::TABLE_REG_BASE + 2 * index + 1, 0);

        Ok(())
    }

    /// Returns the base number of the global system interrupts controlled by the I/O APIC.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.interrupt_base())]
    pub(super) fn interrupt_base(&self) -> u32 {
        self.interrupt_base
    }
}

#[verus_verify]
struct IoApicAccess {
    register: VolatileRef<'static, u32, WriteOnly>,
    data: VolatileRef<'static, u32, ReadWrite>,
}

verus! {

impl IoApicAccess {
    spec fn addresses(&self) -> (usize, usize) {
        (volatile_ref_addr(&self.register), volatile_ref_addr(&self.data))
    }
}

} // verus!

#[verus_verify]
impl IoApicAccess {
    /*/// # Safety
    ///
    /// The caller must ensure that the base address is a valid I/O APIC base address.
    pub(self) unsafe fn new(base_address: usize, io_mem_builder: &IoMemAllocatorBuilder) -> Self {
        io_mem_builder.remove(base_address..(base_address + 0x20));
        if_tdx_enabled!({
            assert_eq!(
                base_address % crate::mm::PAGE_SIZE,
                0,
                "[IOAPIC]: I/O memory is not page aligned, which cannot be unprotected in TDX: {:#x}",
                base_address,
            );
            // SAFETY:
            //  - The address range is page aligned, as we've checked above.
            //  - The caller guarantees that the address range represents the MMIO region for I/O
            //    APICs, so the address range must fall in the GPA limit.
            //  - FIXME: The I/O memory can be at a high address, so it may not be contained in the
            //    linear mapping.
            //  - Operations on the I/O memory can have side effects that may cause soundness
            //    problems, so the pages are not trivially untyped memory. However, since
            //    `io_mem_builder.remove()` ensures exclusive ownership, it's still fine to
            //    unprotect only once, before the I/O memory is used.
            unsafe { tdx_guest::unprotect_gpa_range(base_address, 1).unwrap() };
        });

        let register_addr = NonNull::new(paddr_to_vaddr(base_address) as *mut u32).unwrap();
        // SAFETY:
        // - The caller guarantees that the memory is an I/O APIC register.
        // - `io_mem_builder.remove()` guarantees that we have exclusive ownership of the register.
        let register = unsafe { VolatileRef::new_restricted(WriteOnly, register_addr) };

        let data_addr = NonNull::new(paddr_to_vaddr(base_address + 0x10) as *mut u32).unwrap();
        // SAFETY:
        // - The caller guarantees that the memory is an I/O APIC register.
        // - `io_mem_builder.remove()` guarantees that we have exclusive ownership of the register.
        let data = unsafe { VolatileRef::new(data_addr) };

        Self { register, data }
    }*/

    #[verus_spec(value =>
        with Tracked(log): Tracked<&mut Option<AccessLog>>
        ensures
            *final(self) == *old(self),
            accesses(final(log)) == after_read(old(self).addresses(), accesses(old(log)), register, value),
        no_unwind
    )]
    pub(self) fn read(&mut self, register: u8) -> u32 {
        /* Each volatile access carries the tracked log through its adapter.
         * Origin Rust:
         * self.register.as_mut_ptr().write(register as u32);
         * self.data.as_ptr().read()
         */
        #[verus_spec(with Tracked(log))]
        mmio::write_u32(&mut self.register, register as u32);
        #[verus_spec(with Tracked(log))]
        mmio::read_u32(&self.data)
    }

    #[verus_spec(
        with Tracked(log): Tracked<&mut Option<AccessLog>>
        ensures
            *final(self) == *old(self),
            accesses(final(log)) == after_write(old(self).addresses(), accesses(old(log)), register, data),
        no_unwind
    )]
    pub(self) fn write(&mut self, register: u8, data: u32) {
        /* Each volatile access carries the tracked log through its adapter.
         * Origin Rust:
         * self.register.as_mut_ptr().write(register as u32);
         * self.data.as_mut_ptr().write(data);
         */
        #[verus_spec(with Tracked(log))]
        mmio::write_u32(&mut self.register, register as u32);
        #[verus_spec(with Tracked(log))]
        mmio::write_u32(&mut self.data, data);
    }

    #[verus_spec(
        with Tracked(log): Tracked<&mut Option<AccessLog>>
        ensures
            *final(self) == *old(self),
            accesses(final(log)) == after_read(old(self).addresses(), accesses(old(log)), 0, accesses(final(log)).last()->sample),
        returns ((accesses(final(log)).last()->sample >> 24) & 15) as u8,
    )]
    pub(self) fn id(&mut self) -> u8 {
        proof! { assert((u32::MAX >> 28) == 15u32) by (compute); }
        (#[verus_spec(with Tracked(log))]
        self.read(0))
        .get_bits(24..28) as u8
    }

    #[verus_spec(
        with Tracked(log): Tracked<&mut Option<AccessLog>>
        ensures
            *final(self) == *old(self),
            accesses(final(log)) == after_read(old(self).addresses(), accesses(old(log)), 1, accesses(final(log)).last()->sample),
        returns (accesses(final(log)).last()->sample & 0x1ff) as u8,
    )]
    pub(self) fn version(&mut self) -> u8 {
        proof! {
            assert((u32::MAX >> 23) == 511u32) by (compute);
            assert(forall|x: u32| #[trigger] (x >> 0) == x) by (bit_vector);
        }
        (#[verus_spec(with Tracked(log))]
        self.read(1))
        .get_bits(0..9) as u8
    }

    #[verus_spec(
        with Tracked(log): Tracked<&mut Option<AccessLog>>
        ensures
            *final(self) == *old(self),
            accesses(final(log)) == after_read(old(self).addresses(), accesses(old(log)), 1, accesses(final(log)).last()->sample),
        returns (((accesses(final(log)).last()->sample >> 16) & 0xff) + 1) as u8,
    )]
    pub(self) fn max_redirection_entry(&mut self) -> u8 {
        proof! {
            assert((u32::MAX >> 24) == 255u32) by (compute);
            assert(forall|x: u32| #[trigger] ((x >> 16) & 0xff) <= 255) by (bit_vector);
        }
        ((#[verus_spec(with Tracked(log))]
        self.read(1))
        .get_bits(16..24)
            + 1) as u8
    }
}
