// SPDX-License-Identifier: MPL-2.0
//! I/O port and its allocator that allocates port I/O (PIO) to device drivers.
use vstd::{prelude::*, resource::set::GhostSubset};

use crate::arch::device::io_port::valid_io_port_access;

use crate::arch::device::io_port::{IoPortReadAccess, IoPortWriteAccess, PortRead, PortWrite};
mod allocator;

use core::{marker::PhantomData, mem::size_of};

pub(super) use self::allocator::init;
use crate::{Error, prelude::*};

verus! {

broadcast use crate::arch::device::io_port::group_io_port_models;

} // verus!
/// An I/O port, representing a specific address in the I/O address of x86.
///
/// The following code shows and example to read and write u32 value to an I/O port:
///
/// ```rust
/// static PORT: IoPort<u32, ReadWriteAccess> = unsafe { IoPort::new(0x12) };
///
/// fn port_value_increase(){
///     PORT.write(PORT.read() + 1)
/// }
/// ```
///
#[derive(Debug)]
#[verus_verify]
pub struct IoPort<T, A> {
    port: u16,
    is_overlapping: bool,
    tracked_claim: Option<Tracked<GhostSubset<usize>>>,
    value_marker: PhantomData<T>,
    access_marker: PhantomData<A>,
}

verus! {

impl<T, A> View for IoPort<T, A> {
    type V = u16;

    closed spec fn view(&self) -> u16 {
        self.port
    }
}

impl<T, A> IoPort<T, A> {
    /// The complete byte range occupied by this typed port lies in the x86 PIO address space.
    #[verifier::type_invariant]
    pub open spec fn type_inv(&self) -> bool {
        &&& valid_io_port_access::<T>(self@)
        &&& self@ + size_of::<T>() <= u16::MAX
        &&& self.is_overlapping() ==> self@ + 1 <= u16::MAX
        &&& self.allocator_claim_inv()
    }

    /// Whether this port owns a claim minted by the allocator.
    pub closed spec fn is_allocated(&self) -> bool {
        self.tracked_claim is Some
    }

    /// The invariant relating the runtime allocation marker to its tracked claim.
    pub closed spec fn allocator_claim_inv(&self) -> bool {
        self.tracked_claim matches Some(claim) ==> {
            &&& allocator::io_port_allocator_initialized()
            &&& self.claim_matches_set(claim@@)
            &&& claim@.id() == allocator::io_port_allocator_instance_id()
        }
    }

    /// Whether the port was acquired as overlapping: it occupies only its first port.
    ///
    /// Marks the occupied range of [`Self::claim_matches_set`] and the released range of
    /// [`Self::drop`].
    pub closed spec fn is_overlapping(&self) -> bool {
        self.is_overlapping
    }

    /// Whether `claim` is the allocator-issued ownership token for this port's occupied range:
    /// the complete typed range, or only the first port if the port was acquired as
    /// overlapping.
    pub open spec fn claim_matches_set(&self, claim: Set<usize>) -> bool {
        claim == Set::<usize>::range(
            self@ as usize,
            if self.is_overlapping() {
                (self@ as usize + 1) as usize
            } else {
                (self@ as usize + size_of::<T>()) as usize
            },
        )
    }
}

} // verus!
/// Returns the initialized global PIO allocator.
///
/// The executable body intentionally preserves the original `get().unwrap()` behavior. This
/// helper is trusted only because Verus cannot connect an `exec static` to a spec-level boot-state
/// predicate.
#[verifier::external_body]
#[verus_spec(
    requires allocator::io_port_allocator_initialized(),
)]
fn initialized_allocator() -> &'static allocator::IoPortAllocator {
    allocator::IO_PORT_ALLOCATOR.get().unwrap()
}

#[verus_verify]
impl<T, A> IoPort<T, A> {
    /// Acquires an `IoPort` instance for the given range.
    ///
    /// This method will mark all ports in the PIO range as occupied.
    #[verus_spec(result =>
        requires
            size_of::<T>() <= u16::MAX,
            port + size_of::<T>() <= u16::MAX,
            valid_io_port_access::<T>(port),
            allocator::io_port_allocator_initialized(),
        ensures
            result matches Ok(io_port) ==> {
                &&& io_port@ == port
                &&& !io_port.is_overlapping()
                &&& io_port.is_allocated()
            },
    )]
    pub fn acquire(port: u16) -> Result<IoPort<T, A>> {
        let port = {
            /* Original Rust: allocator::IO_PORT_ALLOCATOR.get().unwrap() */
            initialized_allocator().acquire(port, false)
        };
        port.ok_or(Error::AccessDenied)
    }

    /// Acquires an `IoPort` instance that may overlap with other `IoPort`s.
    ///
    /// This method will only mark the first port in the PIO range as occupied.
    #[verus_spec(result =>
        requires
            size_of::<T>() <= u16::MAX,
            port + size_of::<T>() <= u16::MAX,
            valid_io_port_access::<T>(port),
            allocator::io_port_allocator_initialized(),
        ensures
            result matches Ok(io_port) ==> {
                &&& io_port@ == port
                &&& io_port.is_overlapping()
                &&& io_port.is_allocated()
            },
    )]
    pub fn acquire_overlapping(port: u16) -> Result<IoPort<T, A>> {
        let port = {
            /* Original Rust: allocator::IO_PORT_ALLOCATOR.get().unwrap() */
            initialized_allocator().acquire(port, true)
        };
        port.ok_or(Error::AccessDenied)
    }

    /// Returns the port number.
    #[verus_spec(returns self@)]
    pub const fn port(&self) -> u16 {
        self.port
    }

    /// Returns the size of the I/O port.
    pub const fn size(&self) -> u16 {
        size_of::<T>() as u16
    }

    /// Creates an I/O port.
    ///
    /// # Safety
    ///
    /// Reading from or writing to the I/O port may have side effects. Those side effects must
    /// not cause soundness problems (e.g., they must not corrupt the kernel memory).
    #[verus_spec(ret =>
        requires
            size_of::<T>() <= u16::MAX,
            port + size_of::<T>() <= u16::MAX,
            valid_io_port_access::<T>(port),
        ensures
            ret@ == port,
            !ret.is_overlapping(),
    )]
    pub(crate) const unsafe fn new(port: u16) -> Self {
        // SAFETY: The safety is upheld by the caller.
        /* The optional claim distinguishes statically reserved ports from allocator-owned ports.
         * Origin Rust: unsafe { Self::new_overlapping(port, false) }
         */
        unsafe { Self::new_overlapping(port, false, None) }
    }

    /// Creates an I/O port.
    ///
    /// See [`allocator::IoPortAllocator::acquire`] for an explanation of the `is_overlapping`
    /// argument.
    ///
    /// # Safety
    ///
    /// Reading from or writing to the I/O port may have side effects. Those side effects must
    /// not cause soundness problems (e.g., they must not corrupt the kernel memory).
    #[verus_spec(ret =>
        requires
            size_of::<T>() <= u16::MAX,
            port + size_of::<T>() <= u16::MAX,
            is_overlapping ==> port + 1 <= u16::MAX,
            valid_io_port_access::<T>(port),
            tracked_claim matches Some(claim) ==> {
                &&& allocator::io_port_allocator_initialized()
                &&& claim@.id() == allocator::io_port_allocator_instance_id()
                &&& claim@@ == Set::<usize>::range(
                    port as usize,
                    if is_overlapping {
                        (port as usize + 1) as usize
                    } else {
                        (port as usize + size_of::<T>()) as usize
                    },
                )
            },
        ensures
            ret@ == port,
            ret.is_overlapping() == is_overlapping,
            ret.is_allocated() == (tracked_claim is Some),
    )]
    const unsafe fn new_overlapping(
        port: u16,
        is_overlapping: bool,
        tracked_claim: Option<Tracked<GhostSubset<usize>>>,
    ) -> Self {
        Self {
            port,
            is_overlapping,
            tracked_claim,
            value_marker: PhantomData,
            access_marker: PhantomData,
        }
    }

    /// Releases this port's allocator claim, if it was dynamically acquired.
    /* VERUS LIMITATION: Verus cannot verify a lock-taking `Drop` implementation under
     * `opens_invariants none`.
     * Origin Rust:
     * impl<T, A> Drop for IoPort<T, A> {
     *     fn drop(&mut self) {
     *         let range = if !self.is_overlapping {
     *             self.port..(self.port + size_of::<T>() as u16)
     *         } else {
     *             self.port..(self.port + 1)
     *         };
     *
     *         // SAFETY: We have ownership of the PIO region.
     *         unsafe { allocator::IO_PORT_ALLOCATOR.get().unwrap().recycle(range) };
     *     }
    * }
     */
    pub fn drop(self) {
        proof! { use_type_invariant(&self); }
        let Some(claim) = self.tracked_claim else {
            return;
        };
        let range = if self.is_overlapping {
            self.port..(self.port + 1)
        } else {
            self.port..(self.port + size_of::<T>() as u16)
        };

        proof_decl! {
            let tracked claim = claim.get();
        }
        unsafe {
            #[verus_spec(with Tracked(claim))]
            initialized_allocator().recycle(range);
        }
    }
}

#[verus_verify]
#[verifier::allow(undeclared_external_trait)]
impl<T: PortRead, A: IoPortReadAccess> IoPort<T, A> {
    /// Reads from the I/O port
    pub fn read(&self) -> T {
        proof! { use_type_invariant(self); }
        unsafe { PortRead::read_from_port(self.port) }
    }
}

#[verus_verify]
#[verifier::allow(undeclared_external_trait)]
impl<T: PortWrite, A: IoPortWriteAccess> IoPort<T, A> {
    /// Writes to the I/O port
    pub fn write(&self, value: T) {
        proof! { use_type_invariant(self); }
        unsafe { PortWrite::write_to_port(self.port, value) }
    }
}

/// Reserves an I/O port range which may refer to the port I/O range used by the
/// system device driver.
///
/// # Example
/// ```
/// reserve_io_port_range!(0x60..0x64);
/// ```
macro_rules! reserve_io_port_range {
    ($range:expr) => {
        crate::const_assert!(
            $range.start < $range.end,
            "I/O port range must be valid (start < end)"
        );

        const _: () = {
            #[used]
            // SAFETY: This is properly handled in the linker script.
            #[unsafe(link_section = ".sensitive_io_ports")]
            static _RANGE: crate::io::RawIoPortRange = crate::io::RawIoPortRange {
                begin: $range.start,
                end: $range.end,
            };
        };
    };
}

/// Declares one or multiple sensitive I/O ports.
///
/// # Safety
///
/// User must ensures that:
/// - The I/O port is valid and doesn't overlap with other sensitive I/O ports.
/// - The I/O port is used by the target system device driver.
///
/// # Example
/// ```no_run
/// sensitive_io_port! {
///     unsafe {
///         /// Master PIC command port
///         static MASTER_CMD: IoPort<u8, WriteOnlyAccess> = IoPort::new(0x20);
///         /// Master PIC data port
///         static MASTER_DATA: IoPort<u8, WriteOnlyAccess> = IoPort::new(0x21);
///     }
/// }
/// ```
macro_rules! sensitive_io_port {
    (unsafe { $(
        $(#[$meta:meta])*
        $vis:vis static $name:ident: IoPort<$size:ty, $access:ty> = IoPort::new($port:expr);
    )* }) => {
        $(
            $(#[$meta])*
            $vis static $name: IoPort<$size, $access> = {
                #[used]
                // SAFETY: This is properly handled in the linker script.
                #[unsafe(link_section = ".sensitive_io_ports")]
                static _RESERVED_IO_PORT_RANGE: crate::io::RawIoPortRange = crate::io::RawIoPortRange {
                    begin: $name.port(),
                    end: $name.port() + $name.size(),
                };

                unsafe { IoPort::new($port) }
            };
        )*
    };
}

pub(crate) use reserve_io_port_range;
pub(crate) use sensitive_io_port;

#[doc(hidden)]
#[repr(C)]
#[derive(Clone, Copy, Debug)]
#[verus_verify]
pub(crate) struct RawIoPortRange {
    pub(crate) begin: u16,
    pub(crate) end: u16,
}
