// SPDX-License-Identifier: MPL-2.0
//! I/O port and its allocator that allocates port I/O (PIO) to device drivers.
use vstd::prelude::*;

use crate::arch::device::io_port::{
    IoPortReadAccess, IoPortWriteAccess, PortRead, PortWrite, valid_io_port_access,
};
mod allocator;

use core::{marker::PhantomData, mem::size_of};

pub(super) use self::allocator::init;
use crate::{Error, prelude::*};

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
#[verus_verify]
pub struct IoPort<T, A> {
    port: u16,
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
    pub open spec fn well_formed(&self) -> bool {
        valid_io_port_access::<T>(self@ as int)
    }

    /// Whether `claim` is the allocator-issued ownership token for this complete typed range.
    pub open spec fn claim_matches_set(&self, claim: Set<usize>) -> bool {
        claim == port_id_set(self@ as usize, (self@ as usize + size_of::<T>()) as usize)
    }
}

/// Set of byte-sized PIO numbers in the half-open interval `[start, end)`.
pub open spec fn port_id_set(start: usize, end: usize) -> Set<usize>
    decreases end - start,
{
    if start < end {
        port_id_set(start, (end - 1) as usize).insert((end - 1) as usize)
    } else {
        Set::empty()
    }
}

/// Extending a PIO interval by one byte is equivalent to inserting its old endpoint.
pub proof fn lemma_port_id_set_insert(start: usize, end: usize)
    requires
        start <= end,
        end < usize::MAX,
    ensures
        port_id_set(start, end).insert(end) == port_id_set(start, (end + 1) as usize),
{
}

/// Membership characterization for [`port_id_set`].
pub proof fn lemma_port_id_set_contains(start: usize, end: usize, id: usize)
    requires
        start <= end,
    ensures
        port_id_set(start, end).contains(id) <==> start <= id < end,
    decreases end - start,
{
    if start < end {
        lemma_port_id_set_contains(start, (end - 1) as usize, id);
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
    #[verus_spec(result =>
        with
            -> claim: Tracked<Option<allocator::IoPortClaim>>,
        requires
            vstd::layout::size_of::<T>() <= u16::MAX,
            size_of::<T>() <= u16::MAX,
            port as usize + size_of::<T>() <= u16::MAX,
            allocator::io_port_allocator_initialized(),
        ensures
            result is Ok ==> result->Ok_0@ == port,
            result is Ok ==> result->Ok_0.well_formed(),
            result is Ok <==> claim@ is Some,
            result is Ok ==> claim@->Some_0.instance_id() ==
                allocator::io_port_allocator_instance_id(),
            result is Ok ==> result->Ok_0.claim_matches_set(claim@->Some_0.set()),
    )]
    pub fn acquire(port: u16) -> Result<IoPort<T, A>> {
        proof_decl! {
            let tracked claim: Option<allocator::IoPortClaim>;
        }
        #[verus_spec(with => Tracked(claim))]
        let port = initialized_allocator().acquire(port);
        let result = port.ok_or(Error::AccessDenied);
        proof_with!(|= Tracked(claim));
        result
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

    /// Create an I/O port.
    ///
    /// # Safety
    ///
    /// This function is marked unsafe as creating an I/O port is considered
    /// a privileged operation.
    #[verus_spec(ret =>
        requires
            vstd::layout::size_of::<T>() <= u16::MAX,
            size_of::<T>() <= u16::MAX,
            port as usize + size_of::<T>() <= u16::MAX,
        ensures
            ret@ == port,
            ret.well_formed(),
    )]
    pub const unsafe fn new(port: u16) -> Self {
        Self {
            port,
            value_marker: PhantomData,
            access_marker: PhantomData,
        }
    }

    /// Releases the allocator claim for this port.
    ///
    /// VERUS LIMITATION: this is called explicitly because Verus does not yet support proving the
    /// standard `Drop` implementation below.
    #[verus_spec(
        with
            Tracked(claim): Tracked<allocator::IoPortClaim>,
        requires
            allocator::io_port_allocator_initialized(),
            claim.instance_id() == allocator::io_port_allocator_instance_id(),
            self.claim_matches_set(claim.set()),
            self@ as usize + size_of::<T>() <= u16::MAX,
    )]
    pub fn drop(self) {
        let range = self.port..(self.port + size_of::<T>() as u16);
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
    #[inline]
    #[verus_spec(requires self.well_formed())]
    pub fn read(&self) -> T {
        unsafe { PortRead::read_from_port(self.port) }
    }
}

#[verus_verify]
#[verifier::allow(undeclared_external_trait)]
impl<T: PortWrite, A: IoPortWriteAccess> IoPort<T, A> {
    /// Writes to the I/O port
    #[inline]
    #[verus_spec(requires self.well_formed())]
    pub fn write(&self, value: T) {
        unsafe { PortWrite::write_to_port(self.port, value) }
    }
}

/* impl<T, A> Drop for IoPort<T, A> {
    fn drop(&mut self) {
        // SAFETY: The caller have ownership of the PIO region.
        unsafe {
            allocator::IO_PORT_ALLOCATOR
                .get()
                .unwrap()
                .recycle(self.port..(self.port + size_of::<T>() as u16));
        }
    }
} */

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
            #[link_section = ".sensitive_io_ports"]
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
                #[link_section = ".sensitive_io_ports"]
                static _RESERVED_IO_PORT_RANGE: crate::io::RawIoPortRange = crate::io::RawIoPortRange {
                    begin: $name.port(),
                    end: $name.port() + $name.size(),
                };

            	unsafe {
                     IoPort::new($port)
            	}
            };
        )*
    };
}

pub(crate) use reserve_io_port_range;
pub(crate) use sensitive_io_port;

#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
#[repr(C)]
#[verus_verify]
pub(crate) struct RawIoPortRange {
    pub(crate) begin: u16,
    pub(crate) end: u16,
}
