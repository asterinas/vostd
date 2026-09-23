// SPDX-License-Identifier: MPL-2.0
#![expect(dead_code)]

//! Remapping structures of DMAR table.
//!
//! This file defines these structures and provides a `Debug` implementation to see the value
//! inside these structures.
//!
//! Most of the introduction are copied from Intel vt-directed-io-specification.
use vstd::{
    prelude::*,
    seq::{
        lemma_seq_ext_equal, lemma_seq_new_index, lemma_seq_new_len,
        lemma_seq_push_index_different, lemma_seq_push_index_same, lemma_seq_push_len,
    },
    utf8::{encode_utf8, valid_utf8},
};
use vstd_extra::{debug_assert, debug_assert_eq};

use core::mem::size_of;
use ostd_pod::{decode_pod, from_bytes_spec};

use alloc::{borrow::ToOwned, string::String, vec::Vec};
use core::fmt::Debug;

use ostd_pod::Pod;

verus! {

/// DMA-remapping hardware unit definition (DRHD).
///
/// A DRHD structure uniquely represents a remapping hardware unit present in the platform.
/// There must be at least one instance of this structure for each PCI segment in the platform.
#[derive(Debug, Clone)]
pub struct Drhd {
    header: DrhdHeader,
    device_scopes: Vec<DeviceScope>,
}

} // verus!
#[verus_verify]
impl Drhd {
    #[verus_verify(dual_spec)]
    pub fn register_base_addr(&self) -> u64 {
        self.header.register_base_addr
    }
}

verus! {

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct DrhdHeader {
    typ: u16,
    length: u16,
    flags: u8,
    size: u8,
    segment_num: u16,
    register_base_addr: u64,
}

// SAFETY: The `DrhdHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for DrhdHeader {

}

/// Reserved Memory Region Reporting (RMRR).
///
/// BIOS allocated reserved memory ranges that may be DMA targets.
/// It may report each such reserved memory region through the RMRR structures, along
/// with the devices that requires access to the specified reserved memory region.
#[derive(Debug, Clone)]
pub struct Rmrr {
    header: RmrrHeader,
    device_scopes: Vec<DeviceScope>,
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct RmrrHeader {
    typ: u16,
    length: u16,
    reserved: u16,
    segment_num: u16,
    reserved_memory_region_base_addr: u64,
    reserved_memory_region_limit_addr: u64,
}

// SAFETY: The `RmrrHeader` struct is `repr(C)` and all its fields are plain
// old data, so any bit pattern is a valid value.
unsafe impl Pod for RmrrHeader {

}

/// Root Port ATS Capability Reporting (ATSR).
///
/// This structure is applicable only for platforms supporting Device-TLBs as reported through the
/// Extended Capability Register.
#[derive(Debug, Clone)]
pub struct Atsr {
    header: AtsrHeader,
    device_scopes: Vec<DeviceScope>,
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct AtsrHeader {
    typ: u16,
    length: u16,
    flags: u8,
    reserved: u8,
    segment_num: u16,
}

// SAFETY: The `AtsrHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for AtsrHeader {

}

/// Remapping Hardware Status Affinity (RHSA).
///
/// It is applicable for platforms supporting non-uniform memory (NUMA),
/// where Remapping hardware units spans across nodes.
/// This optional structure provides the association between each Remapping hardware unit (identified
/// by its espective Base Address) and the proximity domain to which that hardware unit belongs.
#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct Rhsa {
    typ: u16,
    length: u16,
    flags: u32,
    register_base_addr: u64,
    proximity_domain: u32,
}

// SAFETY: The `Rhsa` struct is `repr(C)` and all its fields are plain old data,
// so any bit pattern is a valid value.
unsafe impl Pod for Rhsa {

}

/// ACPI Name-space Device Declaration (ANDD).
///
/// An ANDD structure uniquely represents an ACPI name-space
/// enumerated device capable of issuing DMA requests in the platform.
#[derive(Debug, Clone)]
pub struct Andd {
    header: AnddHeader,
    acpi_object_name: String,
}

impl Andd {
    /// The characters of the ACPI object name.
    pub closed spec fn acpi_object_name_spec(self) -> Seq<char> {
        self.acpi_object_name@
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct AnddHeader {
    typ: u16,
    length: u16,
    reserved: [u8; 3],
    acpi_device_num: u8,
}

// SAFETY: The `AnddHeader` struct is `repr(C)` and all its fields are plain
// old data, so any bit pattern is a valid value.
unsafe impl Pod for AnddHeader {

}

/// SoC Integrated Address Translation Cache (SATC).
///
/// The SATC reporting structure identifies devices that have address translation cache (ATC),
/// as defined by the PCI Express Base Specification.
#[derive(Debug, Clone)]
pub struct Satc {
    header: SatcHeader,
    device_scopes: Vec<DeviceScope>,
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct SatcHeader {
    typ: u16,
    length: u16,
    flags: u8,
    reserved: u8,
    segment_num: u16,
}

// SAFETY: The `SatcHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for SatcHeader {

}

/// SoC Integrated Device Property Reporting (SIDP).
///
/// The (SIDP) reporting structure identifies devices that have special
/// properties and that may put restrictions on how system software must configure remapping
/// structures that govern such devices in a platform where remapping hardware is enabled.
#[derive(Debug, Clone)]
pub struct Sidp {
    header: SidpHeader,
    device_scopes: Vec<DeviceScope>,
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct SidpHeader {
    typ: u16,
    length: u16,
    reserved: u16,
    segment_num: u16,
}

// SAFETY: The `SidpHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for SidpHeader {

}

/// The Device Scope Structure is made up of Device Scope Entries. Each Device Scope Entry may be
/// used to indicate a PCI endpoint device
#[derive(Debug, Clone)]
pub struct DeviceScope {
    header: DeviceScopeHeader,
    path: Vec<(u8, u8)>,
}

impl DeviceScope {
    /// The parsed path of the Device Scope Entry, as a sequence of byte pairs.
    pub closed spec fn path_spec(self) -> Seq<(u8, u8)> {
        self.path@
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct DeviceScopeHeader {
    typ: u8,
    length: u8,
    flags: u8,
    reserved: u8,
    enum_id: u8,
    start_bus_number: u8,
}

// SAFETY: The `DeviceScopeHeader` struct is `repr(C)` and all its fields are
// plain old data, so any bit pattern is a valid value.
unsafe impl Pod for DeviceScopeHeader {

}

/// The sequence of byte pairs read from `bytes[start..end]`, two bytes per element.
pub open spec fn path_pairs_spec(bytes: Seq<u8>, start: int, end: int) -> Seq<(u8, u8)> {
    Seq::new(((end - start) / 2) as nat, |i: int| (bytes[start + 2 * i], bytes[start + 2 * i + 1]))
}

/// Whether `bytes` is a sequence of complete device-scope entries.
pub open spec fn valid_device_scopes(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        true
    } else {
        let scope_len = from_bytes_spec::<DeviceScopeHeader>(bytes).length_spec() as int;
        &&& 0 < scope_len
        &&& size_of::<DeviceScopeHeader>() <= scope_len <= bytes.len()
        &&& (scope_len - size_of::<DeviceScopeHeader>()) % 2 == 0
        &&& valid_device_scopes(bytes[scope_len..])
    }
}

} // verus!
macro_rules! impl_header_spec {
    ($(($struct:ident, $header:ident),)*) => {
        verus! {
            $(impl $struct {
                #[doc = concat!("The header of [`", stringify!($struct), "`].")]
                pub closed spec fn header_spec(self) -> $header {
                    self.header
                }
            })*
        }
    };
}

impl_header_spec!(
    (Drhd, DrhdHeader),
    (Rmrr, RmrrHeader),
    (Atsr, AtsrHeader),
    (Andd, AnddHeader),
    (Satc, SatcHeader),
    (Sidp, SidpHeader),
    (DeviceScope, DeviceScopeHeader),
);
macro_rules! impl_length_spec {
    ($(($struct:ident, $len:ty),)*) => {
        verus! {
            $(impl $struct {
                #[doc = concat!("The total length of the [`", stringify!($struct), "`], in bytes.")]
                pub closed spec fn length_spec(self) -> $len {
                    self.length
                }
            })*
        }
    };
}

impl_length_spec!(
    (DrhdHeader, u16),
    (RmrrHeader, u16),
    (AtsrHeader, u16),
    (Rhsa, u16),
    (AnddHeader, u16),
    (SatcHeader, u16),
    (SidpHeader, u16),
    (DeviceScopeHeader, u8),
);
macro_rules! impl_from_bytes {
    ($(($struct:tt, $header_struct:tt),)*) => {
        $(#[verus_verify]
        impl $struct {
            #[doc = concat!("Parses a [`", stringify!($struct), "`] from bytes.")]
            ///
            /// # Panics
            ///
            #[doc = concat!(
                "This method may panic if the bytes do not represent a valid [`",
                stringify!($struct),
                "`].",
            )]
            #[verus_spec(ret =>
                requires
                    bytes@.len() >= size_of::<$header_struct>(),
                    from_bytes_spec::<$header_struct>(bytes@).length_spec() == bytes@.len(),
                    valid_device_scopes(bytes@[size_of::<$header_struct>()..]),
                ensures
                    ret.header_spec() == decode_pod::<$header_struct>(
                        bytes@[..size_of::<$header_struct>()],
                    ),
            )]
            pub fn from_bytes(bytes: &[u8]) -> Self {
                let header = $header_struct::from_bytes(bytes);
                debug_assert_eq!(header.length as usize, bytes.len());

                let mut index = core::mem::size_of::<$header_struct>();
                let mut device_scopes = Vec::new();
                #[verus_spec(invariant
                    size_of::<$header_struct>() <= index <= header.length,
                    header.length == bytes@.len(),
                    valid_device_scopes(bytes@[index..]),
                    decreases header.length as usize - index,
                )]
                while index != (header.length as usize) {
                    let val = DeviceScope::from_bytes_prefix(&bytes[index..]);
                    proof! {
                        let scope_len = val.header.length as int;
                        assert(bytes@[index..][scope_len..] == bytes@[index + scope_len..]);
                    }
                    index += val.header.length as usize;
                    device_scopes.push(val);
                }

                Self{
                    header,
                    device_scopes,
                }
            }
        })*
    };
}

impl_from_bytes!(
    (Drhd, DrhdHeader),
    (Rmrr, RmrrHeader),
    (Atsr, AtsrHeader),
    (Satc, SatcHeader),
    (Sidp, SidpHeader),
);

#[verus_verify]
impl DeviceScope {
    /// Parses a [`DeviceScope`] from a prefix of the bytes.
    ///
    /// # Panics
    ///
    /// This method may panic if the byte prefix does not represent a valid [`DeviceScope`].
    #[verus_spec(ret =>
        requires
            size_of::<DeviceScopeHeader>()
                <= from_bytes_spec::<DeviceScopeHeader>(bytes@).length_spec()
                <= bytes@.len(),
            (
                (from_bytes_spec::<DeviceScopeHeader>(bytes@).length_spec() as usize)
                    - size_of::<DeviceScopeHeader>()
            ) % 2 == 0,
        ensures
            ret.header_spec() == decode_pod::<DeviceScopeHeader>(
                bytes@[..size_of::<DeviceScopeHeader>()],
            ),
            ret.path_spec() =~= path_pairs_spec(
                bytes@,
                size_of::<DeviceScopeHeader>() as int,
                ret.header_spec().length_spec() as int,
            ),
    )]
    fn from_bytes_prefix(bytes: &[u8]) -> Self {
        let header = DeviceScopeHeader::from_bytes(bytes);
        debug_assert!((header.length as usize) <= bytes.len());

        let mut index = core::mem::size_of::<DeviceScopeHeader>();
        debug_assert!((header.length as usize) >= index);

        let mut path = Vec::new();
        proof! {
            assert(header == from_bytes_spec::<DeviceScopeHeader>(bytes@));
            assert(bytes@.len() >= header.length);
        }
        #[verus_spec(invariant
            size_of::<DeviceScopeHeader>() <= index <= header.length,
            (header.length as usize - index) % 2 == 0,
            (index - size_of::<DeviceScopeHeader>()) % 2 == 0,
            bytes@.len() >= header.length,
            path@ =~= path_pairs_spec(
                bytes@,
                size_of::<DeviceScopeHeader>() as int,
                index as int,
            ),
            decreases header.length as usize - index,
        )]
        while index != (header.length as usize) {
            let val = (bytes[index], bytes[index + 1]);
            path.push(val);
            proof! {
                lemma_path_pairs_step(
                    bytes@,
                    size_of::<DeviceScopeHeader>() as int,
                    (index + 2) as int,
                );
                assert(path@ =~= path_pairs_spec(
                    bytes@,
                    size_of::<DeviceScopeHeader>() as int,
                    (index + 2) as int,
                ));
            }
            index += 2;
        }

        Self { header, path }
    }
}

#[verus_verify]
impl Rhsa {
    /// Parses an [`Rhsa`] from the bytes.
    ///
    /// # Panics
    ///
    /// This method may panic if the bytes do not represent a valid [`Rhsa`].
    #[verus_spec(
        requires
            bytes@.len() >= size_of::<Self>(),
            from_bytes_spec::<Self>(bytes@).length_spec() == bytes@.len(),
        returns
            decode_pod::<Self>(bytes@[..size_of::<Self>()]),
    )]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let val = <Self as Pod>::from_bytes(bytes);
        debug_assert_eq!(val.length as usize, bytes.len());

        val
    }
}

#[verus_verify]
impl Andd {
    /// Parses an [`Andd`] from the bytes.
    ///
    /// # Panics
    ///
    /// This method may panic if the bytes do not represent a valid [`Andd`].
    #[verus_spec(ret =>
        requires
            bytes@.len() >= size_of::<AnddHeader>(),
            from_bytes_spec::<AnddHeader>(bytes@).length_spec() == bytes@.len(),
            valid_utf8(bytes@[size_of::<AnddHeader>()..]),
        ensures
            ret.header_spec() == decode_pod::<AnddHeader>(
                bytes@[..size_of::<AnddHeader>()],
            ),
            encode_utf8(ret.acpi_object_name_spec()) =~= bytes@[size_of::<AnddHeader>()..],
    )]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let header = AnddHeader::from_bytes(bytes);
        debug_assert_eq!(header.length as usize, bytes.len());

        let header_len = core::mem::size_of::<AnddHeader>();
        let acpi_object_name = core::str::from_utf8(&bytes[header_len..])
            .unwrap()
            .to_owned();

        Self {
            header,
            acpi_object_name,
        }
    }
}

// Auxiliary proof functions

verus! {

/// One accumulation step: the byte pairs of `bytes[start..end)` are the byte
/// pairs of `bytes[start..end-2)` with the last pair appended.
proof fn lemma_path_pairs_step(bytes: Seq<u8>, start: int, end: int)
    requires
        start + 2 <= end <= bytes.len(),
        (end - start) % 2 == 0,
    ensures
        path_pairs_spec(bytes, start, end) == path_pairs_spec(bytes, start, end - 2).push(
            (bytes[end - 2], bytes[end - 1]),
        ),
{
    let f = |i: int| (bytes[start + 2 * i], bytes[start + 2 * i + 1]);
    let n = ((end - start) / 2) as nat;
    let first = path_pairs_spec(bytes, start, end);
    let rest = path_pairs_spec(bytes, start, end - 2);
    assert(first =~= Seq::new(n, f));
    assert(rest =~= Seq::new((n - 1) as nat, f));
    lemma_seq_new_len(n, f);
    lemma_seq_new_len((n - 1) as nat, f);
    lemma_seq_push_len(rest, (bytes[end - 2], bytes[end - 1]));
    assert forall|i: int| 0 <= i < n implies first[i] == rest.push(
        (bytes[end - 2], bytes[end - 1]),
    )[i] by {
        lemma_seq_new_index(n, f, i);
        if i < n - 1 {
            lemma_seq_new_index((n - 1) as nat, f, i);
            lemma_seq_push_index_different(rest, (bytes[end - 2], bytes[end - 1]), i);
        } else {
            lemma_seq_push_index_same(rest, (bytes[end - 2], bytes[end - 1]), i);
        }
    };
    lemma_seq_ext_equal(first, rest.push((bytes[end - 2], bytes[end - 1])));
}

} // verus!
