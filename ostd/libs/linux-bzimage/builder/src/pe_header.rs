// SPDX-License-Identifier: MPL-2.0
//! Big zImage PE/COFF header generation.
//!
//! The definition of the PE/COFF header is in the Microsoft PE/COFF specification:
//! <https://learn.microsoft.com/en-us/windows/win32/debug/pe-format>
//!
//! The reference to the Linux PE header definition:
//! <https://github.com/torvalds/linux/blob/master/include/linux/pe.h>
#![expect(
    non_snake_case,
    reason = "The verified bitflags macro exposes flag names as methods."
)]

use vstd::{
    arithmetic::{div_mod::lemma_mod_multiples_vanish, power2::is_pow2},
    bytes::{spec_u16_to_le_bytes, spec_u32_to_le_bytes},
    prelude::*,
};
use vstd_extra::{
    arithmetic::{lemma_nat_align_up_sound, nat_align_up},
    external::{
        bytemuck::object_bytes,
        xmas_elf::{
            elf_parse_no_unwind, elf_parse_result, elf_program_headers,
            elf_program_headers_readable, header_entry_point, program_header_flags,
        },
    },
};

use crate::mapping::SETUP32_LMA;

use std::{mem::size_of, vec};

use align_ext::AlignExt;
use bytemuck::{Pod, Zeroable};
use serde::Serialize;

use crate::mapping::{LEGACY_SETUP_SEC_SIZE, SetupFileOffset, SetupVA};

// The MS-DOS header.
#[verus_verify]
const MZ_MAGIC: u16 = 0x5a4d; // "MZ"

// The `magic` field in PE header.
#[verus_verify]
const PE_MAGIC: u32 = 0x00004550;

// The `machine` field choices in PE header. Not exhaustive.
#[verus_verify(external_derive(Serialize))]
#[derive(Serialize, Clone, Copy)]
#[repr(u16)]
enum PeMachineType {
    Amd64 = 0x8664,
}

// The `flags` field choices in PE header.
/* The verified macro supplies bitwise contracts, uses public types and flag methods,
 * and needs fixed-width shift operands.
 * Origin Rust:
 * bitflags_upstream::bitflags! {
 *     struct PeFlags: u16 {
 *         const RELOCS_STRIPPED           = 1;
 *         const EXECUTABLE_IMAGE          = 1 << 1;
 *         const LINE_NUMS_STRIPPED        = 1 << 2;
 *         const LOCAL_SYMS_STRIPPED       = 1 << 3;
 *         const AGGRESSIVE_WS_TRIM         = 1 << 4;
 *         const LARGE_ADDRESS_AWARE       = 1 << 5;
 *         const SIXTEEN_BIT_MACHINE       = 1 << 6;
 *         const BYTES_REVERSED_LO         = 1 << 7;
 *         const THIRTY_TWO_BIT_MACHINE    = 1 << 8;
 *         const DEBUG_STRIPPED            = 1 << 9;
 *         const REMOVABLE_RUN_FROM_SWAP   = 1 << 10;
 *         const NET_RUN_FROM_SWAP         = 1 << 11;
 *         const SYSTEM                    = 1 << 12;
 *         const DLL                       = 1 << 13;
 *         const UP_SYSTEM_ONLY            = 1 << 14;
 *     }
 * }
 */
bitflags::bitflags! {
    pub struct PeFlags: u16 {
        const RELOCS_STRIPPED           = 1u16;
        const EXECUTABLE_IMAGE          = 1u16 << 1;
        const LINE_NUMS_STRIPPED        = 1u16 << 2;
        const LOCAL_SYMS_STRIPPED       = 1u16 << 3;
        const AGGRESSIVE_WS_TRIM         = 1u16 << 4;
        const LARGE_ADDRESS_AWARE       = 1u16 << 5;
        const SIXTEEN_BIT_MACHINE       = 1u16 << 6;
        const BYTES_REVERSED_LO         = 1u16 << 7;
        const THIRTY_TWO_BIT_MACHINE    = 1u16 << 8;
        const DEBUG_STRIPPED            = 1u16 << 9;
        const REMOVABLE_RUN_FROM_SWAP   = 1u16 << 10;
        const NET_RUN_FROM_SWAP         = 1u16 << 11;
        const SYSTEM                    = 1u16 << 12;
        const DLL                       = 1u16 << 13;
        const UP_SYSTEM_ONLY            = 1u16 << 14;
    }
}

#[verus_verify(external_derive(Serialize))]
#[derive(Zeroable, Pod, Serialize, Clone, Copy)]
#[repr(C, packed)]
struct PeHdr {
    magic: u32,        // PE magic
    machine: u16,      // machine type
    sections: u16,     // number of sections
    timestamp: u32,    // time_t
    symbol_table: u32, // symbol table offset
    symbols: u32,      // number of symbols
    opt_hdr_size: u16, // size of optional header
    flags: u16,        // flags
}

// The `magic` field in the PE32+ optional header.
#[verus_verify]
const PE32PLUS_OPT_HDR_MAGIC: u16 = 0x020b;

// The `subsys` field choices in the PE32+ optional header. Not exhaustive.
#[verus_verify(external_derive(Serialize))]
#[derive(Serialize, Clone, Copy)]
#[repr(u16)]
enum PeImageSubsystem {
    EfiApplication = 10,
}

#[verus_verify(external_derive(Serialize))]
#[derive(Zeroable, Pod, Serialize, Clone, Copy)]
#[repr(C, packed)]
struct Pe32PlusOptHdr {
    magic: u16,          // file type
    ld_major: u8,        // linker major version
    ld_minor: u8,        // linker minor version
    text_size: u32,      // size of text section(s)
    data_size: u32,      // size of data section(s)
    bss_size: u32,       // size of bss section(s)
    entry_point: u32,    // file offset of entry point
    code_base: u32,      // relative code addr in ram
    image_base: u64,     // preferred load address
    section_align: u32,  // alignment in bytes
    file_align: u32,     // file alignment in bytes
    os_major: u16,       // major OS version
    os_minor: u16,       // minor OS version
    image_major: u16,    // major image version
    image_minor: u16,    // minor image version
    subsys_major: u16,   // major subsystem version
    subsys_minor: u16,   // minor subsystem version
    win32_version: u32,  // reserved, must be 0
    image_size: u32,     // image size
    header_size: u32,    // header size rounded up to file_align
    csum: u32,           // checksum
    subsys: u16,         // subsystem
    dll_flags: u16,      // more flags!
    stack_size_req: u64, // amt of stack requested
    stack_size: u64,     // amt of stack required
    heap_size_req: u64,  // amt of heap requested
    heap_size: u64,      // amt of heap required
    loader_flags: u32,   // reserved, must be 0
    data_dirs: u32,      // number of data dir entries
}

#[verus_verify(external_derive(Serialize))]
#[derive(Zeroable, Pod, Serialize, Clone, Copy)]
#[repr(C, packed)]
struct Pe32PlusOptDataDirEnt {
    /// The RVA is the address of the table relative to the base address of the image when the table is loaded.
    rva: u32,
    size: u32,
}

#[verus_verify]
impl Pe32PlusOptDataDirEnt {
    #[verus_spec(returns (Self { rva: 0, size: 0 }))]
    fn none() -> Self {
        Self { rva: 0, size: 0 }
    }
}

/// The data directories in the PE32+ optional header.
///
/// The `data_dirs` number field in the PE32+ optional header is just an illusion that you can choose to have a
/// subset of the data directories. The actual number of data directories is fixed to 16 and you can only ignore
/// data directories at the end of the list. We ignore data directories after the 8th as what Linux do.
#[verus_verify(external_derive(Serialize))]
#[derive(Zeroable, Pod, Serialize, Clone, Copy)]
#[repr(C, packed)]
struct Pe32PlusOptDataDirs {
    export_table: Pe32PlusOptDataDirEnt,
    import_table: Pe32PlusOptDataDirEnt,
    resource_table: Pe32PlusOptDataDirEnt,
    exception_table: Pe32PlusOptDataDirEnt,
    certificate_table: Pe32PlusOptDataDirEnt,
    base_relocation_table: Pe32PlusOptDataDirEnt,
}

#[verus_verify]
impl Pe32PlusOptDataDirs {
    #[verus_spec(returns 6usize)]
    fn num_dirs() -> usize {
        size_of::<Self>() / size_of::<Pe32PlusOptDataDirEnt>()
    }
}

// The `flags` field choices in the PE section header.
// Excluding the alignment flags, which is not bitflags.
/* The upstream bitflags operations have no Verus contracts; the verified macro
 * preserves their raw masks for section-header construction.
 * Origin Rust: bitflags::bitflags! {
 */
bitflags::bitflags! {
    /* The verified macro's public trait contracts require public flag helpers.
     * The enclosing pe_header module is private.
     * Origin Rust: struct PeSectionHdrFlags: u32 {
     */
    pub struct PeSectionHdrFlags: u32 {
        /* Explicit u32 operands give the verified macro fixed-width shift models.
         * Origin Rust:
         * const CNT_CODE                  = 1 << 5;
         * const CNT_INITIALIZED_DATA      = 1 << 6;
         * const CNT_UNINITIALIZED_DATA    = 1 << 7;
         * const LNK_INFO                  = 1 << 9;
         * const LNK_REMOVE                = 1 << 11;
         * const LNK_COMDAT                = 1 << 12;
         * const GPREL                     = 1 << 15;
         * const MEM_PURGEABLE             = 1 << 16;
         * const LNK_NRELOC_OVFL           = 1 << 24;
         * const MEM_DISCARDABLE           = 1 << 25;
         * const MEM_NOT_CACHED            = 1 << 26;
         * const MEM_NOT_PAGED             = 1 << 27;
         * const MEM_SHARED                = 1 << 28;
         * const MEM_EXECUTE               = 1 << 29;
         * const MEM_READ                  = 1 << 30;
         * const MEM_WRITE                 = 1 << 31;
         */
        const CNT_CODE                  = 1u32 << 5;
        const CNT_INITIALIZED_DATA      = 1u32 << 6;
        const CNT_UNINITIALIZED_DATA    = 1u32 << 7;
        const LNK_INFO                  = 1u32 << 9;
        const LNK_REMOVE                = 1u32 << 11;
        const LNK_COMDAT                = 1u32 << 12;
        const GPREL                     = 1u32 << 15;
        const MEM_PURGEABLE             = 1u32 << 16;
        const LNK_NRELOC_OVFL           = 1u32 << 24;
        const MEM_DISCARDABLE           = 1u32 << 25;
        const MEM_NOT_CACHED            = 1u32 << 26;
        const MEM_NOT_PAGED             = 1u32 << 27;
        const MEM_SHARED                = 1u32 << 28;
        const MEM_EXECUTE               = 1u32 << 29;
        const MEM_READ                  = 1u32 << 30;
        const MEM_WRITE                 = 1u32 << 31;
    }
}

#[verus_verify(external_derive(Serialize))]
#[derive(Zeroable, Pod, Serialize, Clone, Copy)]
#[repr(C, packed)]
struct PeSectionHdr {
    name: [u8; 8],        // name or "/12\0" string tbl offset
    virtual_size: u32,    // size of loaded section in RAM
    virtual_address: u32, // relative virtual address
    raw_data_size: u32,   // size of the section
    data_addr: u32,       // file pointer to first page of sec
    relocs: u32,          // file pointer to relocation entries
    line_numbers: u32,    // line numbers!
    num_relocs: u16,      // number of relocations
    num_lin_numbers: u16, // srsly.
    flags: u32,
}

#[verus_verify]
pub(super) const SECTION_ALIGNMENT: usize = 4096;
#[verus_verify]
const FILE_ALIGNMENT: usize = 512;

/// Constructs the DOS prefix and PE/COFF headers for the setup ELF.
///
/// # Verified Properties
/// For inputs satisfying `valid_setup_elf`, all computed header fields match
/// their models and the returned 368 bytes concatenate the DOS prefix and
/// packed headers in order. External parsing and object representations are
/// trusted through the contracts in `vstd_extra::external`.
#[verus_verify]
#[verus_spec(bin =>
    requires valid_setup_elf(setup_elf),
    ensures
        bin@.len() == 368,
        bin@ == pe_coff_bytes_spec(&elf_parse_result(setup_elf)->Ok_0),
)]
pub(crate) fn make_pe_coff_header(setup_elf: &[u8]) -> Vec<u8> {
    let elf = xmas_elf::ElfFile::new(setup_elf).unwrap();
    let mut bin = Vec::<u8>::new();

    // PE header
    let mut pe_hdr = PeHdr {
        magic: PE_MAGIC,
        machine: PeMachineType::Amd64 as u16,
        sections: 0, // this field will be modified later
        timestamp: 0,
        symbol_table: 0,
        symbols: 1, // I don't know why, Linux header.S says it's 1
        opt_hdr_size: (size_of::<Pe32PlusOptHdr>() + size_of::<Pe32PlusOptDataDirs>()) as u16,
        /* The verified macro exposes flags as methods with bitwise contracts.
         * Origin Rust: flags: (PeFlags::EXECUTABLE_IMAGE | PeFlags::DEBUG_STRIPPED | PeFlags::LINE_NUMS_STRIPPED).bits,
         */
        flags: (PeFlags::EXECUTABLE_IMAGE()
            | PeFlags::DEBUG_STRIPPED()
            | PeFlags::LINE_NUMS_STRIPPED())
        .bits(),
    };

    let sec_hdrs = build_pe_sec_headers_from(&elf);

    // PE32+ optional header
    let pe_opt_hdr = Pe32PlusOptHdr {
        magic: PE32PLUS_OPT_HDR_MAGIC,
        ld_major: 0x02, // there's no linker to this extent, we do linking by ourselves
        ld_minor: 0x14,
        text_size: sec_hdrs.text.raw_data_size,
        data_size: sec_hdrs.rodata.raw_data_size + sec_hdrs.data.raw_data_size,
        bss_size: 0, // bss size is irrelevant
        entry_point: (elf.header.pt2.entry_point() - sec_hdrs.base as u64) as u32,
        code_base: sec_hdrs.text.virtual_address,
        image_base: 0,
        section_align: SECTION_ALIGNMENT as u32,
        file_align: FILE_ALIGNMENT as u32,
        os_major: 0,
        os_minor: 0,
        image_major: 0x3, // see linux/pe.h for more info
        image_minor: 0,
        subsys_major: 0,
        subsys_minor: 0,
        win32_version: 0,
        image_size: sec_hdrs.data.virtual_address + sec_hdrs.data.virtual_size,
        header_size: LEGACY_SETUP_SEC_SIZE as u32,
        csum: 0,
        subsys: PeImageSubsystem::EfiApplication as u16,
        dll_flags: 0x100, // NX compatible
        stack_size_req: 0,
        stack_size: 0,
        heap_size_req: 0,
        heap_size: 0,
        loader_flags: 0,
        data_dirs: Pe32PlusOptDataDirs::num_dirs() as u32,
    };

    let pe_opt_hdr_data_dirs = Pe32PlusOptDataDirs {
        export_table: Pe32PlusOptDataDirEnt::none(),
        import_table: Pe32PlusOptDataDirEnt::none(),
        resource_table: Pe32PlusOptDataDirEnt::none(),
        exception_table: Pe32PlusOptDataDirEnt::none(),
        certificate_table: Pe32PlusOptDataDirEnt::none(),
        base_relocation_table: Pe32PlusOptDataDirEnt::none(),
    };

    // PE section headers
    let AllPeSectionHdrs {
        base: _,
        text,
        rodata,
        data,
    } = sec_hdrs;
    let sec_hdr_vec = vec![text, rodata, data];

    // Write the MS-DOS header
    bin.extend_from_slice(&MZ_MAGIC.to_le_bytes());
    // Write the MS-DOS stub at 0x3c
    bin.extend_from_slice(&[0x0; 0x3c - 0x2]);
    // Write the PE header offset, the header is right after the offset field
    bin.extend_from_slice(&(0x3cu32 + size_of::<u32>() as u32).to_le_bytes());

    // Write the PE header
    pe_hdr.sections = sec_hdr_vec.len() as u16;
    proof! {
        assert(((1u16 << 1) | (1u16 << 9) | (1u16 << 2)) == 0x206u16) by (bit_vector);
    }
    bin.extend_from_slice(bytemuck::bytes_of(&pe_hdr));
    // Write the PE32+ optional header
    bin.extend_from_slice(bytemuck::bytes_of(&pe_opt_hdr));
    bin.extend_from_slice(bytemuck::bytes_of(&pe_opt_hdr_data_dirs));
    // Write the PE section headers
    proof_decl! {
        let ghost prefix = bin@;
        let ghost section_headers = sec_hdr_vec@;
        let ghost expected = pe_coff_bytes_spec(&elf);
    }
    #[verus_spec(sec_iter =>
        invariant
            sec_iter.seq() == section_headers,
            section_headers.len() == 3,
            section_headers[..3] == section_headers,
            bin@.len() == 248 + 40 * sec_iter.index(),
            bin@ == prefix + section_header_bytes(sec_iter.seq()[..sec_iter.index()]),
            prefix + section_header_bytes(section_headers) == expected,
        ensures
            bin@ == expected,
            bin@.len() == 368,
    )]
    for sec_hdr in sec_hdr_vec {
        proof! {
            let next = sec_iter.seq()[..sec_iter.index() + 1];
            assert(next.drop_last() == sec_iter.seq()[..sec_iter.index()]);
        }
        bin.extend_from_slice(bytemuck::bytes_of(&sec_hdr));
    }

    bin
}

#[verus_verify]
impl PeSectionHdr {
    #[verus_spec(returns Self::new_text_spec(virtual_size, virtual_address, raw_data_size, data_addr))]
    fn new_text(
        virtual_size: u32,
        virtual_address: u32,
        raw_data_size: u32,
        data_addr: u32,
    ) -> Self {
        proof! {
            assert(((1u32 << 5) | (1u32 << 30) | (1u32 << 29)) == 0x6000_0020u32)
                by (bit_vector);
        }
        Self {
            name: [b'.', b't', b'e', b'x', b't', 0, 0, 0],
            virtual_size,
            virtual_address,
            raw_data_size,
            data_addr,
            relocs: 0,
            line_numbers: 0,
            num_relocs: 0,
            num_lin_numbers: 0,
            /* The verified bitflags macro exposes flags as functions.
             * Origin Rust: flags: (PeSectionHdrFlags::CNT_CODE
             *     | PeSectionHdrFlags::MEM_READ
             *     | PeSectionHdrFlags::MEM_EXECUTE)
             *     .bits(),
             */
            flags: (PeSectionHdrFlags::CNT_CODE()
                | PeSectionHdrFlags::MEM_READ()
                | PeSectionHdrFlags::MEM_EXECUTE())
            .bits(),
        }
    }

    #[verus_spec(returns Self::new_data_spec(virtual_size, virtual_address, raw_data_size, data_addr))]
    fn new_data(
        virtual_size: u32,
        virtual_address: u32,
        raw_data_size: u32,
        data_addr: u32,
    ) -> Self {
        proof! {
            assert(((1u32 << 6) | (1u32 << 30) | (1u32 << 31)) == 0xc000_0040u32)
                by (bit_vector);
        }
        Self {
            name: [b'.', b'd', b'a', b't', b'a', 0, 0, 0],
            virtual_size,
            virtual_address,
            raw_data_size,
            data_addr,
            relocs: 0,
            line_numbers: 0,
            num_relocs: 0,
            num_lin_numbers: 0,
            /* The verified bitflags macro exposes flags as functions.
             * Origin Rust: flags: (PeSectionHdrFlags::CNT_INITIALIZED_DATA
             *     | PeSectionHdrFlags::MEM_READ
             *     | PeSectionHdrFlags::MEM_WRITE)
             *     .bits(),
             */
            flags: (PeSectionHdrFlags::CNT_INITIALIZED_DATA()
                | PeSectionHdrFlags::MEM_READ()
                | PeSectionHdrFlags::MEM_WRITE())
            .bits(),
        }
    }

    #[verus_spec(returns Self::new_rodata_spec(virtual_size, virtual_address, raw_data_size, data_addr))]
    fn new_rodata(
        virtual_size: u32,
        virtual_address: u32,
        raw_data_size: u32,
        data_addr: u32,
    ) -> Self {
        proof! {
            assert(((1u32 << 6) | (1u32 << 30)) == 0x4000_0040u32) by (bit_vector);
        }
        Self {
            name: [b'.', b'r', b'o', b'd', b'a', b't', b'a', 0],
            virtual_size,
            virtual_address,
            raw_data_size,
            data_addr,
            relocs: 0,
            line_numbers: 0,
            num_relocs: 0,
            num_lin_numbers: 0,
            /* The verified bitflags macro exposes flags as functions.
             * Origin Rust: flags: (PeSectionHdrFlags::CNT_INITIALIZED_DATA | PeSectionHdrFlags::MEM_READ).bits(),
             */
            flags: (PeSectionHdrFlags::CNT_INITIALIZED_DATA() | PeSectionHdrFlags::MEM_READ())
                .bits(),
        }
    }
}

#[verus_verify]
struct AllPeSectionHdrs {
    /// The base for all virtual addresses in the PE/COFF header.
    ///
    /// We need this because we want to set `image_base` in `Pe32PlusOptHdr` to zero. Otherwise
    /// some UEFI firmware will refuse to load the image. (FIXME: This is what Linux does, but I
    /// can't find any specification that says we have to do this).
    base: usize,
    text: PeSectionHdr,
    rodata: PeSectionHdr,
    data: PeSectionHdr,
}

#[verus_verify]
#[verus_spec(
    requires
        elf_program_headers_readable(elf),
        valid_pe_segments(elf_program_headers(elf)),
    returns all_pe_section_headers_spec(elf_program_headers(elf)),
)]
fn build_pe_sec_headers_from(elf: &xmas_elf::ElfFile) -> AllPeSectionHdrs {
    #[verus_verify]
    #[verus_spec(ret =>
        requires
            segment.virtual_addr() <= usize::MAX,
            segment.mem_size() <= usize::MAX,
            valid_pe_section(segment.virtual_addr() as usize, segment.mem_size() as usize, base),
            f.requires(pe_section_constructor_args(
                segment.virtual_addr() as usize, segment.mem_size() as usize, base,
            )),
        ensures
            f.ensures(pe_section_constructor_args(
                segment.virtual_addr() as usize, segment.mem_size() as usize, base,
            ), ret),
            ({
                let addr = segment.virtual_addr() as usize;
                let size = segment.mem_size() as usize;
                let layout = pe_section_layout_spec(addr, size, base);
                &&& size <= layout.0 < size + SECTION_ALIGNMENT
                &&& layout.0 % (SECTION_ALIGNMENT as u32) == 0
                &&& layout.1 % (SECTION_ALIGNMENT as u32) == 0
                &&& layout.2 % (FILE_ALIGNMENT as u32) == 0
                &&& base == SETUP32_LMA - LEGACY_SETUP_SEC_SIZE ==> layout.1 == layout.2
            }),
    )]
    fn new_pe_sec_header(
        segment: &xmas_elf::program::ProgramHeader,
        base: usize,
        f: impl FnOnce(u32, u32, u32, u32) -> PeSectionHdr,
    ) -> PeSectionHdr {
        proof! {
            reveal(is_pow2);
            assert(is_pow2(SECTION_ALIGNMENT as int)) by (compute_only);
            lemma_nat_align_up_sound(segment.mem_size() as nat, SECTION_ALIGNMENT as nat);
            lemma_mod_multiples_vanish(
                (LEGACY_SETUP_SEC_SIZE - SETUP32_LMA) / (FILE_ALIGNMENT as int),
                segment.virtual_addr() as int,
                FILE_ALIGNMENT as int,
            );
        }
        assert_eq!(
            segment.virtual_addr() as usize % SECTION_ALIGNMENT,
            0,
            "the segment virtual address must be aligned",
        );
        let va = SetupVA::from(segment.virtual_addr() as usize);
        let len = (segment.mem_size() as usize).align_up(SECTION_ALIGNMENT);
        f(
            len as u32,
            (usize::from(va) - base) as u32,
            len as u32,
            usize::from(SetupFileOffset::from(va)) as u32,
        )
    }

    let segments = elf.program_iter().collect::<Vec<_>>();

    // There should be four segments: "header", "text", "rodata", and "data".
    assert_eq!(segments.len(), 4, "there must be four segments");
    assert!(
        segments[1].flags().is_execute(),
        "the text segment must be executable",
    );
    assert!(
        segments[2].flags().is_read(),
        "the text segment must be readable",
    );
    assert!(
        segments[3].flags().is_write(),
        "the data segment must be writable",
    );

    // The "header" segment won't be loaded. See the linker script for details.

    let base = segments[1].virtual_addr() as usize - SECTION_ALIGNMENT;
    AllPeSectionHdrs {
        base,
        text: new_pe_sec_header(&segments[1], base, PeSectionHdr::new_text),
        rodata: new_pe_sec_header(&segments[2], base, PeSectionHdr::new_rodata),
        data: new_pe_sec_header(&segments[3], base, PeSectionHdr::new_data),
    }
}
verus! {

global layout PeHdr is size == 24, align == 1;

global layout Pe32PlusOptHdr is size == 112, align == 1;

global layout Pe32PlusOptDataDirEnt is size == 8, align == 1;

global layout Pe32PlusOptDataDirs is size == 48, align == 1;

global layout PeSectionHdr is size == 40, align == 1;

/// The four ELF segments and the address/size bounds required by the original
/// assertions and per-segment constructor. These are caller obligations.
closed spec fn valid_pe_segments(segments: Seq<xmas_elf::program::ProgramHeader<'_>>) -> bool {
    &&& segments.len() == 4
    &&& program_header_flags(&segments[1]).0 & 1 == 1
    &&& program_header_flags(&segments[2]).0 & 4 == 4
    &&& program_header_flags(&segments[3]).0 & 2 == 2
    &&& SECTION_ALIGNMENT <= segments[1].virtual_addr() <= usize::MAX
    &&& forall|i: int|
        1 <= i < 4 ==> {
            &&& #[trigger] segments[i].virtual_addr() <= usize::MAX
            &&& segments[i].mem_size() <= usize::MAX
            &&& valid_pe_section(
                segments[i].virtual_addr() as usize,
                segments[i].mem_size() as usize,
                (segments[1].virtual_addr() - SECTION_ALIGNMENT) as usize,
            )
        }
}

/// The base and three exact section headers computed from the ELF segments.
closed spec fn all_pe_section_headers_spec(
    segments: Seq<xmas_elf::program::ProgramHeader<'_>>,
) -> AllPeSectionHdrs {
    let base = (segments[1].virtual_addr() - SECTION_ALIGNMENT) as usize;
    let text = pe_section_layout_spec(
        segments[1].virtual_addr() as usize,
        segments[1].mem_size() as usize,
        base,
    );
    let rodata = pe_section_layout_spec(
        segments[2].virtual_addr() as usize,
        segments[2].mem_size() as usize,
        base,
    );
    let data = pe_section_layout_spec(
        segments[3].virtual_addr() as usize,
        segments[3].mem_size() as usize,
        base,
    );
    AllPeSectionHdrs {
        base,
        text: PeSectionHdr::new_text_spec(text.0, text.1, text.0, text.2),
        rodata: PeSectionHdr::new_rodata_spec(rodata.0, rodata.1, rodata.0, rodata.2),
        data: PeSectionHdr::new_data_spec(data.0, data.1, data.0, data.2),
    }
}

/// Successful, readable setup ELF input whose computed optional-header fields
/// fit their PE widths. Malformed-input panic paths remain executable.
pub(crate) closed spec fn valid_setup_elf(input: &[u8]) -> bool {
    &&& elf_parse_no_unwind(input)
    &&& elf_parse_result(input) matches Ok(elf) && {
        let headers = all_pe_section_headers_spec(elf_program_headers(&elf));
        &&& elf_program_headers_readable(&elf)
        &&& valid_pe_segments(elf_program_headers(&elf))
        &&& headers.base <= header_entry_point(&elf.header.pt2) <= headers.base + u32::MAX
        &&& headers.rodata.raw_data_size + headers.data.raw_data_size <= u32::MAX
        &&& headers.data.virtual_address + headers.data.virtual_size <= u32::MAX
    }
}

/// The PE/COFF fixed header after setting its three-section count.
closed spec fn pe_header_spec() -> PeHdr {
    PeHdr {
        magic: PE_MAGIC,
        machine: 0x8664,
        sections: 3,
        timestamp: 0,
        symbol_table: 0,
        symbols: 1,
        opt_hdr_size: 160,
        flags: 0x206,
    }
}

/// Every field of the PE32+ optional header computed from the ELF layout.
closed spec fn pe_optional_header_spec(
    elf: &xmas_elf::ElfFile<'_>,
    headers: AllPeSectionHdrs,
) -> Pe32PlusOptHdr {
    Pe32PlusOptHdr {
        magic: PE32PLUS_OPT_HDR_MAGIC,
        ld_major: 2,
        ld_minor: 0x14,
        text_size: headers.text.raw_data_size,
        data_size: (headers.rodata.raw_data_size + headers.data.raw_data_size) as u32,
        bss_size: 0,
        entry_point: (header_entry_point(&elf.header.pt2) - headers.base) as u32,
        code_base: headers.text.virtual_address,
        image_base: 0,
        section_align: SECTION_ALIGNMENT as u32,
        file_align: FILE_ALIGNMENT as u32,
        os_major: 0,
        os_minor: 0,
        image_major: 3,
        image_minor: 0,
        subsys_major: 0,
        subsys_minor: 0,
        win32_version: 0,
        image_size: (headers.data.virtual_address + headers.data.virtual_size) as u32,
        header_size: LEGACY_SETUP_SEC_SIZE as u32,
        csum: 0,
        subsys: 10,
        dll_flags: 0x100,
        stack_size_req: 0,
        stack_size: 0,
        heap_size_req: 0,
        heap_size: 0,
        loader_flags: 0,
        data_dirs: 6,
    }
}

/// The six unused data-directory entries are zero.
closed spec fn pe_data_dirs_spec() -> Pe32PlusOptDataDirs {
    let zero = Pe32PlusOptDataDirEnt { rva: 0, size: 0 };
    Pe32PlusOptDataDirs {
        export_table: zero,
        import_table: zero,
        resource_table: zero,
        exception_table: zero,
        certificate_table: zero,
        base_relocation_table: zero,
    }
}

/// Byte concatenation in section order, using bytemuck's object representation.
closed spec fn section_header_bytes(headers: Seq<PeSectionHdr>) -> Seq<u8>
    decreases headers.len(),
{
    if headers.len() == 0 {
        Seq::empty()
    } else {
        section_header_bytes(headers.drop_last()) + object_bytes(headers.last())
    }
}

/// The complete DOS prefix, PE/COFF header, optional header, and three sections.
/// Packed object representations remain the audited bytemuck boundary.
pub(crate) closed spec fn pe_coff_bytes_spec(elf: &xmas_elf::ElfFile<'_>) -> Seq<u8> {
    let headers = all_pe_section_headers_spec(elf_program_headers(elf));
    spec_u16_to_le_bytes(MZ_MAGIC) + Seq::new(58, |i: int| 0u8) + spec_u32_to_le_bytes(64)
        + object_bytes(pe_header_spec()) + object_bytes(pe_optional_header_spec(elf, headers))
        + object_bytes(pe_data_dirs_spec()) + section_header_bytes(
        seq![headers.text, headers.rodata, headers.data],
    )
}

/// Input bounds for aligned PE section fields without narrowing or arithmetic overflow.
closed spec fn valid_pe_section(virtual_addr: usize, mem_size: usize, base: usize) -> bool {
    &&& virtual_addr % SECTION_ALIGNMENT == 0
    &&& base % SECTION_ALIGNMENT == 0
    &&& base <= virtual_addr
    &&& SETUP32_LMA - LEGACY_SETUP_SEC_SIZE <= virtual_addr <= usize::MAX - LEGACY_SETUP_SEC_SIZE
    &&& virtual_addr - base <= u32::MAX
    &&& virtual_addr + LEGACY_SETUP_SEC_SIZE - SETUP32_LMA <= u32::MAX
    &&& mem_size + SECTION_ALIGNMENT - 1 <= usize::MAX
    &&& nat_align_up(mem_size as nat, SECTION_ALIGNMENT as nat) <= u32::MAX
}

/// The aligned section size, RVA, and flat-image file offset.
closed spec fn pe_section_layout_spec(virtual_addr: usize, mem_size: usize, base: usize) -> (
    u32,
    u32,
    u32,
) {
    (
        nat_align_up(mem_size as nat, SECTION_ALIGNMENT as nat) as u32,
        (virtual_addr - base) as u32,
        (virtual_addr + LEGACY_SETUP_SEC_SIZE - SETUP32_LMA) as u32,
    )
}

/// The four arguments passed by the original helper to its constructor callback.
closed spec fn pe_section_constructor_args(virtual_addr: usize, mem_size: usize, base: usize) -> (
    u32,
    u32,
    u32,
    u32,
) {
    let layout = pe_section_layout_spec(virtual_addr, mem_size, base);
    (layout.0, layout.1, layout.0, layout.2)
}

} // verus!
macro_rules! impl_pe_section_constructor_specs {
    ($(($name:ident, $section_name:expr, $flags:expr)),* $(,)?) => {
        verus! {
        impl PeSectionHdr {
            $(
                /// The exact section header, including its name, permissions, and zero relocation fields.
                closed spec fn $name(
                    virtual_size: u32,
                    virtual_address: u32,
                    raw_data_size: u32,
                    data_addr: u32,
                ) -> Self {
                    Self {
                        name: $section_name,
                        virtual_size,
                        virtual_address,
                        raw_data_size,
                        data_addr,
                        relocs: 0,
                        line_numbers: 0,
                        num_relocs: 0,
                        num_lin_numbers: 0,
                        flags: $flags,
                    }
                }
            )*
        }
        }
    };
}
impl_pe_section_constructor_specs! {
    (new_text_spec, [b'.', b't', b'e', b'x', b't', 0, 0, 0], 0x6000_0020u32),
    (new_data_spec, [b'.', b'd', b'a', b't', b'a', 0, 0, 0], 0xc000_0040u32),
    (new_rodata_spec, [b'.', b'r', b'o', b'd', b'a', b't', b'a', 0], 0x4000_0040u32),
}
