// SPDX-License-Identifier: MPL-2.0
//! Trusted specifications for xmas-elf 0.10.0's parsing and header access.
use vstd::{
    layout::{align_of, size_of},
    prelude::*,
    std_specs::iter::IteratorSpec,
};
use xmas_elf::{
    ElfFile,
    header::{Class, Header, HeaderPt1, HeaderPt2, HeaderPt2_, Machine_, Type_ as HeaderType},
    program::{
        Flags, ProgramHeader, ProgramHeader32, ProgramHeader64, SegmentData, TYPE_GNU_RELRO,
        TYPE_HIOS, TYPE_HIPROC, TYPE_LOOS, TYPE_LOPROC, Type, Type_,
    },
    sections::{Rela, SectionData, SectionHeader, SectionHeader_, ShType},
};

use super::slice::as_ptr_spec;
use crate::panic::allowed_to_panic_if;

verus! {

#[verifier::external_type_specification]
pub struct ExElfFile<'a>(ElfFile<'a>);

#[verifier::external_type_specification]
pub struct ExHeader<'a>(Header<'a>);

// Its Class_, Data_, Version_, and OsAbi_ fields wrap private bytes.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExHeaderPt1(HeaderPt1);

#[verifier::external_type_specification]
pub struct ExHeaderClass(Class);

#[verifier::external_type_specification]
pub struct ExHeaderPt2<'a>(HeaderPt2<'a>);

#[verifier::external_type_specification]
pub struct ExHeaderPt2Raw<P>(HeaderPt2_<P>);

type ElfHeader32 = HeaderPt2_<u32>;

type ElfHeader64 = HeaderPt2_<u64>;

// Check the sizes and alignments used by the parsing predicates against Rust's layouts.
global layout HeaderPt1 is size == 16, align == 1;

global layout ElfHeader32 is size == 36, align == 4;

global layout ElfHeader64 is size == 48, align == 8;

global layout ProgramHeader32 is size == 32, align == 4;

global layout ProgramHeader64 is size == 56, align == 8;

#[verifier::external_type_specification]
pub struct ExHeaderType(HeaderType);

// Machine_ has a private u16 field; Verus requires an opaque proxy.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExHeaderMachine(Machine_);

/// The parser's normal return value, including its original error string.
pub uninterp spec fn elf_parse_result<'a>(input: &'a [u8]) -> Result<ElfFile<'a>, &'static str>;

/// <https://docs.rs/xmas-elf/0.10.0/src/xmas_elf/header.rs.html#9-52>
pub open spec fn elf_parse_no_unwind(input: &[u8]) -> bool {
    if input@.len() < 16 || input@[..4] != seq![0x7fu8, b'E', b'L', b'F'] {
        true
    } else {
        let addr_pt2 = as_ptr_spec(input).addr() + 16;
        match input@[4] {
            1 => input@.len() < 52 || addr_pt2 % 4 == 0,
            2 => input@.len() < 64 || addr_pt2 % 8 == 0,
            _ => true,
        }
    }
}

/// The sequence yielded before ProgramIter first returns None.
pub uninterp spec fn elf_program_headers<'a>(elf: &ElfFile<'a>) -> Seq<ProgramHeader<'a>>;

/// The class getter's value; HeaderPt1's integer wrapper fields remain opaque.
pub uninterp spec fn header_class(header: &HeaderPt1) -> Class;

/// Empty tables or zero offsets/strides stop iteration without reading an entry.
/// Otherwise every entry must fit in the input, hold the class-specific header,
/// and be aligned. The end bound also excludes arithmetic overflow in any build
/// profile. Program-header class comes from pt1, even for a manually built ElfFile.
pub open spec fn elf_program_headers_readable(elf: &ElfFile<'_>) -> bool {
    let (offset, entry_size, count) = match elf.header.pt2 {
        HeaderPt2::Header32(h) => (h.ph_offset as u64, h.ph_entry_size, h.ph_count),
        HeaderPt2::Header64(h) => (h.ph_offset, h.ph_entry_size, h.ph_count),
    };
    if count == 0 || offset == 0 || entry_size == 0 {
        true
    } else {
        let (size, align): (int, int) = match elf.header.pt1.class() {
            Class::ThirtyTwo => (32, 4),
            Class::SixtyFour => (56, 8),
            _ => (0, 0),
        };
        // parse_program_header casts ph_offset to usize before adding each index.
        let start = if offset <= usize::MAX {
            offset as int
        } else {
            (offset as int) % (usize::MAX + 1)
        };
        let end = start + count * entry_size;
        &&& align > 0
        &&& end <= usize::MAX
        &&& end <= elf.input@.len()
        &&& entry_size >= size
        &&& (as_ptr_spec(elf.input).addr() + start) % align == 0
        &&& (count == 1 || (entry_size as int) % align == 0)
    }
}

#[verifier::when_used_as_spec(header_class)]
pub assume_specification[ HeaderPt1::class ](header: &HeaderPt1) -> Class
    returns
        header_class(header),
    opens_invariants none
    no_unwind
;

/// The entry-point field, widened from either ELF header representation to u64.
pub open spec fn header_entry_point(header: &HeaderPt2<'_>) -> u64 {
    match *header {
        HeaderPt2::Header32(h) => h.entry_point as u64,
        HeaderPt2::Header64(h) => h.entry_point,
    }
}

/// ElfFile::new delegates to parse_header and stores the original input slice on success.
pub assume_specification<'a>[ ElfFile::<'a>::new ](input: &'a [u8]) -> (result: Result<
    ElfFile<'a>,
    &'static str,
>)
    ensures
        result matches Ok(elf) ==> {
            &&& elf.input == input
            &&& as_ptr_spec(elf.input) == as_ptr_spec(input)
        },
    returns
        elf_parse_result(input),
    opens_invariants none
    no_unwind when elf_parse_no_unwind(input)
;

/// The constructor returns ProgramIter at index zero. Its collect result follows
/// the first-None sequence only when the program-table reads cannot panic.
pub assume_specification<'a, 'b>[ ElfFile::<'a>::program_iter ](elf: &'b ElfFile<'a>) -> (iter:
    impl Iterator<Item = ProgramHeader<'a>> + 'b)
    ensures
        elf_program_headers_readable(elf) ==> {
            &&& IteratorSpec::obeys_prophetic_iter_laws(&iter)
            &&& IteratorSpec::remaining(&iter) == elf_program_headers(elf)
            &&& IteratorSpec::produces(&iter) == Seq::new(
                elf_program_headers(elf).len(),
                |i: int| true,
            )
            &&& IteratorSpec::decrease(&iter) == Some(elf_program_headers(elf).len())
        },
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(header_entry_point)]
pub assume_specification<'a>[ HeaderPt2::<'a>::entry_point ](header: &HeaderPt2<'a>) -> u64
    returns
        header_entry_point(header),
    opens_invariants none
    no_unwind
;

#[verifier::external_type_specification]
pub struct ExProgramHeader<'a>(ProgramHeader<'a>);

#[verifier::external_type_specification]
pub struct ExProgramHeader32(ProgramHeader32);

#[verifier::external_type_specification]
pub struct ExProgramHeader64(ProgramHeader64);

#[verifier::external_type_specification]
pub struct ExProgramFlags(Flags);

// Type_ has a private u32 field; Verus requires an opaque proxy.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExProgramType(Type_);

#[verifier::external_type_specification]
pub struct ExProgramTypeValue(Type);

pub assume_specification[ <Type as core::cmp::PartialEq>::eq ](left: &Type, right: &Type) -> bool
    returns
        *left == *right,
;

#[verifier::external_type_specification]
pub struct ExSegmentData<'a>(SegmentData<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
pub struct ExDynamic<P>(xmas_elf::dynamic::Dynamic<P>) where
    xmas_elf::dynamic::Tag_<P>: core::fmt::Debug,
;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
pub struct ExDynamicTag<P>(xmas_elf::dynamic::Tag_<P>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExNoteHeader(xmas_elf::sections::NoteHeader);

/// The private u32 stored by Type_. Only its representation remains opaque;
/// decoding below follows xmas-elf 0.10.0's Type_::as_type.
pub uninterp spec fn program_type_raw(type_: Type_) -> u32;

// Constants from program.rs; keep their trusted values at the external boundary.
pub assume_specification[ xmas_elf::program::TYPE_LOOS ] -> u32
    returns
        0x60000000u32,
;

pub assume_specification[ xmas_elf::program::TYPE_HIOS ] -> u32
    returns
        0x6fffffffu32,
;

pub assume_specification[ xmas_elf::program::TYPE_LOPROC ] -> u32
    returns
        0x70000000u32,
;

pub assume_specification[ xmas_elf::program::TYPE_HIPROC ] -> u32
    returns
        0x7fffffffu32,
;

pub assume_specification[ xmas_elf::program::TYPE_GNU_RELRO ] -> u32
    returns
        0x6474e552u32,
;

/// GNU_RELRO takes precedence over the enclosing OS-specific range.
pub open spec fn program_type_from_raw(raw: u32) -> Result<Type, &'static str> {
    match raw {
        0 => Ok(Type::Null),
        1 => Ok(Type::Load),
        2 => Ok(Type::Dynamic),
        3 => Ok(Type::Interp),
        4 => Ok(Type::Note),
        5 => Ok(Type::ShLib),
        6 => Ok(Type::Phdr),
        7 => Ok(Type::Tls),
        _ => if raw == TYPE_GNU_RELRO {
            Ok(Type::GnuRelro)
        } else if TYPE_LOOS <= raw <= TYPE_HIOS {
            Ok(Type::OsSpecific(raw))
        } else if TYPE_LOPROC <= raw <= TYPE_HIPROC {
            Ok(Type::ProcessorSpecific(raw))
        } else {
            Err("Invalid type")
        },
    }
}

pub open spec fn program_type_result(type_: Type_) -> Result<Type, &'static str> {
    program_type_from_raw(program_type_raw(type_))
}

// Derived Default initializes the private u32 to zero.
pub assume_specification[ <Type_ as core::default::Default>::default ]() -> (ret: Type_)
    ensures
        program_type_raw(ret) == 0,
;

pub open spec fn program_header_type(header: &ProgramHeader<'_>) -> Result<Type, &'static str> {
    match *header {
        ProgramHeader::Ph32(h) => program_type_result(h.type_),
        ProgramHeader::Ph64(h) => program_type_result(h.type_),
    }
}

pub open spec fn program_header_file_size(header: &ProgramHeader<'_>) -> u64 {
    match *header {
        ProgramHeader::Ph32(h) => h.file_size as u64,
        ProgramHeader::Ph64(h) => h.file_size,
    }
}

pub open spec fn program_header_offset(header: &ProgramHeader<'_>) -> u64 {
    match *header {
        ProgramHeader::Ph32(h) => h.offset as u64,
        ProgramHeader::Ph64(h) => h.offset,
    }
}

/// raw_data adds the source fields before casting to usize. In ELF32 that
/// addition is u32, even on a 64-bit host. Empty data bypasses the offset.
pub open spec fn program_load_data_readable(header: &ProgramHeader<'_>, input: Seq<u8>) -> bool {
    let offset = header.offset();
    let size = header.file_size();
    size == 0 || {
        &&& match *header {
            ProgramHeader::Ph32(_) => offset + size <= u32::MAX,
            ProgramHeader::Ph64(_) => offset + size <= u64::MAX,
        }
        &&& offset + size <= usize::MAX
        &&& offset + size <= input.len()
    }
}

pub open spec fn program_load_bytes(header: &ProgramHeader<'_>, input: Seq<u8>) -> Seq<u8> {
    let size = header.file_size();
    if size == 0 {
        Seq::empty()
    } else {
        input[header.offset()..header.offset() + size]
    }
}

#[verifier::when_used_as_spec(program_header_type)]
pub assume_specification<'a>[ ProgramHeader::<'a>::get_type ](header: &ProgramHeader<'a>) -> Result<
    Type,
    &'static str,
>
    returns
        program_header_type(header),
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(program_header_file_size)]
pub assume_specification<'a>[ ProgramHeader::<'a>::file_size ](header: &ProgramHeader<'a>) -> u64
    returns
        program_header_file_size(header),
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(program_header_offset)]
pub assume_specification<'a>[ ProgramHeader::<'a>::offset ](header: &ProgramHeader<'a>) -> u64
    returns
        program_header_offset(header),
    opens_invariants none
    no_unwind
;

/// Audited only for Load: get_data delegates to raw_data and returns Undefined.
/// Other segment types include dynamic/note parsing and receive no guarantees.
pub assume_specification<'a>[ ProgramHeader::<'a>::get_data ](
    header: &ProgramHeader<'a>,
    elf: &ElfFile<'a>,
) -> (ret: Result<SegmentData<'a>, &'static str>)
    ensures
        header.get_type() == Ok(Type::Load) && program_load_data_readable(header, elf.input@) ==> {
            ret matches Ok(SegmentData::Undefined(bytes)) && bytes@ == program_load_bytes(
                header,
                elf.input@,
            )
        },
    opens_invariants none
    no_unwind when header.get_type() == Ok(Type::Load) && program_load_data_readable(
    header,
    elf.input@,
)
;

/// The virtual address stored in either ELF program-header representation.
pub open spec fn program_header_virtual_addr(header: &ProgramHeader<'_>) -> u64 {
    match *header {
        ProgramHeader::Ph32(h) => h.virtual_addr as u64,
        ProgramHeader::Ph64(h) => h.virtual_addr,
    }
}

/// The memory size stored in either ELF program-header representation.
pub open spec fn program_header_mem_size(header: &ProgramHeader<'_>) -> u64 {
    match *header {
        ProgramHeader::Ph32(h) => h.mem_size as u64,
        ProgramHeader::Ph64(h) => h.mem_size,
    }
}

/// The flags field in either program-header representation.
pub open spec fn program_header_flags(header: &ProgramHeader<'_>) -> Flags {
    match *header {
        ProgramHeader::Ph32(h) => h.flags,
        ProgramHeader::Ph64(h) => h.flags,
    }
}

#[verifier::when_used_as_spec(program_header_flags)]
pub assume_specification<'a>[ ProgramHeader::<'a>::flags ](header: &ProgramHeader<'a>) -> Flags
    returns
        program_header_flags(header),
    opens_invariants none
    no_unwind
;

pub assume_specification[ Flags::is_execute ](flags: &Flags) -> bool
    returns
        flags.0 & 1 == 1,
    opens_invariants none
    no_unwind
;

pub assume_specification[ Flags::is_read ](flags: &Flags) -> bool
    returns
        flags.0 & 4 == 4,
    opens_invariants none
    no_unwind
;

pub assume_specification[ Flags::is_write ](flags: &Flags) -> bool
    returns
        flags.0 & 2 == 2,
    opens_invariants none
    no_unwind
;

/// Matches `getter!(virtual_addr, u64)` in xmas-elf 0.10.0's `program.rs`.
#[verifier::when_used_as_spec(program_header_virtual_addr)]
pub assume_specification<'a>[ ProgramHeader::<'a>::virtual_addr ](header: &ProgramHeader<'a>) -> u64
    returns
        program_header_virtual_addr(header),
    opens_invariants none
    no_unwind
;

/// Matches `getter!(mem_size, u64)` in xmas-elf 0.10.0's `program.rs`.
#[verifier::when_used_as_spec(program_header_mem_size)]
pub assume_specification<'a>[ ProgramHeader::<'a>::mem_size ](header: &ProgramHeader<'a>) -> u64
    returns
        program_header_mem_size(header),
    opens_invariants none
    no_unwind
;

#[verifier::external_type_specification]
pub struct ExSectionHeader<'a>(SectionHeader<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
pub struct ExSectionHeaderRaw<P>(SectionHeader_<P>);

#[verifier::external_type_specification]
pub struct ExSectionData<'a>(SectionData<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
pub struct ExRela<P>(Rela<P>);

// Other SectionData payloads contain private fields and are only distinguished by variant.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
pub struct ExRel<P>(xmas_elf::sections::Rel<P>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExEntry32(xmas_elf::symbol_table::Entry32);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExEntry64(xmas_elf::symbol_table::Entry64);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDynEntry32(xmas_elf::symbol_table::DynEntry32);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDynEntry64(xmas_elf::symbol_table::DynEntry64);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExHashTable<'a>(xmas_elf::hash::HashTable<'a>);

#[verifier::external_type_specification]
pub struct ExShType(ShType);

/// The private sh_type field as decoded by ShType_::as_sh_type.
pub uninterp spec fn section_kind(section: &SectionHeader<'_>) -> Result<ShType, &'static str>;

#[verifier::when_used_as_spec(section_kind)]
pub assume_specification<'a>[ SectionHeader::<'a>::get_type ](
    section: &SectionHeader<'a>,
) -> Result<ShType, &'static str>
    returns
        section_kind(section),
    opens_invariants none
    no_unwind
;

/// Successful get_name results in SectionIter order, stopping at its first None
/// or panic (including get_name). The flag records whether iteration reached None.
pub uninterp spec fn named_section_scan<'a>(elf: &ElfFile<'a>) -> (
    Seq<(&'a str, SectionHeader<'a>)>,
    bool,
);

/// Ok(Some) stops at the first match. Err means a read panics before a match or exhaustion.
pub open spec fn elf_section_lookup<'a>(elf: &ElfFile<'a>, name: &str) -> Result<
    Option<SectionHeader<'a>>,
    (),
> {
    let count = match elf.header.pt2 {
        HeaderPt2::Header32(h) => h.sh_count,
        HeaderPt2::Header64(h) => h.sh_count,
    };
    if count == 0 {
        Ok(None)
    } else {
        let (sections, exhausted) = named_section_scan(elf);
        let names = sections.map_values(|entry: (&str, SectionHeader<'a>)| entry.0);
        match names.index_of_first(name) {
            Some(i) => Ok(Some(sections[i].1)),
            None => if exhausted {
                Ok(None)
            } else {
                Err(())
            },
        }
    }
}

pub open spec fn elf_section_by_name<'a>(elf: &ElfFile<'a>, name: &str) -> Option<
    SectionHeader<'a>,
> {
    elf_section_lookup(elf, name)->Ok_0
}

#[verifier::when_used_as_spec(elf_section_by_name)]
pub assume_specification<'a>[ ElfFile::<'a>::find_section_by_name ](
    elf: &ElfFile<'a>,
    name: &str,
) -> (result: Option<SectionHeader<'a>>)
    requires
        allowed_to_panic_if(elf_section_lookup(elf, name) is Err),
    ensures
        elf_section_lookup(elf, name) == Ok(result),
    returns
        elf_section_by_name(elf, name),
    opens_invariants none
    no_unwind when elf_section_lookup(elf, name) is Ok
;

/// The sh_offset and sh_size values widened to u64 as in SectionHeader::raw_data.
pub uninterp spec fn section_file_extent(section: &SectionHeader<'_>) -> (u64, u64);

/// On kinds other than Group, Some is the actual decoder result; None indicates
/// that a bounds, layout, or other decoder check panics before producing it.
pub uninterp spec fn section_decode<'a>(section: &SectionHeader<'a>, elf: &ElfFile<'a>) -> Option<
    Result<SectionData<'a>, &'static str>,
>;

pub open spec fn section_data_result<'a>(section: &SectionHeader<'a>, elf: &ElfFile<'a>) -> Result<
    SectionData<'a>,
    &'static str,
> {
    section_decode(section, elf)->Some_0
}

/// raw_data slices the file; zero::read_array then checks the whole array's size and alignment.
pub open spec fn section_data_readable(section: &SectionHeader<'_>, elf: &ElfFile<'_>) -> bool {
    match section.get_type() {
        Err(_) | Ok(ShType::Null) | Ok(ShType::NoBits) => true,
        Ok(ShType::Rela) => {
            let (offset, len) = section_file_extent(section);
            let (size, align) = match elf.header.pt1.class() {
                Class::ThirtyTwo => (size_of::<Rela<u32>>(), align_of::<Rela<u32>>()),
                Class::SixtyFour => (size_of::<Rela<u64>>(), align_of::<Rela<u64>>()),
                _ => (0, 0),
            };
            &&& offset + len <= usize::MAX
            &&& offset + len <= elf.input@.len()
            &&& size > 0 && len as int % (size as int) == 0
            &&& align > 0 && (as_ptr_spec(elf.input).addr() + offset) % (align as int) == 0
        },
        Ok(ShType::Group) => false,
        _ => section_decode(section, elf) is Some,
    }
}

/// xmas-elf 0.10.0 constructs the Group flags reference before validating its
/// alignment and extent. Callers must exclude that kind before decoding.
#[verifier::when_used_as_spec(section_data_result)]
pub assume_specification<'a>[ SectionHeader::<'a>::get_data ](
    section: &SectionHeader<'a>,
    elf: &ElfFile<'a>,
) -> (result: Result<SectionData<'a>, &'static str>)
    requires
        !(section.get_type() matches Ok(ShType::Group)),
        allowed_to_panic_if(!section_data_readable(section, elf)),
    ensures
        section_decode(section, elf) == Some(result),
        result matches Ok(SectionData::Rela64(_)) ==> {
            &&& section.get_type() matches Ok(ShType::Rela)
            &&& elf.header.pt1.class() == Class::SixtyFour
        },
    returns
        section_data_result(section, elf),
    opens_invariants none
    no_unwind when section_data_readable(section, elf)
;

/// The private ELF64 r_info word, including the symbol index in its high half.
pub uninterp spec fn rela64_info(entry: &Rela<u64>) -> u64;

pub open spec fn rela64_type(entry: &Rela<u64>) -> u32 {
    (rela64_info(entry) & 0xffff_ffff) as u32
}

#[verifier::when_used_as_spec(rela64_type)]
pub assume_specification[ Rela::<u64>::get_type ](entry: &Rela<u64>) -> u32
    returns
        rela64_type(entry),
    opens_invariants none
    no_unwind
;

} // verus!
