// SPDX-License-Identifier: MPL-2.0
//! Trusted specifications for xmas-elf 0.10.0's parsing and header access.
use vstd::{prelude::*, std_specs::iter::IteratorSpec};
use xmas_elf::{
    ElfFile,
    header::{Class, Header, HeaderPt1, HeaderPt2, HeaderPt2_, Machine_, Type_ as HeaderType},
    program::{Flags, ProgramHeader, ProgramHeader32, ProgramHeader64, Type_},
};

use super::slice::as_ptr_spec;

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
        let (size, align): (int, int) = match header_class(elf.header.pt1) {
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

/// ElfFile::new delegates to parse_header and preserves its complete Result.
pub assume_specification<'a>[ ElfFile::<'a>::new ](input: &'a [u8]) -> Result<
    ElfFile<'a>,
    &'static str,
>
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

} // verus!
