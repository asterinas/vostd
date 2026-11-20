// SPDX-License-Identifier: MPL-2.0
use vstd::{
    prelude::*,
    raw_ptr::MemContents,
    std_specs::{iter::IteratorSpec, maybe_uninit::MaybeUninitAdditionalSpecFns},
};
use vstd_extra::external::xmas_elf::{
    elf_parse_result, elf_program_headers, elf_program_headers_readable, program_load_bytes,
    program_load_data_readable,
};

use core::mem::MaybeUninit;

use xmas_elf::program::{ProgramHeader, SegmentData};

/// Load the kernel ELF payload to memory.
#[verus_spec(
    with Tracked(loaded): Tracked<&mut Ghost<Seq<Seq<MaybeUninit<u8>>>>>,
    requires
        elf_parse_result(file) matches Ok(elf) && {
            &&& elf_program_headers_readable(&elf)
            &&& forall|i: int| 0 <= i < elf_program_headers(&elf).len() ==> {
                let ph = #[trigger] elf_program_headers(&elf)[i];
                ph matches ProgramHeader::Ph64(program) && {
                    &&& ph.get_type() is Ok
                    &&& ph.get_type() == Ok(xmas_elf::program::Type::Load) ==> {
                        &&& program_load_data_readable(&ph, elf.input@)
                        &&& program.file_size <= program.mem_size <= usize::MAX
                    }
                }
            }
        },
    ensures
        elf_parse_result(file) matches Ok(parsed) ==> {
            &&& final(loaded)@.len() == elf_program_headers(&parsed).len()
            &&& forall|i: int| 0 <= i < final(loaded)@.len() ==>
                header_initialized(
                    elf_program_headers(&parsed)[i],
                    file@,
                    #[trigger] final(loaded)@[i],
                )
        },
)]
pub fn load_elf(file: &[u8]) {
    let elf = xmas_elf::ElfFile::new(file).unwrap();

    proof! {
        *loaded = Ghost(Seq::empty());
    }
    #[verus_spec(iter =>
        invariant
            elf_parse_result(file) == Ok(elf),
            elf.input@ == file@,
            elf_program_headers_readable(&elf),
            iter.iter.obeys_prophetic_iter_laws(),
            iter.seq() == elf_program_headers(&elf),
            forall|i: int| 0 <= i < elf_program_headers(&elf).len() ==> {
                let ph = #[trigger] elf_program_headers(&elf)[i];
                ph matches ProgramHeader::Ph64(program) && {
                    &&& ph.get_type() is Ok
                    &&& ph.get_type() == Ok(xmas_elf::program::Type::Load) ==> {
                        &&& program_load_data_readable(&ph, elf.input@)
                        &&& program.file_size <= program.mem_size <= usize::MAX
                    }
                }
            },
            loaded@.len() == iter.index(),
            forall|i: int| 0 <= i < loaded@.len() ==>
                header_initialized(elf_program_headers(&elf)[i], file@, #[trigger] loaded@[i]),
    )]
    for ph in elf.program_iter() {
        let ProgramHeader::Ph64(program) = ph else {
            panic!(
                "[setup] Unexpected program header type! Asterinas should be 64-bit ELF binary."
            );
        };

        proof_decl! {
            let tracked mut segment = Ghost(Seq::empty());
        }
        if program.get_type().unwrap() == xmas_elf::program::Type::Load {
            #[verus_spec(with Tracked(&mut segment))]
            load_segment(&elf, program);
        }
        proof! {
            *loaded = Ghost(loaded@.push(segment@));
        }
    }
}

#[verus_spec(
    with Tracked(loaded): Tracked<&mut Ghost<Seq<MaybeUninit<u8>>>>,
    requires
        ProgramHeader::Ph64(program).get_type() == Ok(xmas_elf::program::Type::Load),
        program_load_data_readable(&ProgramHeader::Ph64(program), file.input@),
        program.file_size <= program.mem_size <= usize::MAX,
    ensures
        segment_initialized(program, file.input@, final(loaded)@),
)]
fn load_segment(file: &xmas_elf::ElfFile, program: &xmas_elf::program::ProgramHeader64) {
    let SegmentData::Undefined(segment_data) = program.get_data(file).unwrap() else {
        panic!("[setup] Unexpected segment data type!");
    };

    let dst_slice = crate::x86::alloc_at(program.physical_addr as usize, program.mem_size as usize);

    #[cfg(feature = "debug_print")]
    crate::println!(
        "[setup] Loading an ELF segment: addr={:#x}, size={:#x}",
        program.physical_addr,
        program.mem_size,
    );

    let (left, right) = dst_slice.split_at_mut(program.file_size as usize);
    left.write_copy_of_slice(segment_data);
    /* Rust 1.100 API rename; Origin Rust: MaybeUninit::fill(right, 0); */
    right.write_filled(0);
    proof! {
        let contents = |slot: MaybeUninit<u8>| slot.mem_contents().value();
        assert forall|i: int| 0 <= i < left@.len() implies
            #[trigger] left@[i].mem_contents() == MemContents::Init(segment_data@[i]) by {
            assert(left@.map_values(contents)[i] == segment_data@[i]);
        }
        assert forall|i: int| 0 <= i < right@.len() implies
            #[trigger] right@[i].mem_contents() == MemContents::Init(0u8) by {
            assert(right@.map_values(contents)[i] == 0);
        }
        *loaded = Ghost(dst_slice@);
    }
}

verus! {

pub open spec fn segment_initialized(
    program: &xmas_elf::program::ProgramHeader64,
    input: Seq<u8>,
    loaded: Seq<MaybeUninit<u8>>,
) -> bool {
    &&& loaded.len() == program.mem_size
    &&& forall|i: int|
        0 <= i < loaded.len() ==> #[trigger] loaded[i].mem_contents() == MemContents::Init(
            if i < program.file_size {
                program_load_bytes(&ProgramHeader::Ph64(program), input)[i]
            } else {
                0u8
            },
        )
}

pub open spec fn header_initialized(
    header: ProgramHeader<'_>,
    input: Seq<u8>,
    loaded: Seq<MaybeUninit<u8>>,
) -> bool {
    match header {
        ProgramHeader::Ph64(program) => {
            if header.get_type() == Ok(xmas_elf::program::Type::Load) {
                segment_initialized(program, input, loaded)
            } else {
                loaded == Seq::<MaybeUninit<u8>>::empty()
            }
        },
        ProgramHeader::Ph32(_) => false,
    }
}

} // verus!
