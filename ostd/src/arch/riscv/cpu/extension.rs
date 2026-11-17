// SPDX-License-Identifier: MPL-2.0
//! RISC-V ISA extensions.
use vstd::{
    prelude::*,
    std_specs::{iter::IteratorSpec, slice::spec_slice_starts_with},
    string::StringSliceAdditionalSpecFns,
    utf8::{
        decode_utf8, encode_scalar, encode_utf8, group_utf8_lib, has_width_1_encoding,
        is_ascii_chars, is_char_boundary, is_continuation_byte, last_continuation_byte,
        leading_byte_width_1, leading_byte_width_2, leading_byte_width_3, leading_byte_width_4,
        second_last_continuation_byte, third_last_continuation_byte, valid_utf8,
    },
};
use vstd_extra::panic::{UnwrapOrPanic, allowed_to_panic_if};

/* Origin Rust: use bitflags_upstream::bitflags;
 * Use the verified bitflags implementation. */
use bitflags::bitflags;
/*use spin::Once;

use crate::arch::boot::DEVICE_TREE;

/// Detects available RISC-V ISA extensions.
pub fn init() {
    let mut global_isa_extensions = IsaExtensions::all();

    let device_tree = DEVICE_TREE.get().expect("Device tree not initialized");
    let mut cpu_count = 0;

    for cpu in device_tree.cpus() {
        cpu_count += 1;

        let cpu_isa_extensions = if let Some(isa_extensions) = cpu.property("riscv,isa-extensions")
        {
            parse_isa_extensions_list(&isa_extensions)
        } else if let Some(isa) = cpu.property("riscv,isa") {
            parse_isa_string(&isa)
        } else {
            log::error!(
                "CPU {} has no riscv,isa or riscv,isa-extensions property",
                cpu_count - 1
            );
            continue;
        };

        global_isa_extensions &= cpu_isa_extensions;
    }

    GLOBAL_ISA_EXTENSIONS.call_once(|| global_isa_extensions);
}

/// Checks if the specified set of ISA extensions are available.
pub fn has_extensions(required: IsaExtensions) -> bool {
    GLOBAL_ISA_EXTENSIONS.get().unwrap().contains(required)
}*/

verus! {

spec fn trimmed(b: Seq<u8>, end: int) -> bool {
    0 <= end <= b.len() && (end == 0 || b[end - 1] != 0) && forall|i: int|
        end <= i < b.len() ==> b[i] == 0
}

spec fn trimmed_len(b: Seq<u8>) -> int {
    choose|end: int| trimmed(b, end)
}

spec fn first_end(b: Seq<u8>, lo: int) -> int
    recommends
        0 <= lo <= b.len(),
{
    match b[lo..].index_of_first(b'_') {
        Some(i) => lo + i,
        None => b.len() as int,
    }
}

spec fn isa_start(b: Seq<u8>) -> int {
    if b.len() >= 4 && b[0] == b'r' && b[1] == b'v' && ((b[2] == b'3' && b[3] == b'2') || (b[2]
        == b'6' && b[3] == b'4')) {
        4
    } else {
        0
    }
}

// Whether `name` occurs at `i` as a whole delimited item (or any byte when `delim` is `None`).
spec fn name_at(b: Seq<u8>, lo: int, hi: int, name: Seq<u8>, delim: Option<u8>, i: int) -> bool {
    lo <= i < hi && i + name.len() <= hi && b[i..i + name.len()] == name && match delim {
        Some(d) => (i == lo || b[i - 1] == d) && (i + name.len() == hi || b[i + name.len()] == d),
        None => true,
    }
}

spec fn has_name(b: Seq<u8>, lo: int, hi: int, name: Seq<u8>, delim: Option<u8>) -> bool {
    exists|i: int| name_at(b, lo, hi, name, delim, i)
}

spec fn recognized(b: Seq<u8>, name: Seq<u8>, string: bool) -> bool {
    if string {
        let trimmed = b[..trimmed_len(b)];
        let start = isa_start(trimmed);
        let first = first_end(trimmed, start);
        (name.len() == 1 && has_name(trimmed, start, first, name, None)) || has_name(
            trimmed,
            first + 1,
            trimmed.len() as int,
            name,
            Some(b'_'),
        )
    } else {
        has_name(b, 0, b.len() as int, name, Some(0))
    }
}

spec fn bits_for(pred: spec_fn(ExtensionData) -> bool, count: int) -> u128 {
    extension_table()[..count].fold_left(
        0u128,
        |acc: u128, e: ExtensionData|
            acc | if pred(e) {
                e.flag.bits()
            } else {
                0
            },
    )
}

// Bitwise union of flags in `EXTENSION_TABLE` recognized in `b`.
spec fn table_bits(b: Seq<u8>, string: bool) -> u128 {
    bits_for(
        |e: ExtensionData| recognized(b, e.name.spec_bytes(), string),
        extension_table().len() as int,
    )
}

} // verus!
/* Origin Rust:
 * Replace unspecified str::starts_with/split, BitOrAssign, and requiring-Some Option::unwrap
 * with bytes.starts_with, bounded '_' scans, union, and unwrap_or_panic.
fn parse_isa_string(isa: &fdt::node::NodeProperty) -> IsaExtensions {
    let mut extensions = IsaExtensions::empty();
    let isa_str = isa.as_str().unwrap();

    let mut ext_iter = {
        let ext_start = if isa_str.starts_with("rv32") || isa_str.starts_with("rv64") {
            4
        } else {
            0
        };
        if ext_start >= isa_str.len() {
            return extensions;
        }
        isa_str[ext_start..].split('_')
    };

    // Parse single-letter extensions from first part
    if let Some(first_part) = ext_iter.next() {
        for ch in first_part.chars() {
            if let Some(ext_data) = EXTENSION_TABLE
                .iter()
                .find(|e| e.name.len() == 1 && e.name.chars().next() == Some(ch))
            {
                extensions |= ext_data.flag;
            }
        }
    }

    // Parse multi-letter extensions from remaining parts
    for part in ext_iter {
        if let Some(ext_data) = EXTENSION_TABLE.iter().find(|e| e.name == part) {
            extensions |= ext_data.flag;
        }
    }

    extensions
}
*/
#[verus_spec(result =>
    requires
        allowed_to_panic_if(!valid_utf8(isa.value@)),
    ensures
        valid_utf8(isa.value@),
        result.bits() == table_bits(isa.value@, true),
)]
fn parse_isa_string(isa: &fdt::node::NodeProperty) -> IsaExtensions {
    let mut extensions = IsaExtensions::empty();
    let isa_str = isa.as_str().unwrap_or_panic();
    let bytes = isa_str.as_bytes();
    proof! {
        assert(trimmed(isa.value@, bytes.len() as int));
        let chosen = trimmed_len(isa.value@);
        assert(trimmed(isa.value@, chosen));
        assert(chosen == bytes.len());
        lemma_str_valid_utf8(isa_str);
    }

    let ext_start = if bytes.starts_with(&[b'r', b'v', b'3', b'2'])
        || bytes.starts_with(&[b'r', b'v', b'6', b'4'])
    {
        4
    } else {
        0
    };
    proof! {
        assert(ext_start == isa_start(bytes@)) by {
            let rv32 = &[b'r', b'v', b'3', b'2'];
            let rv64 = &[b'r', b'v', b'6', b'4'];
            if spec_slice_starts_with(bytes, rv32) {
                assert(bytes@[0] == rv32@[0] && bytes@[1] == rv32@[1] && bytes@[2] == rv32@[2]
                    && bytes@[3] == rv32@[3]);
            }
            if spec_slice_starts_with(bytes, rv64) {
                assert(bytes@[0] == rv64@[0] && bytes@[1] == rv64@[1] && bytes@[2] == rv64@[2]
                    && bytes@[3] == rv64@[3]);
            }
        };
    }
    if ext_start >= isa_str.len() {
        proof! {
            let n = extension_table().len() as int;
            assert(first_end(bytes@, ext_start as int) == bytes.len()) by {
                bytes@[ext_start..].index_of_first_ensures(b'_');
            };
            lemma_bits_for_false(
                |e: ExtensionData| recognized(isa.value@, e.name.spec_bytes(), true),
                n,
            );
        }
        return extensions;
    }

    let mut seg_end = ext_start;
    #[verus_spec(
        invariant
            ext_start <= seg_end <= bytes.len(),
            forall|i: int| ext_start <= i < seg_end ==> bytes@[i] != b'_',
        decreases bytes.len() - seg_end,
    )]
    while seg_end < bytes.len() && bytes[seg_end] != b'_' {
        seg_end += 1;
    }
    proof! {
        assert(seg_end == first_end(bytes@, ext_start as int)) by {
            let part = bytes@[ext_start..];
            part.index_of_first_ensures(b'_');
            match part.index_of_first(b'_') {
                Some(i) => {
                    assert(part[i] == bytes@[ext_start + i]);
                    if ext_start + i < seg_end {
                        assert(bytes@[ext_start + i] != b'_');
                    }
                    if seg_end < ext_start + i {
                        assert(part[seg_end - ext_start] == b'_');
                    }
                },
                None => {
                    if seg_end < bytes.len() {
                        assert(part[seg_end - ext_start] == b'_');
                        assert(part.contains(b'_'));
                    }
                },
            }
        };
        if seg_end < bytes.len() {
            lemma_ascii_char_boundary_after(bytes@, seg_end as int);
        }
    }
    let first_prefix = isa_str.split_at(seg_end).0;
    proof! {
        lemma_str_valid_utf8(first_prefix);
        if ext_start == 4 {
            lemma_ascii_char_boundary_after(first_prefix.spec_bytes(), 3);
        }
    }
    let first_part = first_prefix.split_at(ext_start).1;
    proof! {
        assert(first_part.spec_bytes() == bytes@[ext_start..seg_end]);
    }

    proof! {
        lemma_bits_for_false(
            |e: ExtensionData|
                e.name.spec_bytes().len() == 1 && e.name@.len() == 1
                    && first_part@[..0].contains(e.name@[0]),
            extension_table().len() as int,
        );
    }
    // Parse single-letter extensions from first part
    #[verus_spec(it =>
        invariant
            it.seq() == first_part@,
            extensions.bits() == bits_for(
                |e: ExtensionData|
                    e.name.spec_bytes().len() == 1 && e.name@.len() == 1
                        && first_part@[..it.index()].contains(e.name@[0]),
                extension_table().len() as int,
            ),
    )]
    for ch in first_part.chars() {
        let mut table_iter = EXTENSION_TABLE.iter();
        proof_decl! {
            let ghost items = table_iter.remaining();
        }
        proof! {
            lemma_extension_table_wf();
        }
        let found = table_iter.find(
            #[verus_spec(ret: bool =>
                requires
                    e.name.spec_bytes().len() <= usize::MAX,
                ensures
                    ret == (e.name.spec_bytes().len() == 1 && e.name@.len() >= 1 && e.name@[0] == ch),
            )]
            |e: &&ExtensionData| {
                if e.name.len() == 1 {
                    let mut cs = e.name.chars();
                    let next = cs.next();
                    proof! {
                        lemma_single_byte_str(e.name);
                        assert(next == Some(e.name@[0]));
                    }
                    next == Some(ch)
                } else {
                    false
                }
            },
        );
        proof_decl! {
            let ghost prev_bits = extensions.bits();
        }
        if let Some(ext_data) = found {
            extensions = extensions.union(ext_data.flag);
        }
        proof! {
            lemma_first_char_step(
                first_part@,
                it.index(),
                ch,
                items,
                found,
                prev_bits,
                extensions.bits(),
            );
        }
    }

    proof_decl! {
        let ghost single_base = |e: ExtensionData|
            e.name.spec_bytes().len() == 1 && has_name(
                bytes@,
                ext_start as int,
                seg_end as int,
                e.name.spec_bytes(),
                None,
            );
    }
    proof! {
        lemma_first_part_bits_eq(
            bytes@,
            ext_start as int,
            seg_end as int,
            first_part,
        );
        lemma_bits_for_ext(
            |e: ExtensionData|
                (e.name.spec_bytes().len() == 1 && has_name(
                    bytes@,
                    ext_start as int,
                    seg_end as int,
                    e.name.spec_bytes(),
                    None,
                )) || has_name(
                    bytes@,
                    seg_end + 1,
                    seg_end as int,
                    e.name.spec_bytes(),
                    Some(b'_'),
                ),
            |e: ExtensionData|
                single_base(e) || has_name(
                    bytes@,
                    seg_end + 1,
                    seg_end as int,
                    e.name.spec_bytes(),
                    Some(b'_'),
                ),
            extension_table().len() as int,
        );
    }

    // Parse multi-letter extensions from remaining parts
    let mut pos = seg_end;
    #[verus_spec(
        invariant
            ext_start <= seg_end <= pos <= bytes.len(),
            valid_utf8(bytes@),
            is_char_boundary(bytes@, bytes.len() as int),
            bytes@ == isa_str.spec_bytes(),
            0 <= trimmed_len(isa.value@) <= isa.value@.len(),
            bytes@ == isa.value@[..trimmed_len(isa.value@)],
            ext_start == isa_start(bytes@),
            seg_end == first_end(bytes@, ext_start as int),
            pos < bytes.len() ==> bytes@[pos as int] == b'_',
            extensions.bits() == bits_for(
                |e: ExtensionData|
                    single_base(e) || has_name(
                        bytes@,
                        seg_end + 1,
                        pos as int,
                        e.name.spec_bytes(),
                        Some(b'_'),
                    ),
                extension_table().len() as int,
            ),
        decreases bytes.len() - pos,
    )]
    while pos < bytes.len() {
        let part_start = pos + 1;
        let mut part_end = part_start;
        #[verus_spec(
            invariant
                part_start <= part_end <= bytes.len(),
                forall|i: int| part_start <= i < part_end ==> bytes@[i] != b'_',
            decreases bytes.len() - part_end,
        )]
        while part_end < bytes.len() && bytes[part_end] != b'_' {
            part_end += 1;
        }
        proof! {
            if part_end < bytes.len() {
                lemma_ascii_char_boundary_after(bytes@, part_end as int);
            }
        }
        let part_prefix = isa_str.split_at(part_end).0;
        proof! {
            lemma_str_valid_utf8(part_prefix);
            lemma_ascii_char_boundary_after(part_prefix.spec_bytes(), pos as int);
        }
        let part = part_prefix.split_at(part_start).1;
        proof! {
            assert(part.spec_bytes() == bytes@[part_start..part_end]);
        }
        let mut table_iter = EXTENSION_TABLE.iter();
        proof_decl! {
            let ghost items = table_iter.remaining();
        }
        let found = table_iter.find(
            #[verus_spec(ret: bool =>
                ensures ret == (e.name@ == part@),
            )]
            |e: &&ExtensionData| e.name == part,
        );
        proof_decl! {
            let ghost prev_bits = extensions.bits();
        }
        if let Some(ext_data) = found {
            extensions = extensions.union(ext_data.flag);
        }
        proof! {
            lemma_delim_find_step(
                single_base,
                bytes@,
                seg_end + 1,
                pos as int,
                part_start as int,
                part_end as int,
                b'_',
                part,
                items,
                found,
                prev_bits,
                extensions.bits(),
            );
        }
        pos = part_end;
    }

    proof! {
        let n = extension_table().len() as int;
        let p_loop = |e: ExtensionData|
            single_base(e) || has_name(
                bytes@,
                seg_end + 1,
                bytes.len() as int,
                e.name.spec_bytes(),
                Some(b'_'),
            );
        let p_spec = |e: ExtensionData| recognized(isa.value@, e.name.spec_bytes(), true);
        lemma_bits_for_ext(p_loop, p_spec, n);
    }
    extensions
}

/* Origin Rust:
 * Replace unspecified slice::split and BitOrAssign with a bounded NUL scan and union.
fn parse_isa_extensions_list(isa_extensions: &fdt::node::NodeProperty) -> IsaExtensions {
    let mut extensions = IsaExtensions::empty();
    let isa_extensions_list = isa_extensions.value;

    for str in isa_extensions_list.split(|&b| b == 0) {
        if str.is_empty() {
            continue;
        }
        if let Ok(ext_name) = core::str::from_utf8(str) {
            if let Some(ext_data) = EXTENSION_TABLE.iter().find(|e| e.name == ext_name) {
                extensions |= ext_data.flag;
            }
        }
    }

    extensions
}
*/
#[verus_spec(result =>
    ensures
        result.bits() == table_bits(isa_extensions.value@, false),
)]
fn parse_isa_extensions_list(isa_extensions: &fdt::node::NodeProperty) -> IsaExtensions {
    let mut extensions = IsaExtensions::empty();
    let isa_extensions_list = isa_extensions.value;
    proof! {
        lemma_bits_for_false(
            |e: ExtensionData| has_name(isa_extensions_list@, 0, 0, e.name.spec_bytes(), Some(0)),
            extension_table().len() as int,
        );
    }

    let mut pos = 0;
    #[verus_spec(
        invariant_except_break
            0 <= pos <= isa_extensions_list.len(),
            pos > 0 ==> isa_extensions_list@[pos - 1] == 0,
            extensions.bits() == bits_for(
                |e: ExtensionData|
                    has_name(
                        isa_extensions_list@,
                        0,
                        if pos == 0 {
                            0
                        } else {
                            pos - 1
                        },
                        e.name.spec_bytes(),
                        Some(0),
                    ),
                extension_table().len() as int,
            ),
        ensures
            extensions.bits() == bits_for(
                |e: ExtensionData|
                    has_name(
                        isa_extensions_list@,
                        0,
                        isa_extensions_list.len() as int,
                        e.name.spec_bytes(),
                        Some(0),
                    ),
                extension_table().len() as int,
            ),
        decreases isa_extensions_list.len() + 1 - pos,
    )]
    while pos <= isa_extensions_list.len() {
        let mut end = pos;
        #[verus_spec(
            invariant
                pos <= end <= isa_extensions_list.len(),
                forall|i: int| pos <= i < end ==> isa_extensions_list@[i] != 0,
            decreases isa_extensions_list.len() - end,
        )]
        while end < isa_extensions_list.len() && isa_extensions_list[end] != 0 {
            end += 1;
        }
        let str = &isa_extensions_list[pos..end];
        proof_decl! {
            let ghost prev_hi: int = if pos == 0 { 0 } else { pos - 1 };
        }
        if !str.is_empty() {
            if let Ok(ext_name) = core::str::from_utf8(str) {
                let mut table_iter = EXTENSION_TABLE.iter();
                proof_decl! {
                    let ghost items = table_iter.remaining();
                }
                let found = table_iter.find(
                    #[verus_spec(ret: bool =>
                        ensures ret == (e.name@ == ext_name@),
                    )]
                    |e: &&ExtensionData| e.name == ext_name,
                );
                proof_decl! {
                    let ghost prev_bits = extensions.bits();
                }
                if let Some(ext_data) = found {
                    extensions = extensions.union(ext_data.flag);
                }
                proof! {
                    let n = extension_table().len() as int;
                    let base = |_e: ExtensionData| false;
                    lemma_bits_for_ext(
                        |e: ExtensionData|
                            has_name(isa_extensions_list@, 0, prev_hi, e.name.spec_bytes(), Some(0)),
                        |e: ExtensionData|
                            base(e) || has_name(
                                isa_extensions_list@,
                                0,
                                prev_hi,
                                e.name.spec_bytes(),
                                Some(0),
                            ),
                        n,
                    );
                    lemma_delim_find_step(
                        base,
                        isa_extensions_list@,
                        0,
                        prev_hi,
                        pos as int,
                        end as int,
                        0,
                        ext_name,
                        items,
                        found,
                        prev_bits,
                        extensions.bits(),
                    );
                    lemma_bits_for_ext(
                        |e: ExtensionData|
                            base(e) || has_name(
                                isa_extensions_list@,
                                0,
                                end as int,
                                e.name.spec_bytes(),
                                Some(0),
                            ),
                        |e: ExtensionData|
                            has_name(
                                isa_extensions_list@,
                                0,
                                end as int,
                                e.name.spec_bytes(),
                                Some(0),
                            ),
                        n,
                    );
                }
            } else {
                proof! {
                    lemma_delim_skip_step(
                        isa_extensions_list@,
                        prev_hi,
                        pos as int,
                        end as int,
                    );
                }
            }
        } else {
            proof! {
                lemma_delim_skip_step(
                    isa_extensions_list@,
                    prev_hi,
                    pos as int,
                    end as int,
                );
            }
        }
        if end == isa_extensions_list.len() {
            break;
        }
        pos = end + 1;
    }

    proof! {
        let n = extension_table().len() as int;
        let p_loop = |e: ExtensionData|
            has_name(
                isa_extensions_list@,
                0,
                isa_extensions_list.len() as int,
                e.name.spec_bytes(),
                Some(0),
            );
        let p_spec = |e: ExtensionData| recognized(isa_extensions.value@, e.name.spec_bytes(), false);
        lemma_bits_for_ext(p_loop, p_spec, n);
    }
    extensions
}

/*static GLOBAL_ISA_EXTENSIONS: Once<IsaExtensions> = Once::new();*/

/// A macro for RISC-V ISA extension definition and lookup table generation.
macro_rules! define_isa_extensions {
    (
        $(
            $name:ident = $bit:expr, $str:expr, $doc:expr;
        )*
    ) => {
        bitflags! {
            /// RISC-V ISA extensions
            pub struct IsaExtensions: u128 {
                $(
                    #[doc = $doc]
                    const $name = 1u128 << $bit;
                )*
            }
        }

        /* Origin Rust:
         * An array constant carries a verified sequence contract for table indexing.
        const EXTENSION_TABLE: &[ExtensionData] = &[
            $(
                ExtensionData {
                    name: $str,
                    flag: IsaExtensions::$name
                },
            )*
        ];
        */
        verus! {

        #[verifier::opaque]
        spec fn extension_table() -> Seq<ExtensionData> {
            seq![$(ExtensionData { name: $str, flag: IsaExtensions::$name }),*]
        }

        exec const EXTENSION_TABLE: [ExtensionData; 0 $(+ define_isa_extensions!(@one $name))*]
            ensures
                EXTENSION_TABLE@ == extension_table(),
        {
            proof {
                reveal(extension_table);
            }
            [
                $(
                    ExtensionData {
                        name: $str,
                        flag: IsaExtensions::$name
                    },
                )*
            ]
        }

        proof fn lemma_extension_table_names_wf()
            ensures
                forall|i: int|
                    0 <= i < extension_table().len() ==> {
                        let name = (#[trigger] extension_table()[i]).name;
                        &&& 0 < name.spec_bytes().len() <= usize::MAX
                        &&& !name.spec_bytes().contains(0u8)
                        &&& !name.spec_bytes().contains(b'_')
                    },
        {
            broadcast use group_utf8_lib;

            reveal(extension_table);
            $(
                reveal_strlit($str);
            )*
            let t = extension_table();
            assert forall|i: int| 0 <= i < t.len() implies {
                let name = (#[trigger] t[i]).name;
                &&& 0 < name.spec_bytes().len() <= usize::MAX
                &&& !name.spec_bytes().contains(0u8)
                &&& !name.spec_bytes().contains(b'_')
            } by {
                let name = t[i].name;
                assert(is_ascii_chars(name@));
            };
        }

        proof fn lemma_extension_table_names_unique()
            ensures
                forall|i: int, j: int|
                    0 <= i < j < extension_table().len() ==> (#[trigger] extension_table()[i]).name@
                        != (#[trigger] extension_table()[j]).name@,
        {
            reveal(extension_table);
            $(
                reveal_strlit($str);
            )*
        }

        proof fn lemma_extension_table_wf()
            ensures
                forall|i: int|
                    0 <= i < extension_table().len() ==> {
                        let name = (#[trigger] extension_table()[i]).name;
                        &&& 0 < name.spec_bytes().len() <= usize::MAX
                        &&& !name.spec_bytes().contains(0u8)
                        &&& !name.spec_bytes().contains(b'_')
                    },
                forall|i: int, j: int|
                    0 <= i < j < extension_table().len() ==> (#[trigger] extension_table()[i]).name@
                        != (#[trigger] extension_table()[j]).name@,
        {
            lemma_extension_table_names_wf();
            lemma_extension_table_names_unique();
        }

        } // verus!
    };
    (@one $name:ident) => {
        1
    };
}

#[verus_verify]
struct ExtensionData {
    name: &'static str,
    flag: IsaExtensions,
}

define_isa_extensions! {
    // Standard single-letter extensions (0-25)
    A =  0, "a", "Atomic instructions";
    C =  2, "c", "Compressed instructions";
    D =  3, "d", "Double-precision floating-point";
    F =  5, "f", "Single-precision floating-point";
    H =  7, "h", "Hypervisor";
    I =  8, "i", "Base integer instruction set";
    M = 12, "m", "Integer multiplication and division";
    Q = 16, "q", "Quad-precision floating-point";
    V = 21, "v", "Vector extension";

    // Multi-letter extensions
    SSCOFPMF    = 26, "sscofpmf",    "Supervisor-mode counter overflow and privilege mode filtering";
    SSTC        = 27, "sstc",        "Supervisor-mode timer interrupts";
    SVINVAL     = 28, "svinval",     "Fine-grained address-translation cache invalidation";
    SVPBMT      = 29, "svpbmt",      "Page-based memory types";
    ZBB         = 30, "zbb",         "Basic bit manipulation";
    ZICBOM      = 31, "zicbom",      "Cache block management operations";
    ZIHINTPAUSE = 32, "zihintpause", "Pause hint";
    SVNAPOT     = 33, "svnapot",     "NAPOT translation contiguity";
    ZICBOZ      = 34, "zicboz",      "Cache block zero operations";
    SMAIA       = 35, "smaia",       "Advanced interrupt architecture (machine mode)";
    SSAIA       = 36, "ssaia",       "Advanced interrupt architecture (supervisor mode)";
    ZBA         = 37, "zba",         "Address generation for bit manipulation";
    ZBS         = 38, "zbs",         "Single-bit instructions";
    ZICNTR      = 39, "zicntr",      "Base counters and timers";
    ZICSR       = 40, "zicsr",       "Control and status register instructions";
    ZIFENCEI    = 41, "zifencei",    "Instruction-fetch fence";
    ZIHPM       = 42, "zihpm",       "Hardware performance counters";
    SMSTATEEN   = 43, "smstateen",   "State enable extension";
    ZICOND      = 44, "zicond",      "Integer conditional operations";
    ZBC         = 45, "zbc",         "Carry-less multiplication";
    ZBKB        = 46, "zbkb",        "Bit manipulation instructions for cryptography";
    ZBKC        = 47, "zbkc",        "Carry-less multiplication for cryptography";
    ZBKX        = 48, "zbkx",        "Crossbar permutation instructions";
    ZKND        = 49, "zknd",        "AES decryption";
    ZKNE        = 50, "zkne",        "AES encryption";
    ZKNH        = 51, "zknh",        "Hash function instructions";
    ZKR         = 52, "zkr",         "Entropy source";
    ZKSED       = 53, "zksed",       "SM4 encryption/decryption";
    ZKSH        = 54, "zksh",        "SM3 hash function";
    ZKT         = 55, "zkt",         "Data-independent execution latency";
    ZVBB        = 56, "zvbb",        "Vector basic bit manipulation";
    ZVBC        = 57, "zvbc",        "Vector carry-less multiplication";
    ZVKB        = 58, "zvkb",        "Vector bit manipulation instructions for cryptography";
    ZVKG        = 59, "zvkg",        "Vector GCM/GMAC";
    ZVKNED      = 60, "zvkned",      "Vector AES encryption/decryption";
    ZVKNHA      = 61, "zvknha",      "Vector SHA-2 (SHA-256 and SHA-224)";
    ZVKNHB      = 62, "zvknhb",      "Vector SHA-2 (SHA-512, SHA-384, SHA-256, SHA-224)";
    ZVKSED      = 63, "zvksed",      "Vector SM4 encryption/decryption";
    ZVKSH       = 64, "zvksh",       "Vector SM3 hash function";
    ZVKT        = 65, "zvkt",        "Vector data-independent execution latency";
    ZFH         = 66, "zfh",         "Half-precision floating-point";
    ZFHMIN      = 67, "zfhmin",      "Minimal half-precision floating-point";
    ZIHINTNTL   = 68, "zihintntl",   "Non-temporal locality hints";
    ZVFH        = 69, "zvfh",        "Vector half-precision floating-point";
    ZVFHMIN     = 70, "zvfhmin",     "Vector minimal half-precision floating-point";
    ZFA         = 71, "zfa",         "Additional floating-point instructions";
    ZTSO        = 72, "ztso",        "Total store ordering";
    ZACAS       = 73, "zacas",       "Atomic compare-and-swap";
    ZVE32X      = 74, "zve32x",      "Vector extension for embedded processors (32-bit)";
    ZVE32F      = 75, "zve32f",      "Vector extension for embedded processors (32-bit with float)";
    ZVE64X      = 76, "zve64x",      "Vector extension for embedded processors (64-bit)";
    ZVE64F      = 77, "zve64f",      "Vector extension for embedded processors (64-bit with float)";
    ZVE64D      = 78, "zve64d",      "Vector extension for embedded processors (64-bit with double)";
    ZIMOP       = 79, "zimop",       "May-be-operations";
    ZCA         = 80, "zca",         "Compressed instructions (A subset)";
    ZCB         = 81, "zcb",         "Compressed instructions (B subset)";
    ZCD         = 82, "zcd",         "Compressed instructions (D subset)";
    ZCF         = 83, "zcf",         "Compressed instructions (F subset)";
    ZCMOP       = 84, "zcmop",       "Compressed may-be-operations";
    ZAWRS       = 85, "zawrs",       "Wait-for-reservation-set instructions";
    SVVPTC      = 86, "svvptc",      "Vectored page table cache";
    SMMPM       = 87, "smmpm",       "Machine-mode pointer masking";
    SMNPM       = 88, "smnpm",       "Machine-mode pointer masking (non-pointer)";
    SSNPM       = 89, "ssnpm",       "Supervisor-mode pointer masking (non-pointer)";
    ZABHA       = 90, "zabha",       "Byte and halfword atomic memory operations";
    ZICCRSE     = 91, "ziccrse",     "Main memory supports forward progress on LR/SC sequences";
    SVADE       = 92, "svade",       "Hardware A/D bit updates";
    SVADU       = 93, "svadu",       "Hardware A/D bit updates (user mode)";
    ZFBFMIN     = 94, "zfbfmin",     "Scalar BF16 converts";
    ZVFBFMIN    = 95, "zvfbfmin",    "Vector BF16 converts";
    ZVFBFWMA    = 96, "zvfbfwma",    "Vector BF16 widening mul-add";
    ZAAMO       = 97, "zaamo",       "Atomic memory operations";
    ZALRSC      = 98, "zalrsc",      "Load-reserved/store-conditional";
}

// Auxiliary proof lemmas.
verus! {

proof fn lemma_bits_for_ext(
    pred1: spec_fn(ExtensionData) -> bool,
    pred2: spec_fn(ExtensionData) -> bool,
    count: int,
)
    requires
        0 <= count <= extension_table().len(),
        forall|i: int|
            0 <= i < count ==> pred1(extension_table()[i]) == pred2(extension_table()[i]),
    ensures
        bits_for(pred1, count) == bits_for(pred2, count),
    decreases count,
{
    if count > 0 {
        assert(extension_table()[..count].drop_last() == extension_table()[..count - 1]);
        lemma_bits_for_ext(pred1, pred2, count - 1);
    }
}

proof fn lemma_bits_for_false(pred: spec_fn(ExtensionData) -> bool, count: int)
    requires
        0 <= count <= extension_table().len(),
        forall|i: int| 0 <= i < count ==> !pred(extension_table()[i]),
    ensures
        bits_for(pred, count) == 0u128,
    decreases count,
{
    if count > 0 {
        assert(extension_table()[..count].drop_last() == extension_table()[..count - 1]);
        lemma_bits_for_false(pred, count - 1);
        assert(0u128 | 0u128 == 0u128) by (bit_vector);
    }
}

proof fn lemma_bits_for_add_one(
    pred1: spec_fn(ExtensionData) -> bool,
    pred2: spec_fn(ExtensionData) -> bool,
    idx: int,
    count: int,
)
    requires
        0 <= idx < count <= extension_table().len(),
        pred2(extension_table()[idx]),
        forall|i: int|
            0 <= i < count && i != idx ==> pred2(extension_table()[i]) == pred1(
                extension_table()[i],
            ),
    ensures
        bits_for(pred2, count) == bits_for(pred1, count) | extension_table()[idx].flag.bits(),
    decreases count,
{
    let f = extension_table()[idx].flag.bits();
    assert(extension_table()[..count].drop_last() == extension_table()[..count - 1]);
    if count == idx + 1 {
        lemma_bits_for_ext(pred1, pred2, idx);
        let a = bits_for(pred1, idx);
        assert((a | f) | f == a | f) by (bit_vector);
        assert((a | 0u128) | f == a | f) by (bit_vector);
    } else {
        lemma_bits_for_add_one(pred1, pred2, idx, count - 1);
        let a = bits_for(pred1, count - 1);
        let e = extension_table()[count - 1];
        let g = if pred1(e) {
            e.flag.bits()
        } else {
            0u128
        };
        assert((a | f) | g == (a | g) | f) by (bit_vector);
    }
}

proof fn lemma_str_bytes_eq_iff_view_eq(a: &str, b: &str)
    ensures
        (a.spec_bytes() == b.spec_bytes()) <==> (a@ == b@),
{
    broadcast use group_utf8_lib;

    if a.spec_bytes() == b.spec_bytes() {
        assert(decode_utf8(a.spec_bytes()) == decode_utf8(b.spec_bytes()));
    }
}

proof fn lemma_single_byte_str(s: &str)
    requires
        s.spec_bytes().len() == 1,
    ensures
        s@.len() == 1,
        (s@[0] as u32) < 0x80,
        s.spec_bytes() == seq![s@[0] as u8],
{
    broadcast use group_utf8_lib;

    assert(s@.len() > 0) by {
        if s@.len() == 0 {
            assert(encode_utf8(s@) == Seq::<u8>::empty());
        }
    };
    let c0 = s@[0] as u32;
    assert(encode_utf8(s@) == encode_scalar(c0) + encode_utf8(s@.drop_first()));
    assert(has_width_1_encoding(c0));
    assert(c0 < 0x80);
    assert(encode_scalar(c0) == seq![leading_byte_width_1(c0)]);
    assert(leading_byte_width_1(c0) == c0 as u8) by (bit_vector)
        requires
            has_width_1_encoding(c0),
    ;
    assert(s@.len() == 1) by {
        if s@.len() > 1 {
            let c1 = s@[1] as u32;
            assert(encode_utf8(s@.drop_first()) == encode_scalar(c1) + encode_utf8(
                s@.drop_first().drop_first(),
            ));
        }
    };
}

proof fn lemma_encode_utf8_contains_ascii(chars: Seq<char>, c: char)
    requires
        (c as u32) < 0x80,
    ensures
        (exists|i: int| 0 <= i < encode_utf8(chars).len() && encode_utf8(chars)[i] == c as u8)
            <==> chars.contains(c),
    decreases chars.len(),
{
    broadcast use group_utf8_lib;

    if chars.len() > 0 {
        let head = chars[0];
        let h = head as u32;
        let cu = c as u32;
        let rest = chars.drop_first();
        let hs = encode_scalar(h);
        let rs = encode_utf8(rest);
        assert(encode_utf8(chars) == hs + rs);
        lemma_encode_utf8_contains_ascii(rest, c);
        if has_width_1_encoding(h) {
            assert(hs == seq![leading_byte_width_1(h)]);
            assert(leading_byte_width_1(h) == h as u8) by (bit_vector)
                requires
                    has_width_1_encoding(h),
            ;
            if head == c {
                assert(encode_utf8(chars)[0] == c as u8);
            }
            if encode_utf8(chars)[0] == c as u8 {
                assert(h == cu) by (bit_vector)
                    requires
                        h < 0x80,
                        cu < 0x80,
                        h as u8 == cu as u8,
                ;
            }
        } else {
            assert(leading_byte_width_2(h) >= 0x80 && leading_byte_width_3(h) >= 0x80
                && leading_byte_width_4(h) >= 0x80 && last_continuation_byte(h) >= 0x80
                && second_last_continuation_byte(h) >= 0x80 && third_last_continuation_byte(h)
                >= 0x80) by (bit_vector);
            assert forall|k: int| 0 <= k < hs.len() implies hs[k] >= 0x80 by {};
        }
        if exists|i: int| 0 <= i < encode_utf8(chars).len() && encode_utf8(chars)[i] == c as u8 {
            let i = choose|i: int|
                0 <= i < encode_utf8(chars).len() && encode_utf8(chars)[i] == c as u8;
            if i < hs.len() {
                assert(chars[0] == c);
            } else {
                assert(rs[i - hs.len()] == c as u8);
                let j = choose|j: int| 0 <= j < rest.len() && rest[j] == c;
                assert(chars[j + 1] == c);
            }
        }
        if chars.contains(c) {
            let j = choose|j: int| 0 <= j < chars.len() && chars[j] == c;
            if j == 0 {
                assert(encode_utf8(chars)[0] == c as u8);
            } else {
                assert(rest[j - 1] == c);
                let i = choose|i: int| 0 <= i < rs.len() && rs[i] == c as u8;
                assert(encode_utf8(chars)[hs.len() + i] == c as u8);
            }
        }
    }
}

proof fn lemma_str_valid_utf8(s: &str)
    ensures
        valid_utf8(s.spec_bytes()),
        is_char_boundary(s.spec_bytes(), 0),
        is_char_boundary(s.spec_bytes(), s.spec_bytes().len() as int),
{
    broadcast use group_utf8_lib;

}

proof fn lemma_first_char_step(
    chars: Seq<char>,
    k: int,
    ch: char,
    items: Seq<&ExtensionData>,
    found: Option<&ExtensionData>,
    prev_bits: u128,
    new_bits: u128,
)
    requires
        0 <= k < chars.len(),
        chars[k] == ch,
        items == extension_table().as_ref(),
        prev_bits == bits_for(
            |e: ExtensionData|
                e.name.spec_bytes().len() == 1 && e.name@.len() == 1 && chars[..k].contains(
                    e.name@[0],
                ),
            extension_table().len() as int,
        ),
        found matches Some(ext_data) ==> {
            &&& exists|idx: int| 0 <= idx < items.len() && items[idx] == ext_data
            &&& ext_data.name.spec_bytes().len() == 1 && ext_data.name@.len() >= 1
                && ext_data.name@[0] == ch
            &&& new_bits == prev_bits | ext_data.flag.bits()
        },
        found is None ==> {
            &&& new_bits == prev_bits
            &&& forall|i: int|
                0 <= i < items.len() ==> !((#[trigger] items[i]).name.spec_bytes().len() == 1
                    && items[i].name@.len() >= 1 && items[i].name@[0] == ch)
        },
    ensures
        new_bits == bits_for(
            |e: ExtensionData|
                e.name.spec_bytes().len() == 1 && e.name@.len() == 1 && chars[..k + 1].contains(
                    e.name@[0],
                ),
            extension_table().len() as int,
        ),
{
    lemma_extension_table_wf();
    let n = extension_table().len() as int;
    let pred_old = |e: ExtensionData|
        e.name.spec_bytes().len() == 1 && e.name@.len() == 1 && chars[..k].contains(e.name@[0]);
    let pred_new = |e: ExtensionData|
        e.name.spec_bytes().len() == 1 && e.name@.len() == 1 && chars[..k + 1].contains(e.name@[0]);
    assert forall|c: char| #[trigger]
        chars[..k + 1].contains(c) <==> (chars[..k].contains(c) || c == ch) by {
        if chars[..k + 1].contains(c) {
            let p = choose|p: int| 0 <= p < k + 1 && #[trigger] chars[..k + 1][p] == c;
            if p < k {
                assert(chars[..k][p] == c);
            }
        }
        if chars[..k].contains(c) {
            let p = choose|p: int| 0 <= p < k && #[trigger] chars[..k][p] == c;
            assert(chars[..k + 1][p] == c);
        }
        if c == ch {
            assert(chars[..k + 1][k] == c);
        }
    };
    if let Some(ext_data) = found {
        let idx = choose|idx: int| 0 <= idx < items.len() && items[idx] == ext_data;
        assert(extension_table()[idx] == *ext_data);
        lemma_single_byte_str(extension_table()[idx].name);
        assert forall|j: int| 0 <= j < n && j != idx implies pred_new(extension_table()[j])
            == pred_old(extension_table()[j]) by {
            let e = extension_table()[j];
            if e.name.spec_bytes().len() == 1 {
                lemma_single_byte_str(e.name);
                if e.name@[0] == ch {
                    assert(e.name@ == extension_table()[idx].name@);
                }
            }
        };
        lemma_bits_for_add_one(pred_old, pred_new, idx, n);
    } else {
        assert forall|j: int| 0 <= j < n implies pred_new(extension_table()[j]) == pred_old(
            extension_table()[j],
        ) by {
            let e = extension_table()[j];
            if e.name.spec_bytes().len() == 1 && e.name@.len() == 1 && e.name@[0] == ch {
                assert(items[j] == &extension_table()[j]);
            }
        };
        lemma_bits_for_ext(pred_old, pred_new, n);
    }
}

proof fn lemma_first_part_bits_eq(bytes: Seq<u8>, ext_start: int, seg_end: int, first_part: &str)
    requires
        0 <= ext_start <= seg_end <= bytes.len(),
        first_part.spec_bytes() == bytes[ext_start..seg_end],
    ensures
        bits_for(
            |e: ExtensionData|
                e.name.spec_bytes().len() == 1 && e.name@.len() == 1
                    && first_part@[..first_part@.len()].contains(e.name@[0]),
            extension_table().len() as int,
        ) == bits_for(
            |e: ExtensionData|
                (e.name.spec_bytes().len() == 1 && has_name(
                    bytes,
                    ext_start,
                    seg_end,
                    e.name.spec_bytes(),
                    None,
                )) || has_name(bytes, seg_end + 1, seg_end, e.name.spec_bytes(), Some(b'_')),
            extension_table().len() as int,
        ),
{
    let n = extension_table().len() as int;
    assert(first_part@[..first_part@.len()] == first_part@);
    let p1 = |e: ExtensionData|
        e.name.spec_bytes().len() == 1 && e.name@.len() == 1
            && first_part@[..first_part@.len()].contains(e.name@[0]);
    let p2 = |e: ExtensionData|
        (e.name.spec_bytes().len() == 1 && has_name(
            bytes,
            ext_start,
            seg_end,
            e.name.spec_bytes(),
            None,
        )) || has_name(bytes, seg_end + 1, seg_end, e.name.spec_bytes(), Some(b'_'));
    assert forall|j: int| 0 <= j < n implies p1(extension_table()[j]) == p2(
        extension_table()[j],
    ) by {
        let e = extension_table()[j];
        if e.name.spec_bytes().len() == 1 {
            lemma_single_byte_str(e.name);
            lemma_encode_utf8_contains_ascii(first_part@, e.name@[0]);
            let b = e.name@[0] as u8;
            if first_part@.contains(e.name@[0]) {
                let i = choose|i: int|
                    0 <= i < first_part.spec_bytes().len() && first_part.spec_bytes()[i] == b;
                assert(bytes[ext_start + i..ext_start + i + 1] == e.name.spec_bytes());
                assert(name_at(
                    bytes,
                    ext_start,
                    seg_end,
                    e.name.spec_bytes(),
                    None,
                    ext_start + i,
                ));
            }
            if has_name(bytes, ext_start, seg_end, e.name.spec_bytes(), None) {
                let k = choose|k: int|
                    name_at(bytes, ext_start, seg_end, e.name.spec_bytes(), None, k);
                assert(bytes[k..k + 1][0] == e.name.spec_bytes()[0]);
                assert(first_part.spec_bytes()[k - ext_start] == b);
            }
        }
    };
    lemma_bits_for_ext(p1, p2, n);
}

proof fn lemma_delim_find_step(
    base: spec_fn(ExtensionData) -> bool,
    b: Seq<u8>,
    lo: int,
    prev_hi: int,
    seg_start: int,
    seg_end: int,
    d: u8,
    part: &str,
    items: Seq<&ExtensionData>,
    found: Option<&ExtensionData>,
    prev_bits: u128,
    new_bits: u128,
)
    requires
        0 <= lo,
        prev_hi <= seg_start <= seg_end <= b.len(),
        (seg_start == lo && prev_hi <= lo) || (lo <= prev_hi && seg_start == prev_hi + 1
            && b[prev_hi] == d),
        forall|k: int| seg_start <= k < seg_end ==> b[k] != d,
        part.spec_bytes() == b[seg_start..seg_end],
        d == 0u8 || d == b'_',
        items == extension_table().as_ref(),
        prev_bits == bits_for(
            |e: ExtensionData| base(e) || has_name(b, lo, prev_hi, e.name.spec_bytes(), Some(d)),
            extension_table().len() as int,
        ),
        found matches Some(ext_data) ==> {
            &&& exists|idx: int| 0 <= idx < items.len() && items[idx] == ext_data
            &&& ext_data.name@ == part@
            &&& new_bits == prev_bits | ext_data.flag.bits()
        },
        found is None ==> {
            &&& new_bits == prev_bits
            &&& forall|i: int| 0 <= i < items.len() ==> (#[trigger] items[i]).name@ != part@
        },
    ensures
        new_bits == bits_for(
            |e: ExtensionData| base(e) || has_name(b, lo, seg_end, e.name.spec_bytes(), Some(d)),
            extension_table().len() as int,
        ),
{
    lemma_extension_table_wf();
    let n = extension_table().len() as int;
    let pred_old = |e: ExtensionData|
        base(e) || has_name(b, lo, prev_hi, e.name.spec_bytes(), Some(d));
    let pred_new = |e: ExtensionData|
        base(e) || has_name(b, lo, seg_end, e.name.spec_bytes(), Some(d));
    if let Some(ext_data) = found {
        let idx = choose|idx: int| 0 <= idx < items.len() && items[idx] == ext_data;
        assert(extension_table()[idx] == *ext_data);
        lemma_str_bytes_eq_iff_view_eq(extension_table()[idx].name, part);
        lemma_delim_segment_step(
            b,
            lo,
            prev_hi,
            seg_start,
            seg_end,
            d,
            extension_table()[idx].name.spec_bytes(),
        );
        assert forall|j: int| 0 <= j < n && j != idx implies pred_new(extension_table()[j])
            == pred_old(extension_table()[j]) by {
            let e = extension_table()[j];
            lemma_str_bytes_eq_iff_view_eq(e.name, part);
            lemma_delim_segment_step(b, lo, prev_hi, seg_start, seg_end, d, e.name.spec_bytes());
            if e.name@ == part@ {
                assert(e.name@ == extension_table()[idx].name@);
            }
        };
        lemma_bits_for_add_one(pred_old, pred_new, idx, n);
    } else {
        assert forall|j: int| 0 <= j < n implies pred_new(extension_table()[j]) == pred_old(
            extension_table()[j],
        ) by {
            let e = extension_table()[j];
            lemma_str_bytes_eq_iff_view_eq(e.name, part);
            lemma_delim_segment_step(b, lo, prev_hi, seg_start, seg_end, d, e.name.spec_bytes());
            if e.name@ == part@ {
                assert(items[j] == &extension_table()[j]);
            }
        };
        lemma_bits_for_ext(pred_old, pred_new, n);
    }
}

proof fn lemma_delim_skip_step(b: Seq<u8>, prev_hi: int, seg_start: int, seg_end: int)
    requires
        0 <= prev_hi <= seg_start <= seg_end <= b.len(),
        (seg_start == 0 && prev_hi == 0) || (seg_start == prev_hi + 1 && b[prev_hi] == 0),
        forall|k: int| seg_start <= k < seg_end ==> b[k] != 0,
        seg_start == seg_end || !valid_utf8(b[seg_start..seg_end]),
    ensures
        bits_for(
            |e: ExtensionData| has_name(b, 0, seg_end, e.name.spec_bytes(), Some(0)),
            extension_table().len() as int,
        ) == bits_for(
            |e: ExtensionData| has_name(b, 0, prev_hi, e.name.spec_bytes(), Some(0)),
            extension_table().len() as int,
        ),
{
    lemma_extension_table_wf();
    let n = extension_table().len() as int;
    let pred_old = |e: ExtensionData| has_name(b, 0, prev_hi, e.name.spec_bytes(), Some(0));
    let pred_new = |e: ExtensionData| has_name(b, 0, seg_end, e.name.spec_bytes(), Some(0));
    assert forall|j: int| 0 <= j < n implies pred_new(extension_table()[j]) == pred_old(
        extension_table()[j],
    ) by {
        let e = extension_table()[j];
        lemma_delim_segment_step(b, 0, prev_hi, seg_start, seg_end, 0, e.name.spec_bytes());
        lemma_str_valid_utf8(e.name);
    };
    lemma_bits_for_ext(pred_old, pred_new, n);
}

proof fn lemma_ascii_char_boundary_after(b: Seq<u8>, i: int)
    requires
        valid_utf8(b),
        0 <= i < b.len(),
        b[i] < 0x80,
    ensures
        is_char_boundary(b, i),
        is_char_boundary(b, i + 1),
{
    broadcast use group_utf8_lib;

    assert(!is_continuation_byte(b[i]));
    assert(is_char_boundary(b, i));
    if i + 1 < b.len() {
        let suffix = b[i..];
        assert(valid_utf8(suffix));
        assert(b[i + 1..] == suffix.drop_first());
        assert(valid_utf8(b[i + 1..]));
        assert(!is_continuation_byte(b[i + 1]));
        assert(is_char_boundary(b, i + 1));
    }
}

proof fn lemma_delim_segment_step(
    b: Seq<u8>,
    lo: int,
    prev_hi: int,
    seg_start: int,
    seg_end: int,
    d: u8,
    name: Seq<u8>,
)
    requires
        0 <= lo,
        prev_hi <= seg_start <= seg_end <= b.len(),
        (seg_start == lo && prev_hi <= lo) || (lo <= prev_hi && seg_start == prev_hi + 1
            && b[prev_hi] == d),
        forall|k: int| seg_start <= k < seg_end ==> b[k] != d,
        name.len() > 0,
        !name.contains(d),
    ensures
        has_name(b, lo, seg_end, name, Some(d)) <==> (has_name(b, lo, prev_hi, name, Some(d))
            || b[seg_start..seg_end] == name),
{
    if has_name(b, lo, seg_end, name, Some(d)) {
        let i = choose|i: int| name_at(b, lo, seg_end, name, Some(d), i);
        if i + name.len() <= prev_hi {
            assert(name_at(b, lo, prev_hi, name, Some(d), i));
        } else if i < seg_start {
            assert(i <= prev_hi < i + name.len());
            assert(name[prev_hi - i] == b[prev_hi]);
            assert(name.contains(d));
        } else {
            if i > seg_start {
                assert(b[i - 1] == d);
            }
            if i + name.len() < seg_end {
                assert(b[i + name.len()] == d);
            }
            assert(i == seg_start && i + name.len() == seg_end);
            assert(b[seg_start..seg_end] == name);
        }
    }
    if has_name(b, lo, prev_hi, name, Some(d)) {
        let i = choose|i: int| name_at(b, lo, prev_hi, name, Some(d), i);
        assert(name_at(b, lo, seg_end, name, Some(d), i));
    }
    if b[seg_start..seg_end] == name {
        assert(name_at(b, lo, seg_end, name, Some(d), seg_start));
    }
}

} // verus!
#[cfg(ktest)]
mod tests {
    use super::*;
    use crate::prelude::*;

    struct MockFdtProperty {
        data: Vec<u8>,
    }

    impl MockFdtProperty {
        fn new_string(string: &str) -> Self {
            let mut data = string.as_bytes().to_vec();
            data.push(0);
            Self { data }
        }

        fn new_string_list(strings: &[&str]) -> Self {
            let mut data = Vec::new();
            for string in strings {
                data.extend_from_slice(string.as_bytes());
                data.push(0);
            }
            Self { data }
        }

        // For the extensions list parser
        fn value(&self) -> &[u8] {
            &self.data
        }
    }

    fn parse_isa_string_wrapper(string: &str) -> IsaExtensions {
        let prop = MockFdtProperty::new_string(string);
        let node = fdt::node::NodeProperty {
            name: "riscv,isa",
            value: prop.value(),
        };
        parse_isa_string(&node)
    }

    fn parse_isa_extensions_list_wrapper(strings: &[&str]) -> IsaExtensions {
        let prop = MockFdtProperty::new_string_list(strings);
        let node = fdt::node::NodeProperty {
            name: "riscv,isa-extensions",
            value: prop.value(),
        };
        parse_isa_extensions_list(&node)
    }

    #[ktest]
    fn isa_string_with_basic() {
        let result = parse_isa_string_wrapper("rv64imafdc_zicsr_zifencei");
        assert!(result.contains(IsaExtensions::I));
        assert!(result.contains(IsaExtensions::M));
        assert!(result.contains(IsaExtensions::A));
        assert!(result.contains(IsaExtensions::F));
        assert!(result.contains(IsaExtensions::D));
        assert!(result.contains(IsaExtensions::C));
        assert!(result.contains(IsaExtensions::ZICSR));
        assert!(result.contains(IsaExtensions::ZIFENCEI));
        assert!(!result.contains(IsaExtensions::V));
        assert!(!result.contains(IsaExtensions::H));
    }

    #[ktest]
    fn isa_string_edge_cases() {
        // Empty string
        let result = parse_isa_string_wrapper("");
        assert!(result.is_empty());

        // Empty after prefix
        let result = parse_isa_string_wrapper("rv64");
        assert!(result.is_empty());

        // No prefix
        let result = parse_isa_string_wrapper("imafdc");
        assert!(result.contains(IsaExtensions::I));
        assert!(result.contains(IsaExtensions::M));
        assert!(result.contains(IsaExtensions::A));

        // Only multi-letter extensions
        let result = parse_isa_string_wrapper("rv64_zicsr_zifencei");
        assert!(result.contains(IsaExtensions::ZICSR));
        assert!(result.contains(IsaExtensions::ZIFENCEI));
        assert!(!result.contains(IsaExtensions::I));
    }

    #[ktest]
    fn isa_string_unknown_extensions() {
        // Should ignore unknown extensions without crashing
        let result = parse_isa_string_wrapper("rv64imafdc_zunknown_zicsr_zifencei");
        assert!(result.contains(IsaExtensions::I));
        assert!(result.contains(IsaExtensions::M));
        assert!(result.contains(IsaExtensions::A));
        assert!(result.contains(IsaExtensions::F));
        assert!(result.contains(IsaExtensions::D));
        assert!(result.contains(IsaExtensions::C));
        assert!(result.contains(IsaExtensions::ZICSR));
        assert!(result.contains(IsaExtensions::ZIFENCEI));
    }

    #[ktest]
    fn isa_extensions_list_basic() {
        let result =
            parse_isa_extensions_list_wrapper(&["i", "m", "a", "f", "d", "c", "zicsr", "zifencei"]);
        assert!(result.contains(IsaExtensions::I));
        assert!(result.contains(IsaExtensions::M));
        assert!(result.contains(IsaExtensions::A));
        assert!(result.contains(IsaExtensions::F));
        assert!(result.contains(IsaExtensions::D));
        assert!(result.contains(IsaExtensions::C));
        assert!(result.contains(IsaExtensions::ZICSR));
        assert!(result.contains(IsaExtensions::ZIFENCEI));
        assert!(!result.contains(IsaExtensions::V));
        assert!(!result.contains(IsaExtensions::H));
    }

    #[ktest]
    fn isa_extensions_list_edge_cases() {
        // Empty list
        let result = parse_isa_extensions_list_wrapper(&[]);
        assert!(result.is_empty());

        // List with empty strings
        let result = parse_isa_extensions_list_wrapper(&["", "i", "", "m", ""]);
        assert!(result.contains(IsaExtensions::I));
        assert!(result.contains(IsaExtensions::M));

        // Only empty strings
        let result = parse_isa_extensions_list_wrapper(&["", "", ""]);
        assert!(result.is_empty());
    }

    #[ktest]
    fn isa_extensions_list_unknown_extensions() {
        // Should ignore unknown extensions without crashing
        let result = parse_isa_extensions_list_wrapper(&[
            "i", "m", "a", "f", "d", "c", "zunknown", "zicsr", "zifencei",
        ]);
        assert!(result.contains(IsaExtensions::I));
        assert!(result.contains(IsaExtensions::M));
        assert!(result.contains(IsaExtensions::A));
        assert!(result.contains(IsaExtensions::F));
        assert!(result.contains(IsaExtensions::D));
        assert!(result.contains(IsaExtensions::C));
        assert!(result.contains(IsaExtensions::ZICSR));
        assert!(result.contains(IsaExtensions::ZIFENCEI));
    }
}
