// SPDX-License-Identifier: MPL-2.0
//! RISC-V ISA extensions.
use vstd::{
    prelude::*, std_specs::cmp::PartialEqSpec, string::StringSliceAdditionalSpecFns,
    utf8::valid_utf8,
};

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

// fdt 0.1.5 exposes both fields; no opaque wrapper or method assumptions.
#[verifier::external_type_specification]
pub struct ExNodeProperty<'a>(fdt::node::NodeProperty<'a>);

spec fn trimmed(b: Seq<u8>, end: int) -> bool {
    0 <= end <= b.len() && (end == 0 || b[end - 1] != 0) && forall|i: int|
        end <= i < b.len() ==> b[i] == 0
}

spec fn trimmed_len(b: Seq<u8>) -> int {
    choose|end: int| trimmed(b, end)
}

spec fn first_end(b: Seq<u8>, lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi <= b.len(),
{
    match b[lo..hi].index_of_first(b'_') {
        Some(i) => lo + i,
        None => hi,
    }
}

spec fn isa_start(b: Seq<u8>, end: int) -> int {
    if end >= 4 && b[0] == b'r' && b[1] == b'v' && ((b[2] == b'3' && b[3] == b'2') || (b[2] == b'6'
        && b[3] == b'4')) {
        4
    } else {
        0
    }
}

// A name occurs as a whole delimited item, or (for the first ISA part)
// as a one-byte single-letter extension. This is independent of scanning order.
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
        let end = trimmed_len(b);
        let start = isa_start(b, end);
        let first = first_end(b, start, end);
        (name.len() == 1 && has_name(b, start, first, name, None)) || has_name(
            b,
            first + 1,
            end,
            name,
            Some(b'_'),
        )
    } else {
        has_name(b, 0, b.len() as int, name, Some(0))
    }
}

// Union over the original table, including precisely the entries related to
// the input above. The result includes every matching flag and no other bits.
spec fn table_bits(b: Seq<u8>, string: bool, count: int) -> u128
    decreases count,
{
    if count <= 0 {
        0
    } else {
        table_bits(b, string, count - 1) | if recognized(
            b,
            extension_table()[count - 1].name.spec_bytes(),
            string,
        ) {
            extension_table()[count - 1].flag.bits()
        } else {
            0
        }
    }
}

} // verus!
/* Origin Rust:
 * Replace unsupported split/trim/iterator adapters with bounded byte scans.
 * Validate the whole property before trimming; ASCII table names and delimiters
 * cannot occur inside a non-ASCII UTF-8 character.
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
    requires valid_utf8(isa.value@),
    ensures result.bits() == table_bits(isa.value@, true, extension_table().len() as int),
)]
fn parse_isa_string(isa: &fdt::node::NodeProperty) -> IsaExtensions {
    let isa_str = core::str::from_utf8(isa.value).ok().unwrap();
    let bytes = isa_str.as_bytes();
    let mut end = bytes.len();
    #[verus_spec(
        invariant
            end <= bytes.len(),
            bytes@ == isa.value@,
            forall|i: int| end <= i < bytes@.len() ==> bytes@[i] == 0,
        decreases end,
    )]
    while end > 0 && bytes[end - 1] == 0 {
        end -= 1;
    }
    proof! {
        assert(trimmed(bytes@, end as int));
    }
    let start = if end >= 4
        && bytes[0] == b'r'
        && bytes[1] == b'v'
        && ((bytes[2] == b'3' && bytes[3] == b'2') || (bytes[2] == b'6' && bytes[3] == b'4'))
    {
        4
    } else {
        0
    };
    let mut first = start;
    #[verus_spec(
        invariant
            start <= first <= end <= bytes.len(),
            start == isa_start(bytes@, end as int),
            end == trimmed_len(bytes@),
            bytes@ == isa.value@,
            forall|i: int| start <= i < first ==> bytes@[i] != b'_',
        decreases end - first,
    )]
    while first < end && bytes[first] != b'_' {
        first += 1;
    }
    proof! {
        let part = bytes@[start..end];
        part.index_of_first_ensures(b'_');
        match part.index_of_first(b'_') {
            Some(i) => {
                assert(part[i] == bytes@[start + i]);
                if start + i < first {
                    assert(bytes@[start + i] != b'_');
                }
                if first < start + i {
                    assert(part[first - start] == b'_');
                }
            },
            None => {
                if first < end {
                    assert(part[first - start] == b'_');
                    assert(part.contains(b'_'));
                }
            },
        }
        assert(first == first_end(bytes@, start as int, end as int));
    }
    let mut extensions = IsaExtensions::empty();
    let table = &EXTENSION_TABLE;
    let mut index = 0;
    #[verus_spec(
        invariant
            index <= table.len(),
            table@ == extension_table(),
            extensions.bits() == table_bits(bytes@, true, index as int),
            bytes@ == isa.value@,
            start <= first <= end <= bytes.len(),
            end == trimmed_len(bytes@),
            start == isa_start(bytes@, end as int),
            first == first_end(bytes@, start as int, end as int),
        decreases table.len() - index,
    )]
    while index < table.len() {
        let entry = &table[index];
        let name = entry.name.as_bytes();
        let single = name.len() == 1 && contains_name(bytes, start, first, name, None);
        let remaining = if first < end {
            contains_name(bytes, first + 1, end, name, Some(b'_'))
        } else {
            false
        };
        if single || remaining {
            extensions = extensions.union(entry.flag);
        }
        proof! {
            assert(extensions.bits() | 0u128 == extensions.bits()) by (bit_vector);
        }
        index += 1;
    }
    extensions
}

/* Origin Rust:
 * Replace unsupported slice splitting and iterator lookup with bounded scans.
 * Exact equality to a nonempty ASCII table name excludes invalid UTF-8 items;
 * unique table names and idempotent union permit visiting the table first.
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
    ensures result.bits() == table_bits(isa_extensions.value@, false, extension_table().len() as int),
)]
fn parse_isa_extensions_list(isa_extensions: &fdt::node::NodeProperty) -> IsaExtensions {
    let mut extensions = IsaExtensions::empty();
    let bytes = isa_extensions.value;
    let table = &EXTENSION_TABLE;
    let mut index = 0;
    #[verus_spec(
        invariant
            index <= table.len(),
            table@ == extension_table(),
            extensions.bits() == table_bits(bytes@, false, index as int),
        decreases table.len() - index,
    )]
    while index < table.len() {
        let entry = &table[index];
        // All table names are nonempty ASCII. Exact byte equality to a table
        // name implies valid UTF-8, so invalid items cannot match.
        if contains_name(bytes, 0, bytes.len(), entry.name.as_bytes(), Some(0)) {
            extensions = extensions.union(entry.flag);
        }
        proof! {
            assert(extensions.bits() | 0u128 == extensions.bits()) by (bit_vector);
        }
        index += 1;
    }
    extensions
}

// Origin Rust: EXTENSION_TABLE.iter().find(|e| e.name == part)
// Share a bounded byte search because the split/iterator adapters lack specifications.
#[verus_spec(
    requires lo <= hi <= bytes.len(),
    returns has_name(bytes@, lo as int, hi as int, name@, delim),
)]
fn contains_name(bytes: &[u8], lo: usize, hi: usize, name: &[u8], delim: Option<u8>) -> bool {
    let mut i = lo;
    #[verus_spec(
        invariant
            lo <= i <= hi <= bytes.len(),
            forall|j: int| lo <= j < i ==> !name_at(bytes@, lo as int, hi as int, name@, delim, j),
        decreases hi - i,
    )]
    while i < hi {
        if name.len() <= hi - i {
            let stop = i + name.len();
            let left = match delim {
                Some(d) => i == lo || bytes[i - 1] == d,
                None => true,
            };
            let right = match delim {
                Some(d) => stop == hi || bytes[stop] == d,
                None => true,
            };
            let part = &bytes[i..stop];
            proof! {
                assert(part.eq_spec(name) <==> part@ == name@) by {
                    if part.eq_spec(name) { assert(part@ == name@); }
                }
            }
            if left && right && part == name {
                proof! { assert(name_at(bytes@, lo as int, hi as int, name@, delim, i as int)); }
                return true;
            }
        }
        i += 1;
    }
    false
}

/*static GLOBAL_ISA_EXTENSIONS: Once<IsaExtensions> = Once::new();*/

/// A macro for RISC-V ISA extension definition and lookup table generation.
macro_rules! define_isa_extensions { (@one $name:ident) => { 1 };
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
        spec fn extension_table() -> Seq<ExtensionData> {
            seq![$(ExtensionData { name: $str, flag: IsaExtensions::$name }),*]
        }
        exec const EXTENSION_TABLE: [ExtensionData; 0 $(+ define_isa_extensions!(@one $name))*]
            ensures EXTENSION_TABLE@ == extension_table()
        { [
            $(
                ExtensionData {
                    name: $str,
                    flag: IsaExtensions::$name
                },
            )*
        ] }
        }
    };
}

verus! {

struct ExtensionData {
    name: &'static str,
    flag: IsaExtensions,
}

} // verus!
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
