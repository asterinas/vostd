// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

use crate::prelude::Vaddr;

#[verus_verify]
#[repr(C)]
struct ExTableItem {
    inst_addr: Vaddr,
    recovery_inst_addr: Vaddr,
}

extern "C" {
    fn __ex_table();
    fn __ex_table_end();
}

verus! {

/// Linker-ordered (instruction, recovery) address pairs.
pub uninterp spec fn table_model() -> Seq<(Vaddr, Vaddr)>;

} // verus!
/// A structure representing the usage of exception table (ExTable).
/// This table is used for recovering from specific exception handling faults
/// occurring at known points in the code.
///
/// To add a recovery instruction for a target assembly instruction, one should add
/// the following statements:
///
/// ```
/// .pushsection .ex_table, "a"
/// .align 8
/// .quad [.target_label],
/// .quad [.recovery_label],
/// .popsection
/// ```
///
/// where the `target_label` and `recovery_label` are the labels of the target instruction
/// and the label of recovery instruction respectively.
///
/// For example, we have the following assembly code snippets in an input file:
/// ```
/// .label1:
///     rep movsb
///     mov rax, rcx
/// .label2:
///     ret
/// ```
///
/// We can add the following statements in the same file (`label1` and `label2` are local
/// labels):
///
/// ```
/// .pushsection .ex_table, "a"
/// .align 8
/// .quad [.label1],
/// .quad [.label2],
/// .popsection
/// ```
///
/// After that, we can use the API of `ExTable` to resume execution when handling
/// exceptions caused by `rep movsb` (which `label1` point to) failing.
#[verus_verify]
pub(crate) struct ExTable;

#[verus_verify]
impl ExTable {
    /// Finds the recovery instruction address for a given instruction address.
    ///
    /// This function is generally used when an exception (such as a page fault) occurs.
    /// if the exception handling fails and there is a predefined recovery action,
    /// then the found recovery action will be taken.
    ///
    /// # Verified Properties
    ///
    /// Returns the first match in `table_model()`, or `None` iff no entry matches.
    #[verus_spec(r =>
        ensures
            r matches Some(recovery) ==> exists|i: int| 0 <= i < table_model().len()
                && #[trigger] table_model()[i].0 == inst_addr
                && recovery == table_model()[i].1
                && table_model()[..i].all(|entry: (Vaddr, Vaddr)| entry.0 != inst_addr),
            r is None ==> !table_model().any(|entry: (Vaddr, Vaddr)| entry.0 == inst_addr),
    )]
    pub fn find_recovery_inst_addr(inst_addr: Vaddr) -> Option<Vaddr> {
        /* `read_table` isolates linker-symbol casts unsupported by Verus.
         * Origin Rust:
         * let table_size =
         *     (__ex_table_end as usize - __ex_table as usize) / core::mem::size_of::<ExTableItem>();
         * // SAFETY: `__ex_table` is a static section consisting of `ExTableItem`.
         * let ex_table =
         *     unsafe { core::slice::from_raw_parts(__ex_table as *const ExTableItem, table_size) };
         */
        let ex_table = read_table();
        #[verus_spec(iter =>
            invariant
                ex_table@.map_values(|item: ExTableItem|
                    (item.inst_addr, item.recovery_inst_addr)) == table_model(),
                table_model()[..iter.index()].all(|entry: (Vaddr, Vaddr)|
                    entry.0 != inst_addr),
        )]
        for item in ex_table {
            if item.inst_addr == inst_addr {
                proof! {
                    assert(table_model()[iter.index()].0 == inst_addr);
                }
                return Some(item.recovery_inst_addr);
            }
        }
        proof! {
            assert(table_model()[..table_model().len()] == table_model());
        }
        None
    }
}
/* Isolates linker-symbol casts unsupported by Verus.
 * Origin Rust: <none; new executable code>
 */
/// Trusted linker boundary: the section is non-null, aligned, initialized,
/// readable and immutable for the kernel lifetime, and matches `table_model()`.
/// Its bounds are ordered; its byte length is an entry-size multiple <= `isize::MAX`.
#[verifier::external_body]
#[verus_spec(r =>
    ensures
        r@.map_values(|item: ExTableItem|
            (item.inst_addr, item.recovery_inst_addr)) == table_model(),
)]
fn read_table() -> &'static [ExTableItem] {
    let table_size =
        (__ex_table_end as usize - __ex_table as usize) / core::mem::size_of::<ExTableItem>();
    // SAFETY: `__ex_table` is a static section consisting of `ExTableItem`.
    let ex_table =
        unsafe { core::slice::from_raw_parts(__ex_table as *const ExTableItem, table_size) };
    ex_table
}
