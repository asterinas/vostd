use vstd::prelude::*;

use crate::panic::*;

#[macro_export]
macro_rules! assert {
    ($cond:expr) => {
        if !($cond) {
            $crate::panic::panic_diverge()
        }
    };
    ($cond:expr, $msg:literal) => {
        if !($cond) {
            $crate::panic::panic_diverge()
        }
    };
}

#[macro_export]
macro_rules! assert_eq {
    ($l:expr, $r:expr) => {
        if ($l != $r) {
            $crate::panic::panic_diverge()
        }
    };
}

#[macro_export]
macro_rules! borrow_field {
    ($ptr:expr) => {
        $ptr
    };
    // Meta-cell read: borrows only the metadata `M` view of a slot's storage
    // cell (analogous to `unsafe { ptr.as_ref() }.field` in ../vostd). Requires
    // `Metadata` to be in scope at the call site. MUST come before the generic
    // `$perm:expr` arm — otherwise the latter matches greedily, treating
    // `Meta(perm)` as a function-call expression.
    ($ptr:expr => $field:tt, Meta($perm:expr)) => {
        verus_exec_expr!($ptr.borrow(Tracked($perm)).metadata.$field)
    };
    ($ptr:expr => $field:tt, $perm:expr) => {
        verus_exec_expr!($ptr.borrow(Tracked($perm)).$field)
    };
    ($ptr:expr => $field1:tt . $field2:tt, $perm:expr) => {
        verus_exec_expr!($ptr.borrow(Tracked($perm)).$field1.$field2)
    };
}

pub use crate::borrow_field;
