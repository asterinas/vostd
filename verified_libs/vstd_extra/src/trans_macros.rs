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

#[macro_export]
macro_rules! update_field {
    ($ptr:expr => $field:tt <- $val:expr; $set:expr , $idx:expr) => {
        verus_exec_expr!(
        {
            let tracked mut __own = $set.tracked_remove($idx);
            let mut __tmp = $ptr.take(Tracked(&mut __own));
            __tmp.$field = $val;
            $ptr.put(Tracked(&mut __own), __tmp);
            proof { $set.tracked_insert($idx, __own); }
        })
    };
    ($ptr:expr => $field1:tt . $field2:tt <- $val:expr; $set:expr , $idx:expr) => {
        verus_exec_expr!(
        {
            let tracked mut __own = $set.tracked_remove($idx);
            let mut __tmp = $ptr.take(Tracked(&mut __own));
            __tmp.$field1.$field2 = $val;
            $ptr.put(Tracked(&mut __own), __tmp);
            proof { $set.tracked_insert($idx, __own); }
        })
    };
    ($ptr:expr => $field:tt <- $val:expr; $set:expr , $idx:expr, inner) => {
        verus_exec_expr!(
        {
            let tracked mut __own = $set.tracked_remove($idx);
            let mut __tmp = $ptr.take(Tracked(&mut __own));
            __tmp.$field = $val;
            $ptr.put(Tracked(&mut __own.points_to), __tmp);
            proof { $set.tracked_insert($idx, __own); }
        })
    };
    ($ptr:expr => $field1:tt . $field2:tt <- $val:expr; $set:expr , $idx:expr, inner) => {
        verus_exec_expr!(
        {
            let tracked mut __own = $set.tracked_remove($idx);
            let mut __tmp = $ptr.take(Tracked(&mut __own));
            __tmp.$field1.$field2 = $val;
            $ptr.put(Tracked(&mut __own.points_to), __tmp);
            proof { $set.tracked_insert($idx, __own); }
        })
    };
    ($ptr:expr => $field:tt <- $val:expr; $perm:expr) => {
        verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked(&mut $perm));
            __tmp.$field = $val;
            $ptr.put(Tracked(&mut $perm), __tmp);
        })
    };
    ($ptr:expr => $field1:tt . $field2:tt <- $val:expr; $perm:expr) => {
        verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked(&mut $perm));
            __tmp.$field1.$field2 = $val;
            $ptr.put(Tracked(&mut $perm), __tmp);
        })
    };
    ($ptr:expr => $field:tt += $val:expr; $perm:expr) => {
        verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked(&mut $perm));
            __tmp.$field = __tmp.$field + $val;
            $ptr.put(Tracked(&mut $perm), __tmp);
        })
    };
    ($ptr:expr => $field:tt -= $val:expr; $perm:expr) => {
        verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked(&mut $perm));
            __tmp.$field = __tmp.$field - $val;
            $ptr.put(Tracked(&mut $perm), __tmp);
        })
    };
    // Meta-cell write: mutates a single field of the metadata `M` via a
    // surgical view on the storage cell, leaving ref_count/in_list/vtable_ptr
    // perms untouched (analogous to `unsafe { ptr.as_mut() }.field = val` in
    // ../vostd, but verified). Requires `Metadata` to be in scope.
    ($ptr:expr => $field:tt <- $val:expr, Meta($perm:expr)) => {
        verus_exec_expr!(
        {
            let __link = $ptr.borrow_mut(Tracked($perm));
            let __contents = &mut __link.metadata;
            __contents.$field = $val;
        })
    };
}

pub use crate::{borrow_field, update_field};
