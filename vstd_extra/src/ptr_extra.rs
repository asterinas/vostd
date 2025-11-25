use vstd::prelude::*;

use vstd::simple_pptr::*;

verus! {

#[macro_export]
macro_rules! borrow_field {
    ($ptr:expr) => { $ptr };
    ($ptr:expr => $field:tt, $perm:expr) => {
        verus_exec_expr!(
            $ptr.borrow(Tracked($perm.borrow())).$field
    )};
}

#[macro_export]
macro_rules! update_field {
    ($ptr:expr => $field:tt <- $val:expr; $set:expr , $idx:expr) => {
        verus_exec_expr!(
        {
            let tracked mut __own = $set.tracked_remove($idx);
            let mut __tmp = $ptr.take(Tracked(__own.borrow_mut()));
            __tmp.$field = $val;
            $ptr.put(Tracked(__own.borrow_mut()), __tmp);
            proof { $set.tracked_insert($idx, __own); }
        })
    };
    ($ptr:expr => $field:tt <- $val:expr; $perm:expr) => {
        verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm.borrow_mut()));
            __tmp.$field = $val;
            $ptr.put(Tracked($perm.borrow_mut()), __tmp);
        })
    };
    ($ptr:expr => $field:tt += $val:expr; $perm:expr) => {
        verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm.borrow_mut()));
            __tmp.$field = __tmp.$field + $val;
            $ptr.put(Tracked($perm.borrow_mut()), __tmp);
        })
    };
    ($ptr:expr => $field:tt -= $val:expr; $perm:expr) => {
        verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm.borrow_mut()));
            __tmp.$field = __tmp.$field - $val;
            $ptr.put(Tracked($perm.borrow_mut()), __tmp);
        })
    }
}

} // verus!
pub use {borrow_field, update_field};
