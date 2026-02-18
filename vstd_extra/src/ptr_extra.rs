use vstd::prelude::*;

use vstd::simple_pptr::*;

verus! {

#[macro_export]
macro_rules! borrow_field {
    ($ptr:expr) => { $ptr };
    ($ptr:expr => $field:tt, $perm:expr) => {
        verus_exec_expr!(
            $ptr.borrow(Tracked($perm)).$field
    )};
    ($ptr:expr => $field1:tt . $field2:tt, $perm:expr) => {
        verus_exec_expr!(
            $ptr.borrow(Tracked($perm)).$field1.$field2
    )};
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
    }
}

} // verus!
pub use {borrow_field, update_field};
