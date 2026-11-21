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
    // Borrow each operand once, as in core::assert_eq!, and defer formatting to the panic handler.
    ($l:expr, $r:expr, $($msg:tt)+) => {
        match (&$l, &$r) {
            (left, right) => {
                if !(*left == *right) {
                    ::core::panic!("{}", $crate::panic::PanicMessage(::core::format_args!(
                        "assertion `left == right` failed: {}\n  left: {:?}\n right: {:?}",
                        $crate::panic::PanicMessage(::core::format_args!($($msg)+)),
                        *left, *right,
                    )))
                }
            }
        }
    };
    ($l:expr, $r:expr) => {
        if ($l != $r) {
            $crate::panic::panic_diverge()
        }
    };
}

#[macro_export]
macro_rules! debug_assert {
    ($cond:expr) => {
        #[cfg(debug_assertions)]
        if !($cond) {
            $crate::panic::panic_diverge()
        }
    };
    ($cond:expr, $msg:literal) => {
        #[cfg(debug_assertions)]
        if !($cond) {
            $crate::panic::panic_diverge()
        }
    };
}

#[macro_export]
macro_rules! debug_assert_eq {
    ($l:expr, $r:expr) => {
        #[cfg(debug_assertions)]
        if ($l != $r) {
            $crate::panic::panic_diverge()
        }
    };
}
