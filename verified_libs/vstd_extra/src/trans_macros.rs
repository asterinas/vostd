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
