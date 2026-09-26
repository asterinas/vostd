use vstd::prelude::*;

use crate::panic::*;

/* Verus cannot translate formatting machinery used by `core::panic!`; select the modeled
 * diverging boundary only while retaining ghost bodies.
 * Origin Rust: <none; new executable code>
 */
#[macro_export]
macro_rules! panic {
    ($($arg:tt)*) => {{
        #[cfg(verus_keep_ghost_body)]
        {
            $crate::panic::panic_diverge()
        }
        #[cfg(not(verus_keep_ghost_body))]
        {
            ::core::panic!($($arg)*)
        }
    }};
}

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
