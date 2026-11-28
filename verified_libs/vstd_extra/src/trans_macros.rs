#[doc(hidden)]
pub use vstd as __vstd;

// vpanic! expands through `vstd::`. Supply that path from this crate so
// callers of the exported macros can use them without a direct vstd dependency.
#[doc(hidden)]
#[macro_export]
macro_rules! __vstd_extra_vpanic {
    () => {{
        use $crate::trans_macros::__vstd as vstd;
        vstd::vpanic!("");
    }};
}

/* Verus cannot translate formatting machinery used by `core::panic!`; select the modeled
 * diverging boundary only while retaining ghost bodies.
 * Origin Rust: <none; new executable code>
 */
#[macro_export]
macro_rules! panic {
    ($($arg:tt)*) => {{
        #[cfg(verus_keep_ghost_body)]
        {
            $crate::__vstd_extra_vpanic!()
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
            $crate::__vstd_extra_vpanic!()
        }
    };
    ($cond:expr, $msg:literal) => {
        if !($cond) {
            $crate::__vstd_extra_vpanic!()
        }
    };
}

#[macro_export]
macro_rules! assert_eq {
    ($l:expr, $r:expr) => {
        if ($l != $r) {
            $crate::__vstd_extra_vpanic!()
        }
    };
}

#[macro_export]
macro_rules! debug_assert {
    ($cond:expr) => {
        #[cfg(debug_assertions)]
        if !($cond) {
            $crate::__vstd_extra_vpanic!()
        }
    };
    ($cond:expr, $msg:literal) => {
        #[cfg(debug_assertions)]
        if !($cond) {
            $crate::__vstd_extra_vpanic!()
        }
    };
}

#[macro_export]
macro_rules! debug_assert_eq {
    ($l:expr, $r:expr) => {
        #[cfg(debug_assertions)]
        if ($l != $r) {
            $crate::__vstd_extra_vpanic!()
        }
    };
}
