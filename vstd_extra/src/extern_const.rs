///! This module provides a macro to define a constant that can be used when
///! crossing crates.
#[macro_export]
macro_rules! extern_const {
    ($(#[$doc:meta])* $_vis:vis $name:ident [ $name_spec:ident, $name_const:ident ] : $_ty:ty = $value:expr) => {
        verus! {
        #[doc = concat!("The constant `", stringify!($name), "`.")]
        $(#[$doc])*
        $_vis const $name_const: $_ty = $value;

        #[doc = concat!("The specification of the constant `", stringify!($name), "`.")]
        #[verifier::inline]
        #[allow(non_snake_case)]
        $_vis open spec fn $name_spec() -> $_ty { $name_const }

        #[doc = concat!("The executable code of constant `", stringify!($name), "` when used cross-crate.")]
        #[allow(non_snake_case)]
        #[inline(always)]
        #[verifier::when_used_as_spec($name_spec)]
        $_vis const fn $name() -> (val: $_ty)
            ensures val == $name_const
        { $name_const }
    }
    };
}

pub use extern_const;
