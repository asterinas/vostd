#![allow(non_snake_case)]
//! A verified version of the [`bitflags`](https://docs.rs/bitflags/latest/bitflags/) crate.
//!
//! The macro [`bitflags!`] generates a single `struct` whose layout matches
//! the one produced by the upstream `bitflags` crate
//! (see [`bitflags::example_generated::Flags`]):
//!
//! ```text
//! pub struct Flags { bits: T } // bits is private
//! impl Flags {
//!     pub const fn A() -> Self;   // one factory per declared flag
//!     ...
//!     pub const fn empty() -> Self;
//!     pub const fn all() -> Self;
//!     pub const fn bits(&self) -> T;
//!     pub const fn from_bits(bits: T) -> Option<Self>;
//!     pub const fn from_bits_truncate(bits: T) -> Self;
//!     pub const fn contains(&self, other: Self) -> bool;
//!     pub const fn intersects(&self, other: Self) -> bool;
//!     pub fn insert(&mut self, other: Self);
//!     pub fn toggle(&mut self, other: Self);
//! }
//! ```
//!
//! NOTE: unlike upstream `bitflags`, the per-flag accessors are `pub const fn`
//! factories (`Flags::A()`) instead of associated constants (`Flags::A`). This
//! is required because the `bits` field is private:
//! Verus refuses to publish a constructor for an opaque datatype through a `pub const`.
//!
//! Only **literal** values are supported for each flag.
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

pub use paste;

#[doc(hidden)]
#[macro_export]
macro_rules! __bitflags_cfg_expr {
    (() $base:expr) => {
        $base
    };
    ((#[cfg($($cfg:tt)*)] $($rest:tt)*) $base:expr) => {
        (cfg!($($cfg)*) && $crate::__bitflags_cfg_expr!(($($rest)*) $base))
    };
    ((#[$_other:meta] $($rest:tt)*) $base:expr) => {
        $crate::__bitflags_cfg_expr!(($($rest)*) $base)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __bitflags_cfg_guarded_expr {
    (() $e:expr) => {
        $e
    };
    ((#[cfg($($cfg:tt)*)] $($rest:tt)*) $e:expr) => {{
        #[cfg($($cfg)*)]
        {
            $crate::__bitflags_cfg_guarded_expr!(($($rest)*) $e)
        }
        #[cfg(not($($cfg)*))]
        {
            true
        }
    }};
    ((#[$_other:meta] $($rest:tt)*) $e:expr) => {
        $crate::__bitflags_cfg_guarded_expr!(($($rest)*) $e)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __bitflags_cfg_guarded_stmt {
    (() $stmt:stmt) => {
        $stmt
    };
    ((#[cfg($($cfg:tt)*)] $($rest:tt)*) $stmt:stmt) => {
        #[cfg($($cfg)*)]
        {
            $crate::__bitflags_cfg_guarded_stmt!(($($rest)*) $stmt)
        }
    };
    ((#[$_other:meta] $($rest:tt)*) $stmt:stmt) => {
        $crate::__bitflags_cfg_guarded_stmt!(($($rest)*) $stmt)
    };
}

/// A macro wrapper for quickly defining bitflags with verified
/// properties in Verus. It only supports literal values for the bits.
///
/// # Example
///
/// ```rust,norun
/// bitflags! {
///     pub struct Flags: u32 {
///         const A = 0b00000001;
///         const B = 0b00000010;
///         const C = 0b00000100;
///         const ABC = 0b00000111;
///     }
/// }
///
/// let f = Flags::A | Flags::B;
/// assert!(f.contains(Flags::A));
/// ```
#[verusfmt::skip]
#[macro_export]
macro_rules! bitflags {
    (
        $(#[$outer:meta])*
        $vis:vis struct $name:ident: $T:ty {
            $(
                $(#[$inner:ident $($args:tt)*])*
                const $Flag:ident = $value:expr;
            )*
        }

        $($t:tt)*
    ) => {
        paste::paste! {
        verus! {
            $(#[$outer])*
            #[repr(transparent)]
            $vis struct $name {
                /// The raw bits backing this flags value.
                bits: $T,
            }

            impl ::core::clone::Clone for $name {
                #[inline]
                fn clone(&self) -> (r: Self)
                    returns self
                {
                    Self {
                        bits: self.bits,
                    }
                }
            }

            impl ::core::marker::Copy for $name {}

            impl ::vstd::view::View for $name {
                type V = ::vstd::set::Set<[< __ghost $name >]>;

                open spec fn view(&self) -> Self::V {
                    Self::flags_from_bits(self.bits())
                }
            }

            #[allow(non_camel_case_types)]
            $vis ghost enum [< __ghost $name >] {
                $(
                    [< __ghost $Flag >],
                )*
            }

            impl [< __ghost $name >] {
                $vis open spec fn enabled(self) -> bool {
                    match self {
                        $(
                            [< __ghost $name >]::[< __ghost $Flag >] => $crate::__bitflags_cfg_expr! {
                                ($(#[$inner $($args)*])*) true
                            },
                        )*
                    }
                }

                $vis open spec fn bit(self) -> $T {
                    match self {
                        $(
                            [< __ghost $name >]::[< __ghost $Flag >] => (($value) as $T),
                        )*
                    }
                }
            }

            impl $name {
                $vis open spec fn flags_spec(&self) -> ::vstd::set::Set<[< __ghost $name >]> {
                    Self::flags_from_bits(self.bits())
                }

                $vis open spec fn flags_from_bits(bits: $T) -> ::vstd::set::Set<[< __ghost $name >]> {
                    ::vstd::set::Set::new(|flag: [< __ghost $name >]| {
                        flag.enabled() && (bits & flag.bit()) == flag.bit()
                    })
                }

                closed spec fn from_bits_unchecked_spec(bits: $T) -> Self {
                    Self { bits }
                }

                #[verifier::when_used_as_spec(from_bits_unchecked_spec)]
                const fn from_bits_unchecked(bits: $T) -> (r: Self)
                    ensures
                        r.bits() == bits,
                        r.flags_spec() == Self::flags_from_bits(bits),
                    returns
                        Self::from_bits_unchecked(bits),
                {
                    Self { bits }
                }

                $(
                    $vis closed spec fn [< $Flag _spec >]() -> Self {
                        Self::from_bits_unchecked_spec($value as $T)
                    }

                    $(#[$inner $($args)*])*
                    #[verifier::when_used_as_spec([< $Flag _spec >])]
                    $vis const fn $Flag() -> (r: Self)
                        ensures
                            r.bits() == ($value),
                            r.flags_spec() == Self::flags_from_bits(($value) as $T),
                        returns Self::[< $Flag _spec >](),
                    {
                        Self::from_bits_unchecked($value)
                    }
                )*

                /// The bitwise OR of every declared flag (the "all" bits mask).
                $vis open spec fn all_bits_spec() -> $T {
                    (0 as $T) $(| (
                        if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true } {
                            (($value) as $T)
                        } else {
                            0 as $T
                        }
                    ))*
                }

                #[verifier::when_used_as_spec(all_bits_spec)]
                $vis const fn all_bits() -> $T
                    returns Self::all_bits(),
                {
                    (0 as $T) $(| (
                        if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true } {
                            (($value) as $T)
                        } else {
                            0 as $T
                        }
                    ))*
                }

                $(
                    $(#[$inner $($args)*])*
                    proof fn [< lemma_ $Flag _constant >]()
                        ensures
                            Self::$Flag().bits() == (($value) as $T),
                    {
                        let flag = Self::$Flag();
                        assert(flag.bits() == (($value) as $T));
                    }
                )*

                $vis broadcast proof fn lemma_consts()
                    ensures
                        $(
                            #![trigger $crate::__bitflags_cfg_guarded_expr!(
                                ($(#[$inner $($args)*])*)
                                Self::$Flag().bits()
                            )]
                            $crate::__bitflags_cfg_guarded_expr!(
                                ($(#[$inner $($args)*])*)
                                Self::$Flag().bits() == (($value) as $T)
                            ),
                        )*
                {
                    $(
                        $crate::__bitflags_cfg_guarded_stmt!(
                            ($(#[$inner $($args)*])*)
                            Self::[< lemma_ $Flag _constant >]()
                        );
                    )*
                }

                /// The raw bits stored inside this flags value.
                $vis closed spec fn bits_spec(&self) -> $T { self.bits }

                #[verifier::when_used_as_spec(bits_spec)]
                $vis const fn bits(&self) -> $T
                    returns self.bits(),
                {
                    self.bits
                }

                $vis closed spec fn empty_spec() -> Self {
                    Self::from_bits_unchecked_spec(0)
                }

                #[verifier::when_used_as_spec(empty_spec)]
                $vis const fn empty() -> (r: Self)
                    ensures
                        r.bits() == 0,
                        r.flags_spec() == Self::flags_from_bits(0),
                    returns Self::empty(),
                {
                    Self::from_bits_unchecked(0)
                }

                $vis closed spec fn all_spec() -> Self {
                    Self::from_bits_unchecked_spec(Self::all_bits_spec())
                }

                #[verifier::when_used_as_spec(all_spec)]
                $vis const fn all() -> (r: Self)
                    ensures
                        r == Self::all_spec(),
                {
                    Self::from_bits_unchecked(Self::all_bits())
                }

                $vis open spec fn contains_spec(&self, other: Self) -> bool {
                    other@.subset_of(self@)
                }

                $vis open spec fn contains_flags_spec(&self, other: Self) -> bool {
                    self.contains(other)
                }

                #[verifier::when_used_as_spec(contains_spec)]
                $vis const fn contains(&self, other: Self) -> bool
                    returns self.contains(other),
                {
                    let res = $(
                        (
                            !$crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true }
                            || (other.bits & (($value) as $T)) != (($value) as $T)
                            || (self.bits & (($value) as $T)) == (($value) as $T)
                        )
                    )&&*;
                    proof {
                        assert(self@ =~= Self::flags_from_bits(self.bits()));
                        assert(other@ =~= Self::flags_from_bits(other.bits()));

                        if res {
                            assert forall|flag: [< __ghost $name >]| #[trigger]
                                other@.contains(flag) implies self@.contains(flag) by {
                                match flag {
                                    $(
                                        [< __ghost $name >]::[< __ghost $Flag >] => {
                                            assert(other@.contains(flag));
                                            assert(Self::flags_from_bits(other.bits()).contains(flag));
                                            assert(flag.enabled());
                                            if flag.enabled() {
                                                assert((other.bits() & (($value) as $T)) == (($value) as $T));
                                                assert((self.bits() & (($value) as $T)) == (($value) as $T));
                                                assert(Self::flags_from_bits(self.bits()).contains(flag));
                                            }
                                        },
                                    )*
                                }
                            }
                            assert(other@.subset_of(self@));
                        }

                        if other@.subset_of(self@) {
                            $(
                                if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true }
                                    && (other.bits() & (($value) as $T)) == (($value) as $T)
                                {
                                    assert(Self::flags_from_bits(other.bits()).contains(
                                        [< __ghost $name >]::[< __ghost $Flag >],
                                    ));
                                    assert(other@.contains([< __ghost $name >]::[< __ghost $Flag >]));
                                    assert(self@.contains([< __ghost $name >]::[< __ghost $Flag >]));
                                    assert(Self::flags_from_bits(self.bits()).contains(
                                        [< __ghost $name >]::[< __ghost $Flag >],
                                    ));
                                    assert((self.bits() & (($value) as $T)) == (($value) as $T));
                                }
                            )*
                            assert(res);
                        }
                    }
                    res
                }

                $vis open spec fn intersects_spec(&self, other: Self) -> bool {
                    exists|flag: [< __ghost $name >]| #[trigger] self@.contains(flag) && other@.contains(flag)
                }

                #[verifier::when_used_as_spec(intersects_spec)]
                $vis const fn intersects(&self, other: Self) -> bool
                    returns self.intersects(other),
                {
                    let res = $(
                        (
                            $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true }
                            && (self.bits & (($value) as $T)) == (($value) as $T)
                            && (other.bits & (($value) as $T)) == (($value) as $T)
                        )
                    )||*;
                    proof {

                        if res {
                            $(
                                if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true }
                                    && (self.bits() & (($value) as $T)) == (($value) as $T)
                                    && (other.bits() & (($value) as $T)) == (($value) as $T)
                                {
                                    assert(self@.contains([< __ghost $name >]::[< __ghost $Flag >]));
                                    assert(other@.contains([< __ghost $name >]::[< __ghost $Flag >]));
                                    assert(exists|flag: [< __ghost $name >]|
                                        #[trigger] self@.contains(flag) && other@.contains(flag));
                                }
                            )*
                            assert(exists|flag: [< __ghost $name >]|
                                #[trigger] self@.contains(flag) && other@.contains(flag));
                        }

                        if exists|flag: [< __ghost $name >]| #[trigger] self@.contains(flag) && other@.contains(flag) {
                            let flag = choose|flag: [< __ghost $name >]| self@.contains(flag) && other@.contains(flag);
                            assert(self@.contains(flag));
                            assert(other@.contains(flag));
                            match flag {
                                $(
                                    [< __ghost $name >]::[< __ghost $Flag >] => {
                                        assert(flag.enabled());
                                        assert((self.bits() & (($value) as $T)) == (($value) as $T));
                                        assert((other.bits() & (($value) as $T)) == (($value) as $T));
                                    },
                                )*
                            }
                            assert(res);
                        }
                    }
                    res
                }

                $vis closed spec fn from_bits_truncate_spec(bits: $T) -> Self {
                    Self::from_bits_unchecked_spec(bits & Self::all_bits())
                }

                $vis closed spec fn from_bits_retain_spec(bits: $T) -> Self {
                    Self::from_bits_unchecked_spec(bits)
                }

                #[verifier::when_used_as_spec(from_bits_retain_spec)]
                $vis const fn from_bits_retain(bits: $T) -> (r: Self)
                    ensures
                        r.bits() == bits,
                        r.flags_spec() == Self::flags_from_bits(bits),
                    returns Self::from_bits_retain(bits),
                {
                    Self::from_bits_unchecked(bits)
                }

                #[verifier::when_used_as_spec(from_bits_truncate_spec)]
                $vis const fn from_bits_truncate(bits: $T) -> (r: Self)
                    returns Self::from_bits_truncate(bits),
                {
                    Self::from_bits_unchecked(bits & Self::all_bits())
                }

                $vis closed spec fn from_bits_spec(bits: $T) -> Option<Self> {
                    if (bits & Self::all_bits()) == bits {
                        Some(Self::from_bits_unchecked_spec(bits))
                    } else {
                        None
                    }
                }

                #[verifier::when_used_as_spec(from_bits_spec)]
                $vis const fn from_bits(bits: $T) -> (r: Option<Self>)
                    ensures
                        r is Some == ((bits & Self::all_bits()) == bits),
                        r matches Some(flags_value) ==> {
                            &&& flags_value.bits() == bits
                            &&& flags_value.flags_spec() == Self::flags_from_bits(bits)
                        },
                    returns
                        Self::from_bits(bits),
                {
                    if (bits & Self::all_bits()) == bits {
                        Some(Self::from_bits_unchecked(bits))
                    } else {
                        None
                    }
                }

                $vis closed spec fn remove_spec(self, other: Self) -> Self {
                    Self::from_bits_unchecked_spec(self.bits() & !other.bits())
                }

                $vis fn insert(&mut self, other: Self)
                    ensures
                        final(self).bits() == (old(self).bits() | other.bits()),
                        final(self).flags_spec() == Self::flags_from_bits(
                            old(self).bits() | other.bits(),
                        ),
                {
                    let bits = self.bits | other.bits;
                    *self = Self::from_bits_unchecked(bits);
                }

                $vis fn remove(&mut self, other: Self)
                    ensures
                        *final(self) == old(self).remove_spec(other),
                        final(self).bits() == (old(self).bits() & !other.bits()),
                        final(self).flags_spec() == Self::flags_from_bits(
                            old(self).bits() & !other.bits(),
                        ),
                {
                    let bits = self.bits & !other.bits;
                    *self = Self::from_bits_unchecked(bits);
                }

                /// The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
                $vis fn toggle(&mut self, other: Self)
                    ensures
                        final(self).bits() == (old(self).bits() ^ other.bits()),
                        final(self).flags_spec() == Self::flags_from_bits(
                            old(self).bits() ^ other.bits(),
                        ),
                {
                    let bits = self.bits ^ other.bits;
                    *self = Self::from_bits_unchecked(bits);
                }


                $vis closed spec fn union_spec(self, other: Self) -> Self {
                    Self::from_bits_unchecked_spec(self.bits() | other.bits())
                }

                #[verifier::when_used_as_spec(union_spec)]
                $vis const fn union(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() | other.bits()),
                    returns self.union(other),
                {
                    Self::from_bits_unchecked(self.bits | other.bits)
                }

                $vis closed spec fn intersection_spec(self, other: Self) -> Self {
                    Self::from_bits_unchecked_spec(self.bits() & other.bits())
                }

                #[verifier::when_used_as_spec(intersection_spec)]
                $vis const fn intersection(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() & other.bits()),
                    returns self.intersection(other),
                {
                    Self::from_bits_unchecked(self.bits & other.bits)
                }

                $vis closed spec fn difference_spec(self, other: Self) -> Self {
                    Self::from_bits_unchecked_spec(self.bits() & !other.bits())
                }

                #[verifier::when_used_as_spec(difference_spec)]
                $vis const fn difference(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() & !other.bits()),
                    returns self.difference(other),
                {
                    Self::from_bits_unchecked(self.bits & !other.bits)
                }

                $vis closed spec fn symmetric_difference_spec(self, other: Self) -> Self {
                    Self::from_bits_unchecked_spec(self.bits() ^ other.bits())
                }

                #[verifier::when_used_as_spec(symmetric_difference_spec)]
                $vis const fn symmetric_difference(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() ^ other.bits()),
                    returns self.symmetric_difference(other),
                {
                    Self::from_bits_unchecked(self.bits ^ other.bits)
                }
            }

            impl core::cmp::PartialEq for $name {
                fn eq(&self, other: &Self) -> (r: bool)
                    ensures r == (self.bits() == other.bits()),
                {
                    self.bits == other.bits
                }
            }

            impl ::vstd::std_specs::cmp::PartialEqSpecImpl for $name {
                closed spec fn obeys_eq_spec() -> bool { true }

                closed spec fn eq_spec(&self, other: &Self) -> bool {
                    self.bits() == other.bits()
                }
            }

            impl core::cmp::Eq for $name {}

            impl ::vstd::std_specs::ops::BitOrSpecImpl for $name {
                open spec fn obeys_bitor_spec() -> bool { true }

                open spec fn bitor_req(self, rhs: Self) -> bool { true }

                open spec fn bitor_spec(self, rhs: Self) -> Self::Output {
                    self.union(rhs)
                }
            }

            impl core::ops::BitOr for $name {
                type Output = Self;
                fn bitor(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() | other.bits()),
                {
                    Self::from_bits_unchecked(self.bits | other.bits)
                }
            }

            impl vstd::std_specs::ops::BitAndSpecImpl for $name {
                open spec fn obeys_bitand_spec() -> bool { true }

                open spec fn bitand_req(self, rhs: Self) -> bool { true }

                open spec fn bitand_spec(self, rhs: Self) -> Self::Output {
                    self.intersection(rhs)
                }
            }

            impl core::ops::BitAnd for $name {
                type Output = Self;
                fn bitand(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() & other.bits()),
                {
                    Self::from_bits_unchecked(self.bits & other.bits)
                }
            }

            impl vstd::std_specs::ops::BitXorSpecImpl for $name {
                open spec fn obeys_bitxor_spec() -> bool { true }

                open spec fn bitxor_req(self, rhs: Self) -> bool { true }

                open spec fn bitxor_spec(self, rhs: Self) -> Self::Output {
                    self.symmetric_difference(rhs)
                }
            }

            impl core::ops::BitXor for $name {
                type Output = Self;
                fn bitxor(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() ^ other.bits()),
                {
                    Self::from_bits_unchecked(self.bits ^ other.bits)
                }
            }

            impl vstd::std_specs::ops::SubSpecImpl for $name {
                open spec fn obeys_sub_spec() -> bool { true }

                open spec fn sub_req(self, rhs: Self) -> bool { true }

                open spec fn sub_spec(self, rhs: Self) -> Self::Output {
                    self.difference(rhs)
                }
            }

            impl core::ops::Sub for $name {
                type Output = Self;
                fn sub(self, other: Self) -> (r: Self)
                    ensures
                        r.bits() == (self.bits() & !other.bits()),
                {
                    self.difference(other)
                }
            }

            impl vstd::std_specs::ops::NotSpecImpl for $name {
                open spec fn obeys_not_spec() -> bool { true }

                open spec fn not_req(self) -> bool { true }

                closed spec fn not_spec(self) -> Self::Output {
                    Self::from_bits_unchecked_spec(!self.bits() & Self::all_bits())
                }
            }

            impl core::ops::Not for $name {
                type Output = Self;

                fn not(self) -> (r: Self)
                    ensures
                        r.bits() == (!self.bits() & $name::all_bits()),
                {
                    Self::from_bits_unchecked(!self.bits & $name::all_bits())
                }
            }

        } // verus!

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.bits).finish()
            }
        }

        } // paste!
    };
}

/// Defines quick named compositions of existing flags.
///
/// `bitflags!` only accepts literal values for `const X = ...`, so it cannot
/// express something like `const AB = A | B;`. This helper macro adds extra
/// factory methods to an existing flags type, each one OR-ing together a list
/// of `$T` expressions and truncating any bits that are not declared on the
/// type.
///
/// # Example
///
/// ```rust,ignore
/// bitflags! {
///     pub struct Flags: u32 {
///         const A = 0b001;
///         const B = 0b010;
///         const C = 0b100;
///     }
/// }
///
/// bitflags_quick! {
///     Flags,
///     ab: { Flags::A().bits(), Flags::B().bits() },
///     ac: { Flags::A().bits(), Flags::C().bits() },
/// }
///
/// let f = Flags::ab();          // bits == 0b011
/// assert!(f.contains(Flags::A()));
/// ```
#[macro_export]
#[verusfmt::skip]
macro_rules! bitflags_quick {
    ($name:ident, $($bit_name:ident : { $($bits:expr),* $(,)? }),* $(,)?) => {
        verus! {
            impl $name {
                $(
                    pub fn $bit_name() -> (r: Self)
                        ensures r == Self::from_bits_truncate( ($($bits)|*) as _ ),
                    {
                        Self::from_bits_truncate( ($($bits)|*) as _ )
                    }
                )*
            }
        }
    };
}

// ---------------------------------------------------------------------------
// Smoke test: instantiate the `bitflags!` macro to make sure it expands and
// verifies. Mirrors `bitflags::example_generated::Flags`.
// ---------------------------------------------------------------------------

bitflags! {
    pub struct Flags: u32 {
        const A = 0b00000001;
        const B = 0b00000010;
        const C = 0b00000100;
        const ABC = 0b00000111;
    }
}

verus! {

#[allow(dead_code)]
fn _bitflags_smoke_test() {
    let a = Flags::A();
    let b = Flags::B();
    let c = Flags::C();
    let abc = Flags::ABC();

    assert(a.bits() == 0b001u32);
    assert(a.bits() == Flags::A().bits());
    assert(b.bits() == 0b010u32);
    assert(c.bits() == 0b100u32);
    assert(abc.bits() == 0b111u32);
    assert(a@ =~= Flags::flags_from_bits(a.bits()));
    assert(abc@ =~= Flags::flags_from_bits(abc.bits()));

    let abc_b = abc.bits();
    let a_b = a.bits();
    let b_b = b.bits();
    assert((abc_b & a_b) == a_b) by (bit_vector)
        requires
            abc_b == 0b111u32 && a_b == 0b001u32,
    ;
    assert((abc_b & b_b) == b_b) by (bit_vector)
        requires
            abc_b == 0b111u32 && b_b == 0b010u32,
    ;
    assert((a_b & b_b) != b_b) by (bit_vector)
        requires
            a_b == 0b001u32 && b_b == 0b010u32,
    ;
    assert forall|flag: __ghostFlags| #[trigger] abc@.contains(flag) by {
        assert(abc@ =~= Flags::flags_from_bits(abc.bits()));
        match flag {
            __ghostFlags::__ghostA => {
                assert((abc_b & 0b001u32) == 0b001u32) by (bit_vector)
                    requires abc_b == 0b111u32,
                ;
                assert((abc.bits() & 0b001u32) == 0b001u32);
            },
            __ghostFlags::__ghostB => {
                assert((abc_b & 0b010u32) == 0b010u32) by (bit_vector)
                    requires abc_b == 0b111u32,
                ;
                assert((abc.bits() & 0b010u32) == 0b010u32);
            },
            __ghostFlags::__ghostC => {
                assert((abc_b & 0b100u32) == 0b100u32) by (bit_vector)
                    requires abc_b == 0b111u32,
                ;
                assert((abc.bits() & 0b100u32) == 0b100u32);
            },
            __ghostFlags::__ghostABC => {
                assert((abc_b & 0b111u32) == 0b111u32) by (bit_vector)
                    requires abc_b == 0b111u32,
                ;
                assert((abc.bits() & 0b111u32) == 0b111u32);
            },
        }
    }
    assert(a@.subset_of(abc@));
    assert(b@.subset_of(abc@));
    assert(b@.contains(__ghostFlags::__ghostB)) by {
        assert(b@ =~= Flags::flags_from_bits(b.bits()));
        assert((b_b & 0b010u32) == 0b010u32) by (bit_vector)
            requires b_b == 0b010u32,
        ;
        assert((b.bits() & 0b010u32) == 0b010u32);
    }
    assert(a@.contains(__ghostFlags::__ghostA)) by {
        assert(a@ =~= Flags::flags_from_bits(a.bits()));
        assert((a_b & 0b001u32) == 0b001u32) by (bit_vector)
            requires a_b == 0b001u32,
        ;
        assert((a.bits() & 0b001u32) == 0b001u32);
    }
    assert(!a@.contains(__ghostFlags::__ghostB)) by {
        assert(a@ =~= Flags::flags_from_bits(a.bits()));
        assert((a_b & 0b010u32) != 0b010u32) by (bit_vector)
            requires a_b == 0b001u32,
        ;
        assert((a.bits() & 0b010u32) != 0b010u32);
    }
    assert(!b@.subset_of(a@)) by {
        if b@.subset_of(a@) {
            assert(a@.contains(__ghostFlags::__ghostB));
        }
    }
    assert(abc.contains(a));
    assert(abc.contains(b));
    assert(!a.contains(b));

    let mut removed = abc;
    removed.remove(a);
    let removed_b = removed.bits();
    assert(removed_b == (abc_b & !a_b));
    assert(removed_b == 0b110u32) by (bit_vector)
        requires
            removed_b == (abc_b & !a_b),
            abc_b == 0b111u32 && a_b == 0b001u32,
    ;
    assert(removed@ =~= Flags::flags_from_bits(removed.bits()));

    assert(abc.intersects(a)) by {
        assert(abc@.contains(__ghostFlags::__ghostA));
        assert(a@.contains(__ghostFlags::__ghostA));
        assert(exists|flag: __ghostFlags| #[trigger] abc@.contains(flag) && a@.contains(flag));
    }
    assert(!a.intersects(b)) by {
        assert forall|flag: __ghostFlags| !(#[trigger] a@.contains(flag) && b@.contains(flag)) by {
            match flag {
                __ghostFlags::__ghostA => {
                    assert(b@ =~= Flags::flags_from_bits(b.bits()));
                    assert((b_b & 0b001u32) != 0b001u32) by (bit_vector)
                        requires b_b == 0b010u32,
                    ;
                    assert((b.bits() & 0b001u32) != 0b001u32);
                    assert(!b@.contains(flag));
                },
                __ghostFlags::__ghostB => {
                    assert(!a@.contains(flag));
                },
                __ghostFlags::__ghostC => {
                    assert(a@ =~= Flags::flags_from_bits(a.bits()));
                    assert((a_b & 0b100u32) != 0b100u32) by (bit_vector)
                        requires a_b == 0b001u32,
                    ;
                    assert((a.bits() & 0b100u32) != 0b100u32);
                    assert(!a@.contains(flag));
                },
                __ghostFlags::__ghostABC => {
                    assert(a@ =~= Flags::flags_from_bits(a.bits()));
                    assert((a_b & 0b111u32) != 0b111u32) by (bit_vector)
                        requires a_b == 0b001u32,
                    ;
                    assert((a.bits() & 0b111u32) != 0b111u32);
                    assert(!a@.contains(flag));
                },
            }
        }
        assert(!exists|flag: __ghostFlags| #[trigger] a@.contains(flag) && b@.contains(flag));
    }

}

} // verus!
