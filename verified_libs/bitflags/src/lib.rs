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
//!     pub const fn is_empty(&self) -> bool;
//!     pub const fn is_all(&self) -> bool;
//!     pub const fn contains(&self, other: Self) -> bool;
//!     pub const fn intersects(&self, other: Self) -> bool;
//!     pub fn insert(&mut self, other: Self);
//!     pub fn remove(&mut self, other: Self);
//!     pub fn toggle(&mut self, other: Self);
//!     pub fn set(&mut self, other: Self, value: bool);
//! }
//! ```
//!
//! NOTE: unlike upstream `bitflags`, the per-flag accessors are `pub const fn`
//! factories (`Flags::A()`) instead of associated constants (`Flags::A`). This
//! is required because the `bits` field is private:
//! Verus refuses to publish a constructor for an opaque datatype through a `pub const`.
//!
//! Upstream's `Flags` trait metadata (`FLAGS`, iterators, lookup helpers, etc.)
//! is represented here by Verus-only specs and lemmas around the inherent APIs.
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
/// let f = Flags::A() | Flags::B();
/// assert!(f.contains(Flags::A()));
/// ```
// Upstream expands ordinary Rust; this macro embeds `verus!` and keeps its layout stable.
#[verusfmt::skip]
#[rustfmt::skip]
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
    ) => {
        $crate::paste::paste! {
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

            // Upstream uses `Flags::FLAGS`; specs use this ghost finite set.
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

            impl ::vstd::set_lib::FiniteFull for [< __ghost $name >] {
                proof fn full_properties() {
                    let s = ::vstd::iset::ISet::empty()
                        $(.insert([< __ghost $name >]::[< __ghost $Flag >]))*;
                    assert(::vstd::iset::ISet::new(|a: [< __ghost $name >]| true) =~= s);
                }
            }

            impl $name {
                $vis open spec fn flags_spec(&self) -> ::vstd::set::Set<[< __ghost $name >]> {
                    Self::flags_from_bits(self.bits())
                }

                $vis open spec fn flags_from_bits(bits: $T) -> ::vstd::set::Set<[< __ghost $name >]> {
                    ::vstd::set::Set::< [< __ghost $name >] >::from_finite_type(|flag: [< __ghost $name >]| {
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

                // Upstream computes `all()` from `Self::FLAGS`; specs use this mask.
                closed spec fn declared_bits_spec() -> $T {
                    (0 as $T) $(| (
                        if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true } {
                            (($value) as $T)
                        } else {
                            0 as $T
                        }
                    ))*
                }

                // Upstream has no `all_bits()`; proof facts attach to `all().bits()`.
                $vis proof fn lemma_all_constant()
                    ensures
                        Self::all().bits() == Self::all_spec().bits_spec(),
                        Self::all_spec().bits_spec() == (0 as $T) $(| (
                            if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true } {
                                (($value) as $T)
                            } else {
                                0 as $T
                            }
                        ))*,
                        Self::all().bits() == (0 as $T) $(| (
                            if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true } {
                                (($value) as $T)
                            } else {
                                0 as $T
                        }
                    ))*,
                {
                }

                $vis broadcast proof fn lemma_consts()
                    ensures
                        #![trigger Self::all().bits()]
                        Self::all().bits() == (0 as $T) $(| (
                            if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true } {
                                (($value) as $T)
                            } else {
                                0 as $T
                            }
                        ))*,
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
                    Self::lemma_all_constant();
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
                    Self::from_bits_unchecked_spec(Self::declared_bits_spec())
                }

                #[verifier::when_used_as_spec(all_spec)]
                $vis const fn all() -> (r: Self)
                    ensures
                        r == Self::all_spec(),
                        r.bits() == Self::all().bits(),
                        r.flags_spec() == Self::flags_from_bits(Self::all().bits()),
                {
                    Self::from_bits_unchecked(
                        (0 as $T) $(| (
                            if $crate::__bitflags_cfg_expr! { ($(#[$inner $($args)*])*) true } {
                                (($value) as $T)
                            } else {
                                0 as $T
                            }
                        ))*
                    )
                }

                /// The bits in `self` that correspond to declared flags.
                $vis closed spec fn known_bits_spec(&self) -> $T {
                    self.bits() & Self::all().bits()
                }

                #[verifier::when_used_as_spec(known_bits_spec)]
                $vis const fn known_bits(&self) -> (r: $T)
                    returns self.known_bits(),
                {
                    self.bits & Self::all().bits()
                }

                /// The bits in `self` that do not correspond to declared flags.
                $vis closed spec fn unknown_bits_spec(&self) -> $T {
                    self.bits() & !Self::all().bits()
                }

                #[verifier::when_used_as_spec(unknown_bits_spec)]
                $vis const fn unknown_bits(&self) -> (r: $T)
                    returns self.unknown_bits(),
                {
                    self.bits & !Self::all().bits()
                }

                /// This method returns `true` if any unknown bits are set.
                $vis open spec fn contains_unknown_bits_spec(&self) -> bool {
                    self.unknown_bits() != 0
                }

                #[verifier::when_used_as_spec(contains_unknown_bits_spec)]
                $vis const fn contains_unknown_bits(&self) -> (r: bool)
                    returns self.contains_unknown_bits(),
                {
                    self.unknown_bits() != 0
                }

                /// Whether all bits in `self` are unset.
                $vis open spec fn is_empty_spec(&self) -> bool {
                    self.bits() == 0
                }

                #[verifier::when_used_as_spec(is_empty_spec)]
                $vis const fn is_empty(&self) -> (r: bool)
                    returns self.is_empty(),
                {
                    self.bits == 0
                }

                /// Whether all known bits are set.
                $vis open spec fn is_all_spec(&self) -> bool {
                    Self::all().bits() | self.bits() == self.bits()
                }

                #[verifier::when_used_as_spec(is_all_spec)]
                $vis const fn is_all(&self) -> (r: bool)
                    returns self.is_all(),
                {
                    Self::all().bits() | self.bits == self.bits
                }

                /// Whether all set bits in `other` are also set in `self`.
                $vis open spec fn contains_spec(&self, other: Self) -> bool {
                    (self.bits() & other.bits()) == other.bits()
                }

                $vis open spec fn contains_flags_spec(&self, other: Self) -> bool {
                    self.contains(other)
                }

                #[verifier::when_used_as_spec(contains_spec)]
                $vis const fn contains(&self, other: Self) -> (r: bool)
                    returns self.contains(other),
                {
                    (self.bits & other.bits) == other.bits
                }

                /// Whether any set bits in `other` are also set in `self`.
                $vis open spec fn intersects_spec(&self, other: Self) -> bool {
                    (self.bits() & other.bits()) != 0
                }

                #[verifier::when_used_as_spec(intersects_spec)]
                $vis const fn intersects(&self, other: Self) -> (r: bool)
                    returns self.intersects(other),
                {
                    (self.bits & other.bits) != 0
                }

                $vis closed spec fn from_bits_truncate_spec(bits: $T) -> Self {
                    Self::from_bits_unchecked_spec(bits & Self::all().bits())
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
                    ensures
                        r.bits() == (bits & Self::all().bits()),
                        r.flags_spec() == Self::flags_from_bits(bits & Self::all().bits()),
                    returns Self::from_bits_truncate(bits),
                {
                    Self::from_bits_unchecked(bits & Self::all().bits())
                }

                $vis closed spec fn from_bits_spec(bits: $T) -> Option<Self> {
                    if (bits & Self::all().bits()) == bits {
                        Some(Self::from_bits_unchecked_spec(bits))
                    } else {
                        None
                    }
                }

                #[verifier::when_used_as_spec(from_bits_spec)]
                $vis const fn from_bits(bits: $T) -> (r: Option<Self>)
                    ensures
                        r is Some == ((bits & Self::all().bits()) == bits),
                        r matches Some(flags_value) ==> {
                            &&& flags_value.bits() == bits
                            &&& flags_value.flags_spec() == Self::flags_from_bits(bits)
                        },
                    returns
                        Self::from_bits(bits),
                {
                    if (bits & Self::all().bits()) == bits {
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

                /// Call `insert` when `value` is `true` or `remove` when `value` is `false`.
                $vis fn set(&mut self, other: Self, value: bool)
                    ensures
                        value ==> final(self).bits() == (old(self).bits() | other.bits()),
                        !value ==> final(self).bits() == (old(self).bits() & !other.bits()),
                {
                    if value {
                        self.insert(other);
                    } else {
                        self.remove(other);
                    }
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

                $vis closed spec fn complement_spec(self) -> Self {
                    Self::from_bits_truncate_spec(!self.bits())
                }

                #[verifier::when_used_as_spec(complement_spec)]
                $vis const fn complement(self) -> (r: Self)
                    ensures
                        r.bits() == (!self.bits() & Self::all().bits()),
                        r.flags_spec() == Self::flags_from_bits(!self.bits() & Self::all().bits()),
                    returns self.complement(),
                {
                    Self::from_bits_truncate(!self.bits)
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
                    self.complement()
                }
            }

            impl core::ops::Not for $name {
                type Output = Self;

                fn not(self) -> (r: Self)
                    ensures
                        r.bits() == (!self.bits() & $name::all().bits()),
                {
                    self.complement()
                }
            }

        } // verus!
        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.bits).finish()
            }
        }

        impl ::core::ops::BitOrAssign for $name {
            #[inline]
            fn bitor_assign(&mut self, other: Self) {
                self.bits |= other.bits;
            }
        }

        impl ::core::ops::BitAndAssign for $name {
            #[inline]
            fn bitand_assign(&mut self, other: Self) {
                self.bits &= other.bits;
            }
        }

        impl ::core::ops::BitXorAssign for $name {
            #[inline]
            fn bitxor_assign(&mut self, other: Self) {
                self.bits ^= other.bits;
            }
        }

        impl ::core::ops::SubAssign for $name {
            #[inline]
            fn sub_assign(&mut self, other: Self) {
                self.bits &= !other.bits;
            }
        }

        } // paste!
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
    let mut flags = Flags::ABC();

    flags.remove(a);
    flags.insert(a);
    flags.toggle(b);
    flags.set(c, false);
    flags.set(b, true);
    flags.insert(c);
    flags = flags.intersection(Flags::from_bits_retain(0b101u32));
    flags.toggle(a);

    let unknown = Flags::from_bits_retain(0b1000u32);
    unknown.known_bits();
    unknown.unknown_bits();
    unknown.contains_unknown_bits();
    Flags::from_bits(0b1000u32);
    let truncated_unknown = Flags::from_bits_truncate(0b1001u32);
    truncated_unknown.bits();

}

} // verus!
