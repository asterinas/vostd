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
                const $Flag:ident = $value:literal;
            )*
        }

        $($t:tt)*
    ) => {
        $crate::paste::paste! { verus! {

            $(#[$outer])*
            #[repr(transparent)]
            #[derive(Copy, Clone, Debug, PartialEq, Eq)]
            $vis struct $name {
                /// The raw bits backing this flags value.
                bits: $T,
            }

            impl $name {
                $(
                    pub closed spec fn [< $Flag _spec >]() -> Self {
                        Self { bits: ($value) as $T }
                    }

                    $(#[$inner $($args)*])*
                    #[verifier::when_used_as_spec([< $Flag _spec >])]
                    pub const fn $Flag() -> (r: Self)
                        ensures r.bits() == ($value),
                        returns Self::[< $Flag _spec >](),
                    {
                        Self { bits: ($value) as $T }
                    }
                )*

                /// The bitwise OR of every declared flag (the "all" mask).
                pub closed spec fn all_spec() -> Self {
                    Self { bits: ($( ($value) as $T )|*) as $T }
                }

                #[verifier::when_used_as_spec(all_spec)]
                pub const fn all() -> (r: Self)
                    ensures Self::all_spec().bits() == ($( ($value) as $T )|*) as $T,
                    returns Self::all_spec(),
                {
                    Self { bits: ($( ($value) as $T )|*) as $T }
                }

                /// The raw bits stored inside this flags value.
                pub closed spec fn bits_spec(&self) -> $T { self.bits }

                #[verifier::when_used_as_spec(bits_spec)]
                pub const fn bits(&self) -> $T
                    returns self.bits(),
                {
                    self.bits
                }

                pub closed spec fn empty_spec() -> Self {
                    Self { bits: 0 }
                }

                #[verifier::when_used_as_spec(empty_spec)]
                pub const fn empty() -> (r: Self)
                    ensures r.bits() == 0,
                    returns Self::empty(),
                {
                    Self { bits: 0 }
                }

                pub open spec fn contains_spec(&self, other: Self) -> bool {
                    (self.bits() & other.bits()) == other.bits()
                }

                #[verifier::when_used_as_spec(contains_spec)]
                pub const fn contains(&self, other: Self) -> bool
                    returns self.contains(other),
                {
                    (self.bits & other.bits) == other.bits
                }

                pub open spec fn intersects_spec(&self, other: Self) -> bool {
                    (self.bits() & other.bits()) != 0
                }

                #[verifier::when_used_as_spec(intersects_spec)]
                pub const fn intersects(&self, other: Self) -> bool
                    returns self.intersects(other),
                {
                    (self.bits & other.bits) != 0
                }

                pub closed spec fn from_bits_retain_spec(bits: $T) -> Self {
                    Self { bits: bits }
                }

                #[verifier::when_used_as_spec(from_bits_retain_spec)]
                pub const fn from_bits_retain(bits: $T) -> (r: Self)
                    ensures r.bits() == bits,
                    returns Self::from_bits_retain_spec(bits),
                {
                    Self { bits }
                }

                #[vstd::contrib::auto_spec]
                pub const fn from_bits_truncate(bits: $T) -> Self
                    returns Self::from_bits_truncate(bits),
                {
                    Self::from_bits_retain(bits & Self::all().bits())
                }

                #[vstd::contrib::auto_spec]
                pub const fn from_bits(bits: $T) -> (r: Option<Self>)
                    ensures
                        r is Some == (Self::from_bits_truncate(bits).bits() == bits),
                    returns Self::from_bits(bits),
                {
                    let truncated = Self::from_bits_truncate(bits);
                    if truncated.bits() == bits {
                        Some(truncated)
                    } else {
                        None
                    }
                }

                pub fn insert(&mut self, other: Self)
                    ensures  *final(self) == Self::from_bits_retain(old(self).bits()).union(other),
                {
                    *self = Self::from_bits_retain(self.bits()).union(other);
                }

                /// The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
                pub fn toggle(&mut self, other: Self)
                    ensures *final(self) == Self::from_bits_retain(old(self).bits()).symmetric_difference(other),
                {
                    *self = Self::from_bits_retain(self.bits()).symmetric_difference(other);
                }

                /// The bitwise or (`|`) of the bits in `self` and `other`.
                #[vstd::contrib::auto_spec]
                pub const fn union(self, other: Self) -> (r: Self)
                    returns self.union(other),
                {
                    Self::from_bits_truncate(self.bits() | other.bits())
                }

                /// The bitwise and (`&`) of the bits in `self` and `other`.
                #[vstd::contrib::auto_spec]
                pub const fn intersection(self, other: Self) -> (r: Self)
                    returns self.intersection(other),
                {
                    Self::from_bits_truncate(self.bits() & other.bits())
                }

                #[vstd::contrib::auto_spec]
                pub const fn symmetric_difference(self, other: Self) -> (r: Self)
                    returns self.symmetric_difference(other),
                {
                    Self::from_bits_truncate(self.bits() ^ other.bits())
                }

                /// The intersection of `self` with the complement of `other` (`&!`).
                ///
                /// This method is not equivalent to `self & !other` when `other` has unknown bits set.
                /// `difference` won't truncate `other`, but the `!` operator will.
                #[vstd::contrib::auto_spec]
                pub const fn difference(self, other: Self) -> (r: Self)
                    returns self.difference(other),
                {
                    Self::from_bits_truncate(self.bits() & !other.bits())
                }

                /// The bitwise negation (`!`) of the bits in `self`, truncating the result.
                #[vstd::contrib::auto_spec]
                pub const fn complement(self) -> (r: Self)
                    returns self.complement(),
                {
                    Self::from_bits_truncate(!self.bits())
                }
            }

            impl vstd::std_specs::ops::BitOrSpecImpl for $name {
                open spec fn obeys_bitor_spec() -> bool { true }

                open spec fn bitor_req(self, rhs: Self) -> bool { true }

                open spec fn bitor_spec(self, rhs: Self) -> Self::Output {
                    self.union(rhs)
                }
            }

            impl core::ops::BitOr for $name {
                type Output = Self;
                fn bitor(self, other: Self) -> (r: Self)
                {
                    self.union(other)
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
                {
                    self.intersection(other)
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
                {
                    self.symmetric_difference(other)
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
                {
                    self.difference(other)
                }
            }

            impl vstd::std_specs::ops::NotSpecImpl for $name {
                open spec fn obeys_not_spec() -> bool { true }

                open spec fn not_req(self) -> bool { true }

                open spec fn not_spec(self) -> Self::Output {
                    self.complement()
                }
            }

            impl core::ops::Not for $name {
                type Output = Self;

                fn not(self) -> (r: Self)
                {
                    self.complement()
                }
            }

        }
} // verus! paste!
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
    assert(abc.contains(a));
    assert(abc.contains(b));
    assert(!a.contains(b));

}

} // verus!
