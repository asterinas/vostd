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
use vstd::std_specs::ops::*;

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
        verus! {

            $(#[$outer])*
            #[repr(transparent)]
            #[derive(Copy, Clone, PartialEq, Eq)]
            $vis struct $name {
                /// The raw bits backing this flags value.
                bits: $T,
            }

            impl $name {
                $(
                    $(#[$inner $($args)*])*
                    #[allow(non_snake_case)]
                    pub const fn $Flag() -> (r: Self)
                        ensures r.bits() == ($value),
                    {
                        Self { bits: ($value) as $T }
                    }
                )*

                /// The bitwise OR of every declared flag (the "all" mask).
                pub open spec fn all_bits_spec() -> $T {
                    ($( ($value) as $T )|*) as $T
                }

                #[verifier::when_used_as_spec(all_bits_spec)]
                pub const fn all_bits() -> $T
                    returns Self::all_bits(),
                {
                    $( ($value) as $T )|*
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

                pub closed spec fn all_spec() -> Self {
                    Self { bits: Self::all_bits_spec() }
                }

                #[verifier::when_used_as_spec(all_spec)]
                pub const fn all() -> (r: Self)
                    ensures r == Self::all_spec(),
                {
                    Self { bits: Self::all_bits() }
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

                pub closed spec fn from_bits_truncate_spec(bits: $T) -> Self {
                    Self { bits: bits & Self::all_bits() }
                }

                #[verifier::when_used_as_spec(from_bits_truncate_spec)]
                pub const fn from_bits_truncate(bits: $T) -> Self
                    returns Self::from_bits_truncate(bits),
                {
                    Self { bits: bits & Self::all_bits() }
                }

                pub closed spec fn from_bits_spec(bits: $T) -> Option<Self> {
                    if (bits & Self::all_bits()) == bits {
                        Some(Self { bits })
                    } else {
                        None
                    }
                }

                #[verifier::when_used_as_spec(from_bits_spec)]
                pub const fn from_bits(bits: $T) -> (r: Option<Self>)
                    ensures
                        r is Some == ((bits & Self::all_bits()) == bits),
                        r is Some ==> r->0.bits() == bits,
                    returns
                        Self::from_bits(bits),
                {
                    if (bits & Self::all_bits()) == bits {
                        Some(Self { bits })
                    } else {
                        None
                    }
                }

                pub fn insert(&mut self, other: Self)
                    ensures final(self).bits() == (old(self).bits() | other.bits()),
                {
                    self.bits = self.bits | other.bits;
                }

                pub fn toggle(&mut self, other: Self)
                    ensures final(self).bits() == (old(self).bits() ^ other.bits()),
                {
                    self.bits = self.bits ^ other.bits;
                }


                pub closed spec fn union_spec(self, other: Self) -> Self {
                    Self { bits: self.bits() | other.bits() }
                }

                #[verifier::when_used_as_spec(union_spec)]
                pub const fn union(self, other: Self) -> (r: Self)
                    ensures r.bits() == (self.bits() | other.bits()),
                    returns self.union(other),
                {
                    Self { bits: self.bits | other.bits }
                }

                pub closed spec fn intersection_spec(self, other: Self) -> Self {
                    Self { bits: self.bits() & other.bits() }
                }

                #[verifier::when_used_as_spec(intersection_spec)]
                pub const fn intersection(self, other: Self) -> (r: Self)
                    ensures r.bits() == (self.bits() & other.bits()),
                    returns self.intersection(other),
                {
                    Self { bits: self.bits & other.bits }
                }

                pub closed spec fn symmetric_difference_spec(self, other: Self) -> Self {
                    Self { bits: self.bits() ^ other.bits() }
                }

                #[verifier::when_used_as_spec(symmetric_difference_spec)]
                pub const fn symmetric_difference(self, other: Self) -> (r: Self)
                    ensures r.bits() == (self.bits() ^ other.bits()),
                    returns self.symmetric_difference(other),
                {
                    Self { bits: self.bits ^ other.bits }
                }
            }

            impl BitOrSpecImpl for $name {
                open spec fn obeys_bitor_spec() -> bool { true }

                open spec fn bitor_req(self, rhs: Self) -> bool { true }

                open spec fn bitor_spec(self, rhs: Self) -> Self::Output {
                    self.union(rhs)
                }
            }

            impl core::ops::BitOr for $name {
                type Output = Self;
                #[verifier::external_body]
                fn bitor(self, other: Self) -> (r: Self)
                    ensures r.bits() == (self.bits() | other.bits()),
                {
                    Self { bits: self.bits | other.bits }
                }
            }

            impl BitAndSpecImpl for $name {
                open spec fn obeys_bitand_spec() -> bool { true }

                open spec fn bitand_req(self, rhs: Self) -> bool { true }

                open spec fn bitand_spec(self, rhs: Self) -> Self::Output {
                    self.intersection(rhs)
                }
            }

            impl core::ops::BitAnd for $name {
                type Output = Self;
                #[verifier::external_body]
                fn bitand(self, other: Self) -> (r: Self)
                    ensures r.bits() == (self.bits() & other.bits()),
                {
                    Self { bits: self.bits & other.bits }
                }
            }

            impl BitXorSpecImpl for $name {
                open spec fn obeys_bitxor_spec() -> bool { true }

                open spec fn bitxor_req(self, rhs: Self) -> bool { true }

                open spec fn bitxor_spec(self, rhs: Self) -> Self::Output {
                    self.symmetric_difference(rhs)
                }
            }

            impl core::ops::BitXor for $name {
                type Output = Self;
                #[verifier::external_body]
                fn bitxor(self, other: Self) -> (r: Self)
                    ensures r.bits() == (self.bits() ^ other.bits()),
                {
                    Self { bits: self.bits ^ other.bits }
                }
            }

            impl NotSpecImpl for $name {
                open spec fn obeys_not_spec() -> bool { true }

                open spec fn not_req(self) -> bool { true }

                closed spec fn not_spec(self) -> Self::Output {
                    Self { bits: !self.bits() & Self::all_bits() }
                }
            }

            impl core::ops::Not for $name {
                type Output = Self;

                fn not(self) -> (r: Self)
                    ensures r.bits() == (!self.bits() & $name::all_bits()),
                {
                    Self { bits: !self.bits & $name::all_bits() }
                }
            }

        } // verus!
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
    /// Example flag set, layout-compatible with `bitflags::example_generated::Flags`.
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
    // Each flag is now a `pub const fn` factory (matches the repo's PageFlags
    // convention) rather than an associated const, because the `bits` field
    // is private and Verus refuses to expose a constructor through a public
    // associated constant.
    let a = Flags::A();
    let b = Flags::B();
    let c = Flags::C();
    let abc = Flags::ABC();

    assert(a.bits() == 0b001u32);
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
