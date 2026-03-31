// SPDX-License-Identifier: MPL-2.0
/// A type containing either a [`Left`] value `L` or a [`Right`] value `R`.
///
/// [`Left`]: Self::Left
/// [`Right`]: Self::Right
use vstd::prelude::*;

#[verus_verify]
#[derive(Copy, PartialEq, Eq, Debug)]
pub enum Either<L, R> {
    /// Contains the left value
    Left(L),
    /// Contains the right value
    Right(R),
}

#[verus_verify]
impl<L, R> Clone for Either<L, R>
where
    L: Clone,
    R: Clone,
{
    #[inline(always)]
    #[verus_spec(r =>
      ensures
          (forall|l1, l2: L| call_ensures(L::clone, (l1,), l2) ==> l1 == l2) &&
          (forall|r1, r2: R| call_ensures(R::clone, (r1,), r2) ==> r1 == r2)
            ==> r == self,
    )]
    fn clone(&self) -> Self {
        match self {
            Self::Left(left) => Self::Left(left.clone()),
            Self::Right(right) => Self::Right(right.clone()),
        }
    }
}

impl<L, R> Either<L, R> {
    #[verus_verify(dual_spec)]
    /// Converts to the left value, if any.
    pub fn left(self) -> Option<L> {
        match self {
            Self::Left(left) => Some(left),
            Self::Right(_) => None,
        }
    }

    #[verus_verify(dual_spec)]
    /// Converts to the right value, if any.
    pub fn right(self) -> Option<R> {
        match self {
            Self::Left(_) => None,
            Self::Right(right) => Some(right),
        }
    }

    #[verus_verify(dual_spec)]
    /// Returns true if the left value is present.
    pub fn is_left(&self) -> bool {
        matches!(self, Self::Left(_))
    }

    #[verus_verify(dual_spec)]
    /// Returns true if the right value is present.
    pub fn is_right(&self) -> bool {
        matches!(self, Self::Right(_))
    }

    // TODO: Add other utility methods (e.g. `as_ref`, `as_mut`) as needed.
    // As a good reference, check what methods `Result` provides.
}
