use crate::ownership::Inv;
use vstd::modes::tracked_swap;
use vstd::prelude::*;

verus! {

/// The Sum Type, corresponding to the `Either` type in Rust.
pub tracked enum Sum<L, R> {
    Left(L),
    Right(R),
}

impl<L, R> Sum<L, R> {
    pub open spec fn left(self) -> L {
        self->Left_0
    }

    pub open spec fn right(self) -> R {
        self->Right_0
    }

    pub proof fn new_left(tracked left: L) -> (tracked res: Self)
        returns
            Self::Left(left),
    {
        Self::Left(left)
    }

    pub proof fn new_right(tracked right: R) -> (tracked res: Self)
        returns
            Self::Right(right),
    {
        Self::Right(right)
    }

    pub proof fn tracked_take_left(tracked self) -> (tracked res: L)
        requires
            self is Left,
        returns
            self->Left_0,
    {
        match self {
            Self::Left(left) => left,
            Self::Right(_) => proof_from_false(),
        }
    }

    pub proof fn tracked_take_right(tracked self) -> (tracked res: R)
        requires
            self is Right,
        returns
            self->Right_0,
    {
        match self {
            Self::Left(_) => proof_from_false(),
            Self::Right(right) => right,
        }
    }

    pub proof fn tracked_borrow_left(tracked &self) -> (tracked res: &L)
        requires
            self is Left,
        ensures
            *res == self->Left_0,
    {
        match self {
            Self::Left(left) => left,
            Self::Right(_) => proof_from_false(),
        }
    }

    pub proof fn tracked_borrow_right(tracked &self) -> (tracked res: &R)
        requires
            self is Right,
        ensures
            *res == self->Right_0,
    {
        match self {
            Self::Left(_) => proof_from_false(),
            Self::Right(right) => right,
        }
    }

    pub open spec fn lift_map_left<K>(m: Map<K, L>) -> Map<K, Self> {
        m.map_values(|w| Sum::<L, R>::Left(w))
    }

    pub open spec fn lift_map_right<K>(m: Map<K, R>) -> Map<K, Self> {
        m.map_values(|v| Sum::<L, R>::Right(v))
    }

    pub proof fn tracked_swap_left(tracked &mut self, tracked new_left: L) -> (tracked res: L)
        requires
            *old(self) is Left,
        ensures
            res == old(self)->Left_0,
            *final(self) is Left,
            final(self)->Left_0 == new_left,
    {
        let tracked mut tmp = Self::new_left(new_left);
        tracked_swap(self, &mut tmp);
        tmp.tracked_take_left()
    }

    pub proof fn tracked_swap_right(tracked &mut self, tracked new_right: R) -> (tracked res: R)
        requires
            *old(self) is Right,
        ensures
            res == old(self)->Right_0,
            *final(self) is Right,
            final(self)->Right_0 == new_right,
    {
        let tracked mut tmp = Self::new_right(new_right);
        tracked_swap(self, &mut tmp);
        tmp.tracked_take_right()
    }
}

impl<L: Inv, R: Inv> Inv for Sum<L, R> {
    open spec fn inv(self) -> bool {
        match self {
            Self::Left(left) => left.inv(),
            Self::Right(right) => right.inv(),
        }
    }
}

} // verus!
