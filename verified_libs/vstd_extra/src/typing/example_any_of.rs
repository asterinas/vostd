//! [`AnyOf`](crate::AnyOf) applied to a three-member world.
//!
//! The same aggregate [`super::example`] builds by hand, to check that the
//! generated impls are the ones the laws need. Note the macro call sits outside
//! any `verus!` block — see the [macro docs](super::any_of) for why it must.
use vstd::prelude::*;

use super::types::*;

verus! {

/// Three members with no shared behavior, only ids.
pub struct W1(pub u64);

/// Second member.
pub struct W2(pub u64);

/// Third member.
pub struct W3(pub u64);

} // verus!
AnyOf!(World = [W1 = 1, W2 = 2, W3 = 3]);

verus! {

/// A one-member world, to exercise the recursion's base case.
pub struct S1(pub u64);

/// A two-member world's members. Fresh types, not reused from `World`: a type
/// belongs to exactly one world, since its id lives in its own `TypeId` impl.
/// Reusing `W1` here fails with `E0119 conflicting implementations`.
pub struct P1(pub u64);

/// Second member of the pair.
pub struct P2(pub u64);

} // verus!
AnyOf!(Single = [S1 = 7]);

AnyOf!(Pair = [P1 = 8, P2 = 9]);

verus! {

/// The generated tree admits exactly the three ids.
pub proof fn world_admits_three(t: nat)
    ensures
        World::inhabits(t) <==> (t == 1 || t == 2 || t == 3),
{
}

/// A member of the world lands in exactly one leaf.
///
/// This is the property the hand-written example proves as `exactly_one_leaf`; it
/// holds here with no hand-written disjointness at all.
pub proof fn world_exactly_one(t: nat)
    requires
        World::inhabits(t),
    ensures
        ({
            &&& W1::inhabits(t) ==> !W2::inhabits(t) && !W3::inhabits(t)
            &&& W2::inhabits(t) ==> !W1::inhabits(t) && !W3::inhabits(t)
            &&& W3::inhabits(t) ==> !W1::inhabits(t) && !W2::inhabits(t)
        }),
{
}

/// The generated `HasId` satisfies its law.
pub proof fn world_id_of_inhabits(v: W2)
    ensures
        W2::inhabits(v.id_of()),
{
    v.id_of_inhabits();
}

} // verus!
