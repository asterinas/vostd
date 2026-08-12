//! The [`AnyOf`] macro: build a closed world of types from a list.
//!
//! Writing an aggregate by hand means writing, per member, a [`TypeId`] impl and a
//! [`HasId`] impl, then one `DisjointFrom` witness per nesting node, then the
//! nested type itself. All of it is mechanical, and all of it is the part a person
//! gets wrong — a reused id is a soundness bug that no single declaration looks
//! wrong in isolation.
//!
//! [`TypeId`]: super::types::TypeId
//! [`HasId`]: super::types::HasId
//!
//! # Why it emits `verus!` blocks
//!
//! The macro must be invoked *outside* a `verus!` block, and expands to `verus!`
//! blocks of its own. This is forced: `verus!` is a proc macro that consumes its
//! token stream directly, so a `macro_rules!` call appearing inside one is never
//! expanded — Verus would see the literal tokens `AnyOf!(..)` and reject them. The
//! tree recursion therefore emits one small `verus!` block per step rather than
//! accumulating everything into a single one.
//!
//! # Nesting direction
//!
//! The tree is built *left*-nested — `Node<Node<Leaf<A>, Leaf<B>>, Leaf<C>>` — for
//! a mechanical reason rather than a semantic one. Both directions are equivalent
//! (`inhabits` and `holds` are unions, and union is associative), but a
//! `macro_rules!` accumulator can only grow outward, and right-nesting would need
//! it to grow into a hole in the middle of an already-built type.
//!
//! # Collisions fail verification, they are not merely undetected
//!
//! The macro does not check that the ids differ, and does not need to. A duplicate
//! id makes one of the generated `DisjointFrom` proofs unprovable, so the build
//! fails at the node that joins the colliding members. That is the property the
//! whole design exists for: uniqueness is enforced per node, at compile time,
//! instead of by a global registry someone has to remember to audit.
//!
//! # A type belongs to exactly one world
//!
//! Ids live in the member's own `TypeId` impl, so a type cannot appear in two
//! `AnyOf!` invocations — the second expansion collides with `E0119 conflicting
//! implementations`. This is the right constraint rather than a limitation, and it
//! matches `core::any::TypeId`, which is likewise global to the type: an id
//! meaning different things in different aggregates would make the ids useless as
//! identity. Two worlds sharing members means one world with the union of them.
//!
//! # What it does not generate
//!
//! Nothing about representation. `Leaf<M>` is a [`Member`] only when `M` is
//! [`ByteRepr`], and a byte layout is a fact about the type that cannot be
//! derived — so each member still needs its own `ByteSized`/`ByteRepr` impls.
//! The split is deliberate: this macro settles *identity*, which is what can be
//! mechanised.
//!
//! [`Member`]: super::types::Member
//! [`ByteRepr`]: super::types::ByteRepr
//!
//! # Example
//!
//! ```ignore
//! AnyOf!(World = [MetaA = 1, MetaB = 2, MetaC = 3]);
//! ```
//!
//! expands to `TypeId`/`HasId` for each of the three, two `DisjointFrom`
//! witnesses, and `pub type World = Node<Node<Leaf<MetaA>, Leaf<MetaB>>,
//! Leaf<MetaC>>`.
/// Defines a closed world of types as a nested `Either` tree.
///
/// See the [module docs](self) for the shape of the expansion, why ids are given
/// explicitly, and what is deliberately left out.
#[macro_export]
macro_rules! AnyOf {
    // ---- entry: a name for the world, then the members and their ids ----
    ($world:ident = [$t0:ty = $id0:literal $(, $t:ty = $id:literal)* $(,)?]) => {
        $crate::AnyOf!(@ids $t0 = $id0 $(, $t = $id)*);
        $crate::AnyOf!(@tree $world; $crate::typing::types::Leaf<$t0> $(; $t)*);
    };

    // ---- per-member identity ----
    //
    // `wf` is `true` because a type owning exactly one id carries its identity in
    // its type: there is no tag that could disagree with anything.
    (@ids $($t:ty = $id:literal),+) => {
        ::vstd::prelude::verus!{
        $(
        impl $crate::typing::types::TypeId for $t {
            open spec fn inhabits(type_id: nat) -> bool {
                type_id == $id as nat
            }
        }

        impl $crate::typing::types::HasId for $t {
            open spec fn id_of(&self) -> nat {
                $id as nat
            }

            open spec fn wf(&self) -> bool {
                true
            }

            proof fn id_of_inhabits(&self) {
            }
        }
        )+
        }
};

    // ---- tree: no members left, name the accumulated type ----
    (@tree $world:ident; $acc:ty) => {
        ::vstd::prelude::verus!{
        pub type $world = $acc;
        }
};

    // ---- tree: join one more member, discharging its node's obligation ----
    //
    // This impl is where a duplicate id is caught: its body is empty, so the
    // proof succeeds only if the two sides really are disjoint.
    (@tree $world:ident; $acc:ty ; $next:ty $(; $rest:ty)*) => {
        ::vstd::prelude::verus!{
        impl $crate::typing::types::DisjointFrom<$crate::typing::types::Leaf<$next>> for $acc {
            proof fn disjoint(type_id: nat) {
            }
        }
        }
$crate::AnyOf!(
            @tree $world;
            $crate::typing::types::Node<$acc, $crate::typing::types::Leaf<$next>>
            $(; $rest)*
        );
    };
}
