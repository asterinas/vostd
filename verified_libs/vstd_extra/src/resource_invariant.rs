// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
#[cfg(feature = "irc11")]
use vstd::thread_view::Objective;

verus! {

/// An invariant that relates a value to a tracked resource.
pub trait ResourceInvariant<V>: Sized {
    /// Immutable ghost configuration fixed at creation time.
    type Constant;

    /// A tracked resource associated with the value and transferred linearly between owners.
    #[cfg(not(feature = "irc11"))]
    type Resource;

    /// The tracked resource stored in an IRC11 atomic invariant.
    ///
    /// It must be objective so moving the resource through a lock does not
    /// implicitly transfer a thread's subjective weak-memory observations.
    #[cfg(feature = "irc11")]
    type Resource: Objective;

    /// The relation that must hold between the value, constant, and tracked resource.
    spec fn inv(constant: Self::Constant, value: V, resource: Self::Resource) -> bool;
}

/// A resource invariant that imposes no condition on the value.
pub struct TrivialResourceInvariant;

impl<V> ResourceInvariant<V> for TrivialResourceInvariant {
    type Constant = ();

    type Resource = ();

    open spec fn inv(_constant: (), _value: V, _resource: ()) -> bool {
        true
    }
}

} // verus!
