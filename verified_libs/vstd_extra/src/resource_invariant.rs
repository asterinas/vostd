// SPDX-License-Identifier: MPL-2.0
#[cfg(feature = "irc11")]
use vstd::thread_view::Objective;
use vstd::{prelude::*, resource};

verus! {

/// An invariant that relates a value to a tracked resource with a constant.
pub trait ResourceInvariant<V> {
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

/// A resource invariant that does not need a constant.
pub trait SimpleResourceInvariant<V> {
    /// A tracked resource associated with the value and transferred linearly between owners.
    #[cfg(not(feature = "irc11"))]
    type Resource;

    /// The tracked resource stored in an IRC11 atomic invariant.
    ///
    /// It must be objective so moving the resource through a lock does not
    /// implicitly transfer a thread's subjective weak-memory observations.
    #[cfg(feature = "irc11")]
    type Resource: Objective;

    // The relation that must hold between the value and tracked resource.
    spec fn inv(value: V, resource: Self::Resource) -> bool;
}

impl<V, T: SimpleResourceInvariant<V>> ResourceInvariant<V> for T {
    type Constant = ();

    type Resource = <T as SimpleResourceInvariant<V>>::Resource;

    open spec fn inv(_constant: (), value: V, resource: Self::Resource) -> bool {
        <T as SimpleResourceInvariant<V>>::inv(value, resource)
    }
}

/// A resource invariant that only considers the value.
pub trait ValueInvariant<V> {
    // The relation that must hold on the value.
    spec fn inv(value: V) -> bool;
}

impl<V, T: ValueInvariant<V>> SimpleResourceInvariant<V> for T {
    type Resource = ();

    open spec fn inv(value: V, _resource: ()) -> bool {
        <T as ValueInvariant<V>>::inv(value)
    }
}

/// A resource invariant that imposes no condition on the value.
pub struct TrivialResourceInvariant;

impl<V> ValueInvariant<V> for TrivialResourceInvariant {
    open spec fn inv(value: V) -> bool {
        true
    }
}

} // verus!
