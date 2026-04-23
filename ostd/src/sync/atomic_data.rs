use core::ops::Deref;

use vstd::{predicate::Predicate, prelude::*};
use vstd_extra::ownership::Inv;

use super::{RwLockReadGuard, SpinGuardian};

verus! {

/// A structure that combines some data with a permission to access it.
///
/// For example, in `aster_common` we can see a lot of structs with
/// its `owner` associated. E.g., `MetaSlotOwner` is the owner of
/// `MetaSlot`. This struct can be used to represent such a combination
/// because now the permission is no longer exclusively owner by some
/// specific CPU and is "shared" among multiple threads via atomic
/// operations.
///
/// This struct is especially useful when used in conjunction with
/// synchronization primitives like [`Once`], where we want to ensure that
/// the data is initialized only once and the permission is preserved
/// throughout the lifetime of the data.
///
/// # Examples
///
/// ```rust,ignore
///  struct MyData {
///     pub foo: u32,
///     pub bar: u32,
///  }
///
/// tracked struct MyDataWithOwner {
///    pub baz: nat,
///    pub quz: Seq<int>,
/// }
///
/// impl Inv for MyData {
///     // inv...
/// }
///
/// impl Predicate<MyData> for MyDataWithOwner {
///    #[verifier::inline]
///    open spec fn inv_with(self, v: MyData) -> bool {
///         &&& self.baz == v.foo as nat
///         &&& self.quz.len() == v.bar as nat
///    }
/// }
///
/// type Data = AtomicDataWithOwner<MyData, MyDataWithOwner>;
/// ```
#[repr(transparent)]
#[allow(repr_transparent_non_zst_fields)]
pub struct AtomicDataWithOwner<V, Own> {
    /// The underlying data.
    pub data: V,
    /// The permission to access the data.
    pub permission: Tracked<Own>,
}

impl<'a, V, Own, G: SpinGuardian> RwLockReadGuard<'a, crate::sync::AtomicDataWithOwner<V, Own>, G> {
    /// Borrows the tracked permission stored in an [`AtomicDataWithOwner`].
    #[verifier::external_body]
    pub proof fn atomic_permission(tracked &self) -> (tracked permission: &'a Own)
        returns
            self@.permission@,
    {
        unimplemented!()
    }
}

impl<V, Own> Deref for AtomicDataWithOwner<V, Own> {
    type Target = V;

    #[inline]
    #[verus_spec(returns self.data)]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<V, Own> AtomicDataWithOwner<V, Own> {
    #[inline]
    pub fn new(data: V, permission: Tracked<Own>) -> Self {
        Self { data, permission }
    }
}

impl<V, Own> !Copy for AtomicDataWithOwner<V, Own> {

}

impl<V, Own> !Clone for AtomicDataWithOwner<V, Own> {

}

impl<V, Own: Predicate<V>> Inv for AtomicDataWithOwner<V, Own> {
    #[verifier::inline]
    open spec fn inv(self) -> bool {
        &&& self.permission.predicate(self.data)
    }
}

impl<T, Own> View for AtomicDataWithOwner<T, Own> {
    type V = T;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.data
    }
}

} // verus!
