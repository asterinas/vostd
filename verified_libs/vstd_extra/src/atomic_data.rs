use core::ops::Deref;

use crate::{ownership::Inv, resource_invariant::SimpleResourceInvariant};
use vstd::prelude::*;

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
/// ghost struct MyDataInvariant;
///
/// impl SimpleResourceInvariant<MyData> for MyDataInvariant {
///
///     type Resource = MyDataWithOwner;
///
///     open spec fn inv(value: MyData, resource: MyDataWithOwner) -> bool {
///         &&& resource.baz == value.foo
///         &&& resource.quz.len() == value.bar
///     }
/// }
///
/// type Data = AtomicDataWithOwner<MyData, MyDataInvariant>;
/// ```
pub struct AtomicDataWithOwner<V, I: SimpleResourceInvariant<V>> {
    /// The underlying data.
    pub data: V,
    /// The permission to access the data.
    pub permission: Tracked<I::Resource>,
}

} // verus!
#[verus_verify]
impl<V, I: SimpleResourceInvariant<V>> Deref for AtomicDataWithOwner<V, I> {
    type Target = V;

    #[inline]
    #[verus_spec(returns self.data)]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

verus! {

impl<V, I: SimpleResourceInvariant<V>> AtomicDataWithOwner<V, I> {
    #[inline]
    pub fn new(data: V, permission: Tracked<I::Resource>, Ghost(_pred): Ghost<I>) -> Self
        requires
            I::inv(data, permission@),
    {
        Self { data, permission }
    }
}

impl<V, I: SimpleResourceInvariant<V>> !Copy for AtomicDataWithOwner<V, I> {

}

impl<V, I: SimpleResourceInvariant<V>> !Clone for AtomicDataWithOwner<V, I> {

}

impl<V, I: SimpleResourceInvariant<V>> Inv for AtomicDataWithOwner<V, I> {
    #[verifier::inline]
    open spec fn inv(self) -> bool {
        I::inv(self.data, self.permission@)
    }
}

impl<T, I: SimpleResourceInvariant<T>> View for AtomicDataWithOwner<T, I> {
    type V = T;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.data
    }
}

} // verus!
