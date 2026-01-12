use vstd::prelude::*;

use core::mem::ManuallyDrop;
use core::ops::Deref;

use super::*;

verus! {

/// A struct that can work as `&'a Frame<M>`.
#[rustc_has_incoherent_inherent_impls]
pub struct FrameRef<'a, M: AnyFrameMeta> {
    pub inner: ManuallyDrop<Frame<M>>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

impl<M: AnyFrameMeta> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(returns &self.inner@)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

} // verus!
