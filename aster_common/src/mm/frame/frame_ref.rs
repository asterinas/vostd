use vstd::prelude::*;

use std::ops::Deref;

use vstd_extra::external::manually_drop::*;
use vstd_extra::undroppable::*;

use super::*;

verus! {

/// A struct that can work as `&'a Frame<M>`.
#[rustc_has_incoherent_inherent_impls]
pub struct FrameRef<'a, M: AnyFrameMeta> {
    pub inner: NeverDrop<Frame<M>>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

impl<M: AnyFrameMeta> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(ensures returns manually_drop_deref_spec(&self.inner.0))]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

} // verus!
