use prelude::verus;
use vstd::*;

verus! {

// TODO: AnyFrameMeta
pub trait AnyFrameMeta {

}

impl AnyFrameMeta for () {

}

// TODO: MetaSlot
pub struct MetaSlot {}

/// The error type for getting the frame from a physical address.
#[derive(Debug)]
pub enum GetFrameError {
    /// The frame is in use.
    InUse,
    /// The frame is not in use.
    Unused,
    /// The frame is being initialized or destructed.
    Busy,
    /// The frame is private to an owner of [`UniqueFrame`].
    ///
    /// [`UniqueFrame`]: super::unique::UniqueFrame
    Unique,
    /// The provided physical address is out of bound.
    OutOfBound,
    /// The provided physical address is not aligned.
    NotAligned,
}

/// Makes a structure usable as a frame metadata.
    ///
    /// Directly implementing [`AnyFrameMeta`] is not safe since the size and alignment
    /// must be checked. This macro provides a safe way to implement the trait with
    /// compile-time checks.
    #[macro_export]
    macro_rules! impl_frame_meta_for {
        // Implement without specifying the drop behavior.
        ($t:ty) => {
            // const_assert!(size_of::<$t>() <= $crate::mm::frame::meta::FRAME_METADATA_MAX_SIZE);
            // const_assert!(align_of::<$t>() <= $crate::mm::frame::meta::FRAME_METADATA_MAX_ALIGN);
            // TODO: Fix assertions
            // SAFETY: The size and alignment of the structure are checked.
            impl $crate::mm::frame::meta::AnyFrameMeta for $t {}
        };
    }

/// The metadata of frames that holds metadata of frames.
#[derive(Debug, Default)]
pub struct MetaPageMeta {}

impl_frame_meta_for!(MetaPageMeta);

} // verus!
