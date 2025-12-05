use vstd::prelude::*;

use super::*;

verus! {

/// The metadata of untyped frame.
///
/// If a structure `M` implements [`AnyUFrameMeta`], it can be used as the
/// metadata of a type of untyped frames [`Frame<M>`]. All frames of such type
/// will be accessible as untyped memory.
pub trait AnyUFrameMeta: AnyFrameMeta {}

/// A smart pointer to an untyped frame with any metadata.
///
/// The metadata of the frame is not known at compile time but the frame must
/// be an untyped one. An [`UFrame`] as a parameter accepts any type of
/// untyped frame metadata.
///
/// The usage of this frame will not be changed while this object is alive.
/// Verus doesn't let us do very much with `dyn` traits, so instead of a `dyn AnyFrameMeta`
/// we use `MetaSlotStorage`, a type that is a tagged union of the metadata types we've worked with so far.
pub type UFrame = Frame<MetaSlotStorage>;

/// A physical memory range that is untyped.
///
/// Untyped frames or segments can be safely read and written by the kernel or
/// the user.
pub trait UntypedMem {
    /// Borrows a reader that can read the untyped memory.
    fn reader(&self) -> VmReader<'_>;
    /// Borrows a writer that can write the untyped memory.
    fn writer(&self) -> VmWriter<'_>;
}

}