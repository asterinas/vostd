pub mod meta_slot;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

pub use meta_slot::*;

verus! {

pub struct MemContent {
    pub meta_slot_array: MetaSlotArray,
}

} // verus!
