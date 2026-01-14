//! Resource algebras based on PCM and storage-protocol inspired by Iris and Leaf.
pub mod pcm;
pub mod storage;

use vstd::prelude::*;

pub type SingleStorage<T> = Map<(), T>;
pub type OptionSingleStorage<T> = Map<(), Option<T>>;
