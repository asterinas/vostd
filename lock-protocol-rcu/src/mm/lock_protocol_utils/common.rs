use std::ops::Range;

use vstd::prelude::*;
use vstd::vstd::arithmetic::power2::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;

use crate::spec::{
    utils::{NodeHelper, group_node_helper_lemmas},
    common::{NodeId, valid_pte_offset},
};
use crate::helpers::bits::low_bits_mask_usize;
pub use crate::mm::{Paddr, Vaddr, PagingLevel};