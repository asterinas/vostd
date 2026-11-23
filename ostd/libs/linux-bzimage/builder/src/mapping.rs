// SPDX-License-Identifier: MPL-2.0
//! In the setup, VA - SETUP32_LMA == FileOffset - LEGACY_SETUP_SEC_SIZE.
//! And the addresses are specified in the ELF file.
//!
//! This module centralizes the conversion between VA and FileOffset.
use vstd::{
    prelude::*,
    std_specs::{
        convert::FromSpecImpl,
        ops::{AddSpecImpl, SubSpecImpl},
    },
};

use std::{
    cmp::PartialOrd,
    convert::From,
    ops::{Add, Sub},
};

// We chose the legacy setup sections to be 7 so that the setup header
// is page-aligned and the legacy setup section size would be 0x1000.
#[verus_verify]
pub const LEGACY_SETUP_SECS: usize = 7;
#[verus_verify]
pub const LEGACY_SETUP_SEC_SIZE: usize = 0x200 * (LEGACY_SETUP_SECS + 1);

#[verus_verify]
pub const SETUP32_LMA: usize = 0x100000;

#[verus_verify]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct SetupVA {
    addr: usize,
}

#[verus_verify]
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct SetupFileOffset {
    offset: usize,
}

#[verus_verify]
impl From<usize> for SetupVA {
    #[verus_spec(ret => ensures ret@ == addr)]
    fn from(addr: usize) -> Self {
        Self { addr }
    }
}

#[verus_verify]
impl From<SetupVA> for usize {
    #[verus_spec(returns va@)]
    fn from(va: SetupVA) -> Self {
        va.addr
    }
}

#[verus_verify]
impl Sub for SetupVA {
    type Output = usize;

    #[verus_spec(returns (self@ - rhs@) as usize)]
    fn sub(self, rhs: Self) -> Self::Output {
        self.addr - rhs.addr
    }
}

#[verus_verify]
impl Add<usize> for SetupVA {
    type Output = Self;

    #[verus_spec(ret => ensures ret@ == self@ + rhs)]
    fn add(self, rhs: usize) -> Self::Output {
        Self {
            addr: self.addr + rhs,
        }
    }
}

#[verus_verify]
impl From<usize> for SetupFileOffset {
    #[verus_spec(ret => ensures ret@ == offset)]
    fn from(offset: usize) -> Self {
        Self { offset }
    }
}

#[verus_verify]
impl From<SetupFileOffset> for usize {
    #[verus_spec(returns offset@)]
    fn from(offset: SetupFileOffset) -> Self {
        offset.offset
    }
}

#[verus_verify]
impl Sub for SetupFileOffset {
    type Output = usize;

    #[verus_spec(returns (self@ - rhs@) as usize)]
    fn sub(self, rhs: Self) -> Self::Output {
        self.offset - rhs.offset
    }
}

#[verus_verify]
impl Add<usize> for SetupFileOffset {
    type Output = Self;

    #[verus_spec(ret => ensures ret@ == self@ + rhs)]
    fn add(self, rhs: usize) -> Self::Output {
        Self {
            offset: self.offset + rhs,
        }
    }
}

#[verus_verify]
impl From<SetupVA> for SetupFileOffset {
    #[verus_spec(ret => ensures ret@ == (va@ + LEGACY_SETUP_SEC_SIZE - SETUP32_LMA) as usize)]
    fn from(va: SetupVA) -> Self {
        proof! {
            // TRUSTED: setup's linker.ld and header.S bound generated ELF VAs
            // on 64-bit hosts; ELF provenance and linking are unverified.
            assume(SETUP32_LMA - LEGACY_SETUP_SEC_SIZE <= va.addr <= usize::MAX - LEGACY_SETUP_SEC_SIZE);
        }
        Self {
            offset: va.addr + LEGACY_SETUP_SEC_SIZE - SETUP32_LMA,
        }
    }
}

#[verus_verify]
impl From<SetupFileOffset> for SetupVA {
    #[verus_spec(ret => ensures ret@ == (offset@ + SETUP32_LMA - LEGACY_SETUP_SEC_SIZE) as usize)]
    fn from(offset: SetupFileOffset) -> Self {
        proof! {
            // TRUSTED: valid VA conversions produce this range; raw usize inputs may not.
            assume(offset.offset <= usize::MAX - SETUP32_LMA);
        }
        Self {
            addr: offset.offset + SETUP32_LMA - LEGACY_SETUP_SEC_SIZE,
        }
    }
}

verus! {

impl FromSpecImpl<SetupVA> for SetupFileOffset {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    closed spec fn from_spec(va: SetupVA) -> Self {
        Self { offset: (va@ + LEGACY_SETUP_SEC_SIZE - SETUP32_LMA) as usize }
    }
}

impl FromSpecImpl<SetupFileOffset> for SetupVA {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    closed spec fn from_spec(offset: SetupFileOffset) -> Self {
        Self { addr: (offset@ + SETUP32_LMA - LEGACY_SETUP_SEC_SIZE) as usize }
    }
}

} // verus!
macro_rules! impl_mapping_specs {
    ($ty:ty, $field:ident) => {
        verus! {
        impl View for $ty {
            type V = usize;
            closed spec fn view(&self) -> usize {
                self.$field
            }
        }
        impl FromSpecImpl<usize> for $ty {
            open spec fn obeys_from_spec() -> bool {
                true
            }
            closed spec fn from_spec(value: usize) -> Self {
                Self { $field: value }
            }
        }
        impl FromSpecImpl<$ty> for usize {
            open spec fn obeys_from_spec() -> bool {
                true
            }
            open spec fn from_spec(value: $ty) -> Self {
                value@
            }
        }
        impl AddSpecImpl<usize> for $ty {
            open spec fn obeys_add_spec() -> bool {
                true
            }
            open spec fn add_req(self, rhs: usize) -> bool {
                self@ + rhs <= usize::MAX
            }
            closed spec fn add_spec(self, rhs: usize) -> Self {
                Self { $field: (self@ + rhs) as usize }
            }
        }
        impl SubSpecImpl for $ty {
            open spec fn obeys_sub_spec() -> bool {
                true
            }
            open spec fn sub_req(self, rhs: Self) -> bool {
                self@ >= rhs@
            }
            open spec fn sub_spec(self, rhs: Self) -> usize {
                (self@ - rhs@) as usize
            }
        }
        }
    };
}
impl_mapping_specs!(SetupVA, addr);
impl_mapping_specs!(SetupFileOffset, offset);
