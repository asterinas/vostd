// SPDX-License-Identifier: MPL-2.0
use core::{
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};
use vstd::prelude::*;
use vstd::std_specs::convert::FromSpecImpl;
use vstd_extra::external::duration_new_spec;

use crate::arch::timer::TIMER_FREQ;
verus! {

pub(crate) exec static ELAPSED: AtomicU64 = AtomicU64::new(0);

} // verus!
/// Jiffies is a term used to denote the units of time measurement by the kernel.
///
/// A jiffy represents one tick of the system timer interrupt,
/// whose frequency is equal to [`TIMER_FREQ`] Hz.
#[verus_verify]
#[derive(Copy, Clone, Debug)]
pub struct Jiffies(u64);

verus! {

impl View for Jiffies {
    type V = u64;

    closed spec fn view(&self) -> Self::V {
        self.0
    }
}

impl Jiffies {
    /// The whole-second component of this jiffy count.
    pub closed spec fn duration_secs(self) -> u64 {
        self@ / TIMER_FREQ
    }

    /// The subsecond nanosecond component of this jiffy count.
    pub closed spec fn duration_nanos(self) -> u32 {
        (((self@ % TIMER_FREQ) * 1_000_000_000u64) / (TIMER_FREQ as int)) as u32
    }
}

impl FromSpecImpl<Jiffies> for Duration {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: Jiffies) -> Duration {
        duration_new_spec(value.duration_secs(), value.duration_nanos())
    }
}

} // verus!
impl Jiffies {
    /// The maximum value of [`Jiffies`].
    pub const MAX: Self = Self(u64::MAX);
}

#[verus_verify]
impl Jiffies {
    /// Creates a new instance.
    #[verus_spec(ret => ensures ret@ == value)]
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    /// Returns the elapsed time since the system boots up.
    pub fn elapsed() -> Self {
        Self::new(ELAPSED.load(Ordering::Relaxed))
    }

    /// Gets the number of jiffies.
    #[verus_spec(returns self@)]
    pub fn as_u64(self) -> u64 {
        self.0
    }

    /// Adds the given number of jiffies, saturating at [`Jiffies::MAX`] on overflow.
    #[verus_spec(
        ensures
            final(self)@ == if old(self)@ + jiffies > u64::MAX {
                u64::MAX
            } else {
                (old(self)@ + jiffies) as u64
            },
    )]
    pub fn add(&mut self, jiffies: u64) {
        self.0 = self.0.saturating_add(jiffies);
    }

    /// Gets the [`Duration`] calculated from the jiffies counts.
    #[verus_spec(returns vstd_extra::external::duration_new_spec(
        self.duration_secs(),
        self.duration_nanos(),
    ))]
    pub fn as_duration(self) -> Duration {
        let secs = self.0 / TIMER_FREQ;
        let nanos = ((self.0 % TIMER_FREQ) * 1_000_000_000) / TIMER_FREQ;
        Duration::new(secs, nanos as u32)
    }
}

#[verus_verify]
impl From<Jiffies> for Duration {
    fn from(value: Jiffies) -> Self {
        value.as_duration()
    }
}
