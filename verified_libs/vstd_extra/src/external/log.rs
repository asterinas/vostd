// SPDX-License-Identifier: MPL-2.0
//! External specifications used by the `log` facade.
use vstd::prelude::*;

use ::log::{Level, LevelFilter};
use core::{fmt::Arguments, panic::Location};

#[doc(hidden)]
pub use ::log::STATIC_MAX_LEVEL;

verus! {

#[verifier::external_type_specification]
pub struct ExLevel(Level);

#[verifier::external_type_specification]
pub struct ExLevelFilter(LevelFilter);

pub assume_specification[ ::log::STATIC_MAX_LEVEL ] -> LevelFilter
;

/// Reads the current runtime filter. A concurrent update can change the next read.
pub assume_specification[ ::log::max_level ]() -> LevelFilter
    opens_invariants none
    no_unwind
;

} // verus!
/* The upstream macro calls a dispatch function whose generic bound is private.
 * Origin Rust: <none; new helpers for the default log::info! invocation>
 */
#[doc(hidden)]
#[inline]
#[verus_spec(result =>
    ensures result ==> (static_limit is Info || static_limit is Debug || static_limit is Trace),
)]
pub fn info_enabled(static_limit: LevelFilter) -> bool {
    match static_limit {
        LevelFilter::Off | LevelFilter::Error | LevelFilter::Warn => false,
        LevelFilter::Info | LevelFilter::Debug | LevelFilter::Trace => {
            Level::Info <= ::log::max_level()
        }
    }
}

/// Forwards an enabled record to the global logger using the caller's module and location.
/// The installed logger and argument formatting may open invariants and unwind.
#[doc(hidden)]
#[track_caller]
#[verus_verify(external_body)]
#[verus_spec(opens_invariants any)]
pub fn emit_info(module: &'static str, args: Arguments<'_>) {
    let caller = Location::caller();
    ::log::logger().log(
        &::log::Record::builder()
            .args(args)
            .level(Level::Info)
            .target(module)
            .module_path_static(Some(module))
            .file_static(Some(caller.file()))
            .line(Some(caller.line()))
            .build(),
    );
}

/// Logs a formatted message at info level with the calling module as its target.
#[macro_export]
macro_rules! info {
    ($($arg:tt)+) => {{
        if $crate::external::log::info_enabled($crate::external::log::STATIC_MAX_LEVEL) {
            $crate::external::log::emit_info(::core::module_path!(), ::core::format_args!($($arg)+));
        }
    }};
}
