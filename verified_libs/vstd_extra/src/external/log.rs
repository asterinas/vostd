// SPDX-License-Identifier: MPL-2.0
//! External specifications used by the `log` facade.
use vstd::prelude::*;

use ::log::{Level, LevelFilter};
use core::{fmt::Arguments, panic::Location};

verus! {

#[verifier::external_type_specification]
pub struct ExLevel(Level);

#[verifier::external_type_specification]
pub struct ExLevelFilter(LevelFilter);

// The log crate selects this value from its Cargo features and build profile.
assume_specification[ ::log::STATIC_MAX_LEVEL ] -> LevelFilter
    opens_invariants none
    no_unwind
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
#[verus_verify]
pub fn info_enabled() -> bool {
    Level::Info <= ::log::STATIC_MAX_LEVEL && Level::Info <= ::log::max_level()
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
        if $crate::external::log::info_enabled() {
            $crate::external::log::emit_info(::core::module_path!(), ::core::format_args!($($arg)+));
        }
    }};
}
