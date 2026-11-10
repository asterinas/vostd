// SPDX-License-Identifier: MPL-2.0
//! Isolated proof entry point for the repository's stack-size parser.
#![feature(proc_macro_hygiene)]

use vstd::prelude::*;

#[path = "../../ostd/src/task/stack_size.rs"]
mod stack_size;
