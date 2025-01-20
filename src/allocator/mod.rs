// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

mod block;
pub mod defs;
mod descriptors;
mod error;

pub use block::AllocBlock;
pub use error::AllocError;
