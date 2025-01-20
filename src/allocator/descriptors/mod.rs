// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

mod buddy;
mod desctype;
mod meta;
mod parts;
mod raw;
mod storage;

pub use buddy::{AllocDesc, CompoundDesc, FreeDesc};
pub use desctype::RawDescType;
pub use meta::MetaDesc;
pub use parts::PartsDesc;
pub use raw::RawDesc;
pub use storage::DescStorage;
