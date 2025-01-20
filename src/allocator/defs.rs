// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use core::mem;
use core::sync::atomic::AtomicU32;

pub type ChunkDescStorageType = AtomicU32;
pub const CHUNK_DESC_SIZE: usize = mem::size_of::<ChunkDescStorageType>();

pub const BLOCK_SIZE: usize = 64 * 1024;
pub const CHUNK_COUNT: usize = 1 << ((BLOCK_SIZE / CHUNK_DESC_SIZE).ilog2() / 2);
pub const CHUNK_SIZE: usize = BLOCK_SIZE / CHUNK_COUNT;
pub const MAX_ORDER: u32 = (CHUNK_COUNT - 1).ilog2();

pub const MIN_ALLOC_SIZE: usize = 16;
