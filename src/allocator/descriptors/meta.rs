// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::{DescStorage, RawDesc, RawDescType};
use crate::AllocBlock;

pub struct MetaDesc<'a> {
    raw: RawDesc<'a>,
}

impl<'a> MetaDesc<'a> {
    pub fn new(block: &'a AllocBlock, index: usize, desc: DescStorage) -> Self {
        Self {
            raw: RawDesc::new(block, index, desc),
        }
    }

    pub fn store(&mut self) {
        self.raw
            .store(DescStorage::new().encode_type(RawDescType::Meta));
    }
}
