// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::super::{AllocBlock, AllocError};
use super::{DescStorage, RawDescType};

#[derive(Debug, Clone)]
pub struct RawDesc<'r> {
    pub block: &'r AllocBlock,
    index: usize,
    orig_desc: DescStorage,
}

impl<'r> RawDesc<'r> {
    pub fn new(block: &'r AllocBlock, index: usize, desc: DescStorage) -> Self {
        Self {
            block,
            index,
            orig_desc: desc,
        }
    }

    pub fn desc_type(&self) -> Result<RawDescType, AllocError> {
        self.orig_desc.get_type()
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn value(&self) -> DescStorage {
        self.orig_desc
    }

    pub fn store(&mut self, desc: DescStorage) {
        self.block.descriptors().store(self.index, desc.bits());
        self.orig_desc = desc
    }

    pub fn update(&mut self, desc: DescStorage) -> Result<(), AllocError> {
        self.block
            .descriptors()
            .update(self.index, self.orig_desc.bits(), desc.bits())?;
        self.orig_desc = desc;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_raw_desc_buddy() {
        let desc = DescStorage::new()
            .encode_type(RawDescType::Alloc)
            .encode_order(2);
        assert_eq!(desc.get_type().unwrap(), RawDescType::Alloc);
        assert_eq!(desc.get_order(), 2);
    }

    #[test]
    fn test_raw_desc_parts() {
        let desc = DescStorage::new()
            .encode_type(RawDescType::Parts)
            .encode_parts_size(128);
        assert_eq!(desc.get_type().unwrap(), RawDescType::Parts);
        assert_eq!(desc.get_parts_size(), 128);
    }
}
