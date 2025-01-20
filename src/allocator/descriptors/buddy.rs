// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::super::{defs::*, AllocBlock, AllocError};
use super::parts::bitmap_in_desc;
use super::{DescStorage, PartsDesc, RawDesc, RawDescType};

use core::cmp;
#[derive(Clone, Debug)]
pub struct BuddyDesc<'a, const T: u32> {
    pub raw: RawDesc<'a>,
    desc: DescStorage,
    order: u32,
}

impl<'a, const T: u32> BuddyDesc<'a, T> {
    pub fn new(block: &'a AllocBlock, index: usize, desc: DescStorage) -> Self {
        let order = desc.get_order();
        Self {
            raw: RawDesc::new(block, index, desc),
            order,
            desc,
        }
    }

    pub fn index(&self) -> usize {
        self.raw.index()
    }

    pub fn get_order(&self) -> u32 {
        self.order
    }

    pub fn set_order(&mut self, order: u32) {
        self.order = order;
    }

    pub fn store(&mut self) {
        self.update_desc();
        self.raw.store(self.desc);
    }

    pub fn update(&mut self) -> Result<(), AllocError> {
        self.update_desc();
        self.raw.update(self.desc)
    }

    fn update_desc(&mut self) {
        let t: RawDescType = RawDescType::try_from(T).unwrap();
        self.desc = DescStorage::new().encode_type(t).encode_order(self.order);
    }

    pub fn convert_from<const R: u32>(desc: BuddyDesc<'a, R>) -> Self {
        Self {
            raw: desc.raw,
            order: desc.order,
            desc: DescStorage::new(),
        }
    }

    pub fn convert_from_raw(desc: RawDesc<'a>) -> Self {
        Self {
            raw: desc,
            order: 0,
            desc: DescStorage::new(),
        }
    }
}

impl<'a, const T: u32> TryFrom<RawDesc<'a>> for BuddyDesc<'a, T> {
    type Error = AllocError;

    fn try_from(desc: RawDesc<'a>) -> Result<Self, Self::Error> {
        let t = desc.desc_type()?;
        if t.bits() != T {
            return Err(AllocError::TypeMismatch);
        }
        let value = desc.value();
        let order = value.get_order();
        Ok(BuddyDesc::<'a, T> {
            raw: desc,
            desc: value,
            order,
        })
    }
}

pub type FreeDesc<'a> = BuddyDesc<'a, { RawDescType::Free as u32 }>;
pub type AllocDesc<'a> = BuddyDesc<'a, { RawDescType::Alloc as u32 }>;
pub type CompoundDesc<'a> = BuddyDesc<'a, { RawDescType::Compound as u32 }>;

impl<'a> FreeDesc<'a> {
    pub fn allocate(self) -> Result<AllocDesc<'a>, AllocError> {
        let mut alloc_desc = AllocDesc::convert_from(self);
        alloc_desc.update()?;
        Ok(alloc_desc)
    }
}

impl<'a> AllocDesc<'a> {
    pub fn free(self) -> FreeDesc<'a> {
        let mut free_desc = FreeDesc::convert_from(self);
        free_desc.update().expect("Atomic freeing of block failed");
        free_desc
    }

    pub fn make_parts(self, size: usize) -> PartsDesc<'a> {
        let mut parts_desc = PartsDesc::from_alloc(self, size);
        if !bitmap_in_desc(size) {
            // Still an allocated chunk, no concurrent accesses to chunk memory
            // expected.
            parts_desc.bitmap_store(0).unwrap();
        }
        parts_desc.store().unwrap();
        parts_desc
    }

    pub fn split(mut self) -> (AllocDesc<'a>, AllocDesc<'a>) {
        assert!(self.order > 0);
        let chunks: usize = 1 << self.order;
        let split_index = self.raw.index() + (chunks / 2);
        let split_order = self.order - 1;

        let raw_split_desc = self.raw.block.load_desc(split_index);
        let compound_desc = CompoundDesc::try_from(raw_split_desc).unwrap();
        let split_alloc_desc = compound_desc.allocate(split_order).unwrap();

        self.set_order(split_order);
        self.update().unwrap();

        (self, split_alloc_desc)
    }

    pub fn try_merge(self) -> Result<AllocDesc<'a>, AllocDesc<'a>> {
        let order = self.order;

        // No point in merging if chunk has maximum size
        if order == MAX_ORDER {
            return Err(self);
        }

        // Find neighbor index
        let neigh_mask: usize = 1 << order;
        let neigh_index = self.raw.index() ^ neigh_mask;

        // Load and check neighbor descriptor
        let raw_chunk = self.raw.block.load_desc(neigh_index);
        let result = FreeDesc::try_from(raw_chunk);
        if result.is_err() {
            return Err(self);
        }
        let free_desc = result.unwrap();
        if free_desc.get_order() != order {
            return Err(self);
        }

        // Looks all good, try to allocate neighbor
        if free_desc.allocate().is_err() {
            return Err(self);
        }

        // Neighbor is secured - now merge both allocations
        let new_order = self.order + 1;
        let chunks: usize = 1 << new_order;

        let first_index = cmp::min(self.raw.index(), neigh_index);
        let raw_desc1 = self.raw.block.load_desc(first_index);
        let mut alloc_desc = AllocDesc::convert_from_raw(raw_desc1);
        alloc_desc.set_order(new_order);
        alloc_desc.store();

        let second_index = first_index + (chunks / 2);
        let raw_desc2 = self.raw.block.load_desc(second_index);
        let mut compound_desc = CompoundDesc::convert_from_raw(raw_desc2);
        compound_desc.set_order(0);
        compound_desc.store();

        Ok(alloc_desc)
    }
}

impl<'a> CompoundDesc<'a> {
    pub fn allocate(self, order: u32) -> Result<AllocDesc<'a>, AllocError> {
        let mut alloc_desc = AllocDesc::convert_from(self);
        alloc_desc.set_order(order);
        alloc_desc.update()?;
        Ok(alloc_desc)
    }
}
