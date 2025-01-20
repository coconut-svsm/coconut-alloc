// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::super::{defs::MIN_ALLOC_SIZE, AllocError};
use super::RawDescType;

const fn bit_mask(bits: u32) -> u32 {
    (1u32 << bits) - 1
}

#[derive(Debug, Default, Copy, Clone)]
#[repr(transparent)]
pub struct DescStorage(u32);

impl DescStorage {
    pub fn new() -> Self {
        Self(0)
    }

    pub fn init(value: u32) -> Self {
        Self(value)
    }

    pub fn bits(&self) -> u32 {
        self.0
    }

    const DESC_TYPE_SHIFT: u32 = 0;
    const DESC_TYPE_BITS: u32 = 3;
    const DESC_TYPE_MASK: u32 = bit_mask(Self::DESC_TYPE_BITS) << Self::DESC_TYPE_SHIFT;

    pub fn encode_type(&self, t: RawDescType) -> Self {
        Self(
            (self.0 & !Self::DESC_TYPE_MASK)
                | (((t as u32) << Self::DESC_TYPE_SHIFT) & Self::DESC_TYPE_MASK),
        )
    }

    pub fn get_type(&self) -> Result<RawDescType, AllocError> {
        RawDescType::try_from((self.0 & Self::DESC_TYPE_MASK) >> Self::DESC_TYPE_SHIFT)
    }

    const DESC_ORDER_SHIFT: u32 = Self::DESC_TYPE_BITS;
    const DESC_ORDER_BITS: u32 = 3;
    const DESC_ORDER_MASK: u32 = bit_mask(Self::DESC_ORDER_BITS) << Self::DESC_ORDER_SHIFT;

    pub fn encode_order(&self, order: u32) -> Self {
        Self(
            (self.0 & !Self::DESC_ORDER_MASK)
                | ((order << Self::DESC_ORDER_SHIFT) & Self::DESC_ORDER_MASK),
        )
    }

    pub fn get_order(&self) -> u32 {
        (self.0 & Self::DESC_ORDER_MASK) >> Self::DESC_ORDER_SHIFT
    }

    const DESC_PARTS_SIZE_SHIFT: u32 = Self::DESC_TYPE_BITS;
    const DESC_PARTS_SIZE_BITS: u32 = 8;
    const DESC_PARTS_SIZE_MASK: u32 =
        bit_mask(Self::DESC_PARTS_SIZE_BITS) << Self::DESC_PARTS_SIZE_SHIFT;

    pub fn encode_parts_size(&self, size: usize) -> Self {
        debug_assert!(size.is_power_of_two());
        let encoded_size: u32 = <usize as TryInto<u32>>::try_into(size / MIN_ALLOC_SIZE).unwrap();
        Self(
            (self.0 & !Self::DESC_PARTS_SIZE_MASK)
                | ((encoded_size << Self::DESC_PARTS_SIZE_SHIFT) & Self::DESC_PARTS_SIZE_MASK),
        )
    }

    pub fn get_parts_size(&self) -> usize {
        (((self.0 & Self::DESC_PARTS_SIZE_MASK) >> Self::DESC_PARTS_SIZE_SHIFT) as usize)
            * MIN_ALLOC_SIZE
    }

    const DESC_BITMAP_SHIFT: u32 = 16;
    const DESC_BITMAP_BITS: u32 = 16;
    const DESC_BITMAP_MASK: u32 = bit_mask(Self::DESC_BITMAP_BITS) << Self::DESC_BITMAP_SHIFT;
    const DESC_BITMAP_FULL_BIT: u32 = 0;
    const DESC_BITMAP_LOCK_BIT: u32 = 1;
    const DESC_BITMAP_FULL_MASK: u32 = 1 << (Self::DESC_BITMAP_FULL_BIT + Self::DESC_BITMAP_SHIFT);
    const DESC_BITMAP_LOCK_MASK: u32 = 1 << (Self::DESC_BITMAP_LOCK_BIT + Self::DESC_BITMAP_SHIFT);

    pub fn encode_bitmap(&self, bitmap: u32) -> Self {
        Self(
            (self.0 & !Self::DESC_BITMAP_MASK)
                | ((bitmap << Self::DESC_BITMAP_SHIFT) & Self::DESC_BITMAP_MASK),
        )
    }

    pub fn get_bitmap(&self) -> u32 {
        (self.0 & Self::DESC_BITMAP_MASK) >> Self::DESC_BITMAP_SHIFT
    }

    pub fn set_full(&self) -> Self {
        Self(self.0 | Self::DESC_BITMAP_FULL_MASK)
    }

    pub fn clear_full(&self) -> Self {
        Self(self.0 & !Self::DESC_BITMAP_FULL_MASK)
    }

    pub fn is_full(&self) -> bool {
        (self.0 & Self::DESC_BITMAP_FULL_MASK) == Self::DESC_BITMAP_FULL_MASK
    }

    pub fn set_lock(&self) -> Self {
        Self(self.0 | Self::DESC_BITMAP_LOCK_MASK)
    }

    pub fn clear_lock(&self) -> Self {
        Self(self.0 & !Self::DESC_BITMAP_LOCK_MASK)
    }

    pub fn is_locked(&self) -> bool {
        (self.0 & Self::DESC_BITMAP_LOCK_MASK) == Self::DESC_BITMAP_LOCK_MASK
    }
}
