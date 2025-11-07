// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::defs::*;
use super::descriptors::{
    AllocDesc, CompoundDesc, DescStorage, FreeDesc, MetaDesc, PartsDesc, RawDesc, RawDescType,
};
use super::AllocError;

use core::cmp;
use core::sync::atomic::{AtomicU32, Ordering};

#[derive(Debug, Copy, Clone)]
#[repr(C)]
struct Chunk {
    data: [u8; CHUNK_SIZE],
}

impl Chunk {
    const fn new() -> Self {
        Chunk {
            data: [0u8; CHUNK_SIZE],
        }
    }
}

impl Default for Chunk {
    fn default() -> Self {
        Chunk {
            data: [0u8; CHUNK_SIZE],
        }
    }
}

#[derive(Debug)]
pub struct MetaChunk {
    descs: [ChunkDescStorageType; CHUNK_SIZE / CHUNK_DESC_SIZE],
}

impl MetaChunk {
    pub fn load(&self, index: usize) -> u32 {
        self.descs[index].load(Ordering::Acquire)
    }

    pub fn store(&self, index: usize, val: u32) {
        self.descs[index].store(val, Ordering::Release);
    }

    pub fn update(&self, index: usize, old_val: u32, new_val: u32) -> Result<(), AllocError> {
        self.descs[index]
            .compare_exchange(old_val, new_val, Ordering::Release, Ordering::Acquire)
            .map(|_| ())
            .map_err(|_| AllocError::Retry)
    }
}

pub struct ChunkIterator<'a> {
    block: &'a AllocBlock,
    next_index: usize,
}

impl ChunkIterator<'_> {
    fn compound_end(index: usize, order: u32) -> usize {
        let chunks: usize = 1 << order;
        let chunk_mask: usize = chunks - 1;
        (index & !chunk_mask) + chunks
    }

    fn skip_compound(&self, start: usize) -> usize {
        for index in start..CHUNK_COUNT {
            let desc = self.block.load_desc(index);
            match desc.value().get_type() {
                Ok(t) => {
                    if t != RawDescType::Compound {
                        return index;
                    } else {
                        continue;
                    }
                }
                Err(_) => {
                    return index;
                }
            }
        }
        CHUNK_COUNT
    }
}

impl<'a> Iterator for ChunkIterator<'a> {
    type Item = Result<RawDesc<'a>, AllocError>;

    fn next(&mut self) -> Option<Self::Item> {
        assert!(self.next_index <= CHUNK_COUNT);
        if self.next_index == CHUNK_COUNT {
            return None;
        }

        let desc = self.block.load_desc(self.next_index);
        let t = desc.value().get_type();
        if let Err(e) = t {
            return Some(Err(e));
        }
        let new_index = match t.unwrap() {
            RawDescType::Free | RawDescType::Alloc => {
                Self::compound_end(self.next_index, desc.value().get_order())
            }
            RawDescType::Compound => self.skip_compound(self.next_index + 1),
            _ => self.next_index + 1,
        };
        self.next_index = new_index;
        Some(Ok(desc))
    }
}

#[derive(Debug)]
#[repr(C, packed(65536))]
pub struct AllocBlock {
    chunks: [Chunk; CHUNK_COUNT],
}

impl Default for AllocBlock {
    fn default() -> Self {
        Self {
            chunks: [Chunk::default(); CHUNK_COUNT],
        }
    }
}

impl<'a> AllocBlock {
    pub const fn new() -> Self {
        AllocBlock {
            chunks: [Chunk::new(); CHUNK_COUNT],
        }
    }

    pub fn descriptors(&'a self) -> &'a MetaChunk {
        // SAFETY: Chunk 0 is always reserved for meta-data; struct Chunk and
        // MetaChunk have the same size.
        unsafe {
            self.chunks[0]
                .data
                .as_ptr()
                .cast::<MetaChunk>()
                .as_ref()
                .unwrap()
        }
    }

    pub fn load_desc(&'a self, index: usize) -> RawDesc<'a> {
        let raw_desc = DescStorage::init(self.descriptors().load(index));
        RawDesc::new(self, index, raw_desc)
    }

    /// Get a reference to an in-chunk allocation bitmap
    ///
    /// # Aguments
    ///
    /// * `index` - Index of the chunk
    ///
    /// # Returns
    ///
    /// Returns a reference to an in-chunk allocation bitmap which can be
    /// atomically updated.
    ///
    /// # Safety
    ///
    /// The caller needs to make sure that `index` points to a chunk reserved
    /// for sub-chunk-size allocations and where the allocation bitmap does not
    /// fit into the chunk descriptor.
    pub unsafe fn chunk_bitmap(&'a self, index: usize) -> &'a AtomicU32 {
        self.chunks[index]
            .data
            .as_ptr()
            .cast::<AtomicU32>()
            .as_ref()
            .unwrap()
    }

    fn make_compound_page(&mut self, index: usize, order: u32) {
        // Check alignment
        assert!(index.trailing_zeros() >= order);

        let count: usize = 1 << order;
        for i in index..index + count {
            if i == index {
                let mut desc = FreeDesc::new(self, i, DescStorage::new());
                desc.set_order(order);
                desc.store();
            } else {
                let mut desc = CompoundDesc::new(self, i, DescStorage::new());
                desc.store();
            }
        }
    }

    pub fn initialize(&mut self) {
        let mut index: usize = 0;
        loop {
            if index == CHUNK_COUNT {
                break;
            }
            if index == 0 {
                // Meta Chunk
                let mut desc = MetaDesc::new(self, index, DescStorage::new());
                desc.store();
                index += 1;
            } else {
                let order = index.trailing_zeros();
                let chunks = 1 << order;
                self.make_compound_page(index, order);
                index += chunks;
            }
        }
    }

    fn chunk_offset(desc: AllocDesc) -> usize {
        desc.index() * CHUNK_SIZE
    }

    fn alloc_buddy_one(&self, order: u32) -> Result<AllocDesc<'_>, AllocError> {
        // Minimal order observed in list
        let mut order_bitmap = 0;

        for desc in self.iter() {
            let raw_desc = desc?;
            let desc_type = raw_desc.desc_type()?;
            if desc_type != RawDescType::Free {
                continue;
            }
            let free_desc = FreeDesc::try_from(raw_desc)?;
            order_bitmap |= 1 << free_desc.get_order();
            if free_desc.get_order() == order {
                let alloc_desc = free_desc.allocate()?;
                return Ok(alloc_desc);
            }
        }

        Err(AllocError::NoMatch(order_bitmap))
    }

    fn alloc_buddy_desc(&self, order: u32) -> Result<AllocDesc<'_>, AllocError> {
        // Retry loop
        loop {
            let order_bmp_mask: u32 = !((1 << order) - 1);

            let result = self.alloc_buddy_one(order);
            if let Err(e) = result {
                match e {
                    AllocError::Retry => continue,
                    AllocError::NoMatch(bmp) => {
                        if (bmp & order_bmp_mask) == 0 {
                            // No more chunk blocks of required size available
                            return Err(AllocError::NoMem);
                        } else {
                            // No exact match, but bigger allocations are
                            // available. Allocate one and split it up.
                            let alloc_desc = self.alloc_buddy_desc(order + 1)?;
                            let (alloc1, alloc2) = alloc_desc.split();
                            alloc2.free();
                            return Ok(alloc1);
                        }
                    }
                    _ => return Err(e),
                }
            } else {
                return result;
            }
        }
    }

    fn alloc_buddy(&self, order: u32) -> Result<usize, AllocError> {
        self.alloc_buddy_desc(order)
            .map(|desc| AllocBlock::chunk_offset(desc))
    }

    fn free_buddy_desc(desc: AllocDesc) {
        match desc.try_merge() {
            // Merge successful - free merged chunk.
            Ok(alloc_desc) => Self::free_buddy_desc(alloc_desc),
            // No merge - free chunk.
            Err(alloc_desc) => {
                let _ = alloc_desc.free();
            }
        }
    }

    fn free_buddy(&self, offset: usize) {
        let index = offset / CHUNK_SIZE;
        let raw_desc = self.load_desc(index);
        let alloc_desc = AllocDesc::try_from(raw_desc)
            .expect("Internal allocator error: Trying to free a non-allocated chunk");
        Self::free_buddy_desc(alloc_desc);
    }

    fn find_parts_chunk(&self, size: usize) -> Result<PartsDesc<'_>, AllocError> {
        for desc in self.iter() {
            let raw_desc = desc?;
            if let Ok(parts_desc) = PartsDesc::try_from(raw_desc) {
                if (size != parts_desc.alloc_size()) || parts_desc.is_full() {
                    continue;
                }
                return Ok(parts_desc);
            }
        }
        Err(AllocError::NoMatch(0))
    }

    fn alloc_parts_chunk(&self, size: usize) -> Result<PartsDesc<'_>, AllocError> {
        // alloc_buddy() does not return AllocError::Retry
        let alloc_desc = self.alloc_buddy_desc(0)?;
        let parts_desc = alloc_desc.make_parts(size);
        Ok(parts_desc)
    }

    fn free_parts(&self, offset: usize) {
        let chunk_offset = offset % CHUNK_SIZE;
        let chunk_index = offset / CHUNK_SIZE;
        assert!(chunk_index > 0);

        loop {
            let raw_desc = self.load_desc(chunk_index);
            let mut parts_desc = PartsDesc::try_from(raw_desc).expect("Exptected PartsDesc");
            let result = parts_desc.free_part(chunk_offset);
            match result {
                Ok(is_empty) => {
                    if is_empty {
                        if let Ok(alloc_desc) = parts_desc.try_to_alloc() {
                            Self::free_buddy_desc(alloc_desc);
                        }
                    }
                    break;
                }
                Err(e) => {
                    assert!(e == AllocError::Retry);
                    continue;
                }
            }
        }
    }

    fn alloc_parts(&self, size: usize) -> Result<usize, AllocError> {
        loop {
            let mut parts_desc = self
                .find_parts_chunk(size)
                .or_else(|_| self.alloc_parts_chunk(size))?;
            let index = parts_desc.index();
            match parts_desc.alloc_part() {
                Ok(offset) => return Ok((index * CHUNK_SIZE) + offset),
                Err(e) => {
                    if e == AllocError::Retry {
                        continue;
                    } else {
                        return Err(e);
                    }
                }
            }
        }
    }

    fn get_order(size: usize) -> u32 {
        (size / CHUNK_SIZE).ilog2()
    }

    fn allocation_size(size: usize) -> Result<usize, AllocError> {
        if size > (BLOCK_SIZE / 2) {
            Err(AllocError::Inval)
        } else {
            Ok(cmp::max(size.next_power_of_two(), MIN_ALLOC_SIZE))
        }
    }

    pub fn alloc(&self, size: usize) -> Result<usize, AllocError> {
        let adjusted_size = Self::allocation_size(size)?;
        if adjusted_size < CHUNK_SIZE {
            self.alloc_parts(adjusted_size)
        } else {
            self.alloc_buddy(Self::get_order(adjusted_size))
        }
    }

    pub fn free(&self, offset: usize) {
        let index = offset / CHUNK_SIZE;
        let raw_chunk = self.load_desc(index);
        let desc_type = raw_chunk.desc_type().unwrap();
        match desc_type {
            RawDescType::Alloc => self.free_buddy(offset),
            RawDescType::Parts => self.free_parts(offset),
            _ => panic!("Unexpected chunk type"),
        }
    }

    fn iter(&'a self) -> ChunkIterator<'a> {
        ChunkIterator {
            block: self,
            next_index: 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::size_of;

    #[test]
    fn test_sizes() {
        assert_eq!(size_of::<AllocBlock>(), BLOCK_SIZE);
        assert_eq!(size_of::<Chunk>(), CHUNK_SIZE);
        assert_eq!(size_of::<MetaChunk>(), CHUNK_SIZE);
    }
}
