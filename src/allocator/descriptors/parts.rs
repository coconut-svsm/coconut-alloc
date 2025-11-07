// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::super::{defs::*, AllocError};
use super::{AllocDesc, DescStorage, RawDesc, RawDescType};

use core::mem;
use core::sync::atomic::Ordering;

pub fn bitmap_in_desc(alloc_size: usize) -> bool {
    (CHUNK_SIZE / alloc_size) <= 16
}

#[derive(Clone, Debug)]
pub struct PartsDesc<'a> {
    raw: RawDesc<'a>,
    desc: DescStorage,
    alloc_size: usize,
    locked: bool,
    full: bool,
}

#[inline(always)]
fn bitmap_unavailable_mask(alloc_size: usize) -> u32 {
    debug_assert!(alloc_size.is_power_of_two());
    let items = CHUNK_SIZE / alloc_size;
    debug_assert!((2..=32).contains(&items));
    let raw_unavail_mask: u32 = if items == 32 {
        0
    } else {
        !((1u32 << items) - 1)
    };
    let bitmap_chunk_mask: u32 = if bitmap_in_desc(alloc_size) {
        0
    } else {
        let bitmap_chunks = (8 * mem::size_of::<u32>()) / alloc_size;
        (1u32 << bitmap_chunks) - 1
    };

    raw_unavail_mask | bitmap_chunk_mask
}

pub struct PartsLockGuard<'a, 'b> {
    parts_desc: &'b mut PartsDesc<'a>,
    chunk_released: bool,
}

impl<'a, 'b> PartsLockGuard<'a, 'b> {
    fn get_bitmap_and_mask(&self) -> (u32, u32) {
        let raw_bitmap: u32 = self.parts_desc.bitmap_load();
        let unavail_mask: u32 = bitmap_unavailable_mask(self.parts_desc.alloc_size);
        assert!((raw_bitmap & unavail_mask) == 0);

        (raw_bitmap | unavail_mask, !unavail_mask)
    }

    /// Tries to allocate a chunk from the locked `PartsDesc`.
    ///
    /// # Returns
    ///
    /// Returns a `[Result]` with the byte offset of the allocated region on success.
    /// On Failure an `Err(AllocError)` is returned. The error values carry the following meaning:
    ///
    /// * `AllocError::Retry` - The atomic update of the chunk descriptor failed, re-read the descriptor and try again.
    /// * `AllocError::NoMem` - No more free parts available in this chunk.
    pub fn try_alloc(&mut self) -> Result<usize, AllocError> {
        let (bitmap, avail_mask) = self.get_bitmap_and_mask();
        let bit: usize = bitmap.trailing_ones() as usize;
        if bit < 32 {
            let alloc_mask: u32 = 1 << bit;
            debug_assert!((alloc_mask & avail_mask) == alloc_mask);

            let bmp = bitmap | alloc_mask;
            debug_assert!(bitmap.count_ones() + 1 == bmp.count_ones());

            self.parts_desc.bitmap_store(bmp & avail_mask)?;
            Ok(self.parts_desc.alloc_size * bit)
        } else {
            if !bitmap_in_desc(self.parts_desc.alloc_size) {
                let desc = self.parts_desc.desc.set_full();
                self.parts_desc
                    .raw
                    .update(desc)
                    .expect("Failed to update locked chunk descriptor");
                self.parts_desc.desc = desc;
            }
            Err(AllocError::NoMem)
        }
    }

    /// Frees the part at the given offset in this chunk.
    ///
    /// # Arguments:
    ///
    /// * `offset` - The byte offset of the part to free from the start of the
    ///   chunk. The value must point to the beginning of the part.
    ///
    /// # Returns:
    ///
    /// Returns `Err(AllocError::Retry)` in case the atomic update of the chunk
    /// descriptor failed and `Ok(bool)` when the operation was successful.
    /// When the `bool` is `true` then the bitmap was empty after freeing
    /// `offset`.
    pub fn free(&mut self, offset: usize) -> Result<bool, AllocError> {
        assert!(offset.is_multiple_of(self.parts_desc.alloc_size));

        let (bitmap, avail_mask) = self.get_bitmap_and_mask();
        let bit = offset / self.parts_desc.alloc_size;
        assert!(bit < 32);

        let alloc_mask: u32 = 1 << bit;
        assert!((alloc_mask & avail_mask) == alloc_mask);
        assert!((bitmap & alloc_mask) == alloc_mask);

        let store_bitmap = (bitmap & !alloc_mask) & avail_mask;
        self.parts_desc.bitmap_store(store_bitmap)?;

        if !bitmap_in_desc(self.parts_desc.alloc_size) {
            let desc = self.parts_desc.desc.clear_full();
            self.parts_desc
                .raw
                .update(desc)
                .expect("Failed to update locked chunk descriptor");
            self.parts_desc.desc = desc;
        }

        Ok(store_bitmap == 0)
    }

    pub fn empty(&mut self) -> bool {
        let (bitmap, avail_mask) = self.get_bitmap_and_mask();
        (bitmap & avail_mask) == 0
    }

    fn make_alloc(&mut self) -> Result<AllocDesc<'a>, AllocError> {
        let desc = self.parts_desc.make_alloc()?;
        self.chunk_released = true;
        Ok(desc)
    }
}

impl Drop for PartsLockGuard<'_, '_> {
    fn drop(&mut self) {
        if self.chunk_released {
            return;
        }
        if !bitmap_in_desc(self.parts_desc.alloc_size) {
            let desc = self.parts_desc.desc.clear_lock();
            assert!(self.parts_desc.raw.update(desc).is_ok());
            self.parts_desc.desc = desc;
        }
        self.parts_desc.locked = false;
    }
}

impl<'a> PartsDesc<'a> {
    pub fn from_raw(raw: RawDesc<'a>) -> Self {
        let desc = raw.value();
        let alloc_size = desc.get_parts_size();
        let (locked, full) = if bitmap_in_desc(alloc_size) {
            let full_bitmap = !bitmap_unavailable_mask(alloc_size);
            (false, (desc.get_bitmap() & full_bitmap) == full_bitmap)
        } else {
            (desc.is_locked(), desc.is_full())
        };

        Self {
            raw,
            desc,
            alloc_size,
            locked,
            full,
        }
    }

    pub fn from_alloc(alloc_desc: AllocDesc<'a>, size: usize) -> Self {
        let desc = DescStorage::new()
            .encode_type(RawDescType::Parts)
            .encode_parts_size(size)
            .encode_bitmap(0);
        Self {
            raw: alloc_desc.raw,
            desc,
            alloc_size: size,
            locked: false,
            full: false,
        }
    }

    pub fn store(&mut self) -> Result<(), AllocError> {
        self.raw.update(self.desc)
    }

    pub fn alloc_size(&self) -> usize {
        self.alloc_size
    }

    pub fn index(&self) -> usize {
        self.raw.index()
    }

    pub fn is_full(&self) -> bool {
        self.full
    }

    fn make_alloc(&mut self) -> Result<AllocDesc<'a>, AllocError> {
        let desc = DescStorage::new()
            .encode_type(RawDescType::Alloc)
            .encode_order(0);
        self.raw.update(desc)?;

        AllocDesc::try_from(self.raw.clone())
    }

    pub fn bitmap_load(&self) -> u32 {
        if !bitmap_in_desc(self.alloc_size) {
            // SAFETY: This is safe because the code reads from a chunk
            // guaranteed to be reserved for sub-chunk allocations and the
            // bitmap_in_desc() check failed.
            let bmp_ref = unsafe { self.raw.block.chunk_bitmap(self.raw.index()) };
            // The Chunk is locked, so Ordering::Relaxed is sufficient
            bmp_ref.load(Ordering::Relaxed)
        } else {
            self.desc.get_bitmap()
        }
    }

    pub fn bitmap_store(&mut self, bitmap: u32) -> Result<(), AllocError> {
        if !bitmap_in_desc(self.alloc_size) {
            // SAFETY: This is safe because the code reads from a chunk
            // guaranteed to be reserved for sub-chunk allocations and the
            // bitmap_in_desc() check failed.
            let bmp_ref = unsafe { self.raw.block.chunk_bitmap(self.raw.index()) };
            // The Chunk is locked, so Ordering::Relaxed is sufficient
            bmp_ref.store(bitmap, Ordering::Relaxed);
        } else {
            let desc = self.desc.encode_bitmap(bitmap);
            self.raw.update(desc)?;
            self.desc = desc;
        }

        Ok(())
    }

    pub fn try_lock<'b>(&'b mut self) -> Result<PartsLockGuard<'a, 'b>, AllocError> {
        if self.locked {
            return Err(AllocError::Retry);
        }

        if !bitmap_in_desc(self.alloc_size) {
            let desc = self.desc.set_lock();
            self.raw.update(desc)?;
            self.desc = desc;
        }

        self.locked = true;
        Ok(PartsLockGuard {
            parts_desc: self,
            chunk_released: false,
        })
    }

    pub fn alloc_part(&'a mut self) -> Result<usize, AllocError> {
        let mut guard = self.try_lock()?;
        guard.try_alloc()
    }

    pub fn free_part(&mut self, offset: usize) -> Result<bool, AllocError> {
        match self.try_lock() {
            Ok(mut guard) => match guard.free(offset) {
                Ok(is_empty) => Ok(is_empty),
                Err(e) => {
                    assert!(e == AllocError::Retry);
                    Err(e)
                }
            },
            Err(e) => {
                assert!(e == AllocError::Retry);
                Err(e)
            }
        }
    }

    pub fn try_to_alloc(self) -> Result<AllocDesc<'a>, AllocError> {
        // Try to free an empty parts-chunk. Take lock and check bitmap. If
        // lock can not be taken, someone is probably allocating, so don't
        // bother.

        loop {
            // First check if the PartsDesc we are trying to free is still in
            // place by reloading it.
            let raw_desc = self.raw.block.load_desc(self.index());
            let mut parts_desc = PartsDesc::try_from(raw_desc)?;

            // It is still a PartsDesc - Try to free the reloaded one

            match parts_desc.try_lock() {
                Ok(mut guard) => {
                    if !guard.empty() {
                        return Err(AllocError::Inval);
                    }
                    match guard.make_alloc() {
                        Ok(alloc_desc) => {
                            return Ok(alloc_desc);
                        }
                        Err(e) => {
                            if e == AllocError::Retry {
                                continue;
                            } else {
                                return Err(e);
                            }
                        }
                    }
                }
                Err(e) => {
                    if e == AllocError::Retry {
                        continue;
                    } else {
                        return Err(e);
                    }
                }
            };
        }
    }
}

impl<'a> TryFrom<RawDesc<'a>> for PartsDesc<'a> {
    type Error = AllocError;

    fn try_from(value: RawDesc<'a>) -> Result<Self, Self::Error> {
        let t = value.desc_type()?;
        if t != RawDescType::Parts {
            return Err(AllocError::TypeMismatch);
        }
        Ok(PartsDesc::from_raw(value))
    }
}
