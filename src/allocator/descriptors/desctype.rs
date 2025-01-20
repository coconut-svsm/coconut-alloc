// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::super::AllocError;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum RawDescType {
    Meta = 0,
    Free = 1,
    Alloc = 2,
    Compound = 3,
    Parts = 4,
    Unknown = 5,
}

impl TryFrom<u32> for RawDescType {
    type Error = AllocError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value == RawDescType::Meta as u32 {
            Ok(RawDescType::Meta)
        } else if value == RawDescType::Free as u32 {
            Ok(RawDescType::Free)
        } else if value == RawDescType::Alloc as u32 {
            Ok(RawDescType::Alloc)
        } else if value == RawDescType::Compound as u32 {
            Ok(RawDescType::Compound)
        } else if value == RawDescType::Parts as u32 {
            Ok(RawDescType::Parts)
        } else {
            Err(AllocError::Internal)
        }
    }
}

impl RawDescType {
    pub fn bits(&self) -> u32 {
        *self as u32
    }
}
