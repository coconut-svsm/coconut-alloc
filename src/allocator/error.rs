// SPDX-License-Identifier: MIT
//
// Copyright (c) 2025 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum AllocError {
    Retry,
    NoMem,
    Inval,
    NoMatch(u32),
    Internal,
    TypeMismatch,
}
