// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::{map::*, seq::*, bytes::*};

use crate::spec::MapSpec_t::{ID};

verus!{

/// The `AU` type is the type for a unique allocation unit identifier (thus we use `nat`s).
/// 
/// An Allocation Unit (AU) is the minimum disk unit the "external" (i.e.: top-level) allocator
/// allocates to data structures like the Betree and Journal. Allocation Units
/// are made up of contiguous disk sectors. AUs are specified as part of the
/// Splinter implementation. The goal of having large allocation blocks is to
/// amortize allocation costs efficiently for large amounts of data.
pub type AU = nat;

/// A page index within an AU (disk pages, so for SSDs these are on the order of 4KB).
pub type Page = nat;

/// An Address specifies a specific disk address (i.e.: an address that identifies a disk sector (or whatever
/// atomic addressing unit the disk in question uses)).
/// It does this by combining an AU index with a page index within the AU.
pub struct Address {
    /// The Allocation Unit index this address resides within.
    pub au: AU,
    /// Page index within AU for this address. In the range [0,page_count).
    pub page: Page,
}

} // end of !verus