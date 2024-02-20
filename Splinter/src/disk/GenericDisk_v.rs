// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! This file contains types relating to generic disk addressing and referencing.

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

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

/// Returns the number of a disk pages in an Allocation Unit. Left as an uninterpreted function
/// since it's implementation defined.
pub closed spec(checked) fn page_count() -> nat;

/// An Address specifies a specific disk address (i.e.: an address that identifies a disk sector (or whatever
/// atomic addressing unit the disk in question uses)).
/// It does this by combining an AU index with a page index within the AU.
pub struct Address {
    /// The Allocation Unit index this address resides within.
    pub au: AU,
    /// Page index within AU for this address. In the range [0,page_count).
    pub page: Page,
}

impl Address {
    /// Returns true iff this Address is well formed.
    pub open spec(checked) fn wf(self) -> bool {
        self.page < page_count()
    }

    /// Returns the Address for the first page of this AU.
    pub open spec(checked) fn first_page(self) -> Address {
        Address{page: 0, ..self}
    }

    /// Returns the previous Address in this AU (may not be well-formed).
    pub open spec(checked) fn previous(self) -> Address {
        Address{page: (self.page-1) as nat, ..self}
    }
    
    /// Returns the next Address in this AU (may not be well-formed).
    pub open spec(checked) fn next(self) -> Address {
        Address{page: self.page+1, ..self}
    }

    // Returns true for WF addresses within the same AU but after self
    pub open spec(checked) fn after_page(self, addr: Self) -> bool {
        &&& addr.wf()
        &&& addr.au == self.au
        &&& addr.page > self.page
    }
}

pub open spec(checked) fn first_page(ptr: Pointer) -> Pointer {
    match ptr {
        None => None,
        Some(addr) => Some(addr.first_page()),
    }
}

/// Return the lowest of two addresses. Addresses are first compared by AU,
/// then by Page index (if AUs match).
pub open spec(checked) fn min_addr(a: Address, b: Address) -> Address {
    if a.au < b.au { a }
    else if a.au > b.au { b }
    else if a.page <= b.page { a }
    else { b }
}

/// Returns the set of AUs that the provided set of Addresses live in.
pub open spec(checked) fn to_aus(addrs: Set<Address>) -> Set<AU> {
    addrs.map(|addr: Address| addr.au)
}

/// A Pointer is either an Address or None. (i.e.: we wrap Address with the semantics for
/// "NULL" pointers). Used when certain data structures might have unallocated pointers.
pub type Pointer = Option<Address>;
pub type Ranking = Map<Address, nat>;   // Used by Linked* layers to show acyclicity.

}
