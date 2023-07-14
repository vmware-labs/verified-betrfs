// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus!{

pub type AU = nat;
pub type Page = nat;

pub closed spec(checked) fn page_count() -> nat;

pub struct Address {
    pub au: AU,
    pub page: Page,
}

impl Address {
    pub open spec(checked) fn wf(self) -> bool {
        self.page < page_count()
    }

    pub open spec(checked) fn first_page(self) -> Address {
        Address{page: 0, ..self}
    }

    pub open spec(checked) fn next_page(self) -> Address {
        Address{page: self.page+1, ..self}
    }
}

pub open spec(checked) fn min_addr(a: Address, b: Address) -> Address {
    if a.au < b.au { a }
    else if a.au > b.au { b }
    else if a.page <= b.page { a }
    else { b }
}

pub open spec(checked) fn to_aus(addrs: Set<Address>) -> Set<AU> {
    addrs.map(|addr: Address| addr.au)
}

pub type Pointer = Option<Address>;
pub type Ranking = Map<Address, nat>;   // Used by Linked* layers to show acyclicity.

}
