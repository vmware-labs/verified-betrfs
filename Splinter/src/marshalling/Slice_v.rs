// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

verus!{

pub struct Slice {
    pub start: u64,
    pub end: u64,
}

impl Slice {
    // Translates WF'
    pub open spec fn valid<T>(&self, data: Seq<T>) -> bool
    {
        0 <= (self.start as int) <= (self.end as int) <= data.len()
    }

    pub open spec fn i<T>(&self, data: Seq<T>) -> Seq<T>
    recommends
        self.valid(data),
    {
        data.subrange(self.start as int, self.end as int)
    }

    pub open spec fn all<T>(data: Seq<T>) -> Slice
    {
        Slice{start: 0, end: data.len() as u64}
    }
}

} //verus!
