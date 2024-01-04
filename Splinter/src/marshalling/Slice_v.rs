// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

verus!{

pub struct Slice {
    pub start: usize,
    pub end: usize,
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
        Slice{start: 0, end: data.len() as usize}
    }

    pub open spec fn agree_beyond_slice<T>(&self, data: Seq<T>, new_data: Seq<T>) -> bool
    {
        &&& data.len() == new_data.len()
        &&& forall |i| 0<=i<self.start ==> data[i] == new_data[i]
        &&& forall |i| self.end<=i<data.len() ==> data[i] == new_data[i]
    }
}

} //verus!
