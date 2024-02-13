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
    pub open spec fn wf(&self) -> bool
    {
        self.start as int <= self.end as int
    }

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

    pub open spec fn spec_len(&self) -> int
    {
        self.end - self.start
    }

    pub exec fn exec_len(&self) -> (out: usize)
    requires self.wf(),
    ensures out as int == self.spec_len(),
    {
        self.end - self.start
    }

    pub open spec fn all<T>(data: Seq<T>) -> Slice
    {
        Slice{start: 0, end: data.len() as usize}
    }

    pub exec fn exec_all<T>(data: &Vec<T>) -> Slice
    {
        Slice{start: 0, end: data.len() as usize}
    }

    pub open spec fn agree_beyond_slice<T>(&self, data: Seq<T>, new_data: Seq<T>) -> bool
    {
        &&& data.len() == new_data.len()
        &&& forall |i| 0<=i<self.start ==> data[i] == new_data[i]
        &&& forall |i| self.end<=i<data.len() ==> data[i] == new_data[i]
    }

    // TODO(verus): Another nice place for a function-method-like affordance
    pub open spec fn spec_sub(&self, a: usize, b: usize) -> (result: Slice)
    {
        Slice{start: (self.start + a) as usize, end: (self.start + b) as usize}
    }

    pub exec fn exec_sub(&self, a: usize, b: usize) -> (result: Slice)
    requires self.wf(),
        a <= b <= self.end - self.start
    ensures
        result == self.spec_sub(a, b),
    {
        Slice{start: self.start + a, end: self.start + b}
    }
}

} //verus!
