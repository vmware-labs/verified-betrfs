// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

verus!{

// Boy, building these two parallel things is inconvenient. I wonder if there's a better way.
pub struct SpecSlice {
    pub start: int,
    pub end: int,
}

impl SpecSlice {
    pub open spec fn wf(&self) -> bool
    {
        self.start <= self.end
    }

    // Translates WF'
    pub open spec fn valid<T>(&self, data: Seq<T>) -> bool
    {
        0 <= self.start <= self.end <= data.len()
    }

    pub open spec fn i<T>(&self, data: Seq<T>) -> Seq<T>
    recommends
        self.valid(data),
    {
        data.subrange(self.start, self.end)
    }
    
    pub open spec fn len(&self) -> int
    {
        self.end - self.start
    }

    pub open spec fn all<T>(data: Seq<T>) -> SpecSlice
    {
        SpecSlice{start: 0, end: data.len() as int}
    }

    pub proof fn all_ensures<T>()
        ensures forall |data: Seq<T>| (#[trigger] Self::all(data)).i(data) =~= data
    {
    }

    pub open spec fn agree_beyond_slice<T>(&self, data: Seq<T>, new_data: Seq<T>) -> bool
    {
        &&& data.len() == new_data.len()
        &&& forall |i| 0<=i<self.start ==> data[i] == new_data[i]
        &&& forall |i| self.end<=i<data.len() ==> data[i] == new_data[i]
    }

    pub open spec fn is_subslice(&self, big_slice: SpecSlice) -> bool
    {
        &&& big_slice.start <= self.start
        &&& self.end <= big_slice.end
    }

    pub open spec fn subslice(&self, a: int, b: int) -> (result: SpecSlice)
    {
        SpecSlice{start: self.start + a, end: self.start + b}
    }

    pub open spec fn drop(&self, count: int) -> (result: SpecSlice)
    {
        SpecSlice{start: self.start + count, end: self.end}
    }
}

pub struct Slice {
    pub start: usize,
    pub end: usize,
}

impl Slice {
    pub exec fn len(&self) -> (out: usize)
    requires self@.wf()
    ensures out == self@.len()
    {
        self.end - self.start
    }

    pub exec fn all<T>(data: &Vec<T>) -> (out: Slice)
    ensures out@ == SpecSlice::all(data@)
    {
        Slice{start: 0, end: data.len()}
    }

    // TODO(verus): Another nice place for a function-method-like affordance
    pub exec fn subslice(&self, a: usize, b: usize) -> (out: Slice)
    requires a <= b <= self@.len()
    ensures out@ == self@.subslice(a as int, b as int)
    {
        Slice{start: self.start + a, end: self.start + b}
    }

    pub exec fn drop(&self, count: usize) -> (result: Slice)
    requires
        self.start + count <= usize::MAX,
    {
        Slice{start: self.start + count, end: self.end}
    }
}

impl View for Slice {
    type V = SpecSlice;
    open spec fn view(self: &Slice) -> SpecSlice {
        SpecSlice{ start: self.start as int, end: self.end as int }
    }
}

} //verus!
