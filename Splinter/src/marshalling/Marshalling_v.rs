// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
//use vstd::bytes::*;
//use vstd::slice::*;
use crate::marshalling::Slice_v::*;

verus! {

// TODO(jonh): Sizes should be usize, not u64.

pub trait Premarshalling<U> {
    spec fn valid(&self) -> bool;

    spec fn parsable(&self, data: Seq<u8>) -> bool
    recommends self.valid()
    ;

    exec fn exec_parsable(&self, slice: Slice, data: &Vec<u8>) -> (p: bool)
    requires
        self.valid(),
    ensures
        p == self.parsable(slice.i(data@))
    ;

    spec fn marshallable(&self, value: &U) -> bool
    ;

    spec fn spec_size(&self, value: &U) -> u64
    recommends 
        self.valid(),
        self.marshallable(value)
    ;

    exec fn exec_size(&self, value: &U) -> (sz: u64)
    requires 
        self.valid(),
        self.marshallable(value),
    ensures
        sz == self.spec_size(value)
    ;
}

pub trait Marshalling<U> : Premarshalling<U> {
    spec fn parse(&self, data: Seq<u8>) -> U
    recommends 
        self.valid(),
        self.parsable(data)
    ;

    exec fn try_parse(&self, slice: Slice, data: &Vec<u8>) -> (ov: Option<U>)
    requires
        self.valid(),
    ensures
        self.parsable(slice.i(data@)) <==> ov is Some,
        self.parsable(slice.i(data@)) ==> ov.unwrap() == self.parse(slice.i(data@))
    ;

    // jonh skipping translation of Parse -- does it ever save more than
    // a cheap if condition?

    exec fn marshall(&self, value: &U, data: &mut Vec<u8>, start: u64) -> (end: u64)
    requires 
        self.valid(),
        self.marshallable(value),
        start as int + self.spec_size(value) as int <= old(data).len(),
    ensures
        end == start + self.spec_size(value),
        data.len() == old(data).len(),
        forall |i| 0 <= i < start ==> data[i] == old(data)[i],
        forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        self.parsable(data@.subrange(start as int, end as int)),
        self.parse(data@.subrange(start as int, end as int)) == value
    ;
}

} // verus!
