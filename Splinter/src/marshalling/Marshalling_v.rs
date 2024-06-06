// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
//use vstd::bytes::*;
//use vstd::slice::*;
use crate::marshalling::Slice_v::*;

verus! {

pub trait Deepview<DV> {
    //type DV = DV;

    spec fn deepv(&self) -> DV;
}

// VSE == ViewSeqElt
// If you have an Elt type that implements Deepview<DVE>,
// you may have a Vec<Elt> that implements Deepview<Seq<DVE>>.
impl<DVE, Elt: Deepview<DVE>> Deepview<Seq<DVE>> for Vec<Elt> {
    //type DV = Seq<<T as Deepview>::DV>;

    open spec fn deepv(&self) -> Seq<DVE> {
        Seq::new(self.len() as nat, |i: int| self[i].deepv())
    }
}

// Only want this to apply to types that are not already DeepView. :v/
// impl<T: View> Deepview for T {
//     type DV = <T as View>::V;
// 
//     fn deepv(&self) -> Self::DV;
// }

// Marshal is the most basic behavior: A format that implements Marshal
// knows how to parse and marshall the type all at once.
pub trait Marshal {
    type DV;                // The view (spec) type
    type U: Deepview<Self::DV>;    // The runtime type

    spec fn valid(&self) -> bool;

    spec fn parsable(&self, data: Seq<u8>) -> bool
    recommends self.valid()
    ;

    exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    requires
        self.valid(),
        slice@.valid(data@),
    ensures
        p == self.parsable(slice@.i(data@))
    ;

    spec fn marshallable(&self, value: Self::DV) -> bool
    ;

    spec fn spec_size(&self, value: Self::DV) -> usize
    recommends 
        self.valid(),
        self.marshallable(value)
    ;

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    requires 
        self.valid(),
        self.marshallable(value.deepv()),
    ensures
        sz == self.spec_size(value.deepv())
    ;

    spec fn parse(&self, data: Seq<u8>) -> Self::DV
    recommends 
        self.valid(),
        self.parsable(data)
    ;

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    requires
        self.valid(),
        slice@.valid(data@),
    ensures
        self.parsable(slice@.i(data@)) <==> ov is Some,
        self.parsable(slice@.i(data@)) ==> ov.unwrap().deepv() == self.parse(slice@.i(data@))
    ;

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: Self::U)
    requires
        self.valid(),
        slice@.valid(data@),
        self.parsable(slice@.i(data@)),
    ensures
        value.deepv() == self.parse(slice@.i(data@)),
    {
        self.try_parse(slice, data).unwrap()
    }

    // jonh skipping translation of Parse -- does it ever save more than
    // a cheap if condition?

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    requires 
        self.valid(),
        self.marshallable(value.deepv()),
        start as int + self.spec_size(value.deepv()) as int <= old(data).len(),
    ensures
        end == start + self.spec_size(value.deepv()),
        data.len() == old(data).len(),
        forall |i| 0 <= i < start ==> data[i] == old(data)[i],
        forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        self.parsable(data@.subrange(start as int, end as int)),
        self.parse(data@.subrange(start as int, end as int)) == value.deepv()
    ;
}

} // verus!
