// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;

verus! {

//////////////////////////////////////////////////////////////////////////////
// Sequence marshalling
//////////////////////////////////////////////////////////////////////////////

pub trait SeqMarshalling<DVElt, Elt: Deepview<DVElt>> {
    spec fn valid(&self) -> bool;

    spec fn lengthable(&self, data: Seq<u8>) -> bool
    recommends
        self.valid()
    ;

    spec fn length(&self, data: Seq<u8>) -> int
    recommends
        self.valid(),
        self.lengthable(data)
    ;

    exec fn try_length(&self, slice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        out is Some <==> self.lengthable(slice.i(data@)),
        out is Some ==> out.unwrap() as int == self.length(slice.i(data@))
    ;

    exec fn exec_lengthable(&self, slice: &Slice, data: &Vec<u8>) -> (l: bool)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        l == self.lengthable(slice.i(data@))
    // TODO dfy has a default impl here based on try_length
    ;

    exec fn exec_length(&self, slice: &Slice, data: &Vec<u8>) -> (len: usize)
    requires
        self.valid(),
        slice.valid(data@),
        self.lengthable(slice.i(data@)),
    ensures
        len == self.length(slice.i(data@))
    // TODO dfy has a default impl here based on try_length
    ;
}

pub trait UniformSizedElementSeqMarshallingObligations<DVElt, Elt: Deepview<DVElt>/*, M: Marshalling<DVElt, Elt>*/> {
    spec fn valid(&self) -> bool;
    
    spec fn uniform_size(&self) -> (sz: usize)
    //requires self.valid(),
    //ensures 0 < sz
    ;

    proof fn uniform_size_ensures(&self)
    requires self.valid(),
    ensures 0 < self.uniform_size()
    ;

    exec fn exec_uniform_size(&self) -> (sz: usize)
    //requires self.valid(),
    ensures sz == self.uniform_size()
    ;
}

spec fn slice_length<DVElt, Elt: Deepview<DVElt>, /*M: Marshalling<DVElt, Elt>, */USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt/*, M*/>>(selff: &USES, slice: Slice) -> int
recommends selff.valid(), slice.wf(),
{
    slice.spec_len() / (selff.uniform_size() as int)
}

#[verifier(nonlinear)]
proof fn div_mul_order(a: int, b: int)
requires 0 < b
ensures (a/b) * b <= a
{
}

#[verifier(nonlinear)]
proof fn mul_le(a: int, b: int)
    requires 0<=a, 1<=b
    ensures a <= a*b
{
}

proof fn length_ensures<DVElt, Elt: Deepview<DVElt>, /*M: Marshalling<DVElt, Elt>, */USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt/*, M*/>>(selff: &USES, data: Seq<u8>)
requires
    selff.valid(),
    data.len() < usize::MAX,
ensures (
    slice_length(selff, Slice::all(data))
    == selff.length(data)
    <= selff.length(data) * (selff.uniform_size() as int)
    <= data.len()
    )
{
    selff.uniform_size_ensures();
    div_mul_order(data.len() as int, selff.uniform_size() as int);
    mul_le(selff.length(data), selff.uniform_size() as int);
}

// I can't say anything about USES<M> because I haven't told you about M?
impl<DVElt, Elt: Deepview<DVElt>/*, M: Marshalling<DVElt, Elt>*/, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt/*, M*/>>
    SeqMarshalling<DVElt, Elt>
    for USES
{
    open spec fn valid(&self) -> bool {
        USES::valid(self)
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool {
        true
    }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        (data.len() as int) / (self.uniform_size() as int)
    }

    exec fn try_length(&self, slice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        proof { self.uniform_size_ensures() }
        Some(slice.exec_len() / self.exec_uniform_size())
    }

    exec fn exec_lengthable(&self, slice: &Slice, data: &Vec<u8>) -> (l: bool) { true }

    exec fn exec_length(&self, slice: &Slice, data: &Vec<u8>) -> (len: usize)
    {
        proof { self.uniform_size_ensures() }   // 0 < denom
        slice.exec_len() / self.exec_uniform_size()
    }
}


}
