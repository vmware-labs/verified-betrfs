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

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////
    // TODO(robj): Why do these spec fns take slices?
    // Reply from Rob:
    //
    // I don't think I can give a definitive answer, but I have 3 hypotheses:
    //  1. I recall having to go back and add the Slice stuff once I realized that builtin slicing
    //     didn't work on linear sequences.  So I might have added the Slice parameters in a very
    //     mechanical way without thinking about it too much.  So it could just be an accident.
    // 2. Maybe slicing doesn't work on linear sequences?
    // 3. I have a vague recollection that I had the idea that, by making the Slice parameter its
    //    own thing, it might make some proofs easier when you need to prove that two invocations
    //    of get return the same result.  The easiest way to prove that is to prove the parameters
    //    are equal.  By making the Slice explicit, you don't need to do any sequence axiom stuff
    //    in the proof.
    //
    // jonh: somehow get needs a slice but get_elt doesn't? Seems just broken tbh
    //
    // NOPE! The correct answer is: get wants to take a slice argument because it returns
    // an eslice *relative to the original data*. If get only took data, so you had
    // to call get(outerslice.i(data)), then its result would need to be composed with
    // (taken as a subslice of) outerslice to be meaningful. That's a lot of shuffling that
    // we don't do in the exec code. Doing it in spec makes the proofs confusing at best.
    // This is something like Rob's (3) above.
    spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid()
    ;

    spec fn get(&self, dslice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    recommends
        self.valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx)
    ;

    proof fn get_ensures(&self, dslice: Slice, data: Seq<u8>, idx: int)
    requires
        self.valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx),
    ensures
        self.get(dslice, data, idx).valid(data)
    ;

    spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.valid(),
        self.gettable(data, idx)
    // TODO dfy has a default impl here
    ;
//     {
//         self.get(&Slice::all(data), data, idx).i(data)
//     }
    
    spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid(),
        self.gettable(data, idx)
    // TODO dfy has a default impl here
    ;

//     {
//         self.spec_elt_marshalling().parsable(self.get_data(data, idx))
//     }

    spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    recommends
        self.valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
    // TODO dfy has a default impl here
    ;
//     {
//         self.spec_elt_marshalling().parse(self.get_data(data, idx))
//     }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    requires
        self.valid(),
        dslice.valid(data@),
    ensures
        oeslice is Some <==> self.gettable(dslice.i(data@), idx as int),
        oeslice is Some ==> oeslice.unwrap() == self.get(*dslice, data@, idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn exec_gettable(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    requires self.valid(),
        slice.valid(data@),
    ensures g == self.gettable(slice.i(data@), idx as int)
    // TODO dfy has a default impl here
    ;
    
    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    requires
        self.valid(),
        dslice.valid(data@),
        self.gettable(dslice.i(data@), idx as int),
    ensures
        eslice.wf(),
        eslice == self.get(*dslice, data@, idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn try_get_elt(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        oelt is Some <==> {
                &&& self.gettable(slice.i(data@), idx as int)
                &&& self.elt_parsable(slice.i(data@), idx as int)
        },
        oelt is Some ==> oelt.unwrap().deepv() == self.get_elt(slice.i(data@), idx as int)
    // TODO dfy has a default impl here
    ;   

    exec fn exec_get_elt(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        elt.deepv() == self.get_elt(slice.i(data@), idx as int)
    // TODO dfy has a default impl here
    ;   
}

pub trait UniformSizedElementSeqMarshallingObligations<DVElt, Elt: Deepview<DVElt>> {
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

    type EltMarshalling : Marshalling<DVElt, Elt>;

    spec fn spec_elt_marshalling(&self) -> Self::EltMarshalling
        ;

    // PLEASE PLEASE CAN I HAVE SPEC ENSURES
    proof fn spec_elt_marshalling_ensures(&self)
    requires self.valid()
    ensures self.spec_elt_marshalling().valid()
    ;

    exec fn exec_elt_marshalling(&self) -> (eltm: &Self::EltMarshalling)
    requires self.valid()
    ensures eltm.valid(),
        eltm == self.spec_elt_marshalling()
        ;
}

spec fn slice_length<DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>(selff: &USES, slice: Slice) -> int
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

proof fn length_ensures
    <DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>
    (selff: &USES, data: Seq<u8>)
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

proof fn index_bounds_facts
    <DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>
    (selff: &USES, slice: Slice, idx: int)
requires selff.valid(), slice.wf(), idx < slice.spec_len() / (selff.uniform_size() as int)
ensures
    0
        <= idx * (selff.uniform_size() as int)
        < idx * (selff.uniform_size() as int) + (selff.uniform_size() as int)
        == (idx+1) * (selff.uniform_size() as int)
        <= slice.spec_len()
{
}

// I can't say anything about USES<M> because I haven't told you about M?
impl<DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>
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

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        idx < self.length(data)
    }

    open spec fn get(&self, dslice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    {
        dslice.spec_sub(
            ((idx as usize) * self.uniform_size()) as usize,
            ((idx as usize) * self.uniform_size() + self.uniform_size()) as usize
        )
    }

    proof fn get_ensures(&self, dslice: Slice, data: Seq<u8>, idx: int)
    {
    }

    open spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    // TODO factor out this common impl
    {
        self.get(Slice::all(data), data, idx).i(data)
    }
    
    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    // TODO factor out this common impl
    {
        self.spec_elt_marshalling().parsable(self.get_data(data, idx))
    }

    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    // TODO factor out this common impl
    {
        self.spec_elt_marshalling().parse(self.get_data(data, idx))
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let len = self.exec_length(dslice, data);
        if idx < len {
            Some( dslice.exec_sub(
                    (idx as usize) * self.exec_uniform_size(),
                    (idx as usize) * self.exec_uniform_size() + self.exec_uniform_size()) )
        } else {
            None
        }
    }
    
    exec fn exec_gettable(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    {
        let len = self.exec_length(slice, data);
        idx < len
    }

    exec fn exec_get(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    {
        slice.exec_sub(
            (idx as usize) * self.exec_uniform_size(),
            (idx as usize) * self.exec_uniform_size() + self.exec_uniform_size())
    }

    exec fn try_get_elt(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    // TODO factor out this common impl
    {
        proof { self.spec_elt_marshalling_ensures() };  // :v(

        let oeslice = self.try_get(slice, data, idx);
        match oeslice {
            None => None,
            Some(eslice) => {
                proof {
                    self.get_ensures(*slice, data@, idx as int);   // And another 20 minutes wasted
                    index_bounds_facts(self, *slice, idx as int);
                    let edslice = self.get(Slice::all(slice.i(data@)), slice.i(data@), idx as int);
                    assert( edslice.i(slice.i(data@)) == eslice.i(data@));   // trigger
                }
                let oelt = self.exec_elt_marshalling().try_parse(&eslice, data);
                oelt
            }
        }
    }

    exec fn exec_get_elt(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    // TODO factor out this common impl
    {
        let eslice = self.exec_get(slice, data, idx);
        self.exec_elt_marshalling().exec_parse(&eslice, data)
    }
}


}
