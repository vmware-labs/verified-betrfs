// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;

verus! {

//////////////////////////////////////////////////////////////////////////////
// Sequence marshalling
//
// A format that implements SeqMarshal knows how to parse and marshall
// a sequence-like type one element at a time: set and get at an index, or
// append to the end of the sequence.
//////////////////////////////////////////////////////////////////////////////

pub trait SeqMarshal<DVElt, Elt: Deepview<DVElt>> {
    spec fn seq_valid(&self) -> bool;

    spec fn lengthable(&self, data: Seq<u8>) -> bool
    recommends
        self.seq_valid()
    ;

    spec fn length(&self, data: Seq<u8>) -> int
    recommends
        self.seq_valid(),
        self.lengthable(data)
    ;

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
    ensures
        out is Some <==> self.lengthable(dslice@.i(data@)),
        out is Some ==> out.unwrap() as int == self.length(dslice@.i(data@))
    ;

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
    ensures
        l == self.lengthable(dslice@.i(data@))
    {
        self.try_length(dslice, data).is_some()
    }

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.lengthable(dslice@.i(data@)),
    ensures
        len == self.length(dslice@.i(data@))
    {
        self.try_length(dslice, data).unwrap()
    }

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
    // to call get(outerslice@.i(data)), then its result would need to be composed with
    // (taken as a subslice of) outerslice to be meaningful. That's a lot of shuffling that
    // we don't do in the exec code. Doing it in spec makes the proofs confusing at best.
    // This is something like Rob's (3) above.
    spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.seq_valid()
    ;

    spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    recommends
        self.seq_valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx)
    ;

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    requires
        self.seq_valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx),
    ensures
        self.get(dslice, data, idx).valid(data)
    ;

    open spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.seq_valid(),
        self.gettable(data, idx)
    {
        self.get(SpecSlice::all(data), data, idx).i(data)
    }

    // I can't make these two implementations (elt_parsable, get_elt) default without having a way
    // to "dispatch" to the element marshaller, which would require knowing the element marshaller
    // type here in this trait. That's more than I want to encode, so I'll settle for a little
    // duplication in the implementations for now.
    spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.seq_valid(),
        self.gettable(data, idx)
    // TODO dfy has a default impl here
    ;
//     {
//         self.spec_elt_marshalling().parsable(self.get_data(data, idx))
//     }

    spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    recommends
        self.seq_valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
    // TODO dfy has a default impl here
    ;
//     {
//         self.spec_elt_marshalling().parse(self.get_data(data, idx))
//     }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
    ensures
        oeslice is Some <==> self.gettable(dslice@.i(data@), idx as int),
        oeslice is Some ==> oeslice.unwrap()@ == self.get(dslice@, data@, idx as int)
    ;

    exec fn exec_gettable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    requires self.seq_valid(),
        dslice@.valid(data@),
    ensures g == self.gettable(dslice@.i(data@), idx as int)
    {
        // NB this default impl isn't used until VariableSizedElementSeqMarshalling
        self.try_get(dslice, data, idx).is_some()
    }

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.gettable(dslice@.i(data@), idx as int),
    ensures
        eslice@.wf(),
        eslice@ == self.get(dslice@, data@, idx as int)
    // TODO dfy has a default impl here, but none of the three seq marshalling classes use it;
    // they all specialize for performance. So we'll omit the default here.
    ;

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
    ensures
        oelt is Some <==> {
                &&& self.gettable(dslice@.i(data@), idx as int)
                &&& self.elt_parsable(dslice@.i(data@), idx as int)
        },
        oelt is Some ==> oelt.unwrap().deepv() == self.get_elt(dslice@.i(data@), idx as int)
    // TODO the implementations of this method could be factored out into a default method here
    // if we had a way of talking about eltm and its type in this trait.
    ;

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    requires
        self.seq_valid(),
        self.gettable(dslice@.i(data@), idx as int),
        self.elt_parsable(dslice@.i(data@), idx as int),
        dslice@.valid(data@),
    ensures
        elt.deepv() == self.get_elt(dslice@.i(data@), idx as int)
    // TODO the implementations of this method could be factored out into a default method here
    // if we had a way of talking about eltm and its type in this trait.
    ;

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////
    spec fn elt_marshallable(&self, elt: DVElt) -> bool
        ;

    spec fn settable(&self, data: Seq<u8>, idx: int, value: DVElt) -> bool
    recommends
        self.seq_valid(),
        self.elt_marshallable(value)
    ;

    open spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    recommends
        self.seq_valid()
    {
        &&& (self.gettable(data, idx) ==> self.gettable(new_data, idx))
        &&& (self.gettable(data, idx) && self.elt_parsable(data, idx)) ==> {
            &&& self.elt_parsable(new_data, idx)
            &&& self.get_elt(new_data, idx) == self.get_elt(data, idx)
            }
    }

    // proof fn preserves_entry_transitive

    open spec fn sets(&self, data: Seq<u8>, idx: int, value: DVElt, new_data: Seq<u8>) -> bool
    recommends
        self.seq_valid(),
        self.elt_marshallable(value),
        self.settable(data, idx, value)
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(data) ==> {
            &&& self.lengthable(new_data)
            &&& self.length(new_data) == self.length(data)
            }
        &&& forall |i| i!=idx ==> self.preserves_entry(data, i, new_data)
        &&& self.gettable(new_data, idx)
        &&& self.elt_parsable(new_data, idx)
        &&& self.get_elt(new_data, idx) == value
    }

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &Elt) -> (s: bool)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.elt_marshallable(value.deepv()),
    ensures
        s == self.settable(dslice@.i(data@), idx as int, value.deepv())
    ;

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    requires
        self.seq_valid(),
        dslice@.valid(old(data)@),
        self.elt_marshallable(value.deepv()),
        self.settable(dslice@.i(old(data)@), idx as int, value.deepv()),
    ensures
        dslice@.agree_beyond_slice(old(data)@, data@),
        self.sets(dslice@.i(old(data)@), idx as int, value.deepv(), dslice@.i(data@)),
    ;


    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool
        recommends self.seq_valid()
        ;

    open spec fn resizes(&self, data: Seq<u8>, newlen: int, new_data: Seq<u8>) -> bool
        recommends self.seq_valid(), self.resizable(data, newlen)
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(new_data)
        &&& self.length(new_data) == newlen
        &&& forall |i| self.preserves_entry(data, i, new_data)
    }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool)
        requires self.seq_valid(), dslice@.valid(data@),
        ensures r == self.resizable(dslice@.i(data@), newlen as int)
        ;

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize)
        requires self.seq_valid(), dslice@.valid(old(data)@), self.resizable(dslice@.i(old(data)@), newlen as int)
        ensures data@.len() == old(data)@.len(),
            dslice@.agree_beyond_slice(old(data)@, data@),
            self.resizes(dslice@.i(old(data)@), newlen as int, dslice@.i(data@)),
    ;

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////
    spec fn well_formed(&self, data: Seq<u8>) -> bool
        recommends self.seq_valid()
        ;

    proof fn well_formed_ensures(&self, data: Seq<u8>)
        requires self.seq_valid()
        ensures self.well_formed(data) ==> self.lengthable(data)
        ;

    spec fn appendable(&self, data: Seq<u8>, value: DVElt) -> bool
        recommends self.seq_valid(), self.well_formed(data), self.elt_marshallable(value)
        ;

    spec fn appends(&self, data: Seq<u8>, value: DVElt, newdata: Seq<u8>) -> bool
    recommends
        self.seq_valid(),
        self.well_formed(data),
        self.elt_marshallable(value),
        self.appendable(data, value)
    // TODO dfy has a default impl here
        ;


    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
    ensures
            w == self.well_formed(dslice@.i(data@))
        ;

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: &Elt) -> (r: bool)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.well_formed(dslice@.i(data@)),
        self.elt_marshallable(value.deepv()),
    ensures
        r == self.appendable(dslice@.i(data@), value.deepv())
    ;

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: &Elt)
    requires
        self.seq_valid(),
        dslice@.valid(old(data)@),
        self.well_formed(dslice@.i(old(data)@)),
        self.elt_marshallable(value.deepv()),
        self.appendable(dslice@.i(old(data)@), value.deepv()),
    ensures
        data@.len() == old(data)@.len(),
        dslice@.agree_beyond_slice(old(data)@, data@),
        self.appends(dslice@.i(old(data)@), value.deepv(), dslice@.i(data@))
    ;

    /////////////////////////////////////////////////////////////////////////
    // parse (entire sequence)
    /////////////////////////////////////////////////////////////////////////
    open spec fn gettable_to_len(&self, data: Seq<u8>, len: int) -> bool
    recommends self.seq_valid()
    {
        forall |i: int| 0<=i && i<len ==> self.gettable(data, i)
    }

    open spec fn elt_parsable_to_len(&self, data: Seq<u8>, len: int) -> bool
    recommends self.seq_valid(), self.gettable_to_len(data, len)
    {
        forall |i: int| 0<=i && i<len ==> self.elt_parsable(data, i)
    }

    // TODO(robj): why switch to usize in spec land here?
    open spec fn parsable_to_len(&self, data: Seq<u8>, len: usize) -> bool
    recommends self.seq_valid()
    {
        &&& self.gettable_to_len(data, len as int)
        &&& self.elt_parsable_to_len(data, len as int)
    }

    open spec fn parse_to_len(&self, data: Seq<u8>, len: usize) -> Seq<DVElt>
    recommends self.seq_valid(), self.parsable_to_len(data, len)
    {
        Seq::new(len as nat, |i: int| self.get_elt(data, i))
    }

    open spec fn loyalty_test(&self) -> int
    {
        7
    }
}


}
