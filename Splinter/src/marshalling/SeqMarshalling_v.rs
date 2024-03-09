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
//////////////////////////////////////////////////////////////////////////////

pub trait SeqMarshalling<DVElt, Elt: Deepview<DVElt>> {
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
        dslice.valid(data@),
    ensures
        out is Some <==> self.lengthable(dslice.i(data@)),
        out is Some ==> out.unwrap() as int == self.length(dslice.i(data@))
    ;

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool)
    requires
        self.seq_valid(),
        dslice.valid(data@),
    ensures
        l == self.lengthable(dslice.i(data@))
    // TODO dfy has a default impl here based on try_length
    ;

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    requires
        self.seq_valid(),
        dslice.valid(data@),
        self.lengthable(dslice.i(data@)),
    ensures
        len == self.length(dslice.i(data@))
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
        self.seq_valid()
    ;

    spec fn get(&self, dslice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    recommends
        self.seq_valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx)
    ;

    proof fn get_ensures(&self, dslice: Slice, data: Seq<u8>, idx: int)
    requires
        self.seq_valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx),
    ensures
        self.get(dslice, data, idx).valid(data)
    ;

    spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.seq_valid(),
        self.gettable(data, idx)
    // TODO dfy has a default impl here
    ;
//     {
//         self.get(&Slice::all(data), data, idx).i(data)
//     }

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
        dslice.valid(data@),
    ensures
        oeslice is Some <==> self.gettable(dslice.i(data@), idx as int),
        oeslice is Some ==> oeslice.unwrap() == self.get(*dslice, data@, idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn exec_gettable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    requires self.seq_valid(),
        dslice.valid(data@),
    ensures g == self.gettable(dslice.i(data@), idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    requires
        self.seq_valid(),
        dslice.valid(data@),
        self.gettable(dslice.i(data@), idx as int),
    ensures
        eslice.wf(),
        eslice == self.get(*dslice, data@, idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    requires
        self.seq_valid(),
        dslice.valid(data@),
    ensures
        oelt is Some <==> {
                &&& self.gettable(dslice.i(data@), idx as int)
                &&& self.elt_parsable(dslice.i(data@), idx as int)
        },
        oelt is Some ==> oelt.unwrap().deepv() == self.get_elt(dslice.i(data@), idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    requires
        self.seq_valid(),
        self.gettable(dslice.i(data@), idx as int),
        self.elt_parsable(dslice.i(data@), idx as int),
        dslice.valid(data@),
    ensures
        elt.deepv() == self.get_elt(dslice.i(data@), idx as int)
    // TODO dfy has a default impl here
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

    spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    recommends
        self.seq_valid()
    // TODO dfy has a default impl here
    ;

    // proof fn preserves_entry_transitive

    spec fn sets(&self, data: Seq<u8>, idx: int, value: DVElt, new_data: Seq<u8>) -> bool
    recommends
        self.seq_valid(),
        self.elt_marshallable(value),
        self.settable(data, idx, value)
    // TODO dfy has a default impl here
    ;

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &Elt) -> (s: bool)
    requires
        self.seq_valid(),
        dslice.valid(data@),
        self.elt_marshallable(value.deepv()),
    ensures
        s == self.settable(dslice.i(data@), idx as int, value.deepv())
    ;

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    requires
        self.seq_valid(),
        dslice.valid(old(data)@),
        self.elt_marshallable(value.deepv()),
        self.settable(dslice.i(old(data)@), idx as int, value.deepv()),
    ensures
        dslice.agree_beyond_slice(old(data)@, data@),
        self.sets(dslice.i(old(data)@), idx as int, value.deepv(), dslice.i(data@))
    ;


    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool
        recommends self.seq_valid()
        ;

    spec fn resizes(&self, data: Seq<u8>, newlen: int, newdata: Seq<u8>) -> bool
        recommends self.seq_valid(), self.resizable(data, newlen)
    // TODO dfy has a default impl here
        ;

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool)
        requires self.seq_valid()
        ensures r == self.resizable(dslice.i(data@), newlen as int)
        ;

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize)
        requires self.seq_valid(), dslice.valid(old(data)@), self.resizable(dslice.i(old(data)@), newlen as int)
        ensures data@.len() == old(data)@.len(),
            forall |i| 0 <= i < dslice.start ==> data[i] == old(data)@[i],
            forall |i| dslice.end <= i < data.len() ==> data[i] == old(data)@[i],
            self.resizes(dslice.i(old(data)@), newlen as int, dslice.i(data@)),
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
    ensures
            w == self.well_formed(dslice.i(data@))
        ;

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: Elt) -> (r: bool)
    requires
        self.seq_valid(),
        dslice.valid(data@),
        self.well_formed(data@),
        self.elt_marshallable(value.deepv()),
    ensures
        r == self.appendable(data@, value.deepv())
    ;

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: Elt)
    requires
        self.seq_valid(),
        dslice.valid(old(data)@),
        self.well_formed(old(data)@),
        self.elt_marshallable(value.deepv()),
        self.appendable(old(data)@, value.deepv()),
    ensures
        data@.len() == old(data)@.len(),
        forall |i: int| 0 <= i < dslice.start as int ==> data@[i] == old(data)@[i],
        forall |i: int| dslice.end as int <= i < data.len() ==> data@[i] == old(data)@[i],
        self.appends(old(data)@, value.deepv(), data@)
    ;

    /////////////////////////////////////////////////////////////////////////
    // parse (entire sequence)
    /////////////////////////////////////////////////////////////////////////
    open spec fn gettable_to_len(&self, data: Seq<u8>, len: int) -> bool
    recommends self.seq_valid()
    {
        forall |i: int| 0<=i<len ==> self.gettable(data, i)
    }

    open spec fn elt_parsable_to_len(&self, data: Seq<u8>, len: int) -> bool
    recommends self.seq_valid(), self.gettable_to_len(data, len)
    {
        forall |i: int| 0<=i<len ==> self.elt_parsable(data, i)
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


    /////////////////////////////////////////////////////////////////////////
    // marshall (entire sequence)
    /////////////////////////////////////////////////////////////////////////
    // This isn't very satisfyingly organized; I duplicate these placeholders
    // from Marshalling so we can `impl Marshalling for SeqMarshalling`
    // without them defined yet. Probably need to break Marsalling into
    // pieces and + them together?

    // No, these don't make sense as obligations; in the dfy code they're
    // part of the implementation inheritance impl of Marshalling.
//     spec fn marshallable(&self, value: Seq<DVElt>) -> bool
//         ;
// 
//     spec fn spec_size(&self, value: Seq<DVElt>) -> usize
//     recommends
//         self.seq_valid(),
//         self.marshallable(value)
//     ;
// 
//     exec fn exec_size(&self, value: &Vec<Elt>) -> (sz: usize)
//     requires
//         self.seq_valid(),
//         self.marshallable(value.deepv()),
//     ensures
//         sz == self.spec_size(value.deepv())
//     ;
// 
//     // Defining these default methods so we can define exec_marshall. Bleeghh.
//     spec fn seq_parsable(&self, data: Seq<u8>) -> bool
//     {
//         &&& self.seq_valid()
//         &&& self.lengthable(data)
//         &&& self.length(data) <= usize::MAX
//         &&& self.parsable_to_len(data, self.length(data) as usize)
//     }
// 
//     spec fn seq_parse(&self, data: Seq<u8>) -> Seq<DVElt>
//     {
//         self.parse_to_len(data, self.length(data) as usize)
//     }
// 
// //     exec fn seq_exec_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (value: Vec<Elt>)
// //     requires
// //         self.seq_valid(),
// //         dslice.valid(data@),
// //         self.seq_parsable(dslice.i(data@)),
// //     ensures
// //         value.deepv() == self.seq_parse(dslice.i(data@)),
// //     ;
// 
//     exec fn exec_marshall(&self, value: &Vec<Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     requires
//         self.seq_valid(),
//         self.marshallable(value.deepv()),
//         start as int + self.spec_size(value.deepv()) as int <= old(data).len(),
//     ensures
//         end == start + self.spec_size(value.deepv()),
//         data.len() == old(data).len(),
//         forall |i| 0 <= i < start ==> data[i] == old(data)[i],
//         forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
//         self.seq_parsable(data@.subrange(start as int, end as int)),
//         self.seq_parse(data@.subrange(start as int, end as int)) == value.deepv()
//     ;
}


}
