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

pub trait ResizableUniformSizedElementSeqMarshallingConfig {
    // Need enough constraints that IntegerMarshalling impl can provide Marshalling on the next line.
    type LengthInt : Deepview<int> + builtin::Integer + Copy;

    // Note we require an IntObligations implementation of Marshalling, so we can get at the o_
    // static methods. Is that poor organization? Hmm, we also added some helper methods just
    // to make SeqMarshalling's length work easier, sooooo...
    type LengthMarshalling : IntObligations<Self::LengthInt>;
    //type LengthMarshalling : Marshalling<int, Self::LengthInt>;

    type EltDV;
    type Elt : Deepview<Self::EltDV>;
    type EltMarshalling : Marshalling<Self::EltDV, Self::Elt>;

    // A 3-line function method signature becomes a 7-line 3-signature monstrosity.
    // Missing spec ensures is responsible for 3 of them.
    // Maybe we want some spec/exec (function method) affordance. Not the common case
    // (Dafny goes too far), but we should discuss.
    spec fn spec_uniform_size(&self) -> usize
    ;

    proof fn spec_uniform_size_ensures(&self)
    ensures
        0 < self.spec_uniform_size()
    ;

    exec fn exec_uniform_size(&self) -> (sz: usize)
    ensures
        sz == self.spec_uniform_size()
    ;
}

pub struct ResizableUniformSizedElementSeqMarshalling<C: ResizableUniformSizedElementSeqMarshallingConfig> {
    pub total_size: usize,  // capacity in bytes
    pub length_marshalling: C::LengthMarshalling,
    pub elt_marshalling: C::EltMarshalling,
    pub config: C,
}


// For now, skip the SeqObligations generalization and implement ResizableUniformSizedElementSeqMarshalling
// as if it's all that exists

// impl<C: ResizableUniformSizedElementSeqMarshallingConfig>
//     SeqObligations<C::EltDV, C::Elt>
//     for ResizableUniformSizedElementSeqMarshalling<C>
// {
// }
// 
// impl <EltDV, Elt: Deepview<EltDV>, O: SeqObligations<EltDV, Elt>>
//     Marshalling<Seq<EltDV>, Vec<Elt>>
//     for O

impl<C: ResizableUniformSizedElementSeqMarshallingConfig> ResizableUniformSizedElementSeqMarshalling<C>
{
    pub open spec fn spec_size_of_length_field() -> usize
    {
        C::LengthMarshalling::o_spec_size()
    }

    pub open spec fn lengthable(&self, data: Seq<u8>) -> bool
    {
        &&& self.total_size as int <= data.len()
        &&& self.length_marshalling.parsable(data.subrange(0, Self::spec_size_of_length_field() as int))
        &&& C::LengthMarshalling::spec_this_fits_in_usize(
            self.length_marshalling.parse(data.subrange(0, Self::spec_size_of_length_field() as int)))
    }

    pub open spec fn length(&self, data: Seq<u8>) -> int
    {
        self.length_marshalling.parse(data.subrange(0, Self::spec_size_of_length_field() as int))
    }

    exec fn try_length(&self, slice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        out is Some <==> self.lengthable(slice.i(data@)),
        out is Some ==> out.unwrap() as int == self.length(slice.i(data@))
    {
        proof { C::LengthMarshalling::as_int_ensures(); }

        if slice.exec_len() < self.total_size {
            None
        } else {
            // TODO(jonh): here's a place where we know it's parsable,
            // but we're calling a try_parse method and wasting a conditional.
            let len_slice = slice.exec_sub(0, C::LengthMarshalling::o_exec_size());
            let o_parsed_len = self.length_marshalling.try_parse(&len_slice, data);
            if o_parsed_len.is_none() {
                None
            } else {
                let parsed_len: C::LengthInt = o_parsed_len.unwrap();
                // subrange trigger
                assert( len_slice.i(data@) == slice.i(data@).subrange(0, Self::spec_size_of_length_field() as int) );
                if !C::LengthMarshalling::exec_this_fits_in_usize(parsed_len) {
                    None
                } else {
                    Some(C::LengthMarshalling::to_usize(parsed_len))
                }
            }
        }
    }

    pub open spec fn spec_max_length(self) -> usize
    {
        ((self.total_size - Self::spec_size_of_length_field()) / (self.config.spec_uniform_size() as int)) as usize
    }

    pub open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        &&& self.lengthable(data)
        &&& idx < self.spec_max_length()
    }

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
    pub open spec fn get(&self, slice: &Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    recommends
        self.valid(),
        slice.valid(data),
        self.gettable(slice.i(data), idx)
    {
        slice.spec_sub(
            (Self::spec_size_of_length_field() + idx * self.config.spec_uniform_size()) as usize,
            (Self::spec_size_of_length_field() + idx * self.config.spec_uniform_size() + self.config.spec_uniform_size()) as usize)
    }

    pub open spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.valid(),
        self.gettable(data, idx)
    {
        self.get(&Slice::all(data), data, idx).i(data)
    }

    pub open spec fn gettable_to_len(&self, data: Seq<u8>, len: int) -> bool {
        forall |i: int| 0 <= i < len ==> self.gettable(data, i)
    }

    pub open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid(),
        self.gettable(data, idx)
    {
        self.elt_marshalling.parsable(self.get_data(data, idx))
    }

    pub open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: C::EltDV)
    recommends
        self.valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
    {
        self.elt_marshalling.parse(self.get_data(data, idx))
    }

    // jonh skipped over the `exec fn get` that requires gettable, perhaps a useful optimization
    // for some other day..

    exec fn try_get(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let olen = self.try_length(slice, data);
        if olen.is_none() { return None; }
        let mlen = self.exec_max_length();
        if idx < mlen {
            let ls = C::LengthMarshalling::o_exec_size();
            let us = self.config.exec_uniform_size();
            Some(
                slice.exec_sub(ls + idx * us, ls + idx * us + us))
        } else {
            None
        }
    }

    exec fn try_get_elt(&self, slice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<C::Elt>)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        oelt is Some <==> {
                &&& self.gettable(slice.i(data@), idx as int)
                &&& self.elt_parsable(data@, idx as int)
        },
        oelt is Some ==> oelt.unwrap().deepv() == self.get_elt(slice.i(data@), idx as int),
    {
        assume( false );
        assert( slice.valid(data@) );
//         proof { self.spec_elt_marshalling(); }
        assert( slice.valid(data@) );
        let oelt = 
            match self.try_get(slice, data, idx) {
                None => None,
                Some(slice) => {
                    //assert( slice == old(slice) );
                    //assert( data@ == old(data)@ );
                    assert( slice.valid(data@) );   // Whoah, neither slice nor data is mutable. How could this fail?
                    assert( self.gettable(slice.i(data@), idx as int) );
                    self.elt_marshalling.try_parse(&slice, data)
                }
            };
        assert( oelt is Some <==> {
             &&& self.gettable(slice.i(data@), idx as int)
             &&& self.elt_parsable(data@, idx as int)
        } );
        assert( oelt is Some ==> oelt.unwrap().deepv()== self.get_elt(slice.i(data@), idx as int) );
        oelt
    }

    pub open spec fn elt_parsable_to_len(&self, data: Seq<u8>, len: int) -> bool {
        forall |i: int| 0 <= i < len ==> self.elt_parsable(data, i)
    }

    pub open spec fn parsable_to_len(&self, data: Seq<u8>, len: int) -> bool {
        &&& Self::gettable_to_len(self, data, len as int)
        &&& Self::elt_parsable_to_len(self, data, len as int)
    }

    pub open spec fn parse_to_len(&self, data: Seq<u8>, len: int) -> Seq<C::EltDV>
    {
        Seq::new(len as nat, |i| self.get_elt(data, i))
    }
    
    exec fn exec_max_length(&self) -> usize
    requires
        self.valid(),
    {
        proof { self.config.spec_uniform_size_ensures() };
        (self.total_size - C::LengthMarshalling::o_exec_size()) / self.config.exec_uniform_size()
    }

    pub open spec fn settable(&self, data: Seq<u8>, idx: int, value: C::EltDV) -> bool
    {
        &&& self.lengthable(data)
        &&& idx < self.spec_max_length() as int
        &&& self.elt_marshalling.spec_size(value) == self.config.spec_uniform_size()
    }

    exec fn exec_set(&self, slice: &Slice, data: &mut Vec<u8>, idx: usize, value: &C::Elt)
    {
    }
}

impl<C: ResizableUniformSizedElementSeqMarshallingConfig>
    Marshalling<Seq<C::EltDV>, Vec<C::Elt>>
    for ResizableUniformSizedElementSeqMarshalling<C>
{
    open spec fn valid(&self) -> bool {
        &&& Self::spec_size_of_length_field() <= self.total_size
        &&& self.length_marshalling.valid()
        &&& self.elt_marshalling.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        &&& self.lengthable(data)
        &&& self.length(data) <= usize::MAX as int
        &&& Self::parsable_to_len(self, data, self.length(data))
    }

    exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        assert( self.valid() );
        assert( slice.valid(data@) );

        let olen = self.try_length(slice, data);
        if olen.is_some() {
            if olen.unwrap() <= self.exec_max_length() {
                proof {
                    let datai = slice.i(data@);
                    assert( self.length(datai) <= usize::MAX as int );
                    let len = self.length(datai);
                    assert( forall |i: int| 0 <= i < len ==> self.gettable(datai, i) );
                    assert( Self::gettable_to_len(self, datai, len as int) );
                    assert( Self::elt_parsable_to_len(self, datai, len as int) );
                    assert( Self::parsable_to_len(self, datai, self.length(datai)) );
                }
                assert( self.parsable(slice.i(data@)) );
                true
            } else {
                assert( !self.parsable(slice.i(data@)) );
                false
            }
        } else {
            assert( !self.parsable(slice.i(data@)) );
            false
        }
//         return olen.is_some() && olen.unwrap() <= self.exec_max_length()
    }

    open spec fn marshallable(&self, value: Seq<C::EltDV>) -> bool
    {
        &&& forall |i| #![auto] 0 <= i < value.len() ==> self.elt_marshalling.marshallable(value[i])
        &&& forall |i| #![auto] 0 <= i < value.len() ==> self.elt_marshalling.spec_size(value[i]) == self.config.spec_uniform_size()
        &&& C::LengthMarshalling::spec_this_fits_in_usize(value.len() as int)
        &&& Self::spec_size_of_length_field() as int + value.len() * self.config.spec_uniform_size() as int <= self.total_size
    }

    open spec fn spec_size(&self, value: Seq<C::EltDV>) -> usize
    {
        self.total_size
    }

    exec fn exec_size(&self, value: &Vec<C::Elt>) -> (sz: usize)
    {
        self.total_size
    }

    open spec fn parse(&self, data: Seq<u8>) -> Seq<C::EltDV>
    {
        self.parse_to_len(data, self.length(data))
    }

    // TODO this is common to all implementations of SeqMarshalling; refactor out?
    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Vec<C::Elt>>)
    {
        let olen = self.try_length(slice, data);
        let olen:Option<usize> = None;

        if olen.is_none() {
            assert( !self.parsable(slice.i(data@)) );
            return None;
        }
        let len = olen.unwrap() as usize;

        let mut vec = Vec::with_capacity(len as usize);
        let mut idx: usize = 0;
        while idx < len
        invariant
                0 <= idx <= len,
                forall |j| 0 <= j < idx ==> self.gettable(data@, j),
                forall |j| 0 <= j < idx ==> self.elt_parsable(data@, j),
                forall |j| #![auto] 0 <= j < idx ==> vec.deepv()[j] == self.get_elt(data@, j),
        {
            let oelt = self.try_get_elt(slice, data, idx as usize);
            let oelt:Option<C::Elt> = None;

            if oelt.is_none() {
                assert( !self.parsable(slice.i(data@)) );
                return None;
            }
            // TODO(verus): I wanted to write: vec[idx] = x;
            vec.set(idx, oelt.unwrap());
            idx += 1;
        }
        assert( vec.deepv() == self.parse(slice.i(data@)) );
        Some(vec)
    }

    // TODO this is common to all implementations of SeqMarshalling; refactor out?
    exec fn marshall(&self, value: &Vec<C::Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     requires 
//         self.valid(),
//         self.marshallable(value.deepv()),
//         start as int + self.spec_size(value.deepv()) as int <= old(data).len(),
//     ensures
//         end == start + self.spec_size(value.deepv()),
//         data.len() == old(data).len(),
//         forall |i| 0 <= i < start ==> data[i] == old(data)[i],
//         forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
//         self.parsable(data@.subrange(start as int, end as int)),
//         self.parse(data@.subrange(start as int, end as int)) == value.deepv()
    {
        let len = value.len();
        let end = start + self.total_size;
        let slice = Slice{start, end};

        let mut i: usize = 0;
        while i < len
        invariant
            0 <= i <= value.len(),
            //value.deepv().len() == old(value).deepv().len(),
            //forall |j| 0 <= j < start ==> data@[j] == old(data@)[j],
            //forall |j| end <= j < old(data@).len() ==> data@[j] == old(data@)[j],
            self.lengthable(data@.subrange(start as int, end as int)),
            self.length(data@.subrange(start as int, end as int)) == value.deepv().len(),
            forall |j| start <= j < i ==> self.gettable(data@.subrange(start as int, end as int), j),
            forall |j| start <= j < i ==> self.elt_parsable(data@.subrange(start as int, end as int), j),
            forall |j| #![auto] start <= j < i ==> self.get_elt(data@.subrange(start as int, end as int), j) == value[j].deepv(),
            forall |j| #![auto] start <= j < value.len() ==> self.settable(data@.subrange(start as int, end as int), j, value[j].deepv()),
        {
            self.exec_set(&slice, data, i, &value[i]);
            i += 1;
        }
        end
    }
}


}
