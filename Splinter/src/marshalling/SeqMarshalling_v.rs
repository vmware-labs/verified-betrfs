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

// TODO(andrea): How do we suggest that everyone who implements SeqMarshalling
// shall also implement Marshalling? Adding a subtype ":" is too strong, because
// it forces them to implement it *first*, but their Marshalling implementation
// should exploit this SeqMarshalling stuff.
pub trait SeqMarshalling<DVE, U: Deepview<DVE>, EltMarshalling: Marshalling<DVE, U>>
    : Premarshalling<Seq<DVE>, Vec<U>>
{
    spec fn spec_elt_marshalling(&self) -> EltMarshalling
    ;

    // sure can't stand those spec ensures. Such a hassle!
    proof fn spec_elt_marshalling_ensures(&self)
    requires
        self.valid(),
    ensures
        self.spec_elt_marshalling().valid()
    ;

    exec fn exec_elt_marshalling(&self) -> (elt: EltMarshalling)
    ensures
        elt == self.spec_elt_marshalling(),
    ;

    /////////////////////////////////////////////////////////////////////////
    // observing sequence length (count of elements, not bytes)
    /////////////////////////////////////////////////////////////////////////

    // True if the sequence length (count of elements) in data can be determined from data.
    spec fn lengthable(&self, data: Seq<u8>) -> bool
    recommends
        self.valid()
    ;

    spec fn length(&self, data: Seq<u8>) -> int
    recommends
        self.valid(),
        self.lengthable(data)
    ;

    exec fn try_length(&self, slice: Slice, data: &Vec<u8>) -> (out: Option<usize>)
    requires
        self.valid(),
    ensures
        out is Some <==> self.lengthable(slice.i(data@)),
        out is Some ==> out.unwrap() as int == self.length(slice.i(data@))
    ;

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////
    spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid()
    ;

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
    spec fn get(&self, slice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    recommends
        self.valid(),
        slice.valid(data),
        self.gettable(slice.i(data), idx)
    ;

    proof fn get_ensures(&self, slice: Slice, data: Seq<u8>, idx: int)
    requires
        self.valid(),
        slice.valid(data),
        self.gettable(slice.i(data), idx),
    ensures
        self.get(slice, data, idx).valid(data)
    ;

    spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.valid(),
        self.gettable(data, idx)
    {
//     spec fn valid(&self) -> bool {
//         &&& Self::size_of_length_field() <= Self::cfg().total_size()
//         &&& Self::cfg().length_marshalling.valid()
//         &&& Self::cfg().spec_elt.valid()
//     }
// 
        self.get(Slice::all(data), data, idx).i(data)
    }

    spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid(),
        self.gettable(data, idx)
    {
        self.spec_elt_marshalling().parsable(self.get_data(data, idx))
    }

    spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVE)
    recommends
        self.valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
    {
        self.spec_elt_marshalling().parse(self.get_data(data, idx))
    }

    exec fn try_get(&self, slice: Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        oeslice is Some <==> self.gettable(slice.i(data@), idx as int),
        oeslice is Some ==> oeslice.unwrap() == self.get(slice, data@, idx as int)
    ;

    // jonh skipped over the `exec fn get` that requires gettable, perhaps a useful optimization
    // for some other day..

    exec fn try_get_elt(&self, slice: Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<U>)
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
        proof { self.spec_elt_marshalling(); }
        assert( slice.valid(data@) );
        let oelt = 
            match self.try_get(slice, data, idx) {
                None => None,
                Some(slice) => {
                    //assert( slice == old(slice) );
                    //assert( data@ == old(data)@ );
                    assert( slice.valid(data@) );   // Whoah, neither slice nor data is mutable. How could this fail?
                    assert( self.gettable(slice.i(data@), idx as int) );
                    self.exec_elt_marshalling().try_parse(slice, data)
                }
            };
        assert( oelt is Some <==> {
             &&& self.gettable(slice.i(data@), idx as int)
             &&& self.elt_parsable(data@, idx as int)
        } );
        assert( oelt is Some ==> oelt.unwrap().deepv()== self.get_elt(slice.i(data@), idx as int) );
        oelt
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////
    spec fn settable(&self, data: Seq<u8>, idx: int, value: DVE) -> bool
    recommends
        self.valid(),
        self.spec_elt_marshalling().marshallable(value)
    ;

    spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    recommends
        self.valid()
    {
        &&& self.gettable(data, idx) ==> self.gettable(new_data, idx)
        &&& (self.gettable(data, idx) && self.elt_parsable(new_data, idx)) ==> {
            &&& self.elt_parsable(new_data, idx)
            &&& self.get_elt(new_data, idx) == self.get_elt(new_data, idx)
            }
    }

    // if preserves_entry(data, middle) && preserves_entry(middle, new_data), then preserves_entry(data, new_data)
//  proof fn preserves_entry_transitive(&self, data: Seq<u8>, idx: int, middle: Seq<u8>, new_data: Seq<u8>) -> bool

    spec fn sets(&self, data: Seq<u8>, idx: int, value: DVE, new_data: Seq<u8>) -> bool
    recommends
        self.valid(),
        self.spec_elt_marshalling().marshallable(value),
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
    
    exec fn is_settable(&self, slice: Slice, data: &Vec<u8>, idx: usize, value: &U) -> (s: bool)
    requires
        self.valid(),
        self.spec_elt_marshalling().marshallable(value.deepv())
    ensures
        s == self.settable(slice.i(data@), idx as int, value.deepv())
    ;
    
    exec fn exec_set(&self, slice: Slice, data: &mut Vec<u8>, idx: usize, value: U)
    requires
        self.valid(),
        slice.valid(old(data)@),
        self.spec_elt_marshalling().marshallable(value.deepv()),
        self.settable(slice.i(old(data)@), idx as int, value.deepv()),
    ensures
        slice.agree_beyond_slice(old(data)@, data@),
        self.sets(slice.i(old(data)@), idx as int, value.deepv(), slice.i(data@))
    ;

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////
    spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool
    recommends
        self.valid()
    ;

    spec fn resizes(&self, data: Seq<u8>, newlen: int, new_data: Seq<u8>) -> bool
    recommends
        self.valid(),
        self.resizable(data, newlen)
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(new_data)
        &&& self.length(new_data) == newlen
        &&& forall |i| self.preserves_entry(data, i, new_data)
    }
    
    exec fn is_resizable(&self, slice: Slice, data: &Vec<u8>, newlen: usize) -> (r: bool)
    requires
        self.valid(),
    ensures
        r == self.resizable(slice.i(data@), newlen as int)
    ;

    
    exec fn exec_resize(&self, slice: Slice, data: &mut Vec<u8>, newlen: int)
    requires
        self.valid(),
        slice.valid(old(data)@),
        self.resizable(old(data)@, newlen),
    ensures
        slice.agree_beyond_slice(old(data)@, data@),
        self.resizes(slice.i(old(data)@), newlen as int, slice.i(data@))
    ;

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////
    // postponing for now because we can just resize+set, right?

    /////////////////////////////////////////////////////////////////////////
    // parse_to_len
    /////////////////////////////////////////////////////////////////////////
    // postponing for now

    open spec fn gettable_to_len(&self, data: Seq<u8>, len: int) -> bool {
        forall |i: int| 0 <= i < len ==> self.gettable(data, len)
    }

    open spec fn elt_parsable_to_len(&self, data: Seq<u8>, len: int) -> bool {
        forall |i: int| 0 <= i < len ==> self.elt_parsable(data, i)
    }

    open spec fn parsable_to_len(&self, data: Seq<u8>, len: int) -> bool {
        &&& Self::gettable_to_len(self, data, len as int)
        &&& Self::elt_parsable_to_len(self, data, len as int)
    }

    open spec fn parse_to_len(&self, data: Seq<u8>, len: int) -> Seq<DVE>
    {
        Seq::new(len as nat, |i| self.get_elt(data, i))
    }
}

////////////////////////////////////////////////////////////////////
// Marshalling of sequences of uniform-sized elements, with a length
// field up front so we can resize it. (Resize means change the
// number of "live" elements. The capacity is fixed to total_size.)
////////////////////////////////////////////////////////////////////

pub trait ResizableUniformSizedElementSeqMarshallingConfig {
    type LengthInt : NativePackedInt<int>;
    type LengthMarshalling : Marshalling<int, <Self::LengthInt as NativePackedInt<int>>::IntType>;
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
// Is there such a thing as a trait alias?
//type RUSESMC = ResizableUniformSizedElementSeqMarshallingConfig;

pub struct ResizableUniformSizedElementSeqMarshalling<C: ResizableUniformSizedElementSeqMarshallingConfig> {
    total_size: usize,
    length_marshalling: C::LengthMarshalling,
    elt_marshalling: C::EltMarshalling,
    config: C,
}

impl<C: ResizableUniformSizedElementSeqMarshallingConfig> ResizableUniformSizedElementSeqMarshalling<C> {
    pub open spec fn size_of_length_field() -> usize
    {
        C::LengthInt::spec_size()
    }

    exec fn max_length(self) -> usize
    requires
        self.valid(),
    {
        (self.total_size - Self::size_of_length_field()) / self.config.exec_uniform_size()
    }
}

/*
Deepview<C::Elt> is not implementd for Vec<C::Elt>

impl<VSE> Deepview<Seq<VSE>> for Vec<VSE> {
*/

impl<C: ResizableUniformSizedElementSeqMarshallingConfig> Premarshalling<Seq<C::EltDV>, Vec<C::Elt>> for ResizableUniformSizedElementSeqMarshalling<C> {
    open spec fn valid(&self) -> bool {
        &&& Self::size_of_length_field() <= self.total_size
        &&& self.length_marshalling.valid()
        &&& self.elt_marshalling.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        &&& self.lengthable(data)
        &&& self.length(data) <= usize::MAX as int
        &&& Self::parsable_to_len(self, data, self.length(data))
    }

    exec fn exec_parsable(&self, slice: Slice, data: &Vec<u8>) -> (p: bool)
    {
        let olen = self.try_length(slice, data);
        return olen is Some && olen.unwrap() <= self.max_length()
    }

    open spec fn marshallable(&self, value: Seq<C::EltDV>) -> bool
    {
        &&& forall |i| 0 <= i < value.len() ==> self.elt_marshalling.marshallable(value[i])
        &&& forall |i| 0 <= i < value.len() ==> self.elt_marshalling.spec_size(value[i]) == self.config.spec_uniform_size()
        &&& C::LengthInt::spec_fits_in_integer(value.len() as int)
        &&& Self::size_of_length_field() as int + value.len() * self.config.spec_uniform_size() as int <= self.total_size
    }

    open spec fn spec_size(&self, value: Seq<C::EltDV>) -> usize
    recommends 
        self.valid(),
        self.marshallable(value)
    {
        self.total_size
    }

    exec fn exec_size(&self, value: &Vec<C::Elt>) -> (sz: usize)
    requires 
        self.valid(),
        self.marshallable(value.deepv()),
    ensures
        sz == self.spec_size(value.deepv())
    {
        self.total_size
    }
}

impl<C: ResizableUniformSizedElementSeqMarshallingConfig> Marshalling<Seq<C::EltDV>, Vec<C::Elt>> for ResizableUniformSizedElementSeqMarshalling<C> {
    // TODO this is common to all implementations of SeqMarshalling; refactor out?
    open spec fn parse(&self, data: Seq<u8>) -> Seq<C::EltDV>
    recommends 
        self.valid(),
        self.parsable(data)
    {
        self.parse_to_len(data, self.length(data))
    }

    // TODO this is common to all implementations of SeqMarshalling; refactor out?
    exec fn try_parse(&self, slice: Slice, data: &Vec<u8>) -> (ov: Option<Vec<C::Elt>>)
//     requires
//         self.valid(),
//     ensures
//         self.parsable(slice.i(data@)) <==> ov is Some,
//         self.parsable(slice.i(data@)) ==> ov.unwrap().deepv() == self.parse(slice.i(data@))
    {
        let olen = self.try_length(slice, data);
        if olen.is_none() {
            return None;
        }
        let len = olen.unwrap() as usize;

        let vec = Vec::with_capacity(len as usize);
        let mut idx: usize = 0;
        while idx < len
        invariant
                0 <= idx <= len,
                forall |j| 0 <= j < idx ==> self.gettable(data@, j),
                forall |j| 0 <= j < idx ==> self.elt_parsable(data@, j),
                forall |j| 0 <= j < idx ==> vec.deepv()[j] == self.get_elt(data@, j),
        {
            let oelt = self.try_get_elt(slice, data, idx as usize);
            if oelt.is_none() {
                return None;
            }
            // TODO(verus): I wanted to write: vec[idx] = x;
            vec.set(idx, oelt.unwrap());
            idx += 1;
        }
        Some(vec)
    }

    // TODO this is common to all implementations of SeqMarshalling; refactor out?
    exec fn marshall(&self, value: &Vec<C::Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
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
    {
        let len = value.len();
        let end = start + self.total_size;
        let slice = Slice{start, end};

        let i: usize = 0;
        while i < len
        invariant
            0 <= i < value.len(),
            //value.deepv().len() == old(value).deepv().len(),
            //forall |j| 0 <= j < start ==> data@[j] == old(data@)[j],
            //forall |j| end <= j < old(data@).len() ==> data@[j] == old(data@)[j],
            self.lengthable(data@.subrange(start as int, end as int)),
            self.length(data@.subrange(start as int, end as int)) == value.deepv().len(),
            forall |j| start <= j < i ==> self.gettable(data@.subrange(start as int, end as int), j),
            forall |j| start <= j < i ==> self.elt_parsable(data@.subrange(start as int, end as int), j),
            forall |j| start <= j < i ==> self.get_elt(data@.subrange(start as int, end as int), j) == value[j].deepv(),
            forall |j| start <= j < value.len() ==> self.settable(data@.subrange(start as int, end as int), j, value[j].deepv()),
        {
            self.exec_set(slice, data, i, value[i]);
            i += 1;
        }
        end
    }
}

impl<C: ResizableUniformSizedElementSeqMarshallingConfig> SeqMarshalling<C::EltDV, C::Elt, C::EltMarshalling> for ResizableUniformSizedElementSeqMarshalling<C> {

    open spec fn spec_elt_marshalling(&self) -> C::EltMarshalling
    {
        self.elt_marshalling
    }

    proof fn spec_elt_marshalling_ensures(&self)
    {}

    exec fn exec_elt_marshalling(&self) -> (elt: C::EltMarshalling)
    {
        self.elt_marshalling
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool
    {
        self.total_size as int <= data.len()
    }

    open spec fn length(&self, data: Seq<u8>) -> int
    recommends
        self.valid(),
        self.lengthable(data)
    {
        self.length_marshalling.parse(data.subrange(0, Self::size_of_length_field() as int))
    }

    exec fn try_length(&self, slice: Slice, data: &Vec<u8>) -> (out: Option<usize>)
    requires
        self.valid(),
    ensures
        out is Some <==> self.lengthable(data@),
        out is Some ==> out.unwrap() as int == self.length(data@)
    {
        if slice.exec_len() < self.total_size {
            None
        } else {
            // TODO(jonh): here's a place where we know it's parsable,
            // but we're calling a try_parse method and wasting a conditional.
            let parsed_len = self.length_marshalling.try_parse(
                slice.exec_sub(0, Self::size_of_length_field()),
                data);
            assert( parsed_len is Some );
            Some(C::LengthInt::as_usize(parsed_len.unwrap()))
        }
    }

    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid(),
    {
        &&& self.lengthable(data)
        &&& idx < self.max_length()
    }

    open spec fn get(&self, slice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    recommends
        self.valid(),
        slice.valid(data),
        self.gettable(slice.i(data), idx),
    {
        slice.spec_sub(
            (Self::size_of_length_field() + idx * self.config.spec_uniform_size()) as usize,
            (Self::size_of_length_field() + idx * self.config.spec_uniform_size() + self.config.spec_uniform_size()) as usize)
    }

    proof fn get_ensures(&self, slice: Slice, data: Seq<u8>, idx: int)
    requires
        self.valid(),
        slice.valid(data),
        self.gettable(slice.i(data), idx),
    ensures
        self.get(slice, data, idx).valid(data)
    {
    }

    exec fn try_get(&self, slice: Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let olen = self.try_length(slice, data);
        if olen.is_none() { return None; }
        let mlen = self.max_length();
        if idx < mlen {
            Some(
                slice.exec_sub(Self::size_of_length_field() + idx * self.config.exec_uniform_size(),
                Self::size_of_length_field() + idx * self.config.exec_uniform_size() + self.config.exec_uniform_size()))
        } else {
            None
        }
    }

    open spec fn settable(&self, data: Seq<u8>, idx: int, value: C::EltDV) -> bool
    {
        &&& self.lengthable(data)
        &&& idx < self.max_length() as int
        &&& self.elt_marshalling.spec_size(value) == self.config.spec_uniform_size()
    }
    
    exec fn is_settable(&self, slice: Slice, data: &Vec<u8>, idx: usize, value: &C::Elt) -> (s: bool)
    {
        let olen = self.try_length(slice, data);
        let sz = self.elt_marshalling.exec_size(value);

        &&& !olen.is_none()
        &&& idx < self.max_length()
        &&& sz == self.config.exec_uniform_size()
    }
    
    exec fn exec_set(&self, slice: Slice, data: &mut Vec<u8>, idx: usize, value: C::Elt)
    {
    }

    open spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool
    recommends
        self.valid(),
    {
        &&& self.lengthable(data)
        &&& newlen <= self.max_length() as int
        &&& C::LengthInt::spec_fits_in_integer(newlen)
    }
    
    exec fn is_resizable(&self, slice: Slice, data: &Vec<u8>, newlen: usize) -> (r: bool)
    {
        let olen = self.try_length(slice, data);
        &&& olen.is_some()
        &&& newlen <= self.max_length()
        &&& C::LengthInt::exec_fits_in_integer(newlen)
    }

    
    exec fn exec_resize(&self, slice: Slice, data: &mut Vec<u8>, newlen: int)
    requires
        self.valid(),
        slice.valid(old(data)@),
        self.resizable(old(data)@, newlen),
    ensures
        slice.agree_beyond_slice(old(data)@, data@),
        self.resizes(slice.i(old(data)@), newlen as int, slice.i(data@)),
    {
    }
}

// 
// trait ResizableUniformSizedElementSeqMarshalling<LT, ET, Elt: Marshalling<ET>>
//     : SeqMarshalling<ET, Elt>
// {
//     exec fn size_of_length_field() -> u64 {
//         NativePackedInt::<LT>::size()
//     }
// 
//     spec fn spec_total_size() -> u64;
//     //spec fn spec_length_marshalling() -> IntegerMarshalling<LT>;
// 
//     spec fn uniform_size(&self) -> u64
//     recommends
//         self.valid(),
//     ;
//     
//     proof fn uniform_size_ensures(&self)
//     requires
//         self.valid(),
//     ensures
//         0 < self.uniform_size(),
//     ;
// 
//     exec fn max_length(self) -> u64
//     requires
//         self.valid(),
//     {
//         (self.total_size - Self::size_of_length_field()) / self.uniform_size()
//     }
// 
//     spec fn lengthable(self, data: Seq<u8>) -> bool
//     {
//         self.total_size as nat <= data.len()
//     }
// 
//     spec fn length(self, data: Seq<u8>) -> int
//     {
//         self.length_marshalling.parse(data.subrange(0, Self::size_of_length_field()))
//     }
// 
//     // Stuff I'm deferring until the proof breaks
//     // proof fn length_ensures
//     // proof fn index_bounds_facts
// 
//     exec fn try_length(self, data:Vec<u8>) -> (olen: Option<u64>)
//     {
//         if data.len() < self.total_size {
//             None
//         } else {
//             // original was Parse, so we may be leaving perf on the floor here since we know it's
//             // parsable. Or maybe we should just try_parse instead of testing the length?
//             let len = self.length_marshalling.try_parse(data.subrange(0, Self::size_of_length_field()));
//                 // yeah that's gonna need to be a slice
//             Some(len)
//         }
//     }
// }
// 
// struct ResizableIntegerSeqMarshalling<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>> {
//     total_size: u64,
//     length_marshalling: LM,
//     spec_elt: EM,
// 
//     dummy_l: LT,    // TODO(jonh): phantom something something?
//     dummy_e: ET,
// }
// 
// impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
//     ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
// 
//     // Maybe we don't want function methods, but maybe we do
//     // want some cheap syntax for things that should define exec fn u64
//     // and spec fn int at the same time.
//     spec fn size_of_length_field(&self) -> u64 {
//         self.length_marshalling.size()
//     }
// }
// 
// impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
//     Marshalling<Vec<ET>> for
//     ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
// 
//     spec fn parsable(&self, data: Seq<u8>) -> bool
//     recommends self.valid()
//     {
//         SeqMarshallingDef::parsable(*self, data)
//     }
// 
// //     spec fn parse(&self, data: Seq<u8>) -> U
// //     recommends 
// //         self.valid(),
// //         self.parsable(data)
// //     ;
// // 
// //     // Should this be slices? in verus-ironfleet, jayb used Vec<u8> + start
// //     fn try_parse(&self, data: &Vec<u8>) -> (ov: Option<U>)
// //     requires
// //         self.valid(),
// //     ensures
// //         self.parsable(data@) <==> ov is Some,
// //         self.parsable(data@) ==> ov.unwrap() == self.parse(data@)
// //     ;
// // 
// //     spec fn size(&self, value: &U) -> u64
// //     recommends 
// //         self.valid(),
// //         self.marshallable(value)
// //     ;
// // 
// //     fn exec_size(&self, value: &U) -> (sz: u64)
// //     requires 
// //         self.valid(),
// //         self.marshallable(value),
// //     ensures
// //         sz == self.size(value)
// //     ;
// // 
// //     fn marshall(&self, value: &U, data: &mut Vec<u8>, start: u64) -> (end: u64)
// //     requires 
// //         self.valid(),
// //         self.marshallable(value),
// //         start as int + self.size(value) as int <= old(data).len(),
// //     ensures
// //         end == start + self.size(value),
// //         data.len() == old(data).len(),
// //         forall |i| 0 <= i < start ==> data[i] == old(data)[i],
// //         forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
// //         self.parsable(data@.subrange(start as int, end as int)),
// //         self.parse(data@.subrange(start as int, end as int)) == value
// //     ;
// }
// 
// impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
//     SeqMarshalling<ET, EM> for
//     ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
// }
// 
// // // Marshalling of sequences of uniform-sized elements, with a length
// // // field up front so we can resize it.
// // 
// // struct ResizableUniformSizedElementSeqMarshallingConfig<C: Config, U, Elt: Marshalling<C, U>>
// // {
// //     totalSize: u64,
// //     lengthCfg: IntegerMarshalling,
// //     eltCfg: C,
// // }
// // 
// // struct ResizableUniformSizedElementSeqMarshalling<C: Config, U, Elt: Marshalling<C, U>>
// // {
// // }
// // 
// // impl<C, U, Elt> SeqMarshalling<DefaultConfig, u64, IntegerMarshalling> for ResizableUniformSizedElementSeqMarshalling<C, U, Elt> {
// // }
// // 
// // // struct ResizableIntegerSeqMarshalling {
// // // }
// // // 
// // // impl Marshalling<DefaultConfig, u64> for ResizableIntegerSeqMarshalling {
// // // }
// // // 
// // // // jonh is reifing this with LengthInt==u32, BoundaryInt==u32
// // // // Oh I can't defer ResizableIntegerSeqMarshalling because I need it for the boundary table.
// // // // Or can I recurse?
// // // struct VariableSizedElementSeqMarshallingConfig {
// // //     bsmCfg: VariableSizedElementSeqMarshalling<DefaultConfig, u64, IntegerMarshalling>,
// // //     eltCfg: 
// // // }
// // // 
// // // struct VariableSizedElementSeqMarshalling<C: Config, U, Elt: Marshalling<C, U>>
// // // {
// // // }
// // 
// // // Man we need some associated types to cut down this template type burden.
// // // impl<C, U, Elt> SeqMarshalling<C, U, Elt> for VariableSizedElementSeqMarshalling<C, U, Elt> {
// // // }
// // 
// // /*
// // Roadmap: Here is the module plan Rob laid out in MarshalledAccessors.i.dfy
// // https://github.com/vmware-labs/verified-betrfs/blob/marshalled-accessors-4/lib/Marshalling/MarshalledAccessors.i.dfy#L354
// // 
// // ResizableUniformSizedElementSeqMarshalling
// //     Marshalling of sequences of uniform-sized elements, with a length
// //     field up front so we can resize it.
// // 
// // UniformSizedElementSeqMarshalling
// //     Common parts of implementation of marshalling a sequence of items
// //     that all have the same marshalled size.
// //     We omit the actual parsing and marshalling implementations so that
// //     we can use the optimized integer packing code.
// // 
// // IntegerSeqMarshalling
// //     Implementation for marshalling a sequence of packable integers
// // 
// //     We could just use the UniformSized marshalling code further below,
// //     but that would marshall each integer one at a time, which would
// //     (presumably) be slower.
// // 
// // Uint32SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint32
// // Uint64SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint64
// // 
// // ResizableUniformSizedElementSeqMarshalling
// //     Marshalling of sequences of uniform-sized elements, with a length
// //     field up front so we can resize it.
// // 
// // ResizableIntegerSeqMarshalling
// //     Implementation for marshalling a sequence of packable integers
// // 
// //     We could just use the UniformSized marshalling code further below,
// //     but that would marshall each integer one at a time, which would
// //     (presumably) be slower.
// // 
// // VariableSizedElementSeqMarshalling
// //     Implementation of marshalling a general sequence of items
// // */

} // verus!
