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
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::math_v::*;

verus! {

// pub trait ResizableUniformSizedElementSeqMarshallingOblinfo<DVElt, Elt: Deepview<DVElt>>
//     : UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>
// {
// }

// In a ResizableUniformSizedElementSeqMarshallingOblinfo, the length (set of readable elements) is
// limited by a dynamically-stored length field. The marshaller knows how to read that field and
// prevent the caller from reading off the end of the valid data.
pub struct ResizableUniformSizedElementSeqMarshalling <
    DVElt,
    Elt: Deepview<DVElt>,
    O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy, // Bleargh. Surely I could name this.
    LengthIntObligations: IntObligations<LengthInt>
> {
    pub total_size: usize,
    pub length_int: LengthIntObligations,
    pub oblinfo: O,
    pub eltm: O::EltMarshalling,
    pub _p: std::marker::PhantomData<(DVElt,Elt,LengthInt,)>,
}

impl <
    DVElt,
    Elt: Deepview<DVElt>,
    O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy, // Bleargh. Surely I could name this.
    LengthIntObligations: IntObligations<LengthInt>
>
    ResizableUniformSizedElementSeqMarshalling<DVElt, Elt, O, LengthInt, LengthIntObligations>
{
    // TODO(verus): modify Verus to allow constructing default phantomdata fields
    #[verifier(external_body)]
    pub fn new(oblinfo: O, eltm: O::EltMarshalling, total_size: usize, length_int: LengthIntObligations) -> Self {
        Self{ oblinfo, eltm, _p: Default::default(), total_size, length_int }
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.size_of_length_field() <= self.total_size
        &&& self.length_int.valid()
        &&& self.oblinfo.valid()    // this field is new wrt dafny baseline
        &&& self.eltm.valid()
    }

    pub open spec fn max_length(&self) -> usize
    recommends self.valid()
    {
        // Why does subtraction of usizes produce an int?
        (self.total_size - self.size_of_length_field()) as usize / self.oblinfo.uniform_size()
    }

    // TODO(jonh): this should probably be a const field (with a valid() invariant relating it to
    // total_size, etc) rather than computing it every time.
    exec fn exec_max_length(&self) -> (out: usize)
        requires self.valid()
        ensures out == self.max_length()
    {
        proof { self.oblinfo.uniform_size_ensures(); };
        (self.total_size - self.exec_size_of_length_field()) as usize / self.oblinfo.exec_uniform_size()
    }

    pub open spec fn size_of_length_field(&self) -> usize
    {
        LengthIntObligations::o_spec_size()
    }

    exec fn exec_size_of_length_field(&self) -> (out: usize)
    ensures out == self.size_of_length_field()
    {
        LengthIntObligations::o_exec_size()
    }

    proof fn index_bounds_facts(&self, idx: int)
    requires self.valid(), 0 <= idx, idx < self.max_length()
    ensures
        self.size_of_length_field() as int
            <= self.size_of_length_field() as int + idx * (self.oblinfo.uniform_size() as int)
            <  self.size_of_length_field() as int + idx * (self.oblinfo.uniform_size() as int) + (self.oblinfo.uniform_size() as int)
            == self.size_of_length_field() as int + (idx+1) * (self.oblinfo.uniform_size() as int)
            <= self.size_of_length_field() + (self.max_length() as int) * (self.oblinfo.uniform_size() as int)
            <= self.total_size
    {
        self.oblinfo.uniform_size_ensures();   // TODO(verus): lament of the spec ensures
        nat_mul_nat_is_nat(idx, self.oblinfo.uniform_size() as int);
        pos_mul_preserves_order(idx, idx+1, self.oblinfo.uniform_size() as int);
        distribute_left(idx, 1, self.oblinfo.uniform_size() as int);
        div_mul_order(self.total_size as int, self.oblinfo.uniform_size() as int);
        if idx + 1 < self.max_length() {
            pos_mul_preserves_order(idx + 1, self.max_length() as int, self.oblinfo.uniform_size() as int);
            // (idx+1)*us < m * us
        }
        euclidean_div_truncates(
            (self.total_size - self.size_of_length_field()) as usize as int,
            self.oblinfo.uniform_size() as int);
    }
}

impl <
    DVElt,
    Elt: Deepview<DVElt>,
    O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy, // Bleargh. Surely I could name this.
    LengthIntObligations: IntObligations<LengthInt>
>
    SeqMarshalling<DVElt, Elt>
    for ResizableUniformSizedElementSeqMarshalling<DVElt, Elt, O, LengthInt, LengthIntObligations>
{
    open spec fn seq_valid(&self) -> bool {
        self.valid()
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool {
        &&& self.total_size <= data.len()
        &&& LengthIntObligations::spec_this_fits_in_usize(self.length(data))
    }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        self.length_int.parse(data.subrange(0, self.size_of_length_field() as int))
    }

//     proof fn length_ensures(&self, data: Seq<u8>)
//     ensures self.size_of_length_field() as int <= self.size_of_length_field() as int + self.length(data) * self.uniform_size() as int
//     {
//     }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        if (dslice.exec_len() as usize) < self.total_size {
            return None;    // lengthable first conjunct is false
        }

        let parsed_len = self.length_int.exec_parse(&dslice.exec_sub(0, LengthIntObligations::o_exec_size()), data);

        proof {
            // Took way too long to track down this lemma call. Decent automation would have been nice.
            LengthIntObligations::as_int_ensures();

            assert( dslice.spec_sub(0, LengthIntObligations::o_spec_size()).i(data@)
                    == dslice.i(data@).subrange(0, self.size_of_length_field() as int) );   // subrange trigger
        }

        if !LengthIntObligations::exec_this_fits_in_usize(parsed_len) {
            return None;
        }
        Some(LengthIntObligations::to_usize(parsed_len))
    }

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool) {
        self.try_length(dslice, data).is_some()
    }

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    {
        self.try_length(dslice, data).unwrap()
    }

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    // NB: gettable doesn't care about the stored length field! You can store
    // a too-long value; doesn't matter, if there's not enough data we won't let
    // you index it. Or you can access a field past the stored length field;
    // it's a sign, not a cop.
    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        // This conjunct forces data (and hence the slice arg to get) to be at least total_size
        &&& self.lengthable(data)
        &&& 0 <= idx < self.max_length()
    }

    open spec fn get(&self, dslice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    {
        dslice.spec_sub(
            (self.size_of_length_field() + 
                ((idx as usize) * self.oblinfo.uniform_size())) as usize,
            (self.size_of_length_field() + 
                (idx as usize) * self.oblinfo.uniform_size() + self.oblinfo.uniform_size()) as usize
        )
    }

    proof fn get_ensures(&self, dslice: Slice, data: Seq<u8>, idx: int)
    {
        self.index_bounds_facts(idx as int);
    }

    open spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    // TODO factor out this common impl
    {
        self.get(Slice::all(data), data, idx).i(data)
    }

    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    // TODO factor out this common impl
    {
        self.eltm.parsable(self.get_data(data, idx))
    }

    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    // TODO factor out this common impl
    {
        self.eltm.parse(self.get_data(data, idx))
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let olen = self.try_length(dslice, data);
        if olen.is_none() { return None; }

        if idx < self.exec_max_length() {
            proof { self.index_bounds_facts(idx as int); }
            Some( self.exec_get(dslice, data, idx) )
//             let eslice = dslice.exec_sub(
//                     self.exec_size_of_length_field() + (idx as usize) * self.oblinfo.exec_uniform_size(),
//                     self.exec_size_of_length_field() + (idx as usize) * self.oblinfo.exec_uniform_size() + self.oblinfo.exec_uniform_size());
//             Some( eslice )
        } else {
            None
        }
    }

    exec fn exec_gettable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    {
        self.try_length(dslice, data).is_some() && idx < self.exec_max_length()
    }

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    {
        proof { self.index_bounds_facts(idx as int); }
        dslice.exec_sub(
            self.exec_size_of_length_field() + (idx as usize) * self.oblinfo.exec_uniform_size(),
            self.exec_size_of_length_field() + (idx as usize) * self.oblinfo.exec_uniform_size() + self.oblinfo.exec_uniform_size())
    }

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    // TODO factor out this common impl
    {
        //proof { self.oblinfo.spec_elt_marshalling_ensures() };  // :v(

        let oeslice = self.try_get(dslice, data, idx);
        match oeslice {
            None => None,
            Some(eslice) => {
                proof {
                    self.get_ensures(*dslice, data@, idx as int);   // TODO(verus): lament of spec ensures
                    self.index_bounds_facts(idx as int);
                    let edslice = self.get(Slice::all(dslice.i(data@)), dslice.i(data@), idx as int);
                    assert( edslice.i(dslice.i(data@)) == eslice.i(data@));   // trigger
                }
                let oelt = self.eltm.try_parse(&eslice, data);
                oelt
            }
        }
    }

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    // TODO factor out this common impl
    {
        let eslice = self.exec_get(dslice, data, idx);
        proof { // duplicated from try_get_elt
            self.get_ensures(*dslice, data@, idx as int);   // TODO(verus): lament of spec ensures
            self.index_bounds_facts(idx as int);
            let edslice = self.get(Slice::all(dslice.i(data@)), dslice.i(data@), idx as int);
            assert( edslice.i(dslice.i(data@)) == eslice.i(data@));   // trigger
        }
        self.eltm.exec_parse(&eslice, data)
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn elt_marshallable(&self, elt: DVElt) -> bool
    {
        self.eltm.marshallable(elt)
    }

    open spec fn settable(&self, data: Seq<u8>, idx: int, value: DVElt) -> bool
    {
        &&& self.lengthable(data)
        &&& 0 <= idx < self.max_length() as int
        &&& self.eltm.spec_size(value) == self.oblinfo.uniform_size()
    }

    open spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    {
        &&& self.gettable(data, idx) ==> self.gettable(new_data, idx)
        &&& (self.gettable(data, idx) && self.elt_parsable(new_data, idx)) ==> {
            &&& self.elt_parsable(new_data, idx)
            &&& self.get_elt(new_data, idx) == self.get_elt(new_data, idx)
            }
    }

    open spec fn sets(&self, data: Seq<u8>, idx: int, value: DVElt, new_data: Seq<u8>) -> bool
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
    {
        let olen = self.try_length(dslice, data);
        let sz = self.eltm.exec_size(value);

        let s = {
            &&& olen.is_some()
            &&& idx < self.exec_max_length()
            &&& sz == self.oblinfo.exec_uniform_size()
        };
        assert( s == self.settable(dslice.i(data@), idx as int, value.deepv()) );
        s
    }

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    {
        proof { self.index_bounds_facts(idx as int); }
        let elt_start = dslice.start + self.exec_size_of_length_field() + idx * self.oblinfo.exec_uniform_size();
        let Ghost(elt_end) = self.eltm.exec_marshall(value, data, elt_start);

        // Extensionality trigger.
        assert( dslice.i(data@).subrange(0, self.size_of_length_field() as int)
                =~= dslice.i(old(data)@).subrange(0, self.size_of_length_field() as int) );

        // Extensionality trigger.
        assert( data@.subrange(elt_start as int, elt_end as int) =~= self.get_data(dslice.i(data@), idx as int) );
    }

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    open spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool { false }

    open spec fn resizes(&self, data: Seq<u8>, newlen: int, newdata: Seq<u8>) -> bool { false }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool) { false }

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize) { }

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////

    open spec fn well_formed(&self, data: Seq<u8>) -> bool { false }

    proof fn well_formed_ensures(&self, data: Seq<u8>) {}

    open spec fn appendable(&self, data: Seq<u8>, value: DVElt) -> bool { false }

    open spec fn appends(&self, data: Seq<u8>, value: DVElt, newdata: Seq<u8>) -> bool { false }


    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool) { false }

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: Elt) -> (r: bool) { false }

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: Elt) {}


    // TODO(delete): duplicate of trait default method (verus issue #1006)
    open spec fn gettable_to_len(&self, data: Seq<u8>, len: int) -> bool
    {
        forall |i: int| 0<=i<len ==> self.gettable(data, i)
    }

    // TODO(delete): duplicate of trait default method (verus issue #1006)
    open spec fn elt_parsable_to_len(&self, data: Seq<u8>, len: int) -> bool
    {
        forall |i: int| 0<=i<len ==> self.elt_parsable(data, i)
    }

    // TODO(delete): duplicate of trait default method (verus issue #1006)
    open spec fn parsable_to_len(&self, data: Seq<u8>, len: usize) -> bool
    {
        &&& self.gettable_to_len(data, len as int)
        &&& self.elt_parsable_to_len(data, len as int)
    }

    // TODO(delete): duplicate of trait default method (verus issue #1006)
    open spec fn parse_to_len(&self, data: Seq<u8>, len: usize) -> Seq<DVElt>
    {
        Seq::new(len as nat, |i: int| self.get_elt(data, i))
    }

//     /////////////////////////////////////////////////////////////////////////
//     // marshall
//     /////////////////////////////////////////////////////////////////////////
// 
//     open spec fn marshallable(&self, value: Seq<DVElt>) -> bool { false }
// 
//     open spec fn spec_size(&self, value: Seq<DVElt>) -> usize { 0 }
// 
//     exec fn exec_size(&self, value: &Vec<Elt>) -> (sz: usize) { 0 }
// 
//     exec fn exec_marshall(&self, value: &Vec<Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     {
//         0
//     }
// 
//         // TODO(jonh) [performance]: In Dafny this is a cast operation. We should do this with an
//         // untrusted cast axiom in Rust, I guess.
//         // For now, rely on Marshalling default trait method impl
//     exec fn seq_exec_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (value: Vec<Elt>)
}

// impl<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
//     UniformSizedElementSeqMarshalling<DVElt, Elt, O>
// {
//     pub open spec fn seq_parsable(&self, data: Seq<u8>) -> bool
//     {
//         &&& self.seq_valid()
//         &&& self.lengthable(data)
//         &&& self.length(data) <= usize::MAX
//         &&& self.parsable_to_len(data, self.length(data) as usize)
//     }
// 
//     pub open spec fn seq_parse(&self, data: Seq<u8>) -> Seq<DVElt>
//     {
//         self.parse_to_len(data, self.length(data) as usize)
//     }
// }
// 
// impl<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
//     Marshalling<Seq<DVElt>, Vec<Elt>>
//     for UniformSizedElementSeqMarshalling<DVElt, Elt, O>
// {
//     open spec fn valid(&self) -> bool { self.seq_valid() }
// 
//     exec fn exec_parsable(&self, dslice: &Slice, data: &Vec<u8>) -> (p: bool)
//     {
//         // TODO factor this into Marshalling trait default method
//         let ovalue = self.try_parse(dslice, data);
//         ovalue.is_some()
//     }
// 
//     open spec fn parsable(&self, data: Seq<u8>) -> bool
//     {
//         self.seq_parsable(data)
//     }
// 
//     open spec fn parse(&self, data: Seq<u8>) -> Seq<DVElt>
//     {
//         self.seq_parse(data)
//     }
// 
//     exec fn try_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (ovalue: Option<Vec<Elt>>)
//     {
//         match self.try_length(dslice, data) {
//             None => {
//                 proof {
//                     let ghost idata = dslice.i(data@);
//                     assert( !self.lengthable(idata) );
//                 }
//                 assert( !self.seq_parsable(dslice.i(data@)) );
//                 assert( !self.parsable(dslice.i(data@)) );
//                 return None;
//             },
//             Some(len) => {
//                 assert( len as int == self.length(dslice.i(data@)) );
//                 assert( len <= usize::MAX );
//                 let mut i: usize = 0;
//                 let mut result:Vec<Elt> = Vec::with_capacity(len);
//                 while i < len
//                     invariant i <= len,
//                     self.valid(),   // TODO(verus #984): waste of my debugging time
//                     dslice.valid(data@),   // TODO(verus #984): waste of my debugging time
//                     len == self.length(dslice.i(data@)) as usize, // TODO(verus #984): waste of my debugging time
//                         result.len() == i,
//                         forall |j| 0<=j<i as nat ==> self.gettable(dslice.i(data@), j),
//                         forall |j| 0<=j<i as nat ==> self.elt_parsable(dslice.i(data@), j),
//                         forall |j| #![auto] 0<=j<i as nat ==> result[j].deepv() == self.get_elt(dslice.i(data@), j),
//                 {
//                     let ghost idata = dslice.i(data@);
//                     let oelt = self.try_get_elt(dslice, data, i);
//                     if oelt.is_none() {
//                         return None;
//                     }
//                     result.push(oelt.unwrap());
//                     i += 1;
//                 }
//                 // Looks like this wants extensionality, but no ~! Not sure why it's needed.
//                 // Oh maybe it's the trait-ensures-don't-trigger bug?
//                 assert( result.deepv() == self.parse(dslice.i(data@)) );    // trigger.
//                 return Some(result);
//             }
//         }
//     }
// 
//     // dummy placeholders; I guess we need to implement this yet
//     open spec fn marshallable(&self, value: Seq<DVElt>) -> bool
//     {
//         false
//     }
// 
//     open spec fn spec_size(&self, value: Seq<DVElt>) -> usize
//     {
//         0
//     }
// 
//     exec fn exec_size(&self, value: &Vec<Elt>) -> (sz: usize)
//     {
//         0
//     }
// 
//     exec fn exec_marshall(&self, value: &Vec<Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     {
//         start
//     }
// }

}

