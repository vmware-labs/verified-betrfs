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
// conveyed by a dynamically-stored length field. The marshaller knows how to read that field and
// dissuade the caller from reading off the end of the valid data.
pub struct ResizableUniformSizedElementSeqMarshalling <
    DVElt,
    Elt: Deepview<DVElt>,
    O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy, // Bleargh. Surely I could name this.
    LengthIntObligations: IntObligations<LengthInt>
> {
    // `total_size` is like a "capacity" -- the allocated space.  It's measured in bytes.
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
    pub fn new(oblinfo: O, eltm: O::EltMarshalling, total_size: usize, length_int: LengthIntObligations) -> (s: Self)
        ensures s.total_size == total_size
    {
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
        if (dslice.len() as usize) < self.total_size {
            return None;    // lengthable first conjunct is false
        }

        let sslice = dslice.subslice(0, LengthIntObligations::o_exec_size());

        // TODO(verus): trait instability: this expression appears in exec_parse requires, but
        // mentioning it completes the proof.
        assert( self.length_int.parsable(sslice@.i(data@)) );

        let parsed_len = self.length_int.exec_parse(&sslice, data);

        proof {
            // Took way too long to track down this lemma call. Decent automation would have been nice.
            LengthIntObligations::as_int_ensures();

            assert( dslice@.subslice(0, LengthIntObligations::o_spec_size() as int).i(data@)
                    == dslice@.i(data@).subrange(0, self.size_of_length_field() as int) );   // subrange trigger
        }

        if !LengthIntObligations::exec_this_fits_in_usize(parsed_len) {
            return None;
        }
        Some(LengthIntObligations::to_usize(parsed_len))
    }

//     exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool) {
//         self.try_length(dslice, data).is_some()
//     }

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    // NB: gettable doesn't care about the stored length field! You can store
    // a too-long value; doesn't matter, if there's not enough data we won't let
    // you index it. Or you can access a field past the stored length field;
    // it's a sign, not a cop.
    // TODO it's a bit weird that we need lengthable; that forces a try_length in try_get.
    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        // This conjunct forces data (and hence the slice arg to get) to be at least total_size
        &&& self.lengthable(data)
        &&& 0 <= idx < self.max_length()
    }

    open spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    {
        dslice.subslice(
            self.size_of_length_field() + idx * self.oblinfo.uniform_size(),
            self.size_of_length_field() + idx * self.oblinfo.uniform_size() + self.oblinfo.uniform_size())
    }

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    {
        self.index_bounds_facts(idx as int);
    }

    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    {
        self.eltm.parsable(self.get_data(data, idx))
    }

    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    {
        self.eltm.parse(self.get_data(data, idx))
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        // gettable requires lengthable, so I guess we better go check
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
        dslice.subslice(
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
                    self.get_ensures(dslice@, data@, idx as int);   // TODO(verus): lament of spec ensures
                    self.index_bounds_facts(idx as int);
                    let edslice = self.get(SpecSlice::all(dslice@.i(data@)), dslice@.i(data@), idx as int);
                    assert( edslice.i(dslice@.i(data@)) == eslice@.i(data@));   // trigger
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
            self.get_ensures(dslice@, data@, idx as int);   // TODO(verus): lament of spec ensures
            self.index_bounds_facts(idx as int);
            let edslice = self.get(SpecSlice::all(dslice@.i(data@)), dslice@.i(data@), idx as int);
            assert( edslice.i(dslice@.i(data@)) == eslice@.i(data@));   // trigger
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

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &Elt) -> (s: bool)
    {
        let olen = self.try_length(dslice, data);
        let sz = self.eltm.exec_size(value);

        let s = {
            &&& olen.is_some()
            &&& idx < self.exec_max_length()
            &&& sz == self.oblinfo.exec_uniform_size()
        };
        assert( s == self.settable(dslice@.i(data@), idx as int, value.deepv()) );
        s
    }

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    {
        proof { self.index_bounds_facts(idx as int); }
        let elt_start = dslice.start + self.exec_size_of_length_field() + idx * self.oblinfo.exec_uniform_size();
        let Ghost(elt_end) = self.eltm.exec_marshall(value, data, elt_start);

        // Extensionality trigger.
        assert( dslice@.i(data@).subrange(0, self.size_of_length_field() as int)
                =~= dslice@.i(old(data)@).subrange(0, self.size_of_length_field() as int) );

        // Extensionality trigger.
        assert( data@.subrange(elt_start as int, elt_end as int) =~= self.get_data(dslice@.i(data@), idx as int) );

//         proof {
//         self.sets_final();
//         let old_data = dslice@.i(old(data)@);
//         let new_data = dslice@.i(data@);
//         let iidx = idx as int;
//         let vvalue = value.deepv();
//         assert( self.sets(dslice@.i(old(data)@), idx as int, value.deepv(), dslice@.i(data@))
//                 == 
//             {
//                 &&& new_data.len() == old_data.len()
//                 &&& self.lengthable(old_data) ==> {
//                     &&& self.lengthable(new_data)
//                     &&& self.length(new_data) == self.length(old_data)
//                     }
//                 &&& (forall |i| i!=iidx ==> self.preserves_entry(old_data, i, new_data))
//                 &&& self.gettable(new_data, iidx)
//                 &&& self.elt_parsable(new_data, iidx)
//                 &&& self.get_elt(new_data, iidx) == vvalue
//             } );
//         assert(
//             self.preserves_entry(old_data, iidx, new_data)
//             ==
//             {
//                 &&& (self.gettable(old_data, iidx) ==> self.gettable(new_data, iidx))
//                 &&& (self.gettable(old_data, iidx) && self.elt_parsable(old_data, iidx)) ==> {
//                     &&& self.elt_parsable(new_data, iidx)
//                     &&& self.get_elt(new_data, iidx) == self.get_elt(old_data, iidx)
//                     }
//             }
//         );
//         assert forall |i| i!=iidx implies
//             {
//                 &&& (self.gettable(old_data, i) ==> self.gettable(new_data, i))
//                 &&& (self.gettable(old_data, i) && self.elt_parsable(old_data, i)) ==> {
//                     &&& self.elt_parsable(new_data, i)
//                     &&& self.get_elt(new_data, i) == self.get_elt(old_data, i)
//                     }
//             } by {
//                 if self.gettable(old_data, i) && self.elt_parsable(old_data, i) {
//         // Why does preserves_entry work?
//         // the thing at i needs to still be elt_parsable.
//         // We only touched things between elt_start and elt_end.
//         // That means the data from i_start to i_end didn't get touched.
// 
// //                     assert( self.get_data(old_data, i)
// //                                 == self.get(SpecSlice::all(old_data), old_data, i).i(old_data) );
// // 
//                     let old_data_x = SpecSlice::all(old_data);
//                     let new_data_x = SpecSlice::all(new_data);
// //                     assert( self.get(old_data_x, old_data, i) == self.get(new_data_x, new_data, i) );
// 
//                     assert( self.get_data(old_data, i) == self.get_data(new_data, i) );
//                     assert( self.elt_parsable(old_data, i) );
//                     assert( self.elt_parsable(new_data, i) );
//                     assert( self.get_elt(new_data, i) == self.get_elt(old_data, i) );
//                 }
//             }
//         assert forall |i| i!=iidx implies self.preserves_entry(old_data, i, new_data) by {}
//         assert({
//             &&& new_data.len() == old_data.len()
//             &&& self.lengthable(old_data) ==> {
//                 &&& self.lengthable(new_data)
//                 &&& self.length(new_data) == self.length(old_data)
//                 }
//             &&& forall |i| i!=iidx ==> self.preserves_entry(old_data, i, new_data)
//             &&& self.gettable(new_data, iidx)
//             &&& self.elt_parsable(new_data, iidx)
//             &&& self.get_elt(new_data, iidx) == vvalue
//         });
//         }
                
        assert forall |i: int| i != idx as int && self.gettable(dslice@.i(old(data)@), i)
            implies self.get_data(dslice@.i(data@), i) == self.get_data(dslice@.i(old(data)@), i) by
        {
            self.index_bounds_facts(i);

//             lemma_seq_slice_slice(data@,
//                 dslice.start as int,
//                 dslice.end as int,
//                 self.size_of_length_field() as int + i * self.oblinfo.uniform_size() as int,
//                 self.size_of_length_field() as int + i * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);
//             lemma_seq_slice_slice(old(data)@,
//                 dslice.start as int,
//                 dslice.end as int,
//                 self.size_of_length_field() as int + i * self.oblinfo.uniform_size() as int,
//                 self.size_of_length_field() as int + i * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);

            if i < idx as int {
                mul_preserves_le(i + 1, idx as int, self.oblinfo.uniform_size() as int);
            } else {
                mul_preserves_le(idx as int + 1, i, self.oblinfo.uniform_size() as int);
            }

            // TODO(verus): shouldn't assert-by conclusion give us this trigger for free?
            assert( self.get_data(dslice@.i(data@), i) == self.get_data(dslice@.i(old(data)@), i) );
        }
            
        assert( self.sets(dslice@.i(old(data)@), idx as int, value.deepv(), dslice@.i(data@)) );
    }

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    open spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool {
        &&& self.lengthable(data)
        &&& newlen <= self.max_length() as nat
        &&& LengthIntObligations::spec_fits_in_this(newlen)
    }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool) {
        &&& self.exec_lengthable(dslice, data)
        &&& newlen <= self.exec_max_length()
        &&& LengthIntObligations::exec_fits_in_this(newlen)
    }

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize) {
        let new_end = self.length_int.exec_marshall(
            &LengthIntObligations::from_usize(newlen), data, dslice.start);

        // TODO: there are 31 lines of proof at MarshalledAccessors.i.dfy:1085 to translate
        assume(false);
    }

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

//     proof fn sets_final(&self) {}
}

// TODO(jonh): A great deal of this type duplicates what's in UniformSizedSeq. I'm reasonably
// confident we could shoehorn them together somehow, so that UniformSizedSeq is just a variant
// of ResizableUniformSizedSeq with a 0-byte length field that knows to get its "dynamic"
// length from the static length ("total_size") in the Marshalling object.

impl <
    DVElt,
    Elt: Deepview<DVElt>,
    O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy,
    LengthIntObligations: IntObligations<LengthInt>
>
    ResizableUniformSizedElementSeqMarshalling<DVElt, Elt, O, LengthInt, LengthIntObligations>
{
    pub open spec fn seq_parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.seq_valid()
        &&& self.lengthable(data)
        &&& self.length(data) <= usize::MAX
        &&& self.parsable_to_len(data, self.length(data) as usize)
    }

    pub open spec fn seq_parse(&self, data: Seq<u8>) -> Seq<DVElt>
    {
        self.parse_to_len(data, self.length(data) as usize)
    }

    pub open spec fn marshallable_at(&self, value: Seq<DVElt>, i: int) -> bool
    recommends 0 <= i < value.len()
    {
        &&& self.eltm.marshallable(value[i])
        &&& self.eltm.spec_size(value[i]) == self.oblinfo.uniform_size()
    }

    proof fn marshallable_subrange(&self, value: Seq<DVElt>, l: int)
    requires self.marshallable(value), 0<=l<=value.len()
    ensures self.marshallable(value.subrange(0, l))
    {
        mul_preserves_le(l, value.len() as int, self.oblinfo.uniform_size() as int);
        assert forall |i| 0 <= i < value.subrange(0, l).len() implies self.marshallable_at(value.subrange(0, l), i) by {
            assert( self.marshallable_at(value, i) );
        }
        assume( false );
    }
}

impl <
    DVElt,
    Elt: Deepview<DVElt>,
    O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy,
    LengthIntObligations: IntObligations<LengthInt>
>
     Marshalling<Seq<DVElt>, Vec<Elt>>
     for ResizableUniformSizedElementSeqMarshalling<DVElt, Elt, O, LengthInt, LengthIntObligations>
{
    open spec fn valid(&self) -> bool { self.seq_valid() }

    exec fn exec_parsable(&self, dslice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        // TODO factor this into Marshalling trait default method
        let ovalue = self.try_parse(dslice, data);
        ovalue.is_some()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.seq_parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Seq<DVElt>
    {
        self.seq_parse(data)
    }

    exec fn try_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (ovalue: Option<Vec<Elt>>)
    {
        match self.try_length(dslice, data) {
            None => {
                proof {
                    let ghost idata = dslice@.i(data@);
                    assert( !self.lengthable(idata) );
                }
                assert( !self.seq_parsable(dslice@.i(data@)) );
                assert( !self.parsable(dslice@.i(data@)) );
                return None;
            },
            Some(len) => {
                assert( len as int == self.length(dslice@.i(data@)) );
                assert( len <= usize::MAX );
                let mut i: usize = 0;
                let mut result:Vec<Elt> = Vec::with_capacity(len);
                while i < len
                    invariant i <= len,
                    self.valid(),   // TODO(verus #984): waste of my debugging time
                    dslice@.valid(data@),   // TODO(verus #984): waste of my debugging time
                    len == self.length(dslice@.i(data@)) as usize, // TODO(verus #984): waste of my debugging time
                        result.len() == i,
                        forall |j| 0<=j<i as nat ==> self.gettable(dslice@.i(data@), j),
                        forall |j| 0<=j<i as nat ==> self.elt_parsable(dslice@.i(data@), j),
                        forall |j| #![auto] 0<=j<i as nat ==> result[j].deepv() == self.get_elt(dslice@.i(data@), j),
                {
                    let ghost idata = dslice@.i(data@);
                    let oelt = self.try_get_elt(dslice, data, i);
                    if oelt.is_none() {
                        return None;
                    }
                    result.push(oelt.unwrap());
                    i += 1;
                }
                // Looks like this wants extensionality, but no ~! Not sure why it's needed.
                // Oh maybe it's the trait-ensures-don't-trigger bug?
                assert( result.deepv() == self.parse(dslice@.i(data@)) );    // trigger.
                return Some(result);
            }
        }
    }

    open spec fn marshallable(&self, value: Seq<DVElt>) -> bool
    {
        &&& forall |i| 0 <= i < value.len() ==> self.marshallable_at(value, i)
        &&& LengthIntObligations::spec_fits_in_this(value.len() as int)

        &&& self.size_of_length_field() + value.len() * self.oblinfo.uniform_size() <= self.total_size
    }

    open spec fn spec_size(&self, value: Seq<DVElt>) -> usize
    {
        self.total_size
    }

    exec fn exec_size(&self, value: &Vec<Elt>) -> (sz: usize)
    {
        self.total_size
    }

    exec fn exec_marshall(&self, value: &Vec<Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let end = start + self.total_size;
        let slice = Slice{start, end};

        // Just call resize instead? no, that requires the data already be well-formatted
        // (such as lengthable)
        let length_val = LengthIntObligations::from_usize(value.len());
        let length_end = self.length_int.exec_marshall(&length_val, data, start);
        proof {
            // gosh golly darn lack of spec ensures
            LengthIntObligations::spec_this_fits_in_usize_ensures(value.len() as int);

            // Extensional equality between the thing we know holds length_val and the self.length defn
            assert( slice@.i(data@).subrange(0, self.size_of_length_field() as int)
                    == SpecSlice{start: start as int, end: length_end as int}.i(data@) );

            // gosh golly darn lack of spec ensures
            LengthIntObligations::as_int_ensures();

            assert( self.lengthable(slice@.i(data@)) );
        }

        let mut i: usize = 0;

        assert( value.len() <= self.max_length() as int ) by {
            self.oblinfo.uniform_size_ensures();
            inequality_move_divisor(
                value.len() as int,
                self.total_size as int - self.size_of_length_field() as int,
                self.oblinfo.uniform_size() as int);
        }
        
        assert forall |j| #![auto] 0 <= j < value.len() implies self.settable(slice@.i(data@), j, value[j].deepv()) by {
            assert( self.marshallable_at(value.deepv(), j) );   // trigger
        }

        while i < value.len()
        invariant
            // come ON, #![verifier::spinoff_loop(false)]! Do your thing!
            self.valid(),
            slice == (Slice{start, end}), // shouldn't need this; slice is bound immutably. Try deleting.
            slice@.valid(old(data)@),
            self.marshallable(value.deepv()),

            0 <= i <= value.len(),
            data@.len() == old(data)@.len(),
            forall |j| 0 <= j < start ==> data@[j] == old(data)@[j],
            forall |j| end as int <= j < old(data)@.len() ==> data@[j] == old(data)@[j],
            self.lengthable(slice@.i(data@)),
            self.length(slice@.i(data@)) == value.len(),

            forall |j| 0 <= j < i ==> self.gettable(slice@.i(data@), j),
            forall |j| 0 <= j < i ==> self.elt_parsable(slice@.i(data@), j),
            forall |j| #![auto] 0 <= j < i ==> self.get_elt(slice@.i(data@), j) == value[j].deepv(),
            forall |j| #![auto] 0 <= j < value.len() ==> self.settable(slice@.i(data@), j, value[j].deepv()),
        {
            let ghost prev_data = data@;
            let ghost old_i = i;
            proof {
                self.oblinfo.uniform_size_ensures();
                assert( self.marshallable_at(value.deepv(), i as int) );
            }
            self.exec_set(&slice, data, i, &value[i]);
            i += 1;

            proof {
//                 assert forall |j: int| 0 <= j < old_i
//                     implies self.preserves_entry(slice@.i(prev_data), j as int, slice@.i(data@) ) by {}

                assert forall |j| 0 <= j < i implies self.elt_parsable(slice@.i(data@), j) by {
                    if j < old_i {
                        assert( self.preserves_entry( slice@.i(prev_data), j, slice@.i(data@)) );    // trigger
                    }
                }
                assert forall |j| #![auto] 0 <= j < i implies self.get_elt(slice@.i(data@), j) == value[j].deepv() by {
                    if j < old_i {
                        assert( self.preserves_entry( slice@.i(prev_data), j, slice@.i(data@)) );    // trigger
                    }
                }
            }
        }
        // This is just a postcondition; why wasn't it automatically triggered?
        assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
        end
    }
}

}

