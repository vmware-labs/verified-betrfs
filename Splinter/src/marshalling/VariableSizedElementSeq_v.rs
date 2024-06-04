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
use crate::marshalling::ResizableUniformSizedSeq_v::*;
use crate::marshalling::math_v::*;

verus! {

// A VariableSizedElementSeqMarshalling conveys a variable number of variably-sized elements.
// You can't Set one of these (because we're not gonna do de-fragmentation), only append.
// Layout is:
//     a preallocated capacity
//     an array of boundary pointers that describe where to find each element [i]
//     some free space
//     storage for the elements, allocated from the end towards the middle.
//
// In principle, this means the data structure might be able to use the free space either
// for more boundary pointers (if the data are small) or more data (if there are fewer,
// bigger data). In practice, the array of boundary pointers has a preallocated capacity,
// and this type doesn't anticipate the boundary array's size to change (when a new element is
// appended).

pub struct VariableSizedElementSeqMarshalling <
    // The values we're marshalling and how to marshall each
    DVElt,
    Elt: Deepview<DVElt>,
    EltMarshalling: Marshalling<DVElt, Elt>,

    // The ints we'll use to track the lengths of each value
    LengthInt: Deepview<int> + builtin::Integer + Copy,
    LengthIntObligations: IntObligations<LengthInt>,
    BoundaryInt: Deepview<int> + builtin::Integer + Copy,
    BoundaryIntObligations: IntObligations<BoundaryInt>,
    BoundarySeqO: UniformSizedElementSeqMarshallingOblinfo<int, BoundaryInt>,
> {
    // This field ports bsmCfg
    pub boundary_seq_marshalling: ResizableUniformSizedElementSeqMarshalling<
            int,
            BoundaryInt,
            BoundarySeqO,
            LengthInt,
            LengthIntObligations,
        >,

    // This field ports eltCfg
    pub eltm: EltMarshalling,

    // The pre-allocated capacity (bytes)
    pub total_size: usize,

    pub _p: std::marker::PhantomData<(DVElt,Elt,LengthInt,BoundaryIntObligations,)>,
}


impl <
    DVElt,
    Elt: Deepview<DVElt>,
    EltMarshalling: Marshalling<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy,
    LengthIntObligations: IntObligations<LengthInt>,
    BoundaryInt: Deepview<int> + builtin::Integer + Copy,
    BoundaryIntObligations: IntObligations<BoundaryInt>,
    BoundarySeqO: UniformSizedElementSeqMarshallingOblinfo<int, BoundaryInt>,
>
    VariableSizedElementSeqMarshalling<DVElt, Elt, EltMarshalling, LengthInt, LengthIntObligations, BoundaryInt, BoundaryIntObligations, BoundarySeqO>
{
    // TODO(verus): modify Verus to allow constructing default phantomdata fields
    #[verifier(external_body)]
    pub fn new(boundary_seq_marshalling: ResizableUniformSizedElementSeqMarshalling<
            int,
            BoundaryInt,
            BoundarySeqO,
            LengthInt,
            LengthIntObligations,
        >,
            eltm: EltMarshalling,
            total_size: usize) -> (s: Self)
        ensures s.total_size == total_size
    {
        Self{ boundary_seq_marshalling, eltm, total_size, _p: Default::default(), }
    }

    pub open spec fn max_length(&self) -> usize {
        self.boundary_seq_marshalling.max_length()
    }

    exec fn exec_max_length(&self) -> (out: usize)
        requires self.seq_valid()
        ensures out == self.max_length()
    {
        self.boundary_seq_marshalling.exec_max_length()
    }

    // This ports BoundaryElementGettable
    pub open spec fn element_gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        &&& self.boundary_seq_marshalling.gettable(data, idx)
        &&& self.boundary_seq_marshalling.elt_parsable(data, idx)
    }

    pub open spec fn element_data_begin(&self, data: Seq<u8>, idx: int) -> int
    {
        self.boundary_seq_marshalling.get_elt(data, idx)
    }

    pub exec fn exec_element_data_begin(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (start: usize)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.element_gettable(dslice@.i(data@), idx as int),
    ensures start as int == self.element_data_begin(dslice@.i(data@), idx as int)
    {
        let istart: BoundaryInt = self.boundary_seq_marshalling.exec_get_elt(dslice, data, idx);
        proof {
            BoundaryIntObligations::as_int_ensures();
            self.boundary_ints_fit_in_usize();
        }
        assert( BoundaryIntObligations::as_int(istart) == self.element_data_begin(dslice@.i(data@), idx as int) );
        BoundaryIntObligations::to_usize(istart)
    }

    pub open spec fn element_data_end(&self, data: Seq<u8>, idx: int) -> int
    {
        if idx == 0 { self.total_size as int }
        else { self.boundary_seq_marshalling.get_elt(data, idx - 1) }
    }

    pub exec fn exec_element_data_end(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (end: usize)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.element_gettable(dslice@.i(data@), idx as int),
        // TODO replace this clause with a more generic wf-y invariant
        0 < idx ==> self.element_gettable(dslice@.i(data@), idx - 1 as int),
    ensures
        end as int == self.element_data_end(dslice@.i(data@), idx as int)
    {
        proof {
            BoundaryIntObligations::as_int_ensures();
            self.boundary_ints_fit_in_usize();
        }
        if 0 < idx {
            let iend = self.boundary_seq_marshalling.exec_get_elt(dslice, data, idx - 1);
            BoundaryIntObligations::to_usize(iend)
        } else {
            self.total_size
        }
    }

    // This is lies, but it papers over a module type specialization in the Dafny code that we
    // haven't shoehorned into this trait system yet.
    proof fn boundary_seq_easy_marshalling(&self)
    ensures
        forall |data| self.boundary_seq_marshalling.eltm.parsable(data)
    {
        assume(false);
    }

    // Here's another obligation we'd like to place on the choice of boundary
    // int: don't make me deal with counting things that are beyond the
    // platform usize.
    proof fn boundary_ints_fit_in_usize(&self)
        ensures forall |i| #![auto] BoundaryIntObligations::spec_this_fits_in_usize(BoundaryIntObligations::as_int(i))
    {
        assume(false);
    }
}

impl <
    DVElt,
    Elt: Deepview<DVElt>,
    EltMarshalling: Marshalling<DVElt, Elt>,
    LengthInt: Deepview<int> + builtin::Integer + Copy,
    LengthIntObligations: IntObligations<LengthInt>,
    BoundaryInt: Deepview<int> + builtin::Integer + Copy,
    BoundaryIntObligations: IntObligations<BoundaryInt>,
    BoundarySeqO: UniformSizedElementSeqMarshallingOblinfo<int, BoundaryInt>,
>
    SeqMarshalling<DVElt, Elt>
    for
    VariableSizedElementSeqMarshalling<DVElt, Elt, EltMarshalling, LengthInt, LengthIntObligations, BoundaryInt, BoundaryIntObligations, BoundarySeqO>
{
    open spec fn seq_valid(&self) -> bool {
        &&& self.boundary_seq_marshalling.valid()
        &&& self.eltm.valid()
        &&& LengthIntObligations::spec_fits_in_this(self.boundary_seq_marshalling.total_size as int)
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool {
        self.boundary_seq_marshalling.lengthable(data)
    }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        self.boundary_seq_marshalling.length(data)
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
//         assert( self.seq_valid() );
        assert( self.boundary_seq_marshalling.seq_valid() );    // TODO remove; issue #1150
        let out = self.boundary_seq_marshalling.try_length(dslice, data);
        assert( out is Some ==> out.unwrap() as int == self.length(dslice@.i(data@)) );    // TODO remove; issue #1150
        out
    }

    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        &&& self.lengthable(data)
        &&& idx < self.length(data)
        &&& self.element_gettable(data, idx)
        &&& (0 < idx ==> self.element_gettable(data, idx-1))
        &&& 0 <= self.element_data_begin(data, idx) <= self.element_data_end(data, idx) <= self.total_size as int <= data.len()
    }

    open spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    {
        dslice.subslice(
            self.element_data_begin(dslice.i(data), idx),
            self.element_data_end(dslice.i(data), idx))
    }

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    {}

    // TODO: want to use common impl in SeqMarshalling, but can't refactor due to eltm dispatch problem
    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    {
        self.eltm.parsable(self.get_data(data, idx))
    }

    // TODO: want to use common impl in SeqMarshalling, but can't refactor due to eltm dispatch problem
    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    {
        self.eltm.parse(self.get_data(data, idx))
    }
    
    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let ghost gdata = dslice@.i(data@);
        let olen = self.try_length(dslice, data);
        if olen.is_some() && idx < self.exec_max_length() && idx < olen.unwrap() {
            proof {
                self.boundary_seq_easy_marshalling();
                self.boundary_ints_fit_in_usize();
            }
            let start = self.exec_element_data_begin(dslice, data, idx);
            let end = self.exec_element_data_end(dslice, data, idx);
            if start <= end && end <= self.total_size && self.total_size <= dslice.len() {
                Some(dslice.subslice(start, end))
            } else {
                None
            }
        } else {
            None
        }
    }

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    {
        let start = self.exec_element_data_begin(dslice, data, idx);
        let end = self.exec_element_data_end(dslice, data, idx);
        dslice.subslice(start, end)
    }

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    {
        let oeslice = self.try_get(dslice, data, idx);
        match oeslice {
            None => {
                assert( !self.gettable(dslice@.i(data@), idx as int) );
                None
            }
            Some(eslice) => {
                proof {
                    // TODO(verus): lament of spec ensures
                    self.get_ensures(dslice@, data@, idx as int);
                    SpecSlice::all_ensures::<u8>();
                    // extn equal trigger
                    assert( eslice@.i(data@) =~= self.get_data(dslice@.i(data@), idx as int) );
                }
                let oelt = self.eltm.try_parse(&eslice, data);
                oelt
            }
        }
    }

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    {
        // TODO duplicates same method from Resizable*
        assume( false );    // borrow/refactor proof from Resizable
        let eslice = self.exec_get(dslice, data, idx);
        self.eltm.exec_parse(&eslice, data)
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn elt_marshallable(&self, elt: DVElt) -> bool
    {false}

    open spec fn settable(&self, data: Seq<u8>, idx: int, value: DVElt) -> bool
    {false}

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &Elt) -> (s: bool)
    {false}

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    {}

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    open spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool { false }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool) { false }

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize) {}

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

}


} //verus!
