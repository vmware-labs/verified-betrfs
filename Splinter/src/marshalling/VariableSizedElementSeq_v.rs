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
// use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::*;
// use crate::marshalling::math_v::*;

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
    EltFormat: Marshal,
    BdyType: IntFormattable,
    LenType: IntFormattable,
> {
    // The values we're marshalling and how to marshall each.
    // This field ports eltCfg.
    pub eltf: EltFormat,
    // This field ports bsmCfg.
    pub bdyf: ResizableUniformSizedElementSeqMarshalling<IntFormat<BdyType>, LenType>,
}


impl <
    EltFormat: Marshal,
    BdyType: IntFormattable,
    LenType: IntFormattable,
>
    VariableSizedElementSeqMarshalling<EltFormat, BdyType, LenType>
{
    pub fn new(eltf: EltFormat, bdy_int_format: IntFormat<BdyType>, lenf: IntFormat<LenType>, total_size: usize) -> (s: Self)
    {
        assume( false ); // left off here
        Self{ eltf: eltf, bdyf: ResizableUniformSizedElementSeqMarshalling::new(bdy_int_format, lenf, total_size) }
    }

    // The pre-allocated capacity (bytes) is just whatever we preallocated to the
    // boundary seq array.
    // The idea is that we contain a boundary seq that is allocated to the total
    // size. Each record we append gobbles up a bit of the "free space" at the
    // far end of that allocation; we're careful (TODO: where?) not to let
    // the used portion of the boundary array overlap with the used portion
    // holding the elements.
    // If we only append 0-length records, the boundary seq array could grow to fill the entire
    // allocation. If we append one huge element, it can use all the space except the length field
    // and that first boundary entry that records the length of that element.

    pub open spec fn total_size(&self) -> usize {   // TODO maybe return an int?
        self.bdyf.total_size
    }

    pub exec fn exec_total_size(&self) -> (sz: usize)
        ensures sz == self.total_size()
    {
        self.bdyf.total_size
    }

    pub open spec fn max_length(&self) -> usize {
        self.bdyf.max_length()
    }

    exec fn exec_max_length(&self) -> (out: usize)
        requires self.seq_valid()
        ensures out == self.max_length()
    {
        self.bdyf.exec_max_length()
    }

    // This ports BoundaryElementGettable
    pub open spec fn element_gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        &&& self.bdyf.gettable(data, idx)
        &&& self.bdyf.elt_parsable(data, idx)
    }

    pub open spec fn element_data_begin(&self, data: Seq<u8>, idx: int) -> int
    {
        self.bdyf.get_elt(data, idx)
    }

    pub exec fn exec_element_data_begin(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (start: usize)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.element_gettable(dslice@.i(data@), idx as int),
    ensures start as int == self.element_data_begin(dslice@.i(data@), idx as int)
    {
        assume( false ); // left off here
        let istart: BdyType = self.bdyf.exec_get_elt(dslice, data, idx);
//         proof {
//             BdyType::as_int_ensures();
//             self.boundary_ints_fit_in_usize();
//         }
//         assert( BdyType::as_int(istart) == self.element_data_begin(dslice@.i(data@), idx as int) );
        BdyType::to_usize(istart)
    }

    pub open spec fn element_data_end(&self, data: Seq<u8>, idx: int) -> int
    {
        if idx == 0 { self.total_size() as int }
        else { self.bdyf.get_elt(data, idx - 1) }
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
        assume( false ); // left off here
//         proof {
//             BdyType::as_int_ensures();
//             self.boundary_ints_fit_in_usize();
//         }
        if 0 < idx {
            let iend = self.bdyf.exec_get_elt(dslice, data, idx - 1);
            BdyType::to_usize(iend)
        } else {
            self.exec_total_size()
        }
    }

    // This is lies, but it papers over a module type specialization in the Dafny code that we
    // haven't shoehorned into this trait system yet.
    proof fn boundary_seq_easy_marshalling(&self)
    ensures
        forall |data| self.bdyf.eltf.parsable(data)
    {
        assume(false);
    }

//     // Here's another obligation we'd like to place on the choice of boundary
//     // int: don't make me deal with counting things that are beyond the
//     // platform usize.
//     proof fn boundary_ints_fit_in_usize(&self)
//         ensures forall |i| #![auto] BdyType::spec_this_fits_in_usize(BdyType::as_int(i))
//     {
//         assume(false);
//     }

    pub open spec fn size_of_length_field(&self) -> usize
    {
        LenType::uniform_size()
    }

    pub open spec fn size_of_boundary_entry(&self) -> usize
    {
        BdyType::uniform_size()
    }

    // Why isn't this method defined on ResizableSeq, instead of pieced together here?
    pub open spec fn size_of_table(&self, len: int) -> int
    {
        self.size_of_length_field() as int + len * self.size_of_boundary_entry() as int
    }

    pub open spec fn tableable(&self, data: Seq<u8>) -> (b: bool)
    recommends self.seq_valid()
    {
        self.bdyf.parsable(data)
    }

    pub proof fn tableable_ensures(&self, data: Seq<u8>)
    requires self.seq_valid()
    ensures
        self.tableable(data) ==> self.lengthable(data),
        self.tableable(data) ==> self.size_of_table(self.length(data)) <= self.total_size() as int,
    {
        if self.bdyf.parsable(data) {
            self.bdyf.parsable_length_bounds(data);
        }
        if self.tableable(data) {
            self.bdyf.parsable_length_bounds(data);
            assert( self.bdyf.parsable(data) );
            assert( self.lengthable(data) );

            assert( self.length(data) == self.bdyf.length(data) );

            assert( self.size_of_table(self.length(data)) ==
                LenType::uniform_size() as int + self.length(data) * BdyType::uniform_size() as int );
            let bsm = self.bdyf;
            assert( 
                bsm.length(data) * BdyType::uniform_size() as int
                    <= bsm.total_size as int - bsm.size_of_length_field() as int );
            assert( 
                bsm.size_of_length_field() as int + bsm.length(data) * BdyType::uniform_size() as int
                    <= bsm.total_size as int );
            assert( bsm.size_of_length_field() == LenType::uniform_size() as int );
            assert( bsm.length(data) == self.length(data) );

            assert( bsm.total_size as int <= self.total_size() as int );
                
                    
            assert( self.size_of_table(self.length(data)) <= self.total_size() as int );
        }
    }

    pub open spec fn table(&self, data: Seq<u8>) -> Seq<int>
    recommends self.seq_valid(), self.tableable(data)
    {
        self.bdyf.parse(data)
    }

    // A well-formed boundary seq table should be in reverse sequence
    pub open spec fn valid_table(&self, data: Seq<u8>) -> (b: bool)
    recommends self.seq_valid(), self.tableable(data)
    {
        let t = self.table(data);
        // Every element has non-negative length
        &&& forall |i, j| 0 <= i <= j < t.len() ==> t[j] <= t[i]
        // The last element ends before the end of the VSES total byte allocation
        &&& 0 < t.len() ==> t[0] <= self.total_size() as int
        // The first element starts beyond the end of the table itself.
        &&& 0 < t.len() ==> self.size_of_table(t.len() as int) <= t.last()
    }

    // index into buffer where element data begins (growing from end)
    pub open spec fn elements_start(&self, data: Seq<u8>) -> int {
        7
//         let t = self.table(data);
//         if t.len() == 0 { self.total_size() }
//         else { t.last() }
//         oh left off here
    }
}

impl <
    EltFormat: Marshal,
    BdyType: IntFormattable,
    LenType: IntFormattable,
>
    SeqMarshal< EltFormat::DV, EltFormat::U >
    for
    VariableSizedElementSeqMarshalling<EltFormat, BdyType, LenType>
{
    open spec fn seq_valid(&self) -> bool {
        &&& self.eltf.valid()
        &&& self.bdyf.valid()
        &&& self.bdyf.total_size <= LenType::max()
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool {
        self.bdyf.lengthable(data)
    }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        self.bdyf.length(data)
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
//         assert( self.seq_valid() );
//         assert( self.bdyf.seq_valid() );    // TODO remove; issue #1150
        assume( false );    // left off here
        assert( self.bdyf.seq_valid() );
        let out = self.bdyf.try_length(dslice, data);
        assert( out is Some ==> out.unwrap() as int == self.length(dslice@.i(data@)) );    // TODO remove; issue #1150
        out
    }

    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        &&& self.lengthable(data)
        &&& idx < self.length(data)
        &&& self.element_gettable(data, idx)
        &&& (0 < idx ==> self.element_gettable(data, idx-1))
        &&& 0 <= self.element_data_begin(data, idx) <= self.element_data_end(data, idx) <= self.total_size() as int <= data.len()
    }

    open spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    {
        dslice.subslice(
            self.element_data_begin(dslice.i(data), idx),
            self.element_data_end(dslice.i(data), idx))
    }

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    {}

    // TODO: want to use common impl in SeqMarshal, but can't refactor due to eltf dispatch problem
    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    {
        self.eltf.parsable(self.get_data(data, idx))
    }

    // TODO: want to use common impl in SeqMarshal, but can't refactor due to eltf dispatch problem
    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: EltFormat::DV)
    {
        self.eltf.parse(self.get_data(data, idx))
    }
    
    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        assume( false ); // left off here
        let ghost gdata = dslice@.i(data@);
        let olen = self.try_length(dslice, data);
        if olen.is_some() && idx < self.exec_max_length() && idx < olen.unwrap() {
            proof {
                self.boundary_seq_easy_marshalling();
//                 self.boundary_ints_fit_in_usize();
            }
            let start = self.exec_element_data_begin(dslice, data, idx);
            let end = self.exec_element_data_end(dslice, data, idx);
            let total_size = self.exec_total_size();
            if start <= end && end <= total_size && total_size <= dslice.len() {
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

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<EltFormat::U>)
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
                let oelt = self.eltf.try_parse(&eslice, data);
                oelt
            }
        }
    }

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: EltFormat::U)
    {
        let eslice = self.exec_get(dslice, data, idx);
        proof {
            // TODO(verus): lament of spec ensures
            self.get_ensures(dslice@, data@, idx as int);
            SpecSlice::all_ensures::<u8>();
            // extn equal trigger
            assert( eslice@.i(data@) =~= self.get_data(dslice@.i(data@), idx as int) );
        }
        self.eltf.exec_parse(&eslice, data)
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    // Disallowed for VariableSizedElementSeq, since that would involve
    // creating holes or overlaps.
    /////////////////////////////////////////////////////////////////////////

    open spec fn elt_marshallable(&self, elt: EltFormat::DV) -> bool
    {false}

    open spec fn settable(&self, data: Seq<u8>, idx: int, value: EltFormat::DV) -> bool
    {false}

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &EltFormat::U) -> (s: bool)
    {false}

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &EltFormat::U)
    {}

    /////////////////////////////////////////////////////////////////////////
    // resizing
    // Disallowed for VariableSizedElementSeq; the size is advanced
    // exclusively through append operations.
    /////////////////////////////////////////////////////////////////////////

    open spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool { false }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool) { false }

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize) {}

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////

    // well_formed seems to be an append-specific concept; rename.
    open spec fn well_formed(&self, data: Seq<u8>) -> bool {
        &&& self.tableable(data)
        &&& self.valid_table(data)
    }

    proof fn well_formed_ensures(&self, data: Seq<u8>)
    {
    }

    open spec fn appendable(&self, data: Seq<u8>, value: EltFormat::DV) -> bool { false }

    open spec fn appends(&self, data: Seq<u8>, value: EltFormat::DV, newdata: Seq<u8>) -> bool { false }

    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool) {
        assume( false );
        false
    }

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: &EltFormat::U) -> (r: bool) {
        assume( false );
        false
    }

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: &EltFormat::U) {
        assume( false );
    }

}


} //verus!
