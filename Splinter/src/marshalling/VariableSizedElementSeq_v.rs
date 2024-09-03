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
use crate::marshalling::UniformSized_v::*;
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

pub struct VariableSizedElementSeqFormat <
    EltFormat: Marshal,
    BdyType: IntFormattable,
    LenType: IntFormattable,
> {
    // The values we're marshalling and how to marshall each.
    // This field ports eltCfg.
    pub eltf: EltFormat,

    // This field ports bsmCfg.
    // The bdyf knows "how big" the space we've allocated is, and we "steal"
    // space from the bdyf allocation to store elements at the "end" of the
    // overall allocated space.
    pub bdyf: ResizableUniformSizedElementSeqFormat<IntFormat<BdyType>, LenType>,
}


impl <
    EltFormat: Marshal,
    BdyType: IntFormattable,
    LenType: IntFormattable,
>
    VariableSizedElementSeqFormat<EltFormat, BdyType, LenType>
{
    pub fn new(eltf: EltFormat, bdy_int_format: IntFormat<BdyType>, lenf: IntFormat<LenType>, total_size: usize) -> (s: Self)
        requires LenType::uniform_size() <= total_size
    {
        Self{ eltf: eltf, bdyf: ResizableUniformSizedElementSeqFormat::new(bdy_int_format, lenf, total_size) }
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
        let istart: BdyType = self.bdyf.exec_get_elt(dslice, data, idx);
        proof { BdyType::deepv_is_as_int_forall(); }
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
        if 0 < idx {
            let iend = self.bdyf.exec_get_elt(dslice, data, idx - 1);
            proof { BdyType::deepv_is_as_int_forall(); }
            BdyType::to_usize(iend)
        } else {
            self.exec_total_size()
        }
    }

    // This is lies, but it papers over a module type specialization in the Dafny code that we
    // haven't shoehorned into this trait system yet.
//     proof fn boundary_seq_easy_marshalling(&self)
//     ensures
//         forall |data| self.bdyf.eltf.parsable(data)
//     {
//     }

//     // Here's another obligation we'd like to place on the choice of boundary
//     // int: don't make me deal with counting things that are beyond the
//     // platform usize.
//     proof fn boundary_ints_fit_in_usize(&self)
//         ensures forall |i| #![auto] BdyType::spec_this_fits_in_usize(BdyType::as_int(i))
//     {
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
        let t = self.table(data);
        if t.len() == 0 { self.total_size() as int }
        else { t.last() }
    }

    pub open spec fn free_space(&self, data: Seq<u8>) -> int
    recommends
        self.seq_valid(),
        self.tableable(data),
        self.valid_table(data),
    {
        self.elements_start(data) - self.size_of_table(self.length(data))
    }

    // TODO hey wait this is just elements_start
    spec fn upper_bound(&self, data: Seq<u8>) -> int
    {
        let len = self.length(data);
        if len == 0 {
            self.total_size() as int
        }
        else {
            self.bdyf.get_elt(data, len - 1)
        }
    }

    // exec_appendable and exec_append both need these two bits of info
    exec fn exec_length_and_upper_bound(&self, dslice: &Slice, data: &Vec<u8>) -> (len_and_bound: (usize, usize))
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.lengthable(dslice@.i(data@)),
        self.well_formed(dslice@.i(data@)),
    ensures
        len_and_bound.0 == self.length(dslice@.i(data@)),
        len_and_bound.1 == self.upper_bound(dslice@.i(data@)),
    {
        proof { BdyType::deepv_is_as_int_forall(); }
        let len = self.exec_length(dslice, data);

        let upper_bound =
            if len == 0 {
                self.exec_total_size()
            }
            else {
                BdyType::to_usize(self.bdyf.exec_get_elt(dslice, data, len - 1))
            };
        (len, upper_bound)
    }

    spec fn append_offset(&self, data: Seq<u8>, value: EltFormat::DV) -> int
    recommends
        self.seq_valid(),
        self.lengthable(data),
        self.well_formed(data),
        self.eltf.marshallable(value),
        self.appendable(data, value),
    {
        self.upper_bound(data) - self.eltf.spec_size(value)
    }

    proof fn appendable_implies_bdyf_appendable(&self, data: Seq<u8>, value: EltFormat::DV)
    requires
        self.seq_valid(),
        self.well_formed(data),
        self.eltf.marshallable(value),
        self.appendable(data, value),
    ensures
        self.length(data) + 1 < usize::MAX,
        self.length(data) + 1 < BdyType::max(),
        self.bdyf.appendable(data, self.append_offset(data, value))
    {
        assume(false); // TODO left off here
    }

    // Show that, if the old data table is a prefix of the new,
    // both data agree on all the elements in the old table.
    proof fn elements_identity(self, data: Seq<u8>, newdata: Seq<u8>)
        // TODO left off here
    ensures
        forall |i| self.gettable(data, i) ==> self.gettable(newdata, i),
        forall |i| self.gettable(data, i) ==> self.get_data(newdata, i) == self.get_data(data, i),
    {
        assume(false); // TODO left off here
    }

    // The tricky bit in exec_append is that the bdyf array doesn't change meaning
    // when we write the datum because, even though it occupies space
    // in the capacity of self.bdyf, it doesn't actually interfere
    // with the resident values.
    proof fn table_identity(&self, data: Seq<u8>, newdata: Seq<u8>)
        // TODO left off here
    ensures
        self.tableable(newdata),
        self.table(newdata) == self.table(data),
    {
        assume(false); // TODO left off here
    }

    // TODO move somewhere sane
    proof fn lemma_seq_slice_slice(data: Seq<u8>, i: int, j: int, k: int, l: int)
    requires
        0<=i<=j<=data.len(),
        0<=k<=l<=j-i,
    ensures
        data.subrange(i,j).subrange(k,l) =~= data.subrange(i+k, i+l)
    {
    }
}

impl <
    EltFormat: Marshal,
    BdyType: IntFormattable,
    LenType: IntFormattable,
>
    SeqMarshal< EltFormat::DV, EltFormat::U >
    for
    VariableSizedElementSeqFormat<EltFormat, BdyType, LenType>
{
    open spec fn seq_valid(&self) -> bool {
        &&& self.eltf.valid()
        &&& self.bdyf.seq_valid()
        &&& self.bdyf.total_size <= LenType::max()
        &&& self.bdyf.total_size <= BdyType::max()
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
        let ghost gdata = dslice@.i(data@);
        let olen = self.try_length(dslice, data);
        if olen.is_some() && idx < self.exec_max_length() && idx < olen.unwrap() {
            let ghost sdata = dslice@.i(data@);
            proof {

                // Painfully re-discovered spec ensures on ::all
                SpecSlice::all_ensures::<u8>();

                self.bdyf.get_ensures(SpecSlice::all(sdata), sdata, idx as int);

                // TODO(jonh) file issue about triggering for axiom_seq_subrange_len
                assert( self.element_gettable(dslice@.i(data@), idx as int) );
                if 0 < idx {
                    self.bdyf.get_ensures(SpecSlice::all(sdata), sdata, idx - 1 as int);
                    assert( self.element_gettable(dslice@.i(data@), idx - 1 as int) );
                }
            }
            let start = self.exec_element_data_begin(dslice, data, idx);
            proof {
                if 0 < idx {
                    self.bdyf.get_ensures(SpecSlice::all(sdata), sdata, idx - 1 as int);
                }
            }
            let end = self.exec_element_data_end(dslice, data, idx);

            let total_size = self.exec_total_size();
            if start <= end && end <= total_size && total_size <= dslice.len() {
                assert( self.gettable(dslice@.i(data@), idx as int) );
                Some(dslice.subslice(start, end))
            } else {
                assert( !self.gettable(dslice@.i(data@), idx as int) );
                None
            }
        } else {
            assert( !self.gettable(dslice@.i(data@), idx as int) );
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

    // This definition is also used in exec_appendable.
    open spec fn elt_marshallable(&self, elt: EltFormat::DV) -> bool
    {
        self.eltf.marshallable(elt)
    }

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

    open spec fn appendable(&self, data: Seq<u8>, value: EltFormat::DV) -> bool {
        // We have room for one more bdy entry plus the new datum
        BdyType::uniform_size() + self.eltf.spec_size(value) as nat
            <= self.free_space(data)
    }

    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool) {
        let ghost idata = dslice@.i(data@);
        proof {
            BdyType::deepv_is_as_int_forall();
        }

        match self.bdyf.try_parse(dslice, data) {
            None => false,
            Some(tbl) => {
                let len = tbl.len();
                if len == 0 {
                    return true;
                }
                let size_of_length_field = LenType::exec_uniform_size();
                let size_of_boundary_entry = BdyType::exec_uniform_size();

                // TODO: index_bounds_facts being public is a bit yucky
                proof {
                    self.bdyf.parsable_length_bounds(idata);
                    assert( tbl.len() == self.table(idata).len() );

                    // trigger to learn len-1 < self.bdyf.max_length()
                    assert( self.bdyf.gettable(idata, len as int - 1) );

                    self.bdyf.index_bounds_facts(len as int - 1);
                }

                let tbsz = size_of_length_field + len * size_of_boundary_entry;
                if BdyType::to_usize(tbl[len-1]) < tbsz {
                    // Fails valid_table() third conjunct
                    return false;
                }
                if self.exec_total_size() < BdyType::to_usize(tbl[0]) {
                    // Fails valid_table() second conjunct
                    return false;
                }

                let mut i:usize = 0;
                while i < len - 1
                invariant
                    0 <= i < len,
                    forall |ip, jp| 0 <= ip <= jp <= i ==> tbl[jp] as int <= tbl[ip] as int
                {
                    assert( tbl[i as int] as int == self.table(idata)[i as int] );  // trigger
                    assert( tbl[i as int + 1] as int == self.table(idata)[i as int +1] );   // trigger
                    if BdyType::to_usize(tbl[i]) < BdyType::to_usize(tbl[i+1]) {
                        return false;
                    }
                    i += 1;
                }
                true
            }
        }
    }

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: &EltFormat::U) -> (r: bool) {
        let (len, upper_bound) = self.exec_length_and_upper_bound(dslice, data);

        // TODO factor out this repeated code from exec_well_formed
        let ghost idata = dslice@.i(data@);
        proof {
            self.bdyf.parsable_length_bounds(idata);
            BdyType::deepv_is_as_int_forall();
        }
        let size_of_length_field = LenType::exec_uniform_size();
        let size_of_boundary_entry = BdyType::exec_uniform_size();
        let table_size = size_of_length_field + len * size_of_boundary_entry;

        let free_space = upper_bound - table_size;
        let elt_size = self.eltf.exec_size(value);
        size_of_boundary_entry <= free_space && elt_size <= free_space - size_of_boundary_entry
    }

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: &EltFormat::U) {
        let ghost idata = dslice@.i(data@);
        proof {
            BdyType::deepv_is_as_int_forall();
            self.appendable_implies_bdyf_appendable(idata, value.deepv());
            SpecSlice::all_ensures::<u8>(); // sigh
        }
        let (len, upper_bound) = self.exec_length_and_upper_bound(dslice, data);
        let size = self.eltf.exec_size(value);
        assert( size <= upper_bound );
        let start: usize = upper_bound - size;
        ////////////////////////////////////////////////////////////
        // Write the value into its empty slot
        ////////////////////////////////////////////////////////////
        let after_elt = self.eltf.exec_marshall(value, data, dslice.start + start);

        // Snapshot the data after writing the new datum but before appending the boundary table
        let ghost middle_data_raw = data@;
        let ghost middle_data = dslice@.i(data@);
        proof {
        // middle / dummy proof
        // elements_identity
            // we didn't break the table
            self.table_identity(idata, middle_data);
            // we didn't break any of the old elements
            self.elements_identity(idata, middle_data);
            assert( self.well_formed(middle_data) );
            assert( self.bdyf.appendable(middle_data, start as int) );
        }

        ////////////////////////////////////////////////////////////
        // Append the new boundary element
        ////////////////////////////////////////////////////////////
        self.bdyf.exec_append(dslice, data, &BdyType::from_usize(start));

        let ghost newdata = dslice@.i(data@);
        let ghost raw_new_data = data@;
        let ghost newslot = self.length(idata); // TODO rename from oldlen in SeqMarshalling


        proof {
        // another block of proof
            self.elements_identity(middle_data, newdata);
        }

        assert forall |i| i != newslot implies self.preserves_entry(idata, i, newdata) by {
        }
        assert( self.gettable(newdata, newslot) ) by {
            let oldlen = self.bdyf.length(middle_data);
            if 0 < oldlen {
                assert( self.bdyf.preserves_entry(middle_data, oldlen-1, newdata) ); // trigger
            }
        }

        // bdy points to the right range
        assume( self.get_data(newdata, newslot) == newdata.subrange(dslice.start + start, after_elt as int) );
        // range has the right stuff in it
        assert( self.eltf.parsable(middle_data_raw.subrange(dslice.start + start as int, after_elt as int)) );
//         assert( newdata.subrange(dslice.start + start, after_elt as int)
//             == middle_data_raw.subrange(dslice.start + start, after_elt as int)
//             );
        assert( self.eltf.parsable(middle_data_raw.subrange(dslice.start + start, after_elt as int)) );

        let ghost nslice = SpecSlice::all(newdata);

        // Hey, this is the data that shouldn't have been touched by the second bdyf write.
        // elements_identity doesn't help us, because newslot wasn't yet gettable at middle.
        // bdyf.exec_append's agree_beyond_slice doesn't help us, because we handed it the
        // entire slice.
        // bdyf.append's preserves_entry doesn't help us, because these bytes beyond the appended
        // bdy element don't hold bdyf gettable fields.
        // THE MAGIC is MarshalledAccessors.i.dfy:1138
        assert( self.bdyf.untampered_bytes(dslice@, middle_data_raw, data@) );
        proof {
            assert( self.bdyf.size_of_length_field() == self.size_of_length_field() as int );
            assert( self.bdyf.length(newdata) == self.length(newdata) );
            assert( self.bdyf.eltf.uniform_size() == self.size_of_boundary_entry() as int );

            assert( self.size_of_table(self.length(newdata))
                ==
                self.bdyf.size_of_length_field() + self.bdyf.length(newdata) * self.bdyf.eltf.uniform_size() );

            assert( self.bdyf.first_unused_byte(dslice@, raw_new_data)
                ==
                dslice@.start + self.bdyf.size_of_length_field() + self.bdyf.length(dslice@.i(raw_new_data)) * self.bdyf.eltf.uniform_size() );

            assert( self.bdyf.first_unused_byte(dslice@, raw_new_data)
                == dslice.start + self.size_of_table(self.length(newdata)) );
            assert( self.elements_start(newdata) == self.upper_bound(newdata) );
            assert( self.length(idata) + 1 == self.length(newdata) );
            
            assert( self.length(idata) * self.size_of_boundary_entry() + self.size_of_boundary_entry()
                == (self.length(idata) + 1) * self.size_of_boundary_entry() ) by (nonlinear_arith);

            assert( self.size_of_table(self.length(idata)) + BdyType::uniform_size()
                    == self.size_of_table(self.length(newdata)) );

            // This offset math gets confusing because some values are based at the start of the
            // slice, others are indices into the raw data (already have the slice.start added in).
            //
            // start is relative to the slice.
            // first_unused_byte is relative to the raw data
            // after_elt is relative to the raw data

            assert( self.bdyf.first_unused_byte(dslice@, raw_new_data) <=  dslice.start + start );
            assert( dslice.start + start <= after_elt );
            assert( after_elt <= data@.len() );

            // The value we wrote into the unused region wasn't stomped by the
            // bdy append
            assert( middle_data_raw.len() == data@.len() );
            let msub = middle_data_raw.subrange(dslice.start + start, after_elt as int);
            let dsub = data@.subrange(dslice.start + start, after_elt as int);
            assert( msub.len() == dsub.len() );
            assert forall |i| 0 <= i < msub.len() implies msub[i] == dsub[i] by {
                assert( msub[i] == middle_data_raw[dslice.start + start + i] );
                assert( middle_data_raw[dslice.start + start + i]
                    == middle_data[start + i]
                    );
                assert( dsub[i] == data@[dslice.start + start + i] );
                assert( data@[dslice.start + start + i] == newdata[start + i] );

                // self.bdyf.untampered_bytes
        // forall |i| self.first_unused_byte(dslice, newdata) <= i < newdata.len() ==> olddata[i] == newdata[i]
                let x = dslice.start + start + i;
                let fub = dslice.start + self.bdyf.size_of_length_field() + self.bdyf.length(newdata) * self.bdyf.eltf.uniform_size();

                assert( upper_bound == self.upper_bound(idata) );
                assert( self.free_space(idata) == upper_bound - self.size_of_table(self.length(idata)) );
                assert( start == upper_bound - size );
                assert( self.bdyf.eltf.uniform_size() + size <= self.free_space(idata) );

                let bdysize = BdyType::uniform_size();
                let lensz = LenType::uniform_size();
                let datasize = size;
                let ub = upper_bound;
                let oldlen = self.length(idata);
                let midlen = self.length(middle_data);
                assert( oldlen == midlen );
                let newlen = self.length(newdata);

                self.appends(middle_data, value.deepv(), newdata);
                assert( self.bdyf.length(newdata) == self.bdyf.length(middle_data) + 1 );
                assert( self.length(newdata) == self.length(middle_data) + 1 );

                assert( newlen == oldlen + 1 );
                assert( bdysize + lensz + oldlen * bdysize <= start );
                assert( lensz + newlen * bdysize <= start );


                assert( self.bdyf.size_of_length_field() + self.bdyf.length(newdata) * self.bdyf.eltf.uniform_size() <= start );
                assert( fub <= x );
                assert( self.bdyf.first_unused_byte(dslice@, data@) <= x );
                assert( x < data@.len() );
                assert( middle_data_raw[x] == data@[x] );
                assert( middle_data[start + i] == newdata[start + i] );
            }
            assert( msub == dsub );
        }


        // trigger all_ensures
        assert( self.element_data_begin(nslice.i(newdata), newslot) == start );

        // trigger
        // TODO(verus): all I did here was intros element_data_end. That should never be necessary
        // to tickle a trigger.
        assert(
            if newslot == 0 { self.total_size() as int }
            else { self.bdyf.get_elt(newdata, newslot - 1) }
            == self.element_data_end(newdata, newslot)
        );
        // trigger
        assume( self.element_data_end(newdata, newslot) == after_elt - dslice.start );

//         assert( self.element_data_end(nslice.i(newdata), newslot) == after_elt - dslice.start );

        assert(
            data@.subrange(dslice@.start + start, after_elt as int)
            == self.get_data(newdata, newslot)
        );

//         assert(
//             nslice.subslice(
//                 self.element_data_begin(nslice.i(newdata), newslot),
//                 self.element_data_end(nslice.i(newdata), newslot)).i(newdata)
//             ==
//             self.get(SpecSlice::all(newdata), newdata, newslot).i(newdata)
//         );
// 
//         assert(
//             self.get(SpecSlice::all(newdata), newdata, newslot).i(newdata)
//             == self.get_data(newdata, newslot)
//             );
        assert( self.eltf.parsable(self.get_data(newdata, newslot)) );
        assert( self.elt_parsable(newdata, newslot) );

        assert( self.get_elt(newdata, newslot) == value.deepv() );
        assume( self.tableable(newdata) );
        assume( self.valid_table(newdata) );
        assert( self.well_formed(newdata) );
    }

}


} //verus!
