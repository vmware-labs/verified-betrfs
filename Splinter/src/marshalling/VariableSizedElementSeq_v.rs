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
use crate::marshalling::math_v::*;

verus! {

// A VariableSizedElementSeqMarshalling conveys a variable number of variably-sized elements.
// You can't Set into one of these (because we're not gonna do de-fragmentation), only append.
// Layout is:
//     a preallocated capacity
//     an array of boundary pointers that describe where to find each element [i]
//     some free space
//     storage for the elements, allocated from the end towards the middle.
//
// This layout this means the data structure can use the free space either
// for more boundary pointers (if the data are small) or more data (if there are fewer,
// bigger data items).
//
// In the implementation, the `bdyf` object "owns" the entire preallocated capacity, even
// though we're tucking element data into the free space at the end of its allocation.
// There's a tight coupling between this object and ResizableUniformSizedElementSeqFormat's
// implementation, exploited in the elements_identity and table_identity proofs that show
// that appending to the boundary table doesn't smash any elements and stuffing extra
// elements into the free space doesn't smash the table.

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
    requires
        LenType::uniform_size() <= total_size,
        eltf.valid(),
        bdy_int_format.valid(),
        lenf.valid(),
        total_size <= BdyType::max(),
        total_size <= LenType::max(),
    ensures
        s.seq_valid(),
        s.total_size() == total_size,
    {
        Self{ eltf: eltf, bdyf: ResizableUniformSizedElementSeqFormat::new(bdy_int_format, lenf, total_size) }
    }

    // Initialize a data region to represent a count of zero records
    pub exec fn initialize(&self, dslice: &Slice, data: &mut Vec<u8>)
    requires
        self.seq_valid(),
        dslice@.valid(old(data)@),
        self.total_size() <= dslice@.len(),
    ensures
        data.len() == old(data).len(),
        self.well_formed(dslice@.i(data@)),
        self.lengthable(dslice@.i(data@)),
        self.length(dslice@.i(data@)) == 0,
        dslice@.agree_beyond_slice(old(data)@, data@),
    {
        self.bdyf.initialize(dslice, data);
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
        self.bdyf.spec_max_length()
    }

    exec fn exec_max_length(&self) -> (out: usize)
        requires self.seq_valid()
        ensures out == self.max_length()
    {
        self.bdyf.max_length
    }

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
    ensures
        start as int == self.element_data_begin(dslice@.i(data@), idx as int),
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
        if self.tableable(data) {
            self.bdyf.parsable_length_bounds(data);
        }
    }

    pub open spec fn table(&self, data: Seq<u8>) -> Seq<int>
    recommends self.seq_valid(), self.tableable(data)
    {
        self.bdyf.parse(data)
    }

    // A well-formed boundary seq table should be in reverse order
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

    // exec_appendable and exec_append both need these two bits of info
    exec fn exec_length_and_upper_bound(&self, dslice: &Slice, data: &Vec<u8>) -> (len_and_bound: (usize, usize))
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.lengthable(dslice@.i(data@)),
        self.well_formed(dslice@.i(data@)),
    ensures
        len_and_bound.0 == self.length(dslice@.i(data@)),
        len_and_bound.1 == self.elements_start(dslice@.i(data@)),
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
        self.elements_start(data) - self.eltf.spec_size(value)
    }

    proof fn appendable_implies_bdyf_appendable(&self, data: Seq<u8>, value: EltFormat::DV)
    requires
        self.seq_valid(),
        self.well_formed(data),
        self.eltf.marshallable(value),
        self.appendable(data, value),
    ensures
        self.bdyf.appendable(data, self.append_offset(data, value))
    {

        /*
    // Have
    open spec fn appendable(&self, data: Seq<u8>, value: EltFormat::DV) -> bool {
        // True if we have room for one more bdy entry plus the new datum
        BdyType::uniform_size() + self.eltf.spec_size(value) as nat
            <= self.free_space(data)
        == self.elements_start(data) - self.size_of_table(self.length(data))
    }
        //want
        &&& self.length(data) < self.spec_max_length() as nat
        &&& self.eltf.spec_size(value) == self.eltf.uniform_size()

        // dafny does this computation in a u64; why is it okay with overflow!?
        &&& self.length(data) + 1 <= LenType::max()

        spec_max_length is based on bdyf.total_size

        SOT = LEN * BDYSZ + LENSZ
        BDYSZ + VSZ <= ELST - SOT
        ELST <= TOTSZ
        MAXL = (TOTSZ - LENSZ) / BDYSZ

        BDYSZ + VSZ <= TOTSZ - SOT
        BDYSZ + VSZ <= TOTSZ - LEN * BDYSZ - LENSZ
        if MAXL <= LEN {
            BDYSZ + VSZ <= TOTSZ - MAXL * BDYSZ - LENSZ
            BDYSZ + VSZ <= TOTSZ - (TOTSZ - LENSZ) * BDYSZ - LENSZ
            BDYSZ + VSZ <= TOTSZ - BDYSZ * TOTSZ - BDYSZ * LENSZ - LENSZ
            BDYSZ + VSZ <= (1 - BDYSZ) * TOTSZ + (- BDYSZ - 1) * LENSZ
            BDYSZ <= (1 - BDYSZ) * TOTSZ + (- BDYSZ - 1) * LENSZ
            BDYSZ <= (1 - BDYSZ) * TOTSZ - (BDYSZ + 1) * LENSZ
            BDYSZ  + (BDYSZ + 1) * LENSZ <= (1 - BDYSZ) * TOTSZ
            (BDYSZ + 2) * LENSZ <= (1 - BDYSZ) * TOTSZ
        }
        */


        assume( false ); // LEFT OFF HERE
        assert( self.size_of_table(self.length(data)) == self.bdyf.length(data) );
        assert( self.elements_start(data) <= self.bdyf.total_size );

        assert( self.bdyf.length(data) < self.bdyf.spec_max_length() as nat );

        assume( self.bdyf.length(data) + 1 <= LenType::max() );

        // Discuss with Rob why these proofs weren't needed in Dafny?
        // TODO(jonh): urgent fix assumes
        assert( self.bdyf.appendable(data, self.append_offset(data, value)) );
    }

    // If the old data table is a prefix of the new, both data agree on all the elements in the old
    // table.
    proof fn elements_identity(self, data: Seq<u8>, newdata: Seq<u8>)
    requires
        self.seq_valid(),
        self.tableable(data),
        self.tableable(newdata),
        self.valid_table(data),
        self.valid_table(newdata),
        is_prefix(self.table(data), self.table(newdata)),
        newdata.skip(self.elements_start(data)) == data.skip(self.elements_start(data)),
    ensures
        forall |i| self.gettable(data, i) ==> self.gettable(newdata, i),
        forall |i| self.gettable(data, i) ==> self.get_data(newdata, i) == self.get_data(data, i),
    {
        // TODO(jonh): study and implement broadcasts. I wasted way too much time
        // discovering these missing spec-ensures.
        self.bdyf.length_ensures(data);
        self.bdyf.length_ensures(newdata);
        SpecSlice::all_ensures::<u8>();

        assert forall |i| self.gettable(data, i) implies {
            &&& self.gettable(newdata, i)
            &&& self.get_data(newdata, i) == self.get_data(data, i)
        } by {
            let dt = self.table(data);
            let nt = self.table(newdata);
            assert( nt.take(dt.len() as int)[i] == nt[i] ); // trigger
            if 0 < i {
                assert( nt.take(dt.len() as int)[i-1] == nt[i-1] ); // trigger
            }

            // trigger subrange axioms to appeal to skip requires
            let start = self.element_data_begin(data, i);
            let es = self.elements_start(data);
            let len = self.get_data(newdata, i).len();
            assert forall |k| 0 <= k < len implies
                self.get_data(newdata, i)[k] == self.get_data(data, i)[k] by {
                assert( self.get_data(data, i)[k] == data.skip(es)[start + k - es] );   // trigger
            }
            // trigger extn equality
            assert( self.get_data(newdata, i) == self.get_data(data, i) );
        }
    }

    // The tricky bit in exec_append is that the bdyf array doesn't change meaning
    // when we write the datum because, even though it occupies space
    // in the capacity of self.bdyf, it doesn't actually interfere
    // with the resident values.
    proof fn table_identity(&self, data: Seq<u8>, newdata: Seq<u8>)
    requires
        self.seq_valid(),
        self.tableable(data),
        self.total_size() <= newdata.len(),
        newdata.take(self.size_of_table(self.length(data))) == data.take(self.size_of_table(self.length(data))),
    ensures
        self.tableable(newdata),
        self.table(newdata) == self.table(data),
    {
        self.bdyf.length_ensures(data);
        self.tableable_ensures(data);       // grumble grumble TODO broadcast

        Self::subrange_of_matching_take(newdata, data, 0, self.size_of_length_field() as int, self.size_of_table(self.length(data)));

        let len = self.length(newdata);

        // trigger to satisify bdyf.parsable_to_len and hence tableable
        assert forall |i: int| 0<=i && i<len implies self.bdyf.gettable(newdata, i) by {
            assert( self.bdyf.gettable(data, i) );
        }

        assert forall |i: int| 0<=i<len implies {
            &&& self.bdyf.elt_parsable(newdata, i)
            &&& self.bdyf.gettable(newdata, i)
            &&& self.bdyf.get_data(newdata, i) == self.bdyf.get_data(data, i)
        } by {
            mul_preserves_le(i+1, len, BdyType::uniform_size() as int);

            let a = self.bdyf.size_of_length_field();
            let b = self.bdyf.eltf.uniform_size();
            assert( a + i * b + b == a + (i + 1) * b ) by(nonlinear_arith);

            let ns = self.bdyf.size_of_length_field() + i * self.bdyf.eltf.uniform_size();
            let ne = self.bdyf.size_of_length_field() + i * self.bdyf.eltf.uniform_size() + self.bdyf.eltf.uniform_size();
            Self::subrange_of_matching_take(newdata, data, ns, ne, self.size_of_table(self.length(data)));
        }

        // trigger extn equality from ensures (verus issue #1257)
        assert( self.table(newdata) == self.table(data) );
    }

    // placeholder until verus#1276 is merged
    pub proof fn subrange_of_matching_take<T>(a: Seq<T>, b: Seq<T>, s: int, e: int, l: int)
    requires
        a.take(l) == b.take(l),
        l <= a.len(),
        l <= b.len(),
        0 <= s <= e <= l,
    ensures
        a.subrange(s, e) == b.subrange(s, e),
    {
        assert forall |i| 0 <= i < e - s implies a.subrange(s, e)[i] == b.subrange(s, e)[i] by {
            assert( a.subrange(s, e)[i] == a.take(l)[i + s] );
    //             assert( b.subrange(s, e)[i] == b.take(l)[i + s] );   // either trigger will do
        }
        // trigger extn equality (verus issue #1257)
        assert( a.subrange(s, e) == b.subrange(s, e) );
    }
}

impl <
    EltFormat: Marshal,
    BdyType: IntFormattable,
    LenType: IntFormattable,
>
    SeqMarshal for VariableSizedElementSeqFormat<EltFormat, BdyType, LenType>
{
    type DVElt = EltFormat::DV;
    type Elt = EltFormat::U;

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

    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    {
        self.eltf.parsable(self.get_data(data, idx))
    }

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
                Some(dslice.subslice(start, end))
            } else { None }
        } else { None }
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
            None => { None }
            Some(eslice) => {
                proof {
                    // TODO(verus): lament of spec ensures
                    self.get_ensures(dslice@, data@, idx as int);
                    SpecSlice::all_ensures::<u8>();
                    // extn equal trigger
                    assert( eslice@.i(data@) =~= self.get_data(dslice@.i(data@), idx as int) );
                }
                self.eltf.try_parse(&eslice, data)
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
        // True if we have room for one more bdy entry plus the new datum
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

                proof {
                    self.bdyf.parsable_length_bounds(idata);
                    assert( tbl.len() == self.table(idata).len() );  // trigger

                    // trigger to learn len-1 < self.bdyf.max_length()
                    assert( self.bdyf.gettable(idata, len as int - 1) );

                    // index_bounds_facts being public is a bit yucky. I guess that's a consequence
                    // of the tight coupling between this module and Resizable*.
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

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: &EltFormat::U)
    ensures
        // bonus layer-violating ensures
        self.free_space(dslice@.i(data@)) == self.free_space(dslice@.i(old(data)@))
            - (self.size_of_boundary_entry() + self.eltf.spec_size(value.deepv())),
    {
        let ghost idata = dslice@.i(data@);
        proof {
            BdyType::deepv_is_as_int_forall();
            self.appendable_implies_bdyf_appendable(idata, value.deepv());
            SpecSlice::all_ensures::<u8>(); // sigh
        }
        let (len, upper_bound) = self.exec_length_and_upper_bound(dslice, data);
        let size = self.eltf.exec_size(value);
        let start: usize = upper_bound - size;
        ////////////////////////////////////////////////////////////
        // Write the value into its empty slot
        ////////////////////////////////////////////////////////////
        let after_elt = self.eltf.exec_marshall(value, data, dslice.start + start);

        // Snapshot the data after writing the new datum but before appending the boundary table
        let ghost middle_data_raw = data@;
        let ghost middle_data = dslice@.i(data@);
        proof {
            // we didn't break the table
            assert( middle_data.take(start as int) == idata.take(start as int) );   // verus #1257
            Self::subrange_of_matching_take(middle_data, idata, 0, self.size_of_table(self.length(idata)) as int, start as int);
            self.table_identity(idata, middle_data);

            // we didn't break any of the old elements
            assert( is_prefix(self.table(idata), self.table(middle_data)) ) by {
                // Sheesh, subranges don't trigger very nicely.
                assert( self.table(middle_data).subrange(0, self.table(idata).len() as int) == self.table(middle_data) );
            }
            assert( middle_data.skip(self.elements_start(idata)) == idata.skip(self.elements_start(idata)) );   // extn trigger
            self.elements_identity(idata, middle_data);
        }

        ////////////////////////////////////////////////////////////
        // Append the new boundary element
        ////////////////////////////////////////////////////////////
        let new_bdy = BdyType::from_usize(start);

        // Suppose len(idata) == 19
        // suppose LenType == u16
        // suppose total_size == 25
        // then length(idata) == 9
        // then LenType::max() == 65536
        // 19 < (25 - 2) / bdy2
//         assume( self.bdyf.length(idata) + 1 <= LenType::max() );
// 
// //         assert( self.bdyf.size_of_length_field() == LenType::uniform_size() );
// 
//         assert( self.bdyf.length(idata) < 
//             (self.bdyf.total_size - self.bdyf.size_of_length_field()) as usize / self.bdyf.eltf.uniform_size() );
// 
//         assert( self.bdyf.length(idata) < self.bdyf.spec_max_length() );
//         assert( self.bdyf.appendable(idata, self.append_offset(idata, value.deepv())) );

        self.bdyf.exec_append(dslice, data, &new_bdy);

        // Much of the tricky bit of this proof is that there are data bytes that the bdyf append
        // doesn't touch, expressed as `bdyf.untampered_bytes`. That's a sneaky extra ensures
        // of bdyf append that doesn't appear in the SeqMarshalling.append contract, but we
        // need it for our tightly-coupled dependency on the Resizable implementation.
        // (See MarshalledAccessors.i.dfy:1138 in the original Dafny version.)

        proof {
            let newdata = dslice@.i(data@);
            let newslot = self.length(idata);
            let tbl_orig = self.table(idata);
            let tbl_middle = self.table(middle_data);
            let tbl_new = self.table(newdata);

            assert( self.tableable(newdata) && self.valid_table(newdata) ) by {
                assert forall |i: int| 0<=i<self.length(newdata) implies {
                    &&& self.bdyf.gettable(newdata, i)
                    &&& self.bdyf.elt_parsable(newdata, i)
                } by {
                    if i < self.length(idata) {
                        // trigger
                        assert( self.bdyf.preserves_entry(middle_data, i, newdata) );
                    }
                }

                assert forall |i| 0 <= i < tbl_middle.len() implies tbl_middle[i] == tbl_new[i] by {
                    // trigger
                    assert( self.bdyf.preserves_entry(middle_data, i, newdata) );
                }
                // Every element has non-negative length
                if 0 < tbl_new.len() {
                    // The first element starts beyond the end of the table itself.
                    let size_of_boundary_entry = BdyType::uniform_size();
                    let otl = tbl_middle.len() as int;
                    assert( (otl + 1) * size_of_boundary_entry == otl * size_of_boundary_entry + size_of_boundary_entry ) by(nonlinear_arith);
                }
            }

            assert( is_prefix(tbl_middle, tbl_new) ) by {
                let len = tbl_middle.len() as int;
                assert forall |i| 0 <= i < len implies tbl_middle[i] == tbl_new[i] by {
                    // trigger
                    assert( self.bdyf.preserves_entry(middle_data, i, newdata) );
                }
                assert( tbl_middle == tbl_new.take(len) );  // trigger extn
            }

            assert( newdata.skip(self.elements_start(middle_data)) =~= middle_data.skip(self.elements_start(middle_data)) );

            self.elements_identity(middle_data, newdata);

            assert( self.length(idata) * self.size_of_boundary_entry() + self.size_of_boundary_entry()
                == (self.length(idata) + 1) * self.size_of_boundary_entry() )
                by (nonlinear_arith);

            // The value we wrote into the unused region wasn't stomped by the
            // bdy append
            let msub = middle_data_raw.subrange(dslice.start + start, after_elt as int);
            let dsub = data@.subrange(dslice.start + start, after_elt as int);
            assert( msub == dsub ); // trigger extn

            if 0 < newslot {
                // trigger
                assert( self.bdyf.preserves_entry(middle_data, newslot - 1, newdata) );
            }

            // trigger: extn equality
            assert(
                data@.subrange(dslice@.start + start, after_elt as int)
                == self.get_data(newdata, newslot)
            );

            assert( self.tableable(newdata) ) by {
                assert forall |i: int| 0<=i && i<self.bdyf.length(newdata) implies self.bdyf.elt_parsable(newdata, i) by {
                    if i < newslot {
                    // trigger
                        assert( self.bdyf.preserves_entry(middle_data, i, newdata) );
                    }
                }
            }

            assert( self.valid_table(newdata) ) by {
                assert forall |i, j| 0 <= i <= j < tbl_new.len() implies tbl_new[j] <= tbl_new[i] by {
                    if j < newslot {
                        // trigger preserves_entry
                        assert( self.bdyf.preserves_entry(middle_data, i, newdata) );
                        assert( self.bdyf.preserves_entry(middle_data, j, newdata) );
                        // trigger old valid_table
                        assert( tbl_orig[j] <= tbl_orig[i] );
                    } else if i < j {
                        let k = newslot - 1;
                        // trigger preserves_entry
                        assert( self.bdyf.preserves_entry(middle_data, k, newdata) );
                        assert( self.bdyf.preserves_entry(middle_data, i, newdata) );
                        // trigger old valid_table
                        assert( tbl_orig[k] <= tbl_orig[i] );
                    }
                }
                if 0 < newslot {
                    // trigger preserves_entry
                    assert( self.bdyf.preserves_entry(middle_data, 0, newdata) );
                }
            }
        }
    }
}


} //verus!
