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
use crate::marshalling::math_v::*;

verus! {

// In a UniformSizedElementSeqMarshallingOblinfo, the length (set of readable
// elements) is determined by the size of the u8 slice you hand in and the
// element size. If you put your hands on a bigger slice, you can try to read
// its elements.

pub trait UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt: Deepview<DVElt>> {
    spec fn valid(&self) -> bool
        ;

    spec fn uniform_size(&self) -> (sz: usize)
        ;

    proof fn uniform_size_ensures(&self)
    requires self.valid(),
    ensures 0 < self.uniform_size()
    ;

    exec fn exec_uniform_size(&self) -> (sz: usize)
    requires self.valid(),
    ensures sz == self.uniform_size()
    ;

    type EltMarshalling : Marshalling<DVElt, Elt>;
}

pub struct IntegerSeqMarshallingOblinfo<Elt: Deepview<int> + builtin::Integer, IO: IntObligations<Elt>> {
    pub int_marshalling: IO,
    pub _p: std::marker::PhantomData<(Elt,)>,
}

impl<Elt: Deepview<int> + builtin::Integer, IO: IntObligations<Elt>> IntegerSeqMarshallingOblinfo<Elt, IO> {
    // TODO(verus): modify Verus to allow constructing default phantomdata fields
    #[verifier(external_body)]
    pub fn new(int_marshalling: IO) -> Self {
        Self{ int_marshalling, _p: Default::default() }
    }
}

impl<Elt: Deepview<int> + builtin::Integer + Copy, IO: IntObligations<Elt>>
    UniformSizedElementSeqMarshallingOblinfo<int, Elt>
    for IntegerSeqMarshallingOblinfo<Elt, IO>
{
    type EltMarshalling = IO;

    open spec fn valid(&self) -> bool
    {
        self.int_marshalling.valid()
    }

    open spec fn uniform_size(&self) -> (sz: usize)
    {
        IO::o_spec_size()
    }

    proof fn uniform_size_ensures(&self) {
        IO::o_spec_size_ensures()
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    {
        IO::o_exec_size()
    }
}

pub struct UniformSizedElementSeqMarshalling<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>> {
    pub oblinfo: O,
    pub eltm: O::EltMarshalling,
    pub _p: std::marker::PhantomData<(DVElt,Elt,)>,
}

impl <DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
    UniformSizedElementSeqMarshalling<DVElt, Elt, O>
{
    // TODO(verus): modify Verus to allow constructing default phantomdata fields
    #[verifier(external_body)]
    pub fn new(oblinfo: O, eltm: O::EltMarshalling) -> Self {
        Self{ oblinfo, eltm, _p: Default::default() }
    }

    spec fn slice_length(&self, dslice: SpecSlice) -> int
    recommends self.valid(), dslice.wf(),
    {
        dslice.len() / (self.oblinfo.uniform_size() as int)
    }

    // TODO(delete): dead code
//     proof fn length_ensures(&self, data: Seq<u8>)
//     requires
//         self.valid(),
//         data.len() < usize::MAX,
//     ensures (
//         self.slice_length(SpecSlice::all(data))
//         == self.length(data)
//         <= self.length(data) * (self.oblinfo.uniform_size() as int)
//         <= data.len()
//         )
//     {
//         self.oblinfo.uniform_size_ensures();
//         div_mul_order(data.len() as int, self.oblinfo.uniform_size() as int);
//         mul_le(self.length(data), self.oblinfo.uniform_size() as int);
//     }

    proof fn index_bounds_facts(&self, slice: SpecSlice, idx: int)
    requires self.valid(), slice.wf(), 0 <= idx, idx < slice.len() / (self.oblinfo.uniform_size() as int)
    ensures
        0
            <= idx * (self.oblinfo.uniform_size() as int)
            < idx * (self.oblinfo.uniform_size() as int) + (self.oblinfo.uniform_size() as int)
            == (idx+1) * (self.oblinfo.uniform_size() as int)
            <= slice.len()
    {
        self.oblinfo.uniform_size_ensures();   // TODO(verus): lament of the spec ensures
        nat_mul_nat_is_nat(idx, self.oblinfo.uniform_size() as int);
        pos_mul_preserves_order(idx, idx+1, self.oblinfo.uniform_size() as int);
        distribute_left(idx, 1, self.oblinfo.uniform_size() as int);
        div_mul_order(slice.len(), self.oblinfo.uniform_size() as int);
        if idx + 1 < self.slice_length(slice) {
            pos_mul_preserves_order(idx + 1, self.slice_length(slice), self.oblinfo.uniform_size() as int);
        }
    }
}

impl <DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
    SeqMarshalling<DVElt, Elt>
    for UniformSizedElementSeqMarshalling<DVElt, Elt, O>
{
    open spec fn seq_valid(&self) -> bool {
        &&& self.eltm.valid()
        &&& self.oblinfo.valid()
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool { true }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        (data.len() as int) / (self.oblinfo.uniform_size() as int)
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        proof { self.oblinfo.uniform_size_ensures() }
        Some(dslice.len() / self.oblinfo.exec_uniform_size())
    }

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool) { true }

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    {
        proof { self.oblinfo.uniform_size_ensures() }   // 0 < denom
        dslice.len() / self.oblinfo.exec_uniform_size()
    }

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        0 <= idx < self.length(data)
    }

    open spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    {
        dslice.subslice(
            idx * self.oblinfo.uniform_size(),
            idx * self.oblinfo.uniform_size() + self.oblinfo.uniform_size())
    }

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    {
        self.index_bounds_facts(dslice, idx as int);
        assert( self.get(dslice, data, idx).valid(data) );
    }

    open spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    // TODO factor out this common impl
    {
        self.get(SpecSlice::all(data), data, idx).i(data)
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
        let len = self.exec_length(dslice, data);
        if idx < len {
            proof {
                self.index_bounds_facts(dslice@, idx as int);
            }
            Some( dslice.subslice(
                    (idx as usize) * self.oblinfo.exec_uniform_size(),
                    (idx as usize) * self.oblinfo.exec_uniform_size() + self.oblinfo.exec_uniform_size()) )
        } else {
            None
        }
    }

    exec fn exec_gettable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    {
        let len = self.exec_length(dslice, data);
        idx < len
    }

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    {
        proof { self.index_bounds_facts(dslice@, idx as int); }
        dslice.subslice(
            (idx as usize) * self.oblinfo.exec_uniform_size(),
            (idx as usize) * self.oblinfo.exec_uniform_size() + self.oblinfo.exec_uniform_size())
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
                    self.index_bounds_facts(dslice@, idx as int);
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
            self.index_bounds_facts(dslice@, idx as int);
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
        &&& 0 <= idx < self.length(data)
        &&& self.elt_marshallable(value)
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
        let len = self.exec_length(dslice, data);
        let sz = self.eltm.exec_size(value);
        idx < len && sz == self.oblinfo.exec_uniform_size()
    }

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    {
        proof {
            self.index_bounds_facts(dslice@, idx as int);
            self.oblinfo.uniform_size_ensures();
        }
        let newend = self.eltm.exec_marshall(value, data, dslice.start + idx * self.oblinfo.exec_uniform_size());
        assert forall |i: int| i != idx as int && self.gettable(dslice@.i(old(data)@), i)
            implies self.get_data(dslice@.i(data@), i) == self.get_data(dslice@.i(old(data)@), i) by
        {
            self.index_bounds_facts(dslice@, i);

            lemma_seq_slice_slice(data@,
                dslice.start as int,
                dslice.end as int,
                i * self.oblinfo.uniform_size() as int,
                i * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);
            lemma_seq_slice_slice(old(data)@,
                dslice.start as int,
                dslice.end as int,
                i * self.oblinfo.uniform_size() as int,
                i * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);

            if i < idx as int {
                mul_preserves_le(i + 1, idx as int, self.oblinfo.uniform_size() as int);
            } else {
                mul_preserves_le(idx as int + 1, i, self.oblinfo.uniform_size() as int);
            }

            // TODO(verus): shouldn't assert-by conclusion give us this trigger for free?
            assert( self.get_data(dslice@.i(data@), i) == self.get_data(dslice@.i(old(data)@), i) );
        }

        proof {
            lemma_seq_slice_slice(
                data@,
                dslice.start as int,
                dslice.end as int,
                idx as int * self.oblinfo.uniform_size() as int,
                idx as int * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);
        }
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

impl<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
    UniformSizedElementSeqMarshalling<DVElt, Elt, O>
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
}

impl<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
    Marshalling<Seq<DVElt>, Vec<Elt>>
    for UniformSizedElementSeqMarshalling<DVElt, Elt, O>
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

    // dummy placeholders; I guess we need to implement this yet
    open spec fn marshallable(&self, value: Seq<DVElt>) -> bool
    {
        &&& forall |i| 0 <= i < value.len() ==> #[trigger] self.eltm.marshallable(value[i])
        &&& forall |i| 0 <= i < value.len() ==> #[trigger] self.eltm.spec_size(value[i]) == self.oblinfo.uniform_size()
        &&& value.len() * self.oblinfo.uniform_size() <= usize::MAX
    }

    open spec fn spec_size(&self, value: Seq<DVElt>) -> usize
    {
        (value.len() * self.oblinfo.uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Vec<Elt>) -> (sz: usize)
    {
        value.len() * self.oblinfo.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Vec<Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let mut i: usize = 0;
        let mut end = start;

        // TODO(verus): this is super clumsy, since we know value is a constant throughout the
        // while loop
        let ghost cvalue = value;

        proof {
            assert( end as int <= data@.len() );    // bogus recommendation noise
            let marshalled_data = data@.subrange(start as int, end as int);
            assert( marshalled_data == Seq::<u8>::empty() );
            assert( self.seq_valid() );
            assert( self.lengthable(marshalled_data) );
            assert( self.marshallable(value.deepv()) );
            assert( value.deepv().len() * self.oblinfo.uniform_size() <= usize::MAX );
            assert( value.deepv().len() == value.len() );

            assert forall |l| 0 <= l <= cvalue.len() implies #[trigger] self.marshallable(cvalue.deepv().subrange(0, l)) by {
                mul_preserves_le(l, cvalue.len() as int, self.oblinfo.uniform_size() as int);
            }

            // no spec_ensures wastes another 20 minutes of my life
            self.oblinfo.uniform_size_ensures();

//             assert( marshalled_data.len() <= usize::MAX );
            let a = marshalled_data.len() as int;
            let b = self.oblinfo.uniform_size() as int;
            assert( a <= usize::MAX );
            assert( 0 < b );
            assert( a / b <= usize::MAX );
//             assert(
//                 (marshalled_data.len() as int) / (self.oblinfo.uniform_size() as int) <= usize::MAX );

//             assert( self.length(marshalled_data) <= usize::MAX );
//             assert( self.parsable_to_len(marshalled_data, self.length(marshalled_data) as usize) );
            assert( self.seq_parsable(marshalled_data) );

            assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv().subrange(0, i as int) );
        }
        // proof missing
        
        while i < value.len()
        invariant
            0 <= i <= value.len(),
            data@.len() == old(data)@.len(),

            // TODO(jonh): try Chris' new thingy #![verifier::spinoff_loop(false)]
            // Oh baby that was sweet.
            // Also TODO(chris): The name spinoff is confusing, since it affects explicit context.
            // spinoff_prover at the fn level doesn't have this change in manual effort behavior.
//            cvalue == value,
//             forall |l| 0 <= l <= cvalue.len() ==> #[trigger] self.marshallable(cvalue.deepv().subrange(0, l)),

//            self.marshallable(cvalue.deepv().subrange(0, i as int)),
            end as int == start as int + self.spec_size(value.deepv().subrange(0, i as int)) as int,
            end as int == start as int + i * self.oblinfo.uniform_size(),
//             end as int <= data@.len() as int,
            forall |j| 0 <= j < start ==> data@[j] == old(data)@[j],
            forall |j| end as int <= j < old(data)@.len() ==> data@[j] == old(data)@[j],

            // TODO(verus): another decoy recommends failure that proves if you just ask for it
            end as int <= data@.len(),

            self.parsable(data@.subrange(start as int, end as int)),
            self.parse(data@.subrange(start as int, end as int)) == value.deepv().subrange(0, i as int),
        {
            let ghost oldend = end;
            assert( oldend as int == start as int + self.spec_size(value.deepv().subrange(0, i as int)) as int );
            let ghost olddata = data@.subrange(start as int, end as int);
            let ghost oldi = i;

            proof {
                if i as int + 1 < value.len() {
                    pos_mul_preserves_order(i as int + 1, value.len() as int, self.oblinfo.uniform_size() as int);
                }
                distribute_left(i as int, 1, self.oblinfo.uniform_size() as int);
            }

            assert( self.eltm.marshallable(value.deepv()[i as int]) );
            assert( end as int + self.eltm.spec_size(value.deepv()[i as int]) as int <= data.len() );

            let ghost prior_data = data@;    // note not subranged
            assert( olddata == prior_data.subrange(start as int, end as int) );
            end = self.eltm.exec_marshall(&value[i], data, end);
            i += 1;

            // proof missing
            //

            proof {
                assert( end as int == start as int + i * self.oblinfo.uniform_size() );

                let l = i as int;
                assert( 0 <= l <= value.len() );
                assert( self.marshallable(cvalue.deepv().subrange(0, l)) );
                assert( self.marshallable(value.deepv().subrange(0, i as int)) );
                assert( end as int == start as int + self.spec_size(value.deepv().subrange(0, i as int)) as int );
                assert( value.deepv().subrange(0, i as int) == value.deepv().subrange(0, i-1 as int).push(value[i-1].deepv()) );
                let marshalled_data = data@.subrange(start as int, end as int);
                assert( self.lengthable(marshalled_data) );
                assert( self.length(marshalled_data) <= usize::MAX );
                assert( self.gettable_to_len(marshalled_data, self.length(marshalled_data) as usize as int) );

                assert( self.spec_size(value.deepv().subrange(0, i as int)) == i * self.oblinfo.uniform_size() );

                assert( marshalled_data =~= data@.subrange(start as int, end as int) );

                let old_in_end = oldi * self.oblinfo.uniform_size();
                assert( marshalled_data.subrange(0, oldend as int) =~= olddata.subrange(0, old_in_end) );

//                 assert( marshalled_data.len() == end - start );
//                 assert( marshalled_data.len() == self.oblinfo.uniform_size() * i );
//                 mul_div_identity(i as int, self.oblinfo.uniform_size() as int);
//                 assert( i == self.length(marshalled_data) );
                assert forall |j: int| 0<=j<self.length(marshalled_data) implies self.elt_parsable(marshalled_data, j) by {
                    if j < i {
                        assert( self.parsable(olddata) );
                        assert( self.elt_parsable_to_len(olddata, self.length(olddata)) );
                        assume( j < self.length(olddata) );
                        assert( self.elt_parsable(olddata, j) );
                        assert( self.get(SpecSlice::all(olddata), olddata, j)
                                == self.get(SpecSlice::all(marshalled_data), olddata, j) );
                        let gslice = self.get(SpecSlice::all(olddata), olddata, j);
                        assert( gslice ==
                            SpecSlice::all(olddata).subslice(
                                j * self.oblinfo.uniform_size(),
                                j * self.oblinfo.uniform_size() + self.oblinfo.uniform_size()
                            )
                        );
                        assert( SpecSlice::all(olddata).start == 0 );
                        assert( gslice ==
                            SpecSlice{
                                start: j * self.oblinfo.uniform_size(),
                                end: j * self.oblinfo.uniform_size() + self.oblinfo.uniform_size(),
                            }
                        );

                        assert( gslice.start == j * self.oblinfo.uniform_size() );
                        assert( gslice.start == 0 + (j as usize) * (self.oblinfo.uniform_size() as usize) );

                        assert( self.get_data(olddata, j) == gslice.i(olddata) );
                        assert( self.get_data(marshalled_data, j) == gslice.i(marshalled_data) );
                        assert( gslice.len() < end - start );
                        assert forall |c| gslice.start <= c < gslice.end implies olddata[c] == marshalled_data[c] by {
                            assert( forall |i| 0 <= i < oldend ==> prior_data[i] == data[i] );
                            assert( 0 <= c );
                            assert( c - gslice.start < end - start );
                            assert( olddata[c] == prior_data[start + c] );
                            assert( marshalled_data[c] == data[start + c] );
                            //assert( olddata[c]
                        }
                        assert( 0 <= gslice.start as int );
                        assert( gslice.start as int <= gslice.end as int );
                        assume( gslice.end as int <= data.len() );
                        assume( gslice.valid(olddata) );
                        assert( gslice.i(olddata).len() == gslice.len() );
                        assert( gslice.i(olddata).len() == gslice.i(marshalled_data).len() );
                        assert( gslice.i(olddata) =~= gslice.i(marshalled_data) );
                        assert( self.get_data(olddata, j) =~= self.get_data(marshalled_data, j) );
                        assert( self.elt_parsable(marshalled_data, j) );
                    } else {
                        mul_div_identity(i as int, self.oblinfo.uniform_size() as int);
                    }
                }
                assert( self.elt_parsable_to_len(marshalled_data, self.length(marshalled_data)) );
                assert( self.elt_parsable_to_len(marshalled_data, self.length(marshalled_data) as usize as int) );
                assert( self.parsable_to_len(marshalled_data, self.length(marshalled_data) as usize) );
                assert( self.parsable(marshalled_data) );
                assume( self.parse(marshalled_data) == value.deepv().subrange(0, i as int) );
            }
        }
        assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
        end
    }
}

// DVElt, Elt are the innermost types
// We should be able to marshall a Seq of Seq of (something) if the inner something is
// uniform-sized. So I guess we need a Uniform-sized trait?
// But we'll also need USESM<DVElt, Elt, O> to implement Marshalling.
// We already know it does for O: USESMO. That's SO!
pub struct SeqSeqMarshallingOblinfo
        <DVElt, Elt: Deepview<DVElt>, SO: UniformSizedElementSeqMarshallingOblinfo<Seq<DVElt>, Vec<Elt>>> {
    pub subseq_marshalling: UniformSizedElementSeqMarshalling<Seq<DVElt>, Vec<Elt>, SO>,
    _p: std::marker::PhantomData<(DVElt,Elt,)>,
}

fn is_i_marshalling<M: Marshalling<int, u32>>(m: M) { }
fn is_s_marshalling<M: Marshalling<Seq<int>, Vec<u32>>>(m: M) { }
fn is_ss_marshalling<M: Marshalling<Seq<Seq<int>>, Vec<Vec<u32>>>>(m: M) { }

fn foo<
    SO: UniformSizedElementSeqMarshallingOblinfo<int, u32>,
    SSO: UniformSizedElementSeqMarshallingOblinfo<Seq<int>, Vec<u32>>
>(
    r:  IntMarshalling<u32>,
    o: IntegerSeqMarshallingOblinfo<u32, IntMarshalling<u32>>,
    s:  UniformSizedElementSeqMarshalling<int, u32, IntegerSeqMarshallingOblinfo<u32, IntMarshalling<u32>>>,
    s2: UniformSizedElementSeqMarshalling<int, u32, SO>,
    t:  UniformSizedElementSeqMarshalling<Seq<int>, Vec<u32>, SSO>
    ) {
    is_i_marshalling(r);

    is_s_marshalling(s);

    is_ss_marshalling(t);
}

// impl<DVElt, Elt: Deepview<DVElt>, SO: UniformSizedElementSeqMarshallingOblinfo<Seq<DVElt>, Vec<Elt>>>
//     UniformSizedElementSeqMarshallingOblinfo<Seq<DVElt>, Vec<Elt>>
//     for SeqSeqMarshallingOblinfo<DVElt, Elt, SO>
// {
//     type EltMarshalling = UniformSizedElementSeqMarshalling<Seq<DVElt>, Vec<Elt>, SO>;
// 
//     open spec fn valid(&self) -> bool
//     {
//         self.subseq_marshalling.valid()
//     }
// 
//     open spec fn uniform_size(&self) -> (sz: usize)
//     {
//         self.subseq_marshalling.uniform_size()
//     }
// 
//     proof fn uniform_size_ensures(&self) {
//         self.subseq_marshalling.uniform_size_ensures()
//     }
// 
//     exec fn exec_uniform_size(&self) -> (sz: usize)
//     {
//         self.subseq_marshalling.exec_uniform_size()
//     }
// }

// pub trait ResizableUniformSizedElementSeqMarshallingOblinfo<DVElt, Elt: Deepview<DVElt>, LenT, LenMarshalling: IntMarshalling<LenT>>
//     : UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>
// {
// //     spec fn valid(&self) -> bool
// //         ;
// // 
// //     spec fn uniform_size(&self) -> (sz: usize)
// //         ;
// // 
// //     proof fn uniform_size_ensures(&self)
// //     requires self.valid(),
// //     ensures 0 < self.uniform_size()
// //     ;
// // 
// //     exec fn exec_uniform_size(&self) -> (sz: usize)
// //     requires self.valid(),
// //     ensures sz == self.uniform_size()
// //     ;
// // 
// //     type EltMarshalling : Marshalling<DVElt, Elt>;
// // 
// //     spec fn spec_elt_marshalling(&self) -> Self::EltMarshalling
// //         ;
// // 
// //     // PLEASE PLEASE CAN I HAVE SPEC ENSURES
// //     proof fn spec_elt_marshalling_ensures(&self)
// //     requires self.valid()
// //     ensures self.spec_elt_marshalling().valid()
// //     ;
// // 
// //     exec fn exec_elt_marshalling(&self) -> (eltm: &Self::EltMarshalling)
// //     requires self.valid()
// //     ensures eltm.valid(),
// //         eltm == self.spec_elt_marshalling()
// //         ;
// 
//     spec fn spec_size_of_length_field() -> usize {
//         LenMarshalling::o_spec_size()
//     }
// }

//////////////////////////////////////////////////////////////////////////////
// Convince myself that IntegerSeqMarshalling is indeed SeqMarshalling<T, int>

fn test_is_seq_marshalling<SM: SeqMarshalling<int, u64>>(sm: &SM) { }
fn test_is_marshalling<M: Marshalling<Seq<int>, Vec<u64>>>(m: &M) { }

type IntegerSeqMarshalling<IT> = UniformSizedElementSeqMarshalling<int, IT, IntegerSeqMarshallingOblinfo<IT, IntMarshalling<IT>>>;

fn test(t: IntegerSeqMarshalling<u64>, data: &Vec<u8>) {
    let dslice = Slice::all(data);
    test_is_seq_marshalling(&t);
    test_is_marshalling(&t);
    let oelt = t.try_get_elt(&dslice, data, 0);
}

}
