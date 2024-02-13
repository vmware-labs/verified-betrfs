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

pub trait SeqMarshalling<DVElt, Elt: Deepview<DVElt>> {
    spec fn valid(&self) -> bool;

    spec fn lengthable(&self, data: Seq<u8>) -> bool
    recommends
        self.valid()
    ;

    spec fn length(&self, data: Seq<u8>) -> int
    recommends
        self.valid(),
        self.lengthable(data)
    ;

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    requires
        self.valid(),
        dslice.valid(data@),
    ensures
        out is Some <==> self.lengthable(dslice.i(data@)),
        out is Some ==> out.unwrap() as int == self.length(dslice.i(data@))
    ;

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool)
    requires
        self.valid(),
        dslice.valid(data@),
    ensures
        l == self.lengthable(dslice.i(data@))
    // TODO dfy has a default impl here based on try_length
    ;

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    requires
        self.valid(),
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
        self.valid()
    ;

    spec fn get(&self, dslice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    recommends
        self.valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx)
    ;

    proof fn get_ensures(&self, dslice: Slice, data: Seq<u8>, idx: int)
    requires
        self.valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx),
    ensures
        self.get(dslice, data, idx).valid(data)
    ;

    spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.valid(),
        self.gettable(data, idx)
    // TODO dfy has a default impl here
    ;
//     {
//         self.get(&Slice::all(data), data, idx).i(data)
//     }
    
    spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid(),
        self.gettable(data, idx)
    // TODO dfy has a default impl here
    ;

//     {
//         self.spec_elt_marshalling().parsable(self.get_data(data, idx))
//     }

    spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    recommends
        self.valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
    // TODO dfy has a default impl here
    ;
//     {
//         self.spec_elt_marshalling().parse(self.get_data(data, idx))
//     }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    requires
        self.valid(),
        dslice.valid(data@),
    ensures
        oeslice is Some <==> self.gettable(dslice.i(data@), idx as int),
        oeslice is Some ==> oeslice.unwrap() == self.get(*dslice, data@, idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn exec_gettable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    requires self.valid(),
        dslice.valid(data@),
    ensures g == self.gettable(dslice.i(data@), idx as int)
    // TODO dfy has a default impl here
    ;
    
    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    requires
        self.valid(),
        dslice.valid(data@),
        self.gettable(dslice.i(data@), idx as int),
    ensures
        eslice.wf(),
        eslice == self.get(*dslice, data@, idx as int)
    // TODO dfy has a default impl here
    ;

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    requires
        self.valid(),
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
        self.valid(),
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
        self.valid(),
        self.elt_marshallable(value)
    ;

    spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    recommends
        self.valid()
    // TODO dfy has a default impl here
    ;

    // proof fn preserves_entry_transitive

    spec fn sets(&self, data: Seq<u8>, idx: int, value: DVElt, new_data: Seq<u8>) -> bool
    recommends
        self.valid(),
        self.elt_marshallable(value),
        self.settable(data, idx, value)
    // TODO dfy has a default impl here
    ;
    
    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &Elt) -> (s: bool)
    requires
        self.valid(),
        dslice.valid(data@),
        self.elt_marshallable(value.deepv()),
    ensures
        s == self.settable(dslice.i(data@), idx as int, value.deepv())
    ;
    
    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    requires
        self.valid(),
        dslice.valid(old(data)@),
        self.elt_marshallable(value.deepv()),
        self.settable(dslice.i(old(data)@), idx as int, value.deepv()),
    ensures
        dslice.agree_beyond_slice(old(data)@, data@),
        self.sets(dslice.i(old(data)@), idx as int, value.deepv(), dslice.i(data@))
    ;

    
    
}

pub trait UniformSizedElementSeqMarshallingObligations<DVElt, Elt: Deepview<DVElt>> {
    spec fn valid(&self) -> bool;
    
    spec fn uniform_size(&self) -> (sz: usize)
    //requires self.valid(),
    //ensures 0 < sz
    ;

    proof fn uniform_size_ensures(&self)
    requires self.valid(),
    ensures 0 < self.uniform_size()
    ;

    exec fn exec_uniform_size(&self) -> (sz: usize)
    //requires self.valid(),
    ensures sz == self.uniform_size()
    ;

    type EltMarshalling : Marshalling<DVElt, Elt>;

    spec fn spec_elt_marshalling(&self) -> Self::EltMarshalling
        ;

    // PLEASE PLEASE CAN I HAVE SPEC ENSURES
    proof fn spec_elt_marshalling_ensures(&self)
    requires self.valid()
    ensures self.spec_elt_marshalling().valid()
    ;

    exec fn exec_elt_marshalling(&self) -> (eltm: &Self::EltMarshalling)
    requires self.valid()
    ensures eltm.valid(),
        eltm == self.spec_elt_marshalling()
        ;
}

spec fn slice_length<DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>(selff: &USES, dslice: Slice) -> int
recommends selff.valid(), dslice.wf(),
{
    dslice.spec_len() / (selff.uniform_size() as int)
}

//////////////////////////////////////////////////////////////////////////////
// TODO(jonh): extract to a math library
#[verifier(nonlinear)]
proof fn div_mul_order(a: int, b: int)
requires 0 < b
ensures (a/b) * b <= a
{
}

#[verifier(nonlinear)]
proof fn mul_le(a: int, b: int)
    requires 0<=a, 1<=b
    ensures a <= a*b
{
}

#[verifier(nonlinear)]
proof fn pos_mul_preserves_order(x: int, y: int, m: int)
    requires 0<= x < y, 0 < m
    ensures x*m < y*m
{}

#[verifier(nonlinear)]
proof fn distribute_left(a: int, b: int, c: int)
    ensures (a+b)*c == a*c + b*c {}

#[verifier(nonlinear)]
proof fn mul_preserves_le(a: int, b: int, c: int)
    requires 0 <= a <= b, 0 <= c
    ensures a * c <= b * c
{ }

//////////////////////////////////////////////////////////////////////////////

proof fn length_ensures
    <DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>
    (selff: &USES, data: Seq<u8>)
requires
    selff.valid(),
    data.len() < usize::MAX,
ensures (
    slice_length(selff, Slice::all(data))
    == selff.length(data)
    <= selff.length(data) * (selff.uniform_size() as int)
    <= data.len()
    )
{
    selff.uniform_size_ensures();
    div_mul_order(data.len() as int, selff.uniform_size() as int);
    mul_le(selff.length(data), selff.uniform_size() as int);
}

proof fn nat_mul_nat_is_nat(x: int, y: int)
    requires 0 <= x, 0 <= y
    ensures 0 <= x*y {}

proof fn index_bounds_facts
    <DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>
    (selff: &USES, slice: Slice, idx: int)
requires selff.valid(), slice.wf(), 0 <= idx, idx < slice.spec_len() / (selff.uniform_size() as int)
ensures
    0
        <= idx * (selff.uniform_size() as int)
        < idx * (selff.uniform_size() as int) + (selff.uniform_size() as int)
        == (idx+1) * (selff.uniform_size() as int)
        <= slice.spec_len()
{
    selff.uniform_size_ensures();   // TODO(verus): lament of the spec ensures
    nat_mul_nat_is_nat(idx, selff.uniform_size() as int);
    pos_mul_preserves_order(idx, idx+1, selff.uniform_size() as int);
    distribute_left(idx, 1, selff.uniform_size() as int);
    div_mul_order(slice.spec_len(), selff.uniform_size() as int);
    if idx + 1 < slice_length(selff, slice) {
        pos_mul_preserves_order(idx + 1, slice_length(selff, slice), selff.uniform_size() as int);
    }
}

proof fn lemma_seq_slice_slice<T>(s: Seq<T>, i: int, j: int, k: int, l: int)
    requires 0 <= i <= j <= s.len(),
        0 <= k <= l <= j-i
    ensures s.subrange(i,j).subrange(k,l) =~= s.subrange(i+k, i+l)
{
}

// I can't say anything about USES<M> because I haven't told you about M?
impl<DVElt, Elt: Deepview<DVElt>, USES: UniformSizedElementSeqMarshallingObligations<DVElt, Elt>>
    SeqMarshalling<DVElt, Elt>
    for USES
{
    open spec fn valid(&self) -> bool {
        USES::valid(self)
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool {
        true
    }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        (data.len() as int) / (self.uniform_size() as int)
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        proof { self.uniform_size_ensures() }
        Some(dslice.exec_len() / self.exec_uniform_size())
    }

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool) { true }

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    {
        proof { self.uniform_size_ensures() }   // 0 < denom
        dslice.exec_len() / self.exec_uniform_size()
    }

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        0 <= idx < self.length(data)
    }

    open spec fn get(&self, dslice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    {
        dslice.spec_sub(
            ((idx as usize) * self.uniform_size()) as usize,
            ((idx as usize) * self.uniform_size() + self.uniform_size()) as usize
        )
    }

    proof fn get_ensures(&self, dslice: Slice, data: Seq<u8>, idx: int)
    {
        index_bounds_facts(self, dslice, idx as int);
        assert( self.get(dslice, data, idx).valid(data) );
    }

    open spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    // TODO factor out this common impl
    {
        self.get(Slice::all(data), data, idx).i(data)
    }
    
    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    // TODO factor out this common impl
    {
        self.spec_elt_marshalling().parsable(self.get_data(data, idx))
    }

    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    // TODO factor out this common impl
    {
        self.spec_elt_marshalling().parse(self.get_data(data, idx))
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let len = self.exec_length(dslice, data);
        if idx < len {
            proof { index_bounds_facts(self, *dslice, idx as int); }
            Some( dslice.exec_sub(
                    (idx as usize) * self.exec_uniform_size(),
                    (idx as usize) * self.exec_uniform_size() + self.exec_uniform_size()) )
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
        proof { index_bounds_facts(self, *dslice, idx as int); }
        dslice.exec_sub(
            (idx as usize) * self.exec_uniform_size(),
            (idx as usize) * self.exec_uniform_size() + self.exec_uniform_size())
    }

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    // TODO factor out this common impl
    {
        proof { self.spec_elt_marshalling_ensures() };  // :v(

        let oeslice = self.try_get(dslice, data, idx);
        match oeslice {
            None => None,
            Some(eslice) => {
                proof {
                    self.get_ensures(*dslice, data@, idx as int);   // TODO(verus): lament of spec ensures
                    index_bounds_facts(self, *dslice, idx as int);
                    let edslice = self.get(Slice::all(dslice.i(data@)), dslice.i(data@), idx as int);
                    assert( edslice.i(dslice.i(data@)) == eslice.i(data@));   // trigger
                }
                let oelt = self.exec_elt_marshalling().try_parse(&eslice, data);
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
            index_bounds_facts(self, *dslice, idx as int);
            let edslice = self.get(Slice::all(dslice.i(data@)), dslice.i(data@), idx as int);
            assert( edslice.i(dslice.i(data@)) == eslice.i(data@));   // trigger
        }
        self.exec_elt_marshalling().exec_parse(&eslice, data)
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn elt_marshallable(&self, elt: DVElt) -> bool
    {
        self.spec_elt_marshalling().marshallable(elt)
    }

    open spec fn settable(&self, data: Seq<u8>, idx: int, value: DVElt) -> bool
    {
        &&& 0 <= idx < self.length(data)
        &&& self.elt_marshallable(value)
        &&& self.spec_elt_marshalling().spec_size(value) == self.uniform_size()
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
        let sz = self.exec_elt_marshalling().exec_size(value);
        idx < len && sz == self.exec_uniform_size()
    }

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    {
        proof {
            index_bounds_facts(self, *dslice, idx as int);
            self.uniform_size_ensures();
        }
        let newend = self.exec_elt_marshalling().marshall(value, data, dslice.start + idx * self.exec_uniform_size());
        assert forall |i: int| i != idx as int && self.gettable(dslice.i(old(data)@), i)
            implies self.get_data(dslice.i(data@), i) == self.get_data(dslice.i(old(data)@), i) by
        {
            index_bounds_facts(self, *dslice, i);

            lemma_seq_slice_slice(data@,
                dslice.start as int,
                dslice.end as int,
                i * self.uniform_size() as int,
                i * self.uniform_size() as int + self.uniform_size() as int);
            lemma_seq_slice_slice(old(data)@,
                dslice.start as int,
                dslice.end as int,
                i * self.uniform_size() as int,
                i * self.uniform_size() as int + self.uniform_size() as int);
            
            if i < idx as int {
                mul_preserves_le(i + 1, idx as int, self.uniform_size() as int);
            } else {
                mul_preserves_le(idx as int + 1, i, self.uniform_size() as int);
            }

            // TODO(verus): shouldn't assert-by conclusion give us this trigger for free?
            assert( self.get_data(dslice.i(data@), i) == self.get_data(dslice.i(old(data)@), i) );
        }

        proof {
            lemma_seq_slice_slice(
                data@,
                dslice.start as int,
                dslice.end as int,
                idx as int * self.uniform_size() as int,
                idx as int * self.uniform_size() as int + self.uniform_size() as int);
        }
    }
}


}
