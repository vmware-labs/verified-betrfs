// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;

verus! {

//////////////////////////////////////////////////////////////////////////////
// Integer marshalling
//////////////////////////////////////////////////////////////////////////////

pub trait IntObligations<T: Deepview<int> + builtin::Integer> {
    spec fn o_spec_size() -> usize;

    proof fn o_spec_size_ensures()
        ensures 0 < Self::o_spec_size()
    ;

    exec fn o_exec_size() -> (s: usize)
        ensures s == Self::o_spec_size()
    ;

    // generic wrappers over vstd::bytes, which should probably be rewritten this way.
    spec fn spec_from_le_bytes(s: Seq<u8>) -> T
    ;

    spec fn spec_to_le_bytes(x: T) -> Seq<u8>
    ;

    exec fn to_le_bytes(x: T) -> (s: Vec<u8>)
      ensures 
        s@ == Self::spec_to_le_bytes(x),
        s@.len() == Self::o_spec_size()
    ;
        
    exec fn from_le_bytes(s: &[u8]) -> (x:T)
      requires s@.len() == Self::o_spec_size(),
      ensures x == Self::spec_from_le_bytes(s@)
    ;
        
    proof fn lemma_auto_spec_to_from_le_bytes()
      ensures
        forall |x: T|
            #![trigger Self::spec_to_le_bytes(x)]
        {
          &&& Self::spec_to_le_bytes(x).len() == Self::o_spec_size()
          &&& Self::spec_from_le_bytes(Self::spec_to_le_bytes(x)) == x
        },
        forall |s: Seq<u8>|
          s.len() == Self::o_spec_size() ==> #[trigger] Self::spec_to_le_bytes(Self::spec_from_le_bytes(s)) == s
    ;

    // workaround for #979
    spec fn as_int(t: T) -> (i: int)
        ;

    proof fn as_int_ensures()
    ensures forall |t: T| t.deepv() == #[trigger] Self::as_int(t);

    // Helpers for SeqMarshalling
    open spec fn spec_this_fits_in_usize(v: int) -> bool { v <= usize::MAX as int }

    // It would be cool if we could make a "final" (un-overridable) default spec fn!
    proof fn spec_this_fits_in_usize_ensures(v: int)
        ensures Self::spec_this_fits_in_usize(v) == { v <= usize::MAX as int }
    ;

    exec fn exec_this_fits_in_usize(v: T) -> (rc: bool)
        ensures rc == Self::spec_this_fits_in_usize(Self::as_int(v))
    ;

    exec fn to_usize(v: T) -> (w: usize)
        requires Self::spec_this_fits_in_usize(Self::as_int(v))
        ensures Self::as_int(v) == w as int
    ;

    spec fn spec_fits_in_this(v: int) -> bool
    ;

    exec fn exec_fits_in_this(v: usize) -> (r: bool)
        ensures r == Self::spec_fits_in_this(v as int)
    ;

    exec fn from_usize(v: usize) -> (w: T)
        requires Self::spec_fits_in_this(v as int)
        ensures Self::as_int(w) == v as int
    ;

}

// impl Marshalling helper fn
exec fn install_bytes(source: &Vec<u8>, data: &mut Vec<u8>, start: usize) -> (end: usize)
requires
    start + source.len() <= old(data).len(),
ensures
    data.len() == old(data).len(),
    end == start + source.len(),
    forall |i| 0 <= i < start ==> data[i] == old(data)[i],
    forall |i| 0 <= i < source.len() ==> data[start as int + i] == source[i],
    forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
{
    // Copy the vector byte-by-byte into place
    let count = source.len();
    let end = start + count;
    let mut k:usize = 0;
    while k < count
    invariant
        end == start + source.len(),
        end <= data.len(),  // manual-every-effing-invariant blows
        data.len() == old(data).len(),  // manual-every-effing-invariant blows
        source.len() == count,  // manual-every-effing-invariant blows. source,count aren't even mutable!
        forall |i| 0 <= i < start ==> data[i] == old(data)[i],
        forall |i| 0 <= i < k ==> data[start as int + i] == source[i],
        forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
    {
        //data[k] = s[k];
        // Do we want some sort of intrinsic so we don't have to copy u32s a byte at a time!?
        data.set(start + k, source[k]);
        k += 1;
    }
    assert( data@.subrange(start as int, end as int) =~= source@ );  // extensionality: it's what's for ~.
    end
}

impl<T: Deepview<int> + builtin::Integer + Copy, O: IntObligations<T>> Marshalling<int, T> for O {
    open spec fn valid(&self) -> bool
    {
        true
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        Self::o_spec_size() <= data.len()
    }

    exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        let l = slice.len();
        let p = Self::o_exec_size() <= l;
        assert( slice@.valid(data@) ); // decoy trait recommends
        proof {
            assert( l == slice@.i(data@).len() );
            if p {
                assert( Self::o_spec_size() <= data@.len() );
                assert( self.parsable(slice@.i(data@)) );
            } else {
                assert( !self.parsable(slice@.i(data@)) );
            }
        }
        assert( p == self.parsable(slice@.i(data@)) );
        p
    }

    open spec fn marshallable(&self, value: int) -> bool
    {
        true
    }

    open spec fn spec_size(&self, value: int) -> usize
    {
        Self::o_spec_size()
    }

    fn exec_size(&self, value: &T) -> (sz: usize)
    {
        Self::o_exec_size()
    }

    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        Self::as_int(Self::spec_from_le_bytes(data.subrange(0, Self::o_spec_size() as int)))
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<T>)
    {
        proof { Self::as_int_ensures(); }
        // TODO(verus): shouldn't need to trigger this; it's in our (inherited) requires
        assert( slice@.valid(data@) );

        if Self::o_exec_size() <= slice.len() {
            let sr = slice_subrange(data.as_slice(), slice.start, slice.start+Self::o_exec_size());
            let parsed = Self::from_le_bytes(sr);
            assert( sr@ == slice@.i(data@).subrange(0, Self::o_spec_size() as int) ); // trigger
            assert( parsed.deepv() == self.parse(slice@.i(data@)) );
            Some(parsed)
        } else {
            assert( !self.parsable(slice@.i(data@)) );
            None
        }
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: T)
    {
        proof { Self::as_int_ensures(); }
        let sr = slice_subrange(data.as_slice(), slice.start, slice.start+Self::o_exec_size());
        assert( sr@ == slice@.i(data@).subrange(0, Self::o_spec_size() as int) ); // trigger
        Self::from_le_bytes(sr)
    }

    exec fn exec_marshall(&self, value: &T, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        proof { Self::as_int_ensures(); }

        let s = Self::to_le_bytes(*value);
        assert( s@.subrange(0, Self::o_spec_size() as int) =~= s@ ); // need a little extensionality? Do it by hand!
        let end = install_bytes(&s, data, start);

        assert( data@.subrange(start as int, end as int) == s@ );   // trigger
        assert( Self::spec_from_le_bytes(Self::spec_to_le_bytes(*value)) == *value )
            by { Self::lemma_auto_spec_to_from_le_bytes(); }

        end
    }
}

//////////////////////////////////////////////////////////////////////////////
// Concrete instances
//////////////////////////////////////////////////////////////////////////////

// Empty struct to name this implementation
pub struct IntMarshalling<T> {
    pub _p: std::marker::PhantomData<(T,)>,
}

impl<T> IntMarshalling<T> {
    // TODO(verus): modify Verus to allow constructing default phantomdata fields
    #[verifier(external_body)]
    pub fn new() -> Self {
        Self{ _p: Default::default() }
    }
}

impl Deepview<int> for u32 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl IntObligations<u32> for IntMarshalling<u32> {
    open spec fn o_spec_size() -> usize { 4 } 

    // TODO(verus): Too bad this proof-free obligation can't be handled in the trait
    proof fn o_spec_size_ensures() {}

    exec fn o_exec_size() -> usize { 4 } 

    closed spec fn spec_from_le_bytes(s: Seq<u8>) -> u32
    {
        spec_u32_from_le_bytes(s)
    }

    closed spec fn spec_to_le_bytes(x: u32) -> Seq<u8>
    {
        spec_u32_to_le_bytes(x)
    }

    exec fn to_le_bytes(x: u32) -> (s: Vec<u8>)
    {
        u32_to_le_bytes(x)
    }

    exec fn from_le_bytes(s: &[u8]) -> (x:u32)
    {
        u32_from_le_bytes(s)
    }
        
    proof fn lemma_auto_spec_to_from_le_bytes()
    {
        lemma_auto_spec_u32_to_from_le_bytes();

        assert forall |x: u32| #![auto]
        {
          &&& Self::spec_from_le_bytes(Self::spec_to_le_bytes(x)) == x
        } by {
            assert( spec_u32_to_le_bytes(x).len() == 4 ); // stupid trigger; TODO(jonh): fix vstd::bytes.
                                                          // Comically u64 version has a sane trigger.
        };
    }

    open spec fn as_int(t: u32) -> int { t as int }

    proof fn as_int_ensures() { }

//    open spec fn spec_this_fits_in_usize(v: int) -> bool { v <= usize::MAX as int }

    // proof that I didn't tamper with the default. Erk.
    proof fn spec_this_fits_in_usize_ensures(v: int) { }

    exec fn exec_this_fits_in_usize(v: u32) -> (rc: bool) {
        if u32::BITS <= usize::BITS { true } else { v < usize::MAX as u32  }
    }

    exec fn to_usize(v: u32) -> (w: usize) { v as usize }

    exec fn from_usize(v: usize) -> (w: u32) { v as u32 }

    open spec fn spec_fits_in_this(v: int) -> bool
    {
        0 <= v <= u32::MAX
    }

    exec fn exec_fits_in_this(v: usize) -> (r: bool)
    {
        if usize::BITS <= u32::BITS { true } else { v <= (u32::MAX as usize) }
    }
}

impl Deepview<int> for u64 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl IntObligations<u64> for IntMarshalling<u64> {
    open spec fn o_spec_size() -> usize { 8 } 

    proof fn o_spec_size_ensures() {}

    exec fn o_exec_size() -> usize { 8 } 

    closed spec fn spec_from_le_bytes(s: Seq<u8>) -> u64
    {
        spec_u64_from_le_bytes(s)
    }

    closed spec fn spec_to_le_bytes(x: u64) -> Seq<u8>
    {
        spec_u64_to_le_bytes(x)
    }

    exec fn to_le_bytes(x: u64) -> (s: Vec<u8>)
    {
        u64_to_le_bytes(x)
    }

    exec fn from_le_bytes(s: &[u8]) -> (x:u64)
    {
        u64_from_le_bytes(s)
    }
        
    proof fn lemma_auto_spec_to_from_le_bytes()
    {
        lemma_auto_spec_u64_to_from_le_bytes();
    }

    open spec fn as_int(t: u64) -> int { t as int }

    proof fn as_int_ensures() { }

    proof fn spec_this_fits_in_usize_ensures(v: int) { }

    exec fn exec_this_fits_in_usize(v: u64) -> (rc: bool) {
        if u64::BITS <= usize::BITS { true } else { v <= usize::MAX as u64 }
    }

    exec fn to_usize(v: u64) -> (w: usize) { v as usize }

    exec fn from_usize(v: usize) -> (w: u64) { v as u64 }

    open spec fn spec_fits_in_this(v: int) -> bool
    {
        0 <= v <= u64::MAX
    }

    exec fn exec_fits_in_this(v: usize) -> (r: bool)
    {
        if usize::BITS <= u64::BITS { true } else { v <= (u64::MAX as usize) }
    }
}

// Confirm that I really have built Marshalling<int, u32> and u64
// fn do_thing<T: Deepview<int>, M: Marshalling<int, T>>() {
// }
// 
// fn fiddle() {
// //     do_thing::<u16, IntMarshalling<u16>>();
//     do_thing::<u32, IntMarshalling<u32>>();
//     do_thing::<u64, IntMarshalling<u64>>();
// }

} // verus!
