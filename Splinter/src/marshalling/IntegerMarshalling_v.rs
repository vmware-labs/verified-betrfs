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

// First try: T == u32
struct IntMarshalling<T> {
    _p: std::marker::PhantomData<(T,)>,
}

impl<T> IntMarshalling<T> {
    exec fn install_bytes(&self, source: &Vec<u8>, data: &mut Vec<u8>, start: usize) -> (end: usize)
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
}

pub trait Obligations<T> {
    spec fn o_spec_size() -> usize;

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
}

impl Deepview<int> for u32 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl Obligations<u32> for IntMarshalling<u32> {
    open spec fn o_spec_size() -> usize { 4 } 

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
}

impl Marshalling<int, u32> for IntMarshalling<u32> {
    open spec fn valid(&self) -> bool
    {
        true
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        Self::o_spec_size() <= data.len()
    }

    fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        Self::o_exec_size() <= slice.exec_len()
    }

    open spec fn marshallable(&self, value: int) -> bool
    {
        true
    }

    open spec fn spec_size(&self, value: int) -> usize
    {
        Self::o_spec_size()
    }

    fn exec_size(&self, value: &u32) -> (sz: usize)
    {
        Self::o_exec_size()
    }

    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        Self::spec_from_le_bytes(data.subrange(0, Self::o_spec_size() as int)) as int
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<u32>)
    {
        // TODO(verus): shouldn't need to trigger this; it's in our (inherited) requires
        assert( slice.valid(data@) );

        if Self::o_exec_size() <= slice.exec_len() {
            let sr = slice_subrange(data.as_slice(), slice.start, slice.start+Self::o_exec_size());
            let parsed = Self::from_le_bytes(sr);
            assert( sr@ == slice.i(data@).subrange(0, Self::o_spec_size() as int) ); // trigger
            Some(parsed)
        } else {
            assert( !self.parsable(slice.i(data@)) );
            None
        }
    }

    exec fn marshall(&self, value: &u32, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let s = Self::to_le_bytes(*value);
        assert( s@.subrange(0, Self::o_spec_size() as int) =~= s@ ); // need a little extensionality? Do it by hand!
        let end = self.install_bytes(&s, data, start);

        assert( data@.subrange(start as int, end as int) == s@ );   // trigger
        assert( Self::spec_from_le_bytes(Self::spec_to_le_bytes(*value)) == *value )
            by { Self::lemma_auto_spec_to_from_le_bytes(); }

        end
    }
}

impl Deepview<int> for u64 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl Obligations<u64> for IntMarshalling<u64> {
    open spec fn o_spec_size() -> usize { 8 } 

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
}

impl Marshalling<int, u64> for IntMarshalling<u64> {
    open spec fn valid(&self) -> bool
    {
        true
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        Self::o_spec_size() <= data.len()
    }

    fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        Self::o_exec_size() <= slice.exec_len()
    }

    open spec fn marshallable(&self, value: int) -> bool
    {
        true
    }

    open spec fn spec_size(&self, value: int) -> usize
    {
        Self::o_spec_size()
    }

    fn exec_size(&self, value: &u64) -> (sz: usize)
    {
        Self::o_exec_size()
    }

    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        spec_u64_from_le_bytes(data.subrange(0, 8)) as int
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<u64>)
    {
        // TODO(verus): shouldn't need to trigger this; it's in our (inherited) requires
        assert( slice.valid(data@) );

        if 8 <= slice.exec_len() {
            let sr = slice_subrange(data.as_slice(), slice.start, slice.start+8);
            let parsed = u64_from_le_bytes(sr);
            assert( sr@ == slice.i(data@).subrange(0, 8) ); // trigger
            Some(parsed)
        } else {
            assert( !self.parsable(slice.i(data@)) );
            None
        }
    }

    exec fn marshall(&self, value: &u64, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let s = u64_to_le_bytes(*value);
        proof { lemma_auto_spec_u64_to_from_le_bytes(); }
        assert( s@.subrange(0, 8) =~= s@ ); // need a little extensionality? Do it by hand!
        let end = self.install_bytes(&s, data, start);
        assert( data@.subrange(start as int, end as int) == s@ );   // trigger

        end
    }
}

} // verus!
