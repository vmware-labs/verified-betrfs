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
struct IntMarshalling {
    //_p: std::marker::PhantomData<(T,)>,
}

impl IntMarshalling {
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

impl Deepview<int> for u32 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl Marshalling<int, u32> for IntMarshalling {
    open spec fn valid(&self) -> bool
    {
        true
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        4 <= data.len()
    }

    fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        4 <= slice.exec_len()
    }

    open spec fn marshallable(&self, value: int) -> bool
    {
        true
    }

    open spec fn spec_size(&self, value: int) -> usize
    {
        4
    }

    fn exec_size(&self, value: &u32) -> (sz: usize)
    {
        4
    }

    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        spec_u32_from_le_bytes(data.subrange(0, 4)) as int
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<u32>)
    {
        // TODO(verus): shouldn't need to trigger this; it's in our (inherited) requires
        assert( slice.valid(data@) );

        if 4 <= slice.exec_len() {
            let sr = slice_subrange(data.as_slice(), slice.start, slice.start+4);
            let parsed = u32_from_le_bytes(sr);
            assert( sr@ == slice.i(data@).subrange(0, 4) ); // trigger
            Some(parsed)
        } else {
            assert( !self.parsable(slice.i(data@)) );
            None
        }
    }

    exec fn marshall(&self, value: &u32, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let s = u32_to_le_bytes(*value);
        proof { lemma_auto_spec_u32_to_from_le_bytes(); }
        assert( s@.subrange(0, 4) =~= s@ ); // need a little extensionality? Do it by hand!
        let end = self.install_bytes(&s, data, start);
        assert( data@.subrange(start as int, end as int) == s@ );   // trigger

        end
    }
}

} // verus!
