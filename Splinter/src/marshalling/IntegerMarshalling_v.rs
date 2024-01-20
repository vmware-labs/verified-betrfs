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

pub trait NativePackedInt {
    type IntType : Deepview<int>;

    spec fn spec_size() -> usize
    ;

    proof fn spec_size_ensures()
    ensures
        0 < Self::spec_size() <= 8
    ;

    exec fn exec_size() -> (sz: usize)
    ensures
        sz == Self::spec_size()
    ;

//     spec fn spec_max() -> int;
// 
//     exec fn exec_max() -> (out: usize)
//     ensures out as int <= Self::spec_max()    // <= because usize might be smaller than IntType
//     ;

    // A lot of pain in these conversions because we can't assume whether
    // usize is bigger or smaller than IntType

    spec fn spec_this_fits_in_usize(v: int) -> bool { v <= usize::MAX as int }

    exec fn exec_this_fits_in_usize(v: &Self::IntType) -> (out: bool)
    ensures out == Self::spec_this_fits_in_usize(v.deepv())
    ;

    exec fn to_usize(v: Self::IntType) -> (out: usize)
    requires
        Self::spec_this_fits_in_usize(v.deepv()),
    ensures
        out as int == v.deepv()
    ;

    spec fn spec_usize_fits_in_this(u: usize) -> bool
    ;

    exec fn exec_usize_fits_in_this(u: &usize) -> (out: bool)
    ensures out == Self::spec_usize_fits_in_this(*u)
    ;

    exec fn from_usize(u: usize) -> (out: Self::IntType)
    requires
        Self::spec_usize_fits_in_this(u),
    ensures
        out.deepv() == u as int
    ;

}

pub trait PackedIntMarshallingIfc<U: NativePackedInt> : Premarshalling<int, U::IntType> {
    proof fn parsable_property(&self, data: Seq<u8>)
    ensures
        self.parsable(data) <==> U::spec_size() <= data.len()
    ;
}

pub struct PackedIntMarshalling<U: NativePackedInt> {
    _p: std::marker::PhantomData<(U,)>,
}


impl<U: NativePackedInt> PackedIntMarshalling<U> {
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

impl<U: NativePackedInt> Premarshalling<int, U::IntType> for PackedIntMarshalling<U> {
    open spec fn valid(&self) -> bool
    {
        true
    }

    // TODO(andrea): I want this to be open, but:
    // error: in pub open spec function, cannot refer to private function
    closed spec fn parsable(&self, data: Seq<u8>) -> bool
    {
//        assume( false );// TODO mitigate crash #952
        /*std::mem::size_of<u32>()*/
        U::spec_size() <= data.len()
    }

    fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        assume( false );// TODO mitigate crash #952
        U::exec_size() <= data.len()
    }

    open spec fn marshallable(&self, value: int) -> bool
    {
        true
    }

    // TODO(andrea): I want this to be open, but:
    closed spec fn spec_size(&self, value: int) -> usize
    {
//        assume( false );// TODO mitigate crash #952
        U::spec_size()
    }

    fn exec_size(&self, value: &U::IntType) -> (sz: usize)
    {
        assume( false );// TODO mitigate crash #952
        U::exec_size()
    }
}

impl<U: NativePackedInt> PackedIntMarshallingIfc<U> for PackedIntMarshalling<U>
{
    proof fn parsable_property(&self, data: Seq<u8>)
    ensures
        self.parsable(data) <==> U::spec_size() <= data.len()
    {
    }
}

impl NativePackedInt for u32 {
    type IntType = u32;

    open spec fn spec_size() -> usize { 4 }

    proof fn spec_size_ensures() {}

    exec fn exec_size() -> (sz: usize) { 4 }

    exec fn exec_this_fits_in_usize(v: &Self::IntType) -> (out: bool)
    {
        if u32::BITS <= usize::BITS { true } else { *v <= usize::MAX as u32 }
    }

    exec fn to_usize(v: Self::IntType) -> (out: usize) { v as usize }

    open spec fn spec_usize_fits_in_this(u: usize) -> bool { u <= u32::MAX }

    exec fn exec_usize_fits_in_this(u: &usize) -> (out: bool)
    {
        if usize::BITS <= u32::BITS { true } else { *u <= u32::MAX as usize }
    }

    exec fn from_usize(u: usize) -> (out: Self::IntType) { u as u32 }
}

impl Deepview<int> for u32 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl Marshalling<int, u32> for PackedIntMarshalling<u32> {
    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        spec_u32_from_le_bytes(data.subrange(0, 4)) as int
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<u32>)
    {
        if 4 <= slice.exec_len() {
            let parsed = u32_from_le_bytes(slice_subrange(data.as_slice(), 0, 4));
            assume( parsed.deepv() == self.parse(slice.i(data@)) ); // TODO need to know about u32_from_le_bytes
            Some(parsed)
        } else {
            assert( !self.parsable(slice.i(data@)) );
            None
        }
    }

    exec fn marshall(&self, value: &u32, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        // TODO this interface from verus pervasive bytes.rs can't be fast...
        // Marshal the int into a local vector
        let s = u32_to_le_bytes(*value);
        proof { lemma_auto_spec_u32_to_from_le_bytes(); }
        assert( s@.subrange(0, 4) =~= s@ ); // need a little extensionality? Do it by hand!

        assert( self.parse(s@) == value.deepv() );  // why do we believe this here but not the converse in try_parse?

        let end = self.install_bytes(&s, data, start);
        assert( data@.subrange(start as int, end as int) == s@ );

        // TODO(help): Why isn't this assertion equal to the postcondition?
        // - start is immutable
        // - end is indeed what we're returning (next line)
        // - data is mutable, but we are talking about the last value of it because we don't touch
        // it anymore.
        assume( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );

        end
    }
}

impl NativePackedInt for u64 {
    type IntType = u64;

    open spec fn spec_size() -> usize { 8 }

    proof fn spec_size_ensures() {}

    exec fn exec_size() -> (sz: usize) { 8 }

    exec fn exec_this_fits_in_usize(v: &Self::IntType) -> (out: bool)
    {
        if u64::BITS <= usize::BITS { true } else { *v <= usize::MAX as u64 }
    }

    exec fn to_usize(v: Self::IntType) -> (out: usize) { v as usize }

    open spec fn spec_usize_fits_in_this(u: usize) -> bool { u <= u64::MAX }

    exec fn exec_usize_fits_in_this(u: &usize) -> (out: bool)
    {
        if usize::BITS <= u64::BITS { true } else { *u <= u64::MAX as usize }
    }

    exec fn from_usize(u: usize) -> (out: Self::IntType) { u as u64 }
}

impl Deepview<int> for u64 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl Marshalling<int, u64> for PackedIntMarshalling<u64> {
    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        spec_u64_from_le_bytes(data.subrange(0, 8)) as int
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<u64>)
    {
        if 8 <= slice.exec_len() {
            let parsed = u64_from_le_bytes(slice_subrange(data.as_slice(), 0, 8));
            assume( parsed.deepv() == self.parse(slice.i(data@)) ); // TODO need to know about u64_from_le_bytes
            Some(parsed)
        } else {
            None
        }
    }

    exec fn marshall(&self, value: &u64, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        // TODO this interface from verus pervasive bytes.rs can't be fast...
        // Marshal the int into a local vector
        let s = u64_to_le_bytes(*value);
        proof { lemma_auto_spec_u64_to_from_le_bytes(); }
        assert( s@.subrange(0, 8) =~= s@ ); // need a little extensionality? Do it by hand!

        let end = self.install_bytes(&s, data, start);
        assume( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
        end
    }
}

} // verus!
