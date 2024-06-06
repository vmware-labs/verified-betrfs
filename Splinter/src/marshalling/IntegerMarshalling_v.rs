// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::StaticallySized_v::*;
use crate::marshalling::UniformSized_v::*;

verus! {


// An int type T can be IntFormat<T> if we know these things about it:

// TODO: clean up the usize mess. Require att IntFormattable types to be no bigger than usize.
// (We don't need to support marshalling u64s on a 32-bit-usize platform.)
// TODO: factor out the unsigned (nonnegative) subtrait.

pub trait IntFormattable : Deepview<int> + builtin::Integer + Copy + StaticallySized {

    // generic wrappers over vstd::bytes, which should probably be rewritten this way.
    spec fn spec_from_le_bytes(s: Seq<u8>) -> Self
    ;

    spec fn spec_to_le_bytes(x: Self) -> Seq<u8>
    ;

    exec fn to_le_bytes(x: Self) -> (s: Vec<u8>)
      ensures 
        s@ == Self::spec_to_le_bytes(x),
        s@.len() == Self::uniform_size()
    ;

    exec fn from_le_bytes(s: &[u8]) -> (x:Self)
      requires s@.len() == Self::uniform_size(),
      ensures x == Self::spec_from_le_bytes(s@)
    ;
        
    proof fn lemma_auto_spec_to_from_le_bytes()
      ensures
        forall |x: Self|
            #![trigger Self::spec_to_le_bytes(x)]
        {
          &&& Self::spec_to_le_bytes(x).len() == Self::uniform_size()
          &&& Self::spec_from_le_bytes(Self::spec_to_le_bytes(x)) == x
        },
        forall |s: Seq<u8>|
          s.len() == Self::uniform_size() ==> #[trigger] Self::spec_to_le_bytes(Self::spec_from_le_bytes(s)) == s
    ;

    // workaround for #979
    spec fn as_int(t: Self) -> (i: int)
        ;

    proof fn as_int_ensures()
    ensures forall |t: Self| t.deepv() == #[trigger] Self::as_int(t);

    proof fn this_type_fits_in_usize()
        ensures forall |v: Self| { v as int <= usize::MAX as int }
    ;

    exec fn to_usize(v: Self) -> (w: usize)
        ensures Self::as_int(v) == w as int
    ;

    spec fn spec_fits_in_this(v: int) -> bool
    ;

    exec fn exec_fits_in_this(v: usize) -> (r: bool)
        ensures r == Self::spec_fits_in_this(v as int)
    ;

    exec fn from_usize(v: usize) -> (w: Self)
        requires Self::spec_fits_in_this(v as int)
        ensures Self::as_int(w) == v as int
    ;

    // Maybe this class should be NatObligations? Or have an additional Natty trait?
    proof fn nonnegative()
    ensures forall |t: Self| 0 <= Self::as_int(t);
}

impl Deepview<int> for u32 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl StaticallySized for u32 {
    open spec fn uniform_size() -> usize { 4 } 

    // TODO(verus): Too bad this proof-free obligation can't be handled in the trait
    proof fn uniform_size_ensures() {}

    exec fn exec_uniform_size() -> usize { 4 } 
}

impl IntFormattable for u32 {
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

        // Another case of https://github.com/verus-lang/verus/issues/1150
        assert forall |x: Self|
            #![trigger Self::spec_to_le_bytes(x)]
        {
          &&& Self::spec_to_le_bytes(x).len() == Self::uniform_size()
          &&& Self::spec_from_le_bytes(Self::spec_to_le_bytes(x)) == x
        } by {
        }
    }

    open spec fn as_int(t: u32) -> int { t as int }

    proof fn as_int_ensures() { }

    proof fn this_type_fits_in_usize() {}

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

    proof fn nonnegative() {}
}

impl Deepview<int> for u64 {
    //type DV = int;
    open spec fn deepv(&self) -> int { *self as int }
}

impl StaticallySized for u64 {
    open spec fn uniform_size() -> usize { 8 } 

    // TODO(verus): Too bad this proof-free obligation can't be handled in the trait
    proof fn uniform_size_ensures() {}

    exec fn exec_uniform_size() -> usize { 8 } 
}

impl IntFormattable for u64 {
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

    proof fn this_type_fits_in_usize() {}

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

    proof fn nonnegative() {}
}

//////////////////////////////////////////////////////////////////////////////

pub struct IntFormat<T: IntFormattable> {
    // This field makes Rust stop complaining about the inner type parameters in the parameter
    // list.
    pub _p: std::marker::PhantomData<(T,)>,
}

impl<T: IntFormattable> IntFormat<T>
{
    #[verifier(external_body)]
    pub fn new() -> (s: Self)
        ensures s.valid()
    {
        Self{ _p: Default::default() }
    }
    
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
}

impl<T: IntFormattable> Marshal for IntFormat<T>
{
    type DV = int;
    type U = T;

    open spec fn valid(&self) -> bool
    {
        true
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        T::uniform_size() <= data.len()
    }

    exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        let l = slice.len();
        let p = T::exec_uniform_size() <= l;
        assert( slice@.valid(data@) ); // decoy trait recommends
        proof {
            assert( l == slice@.i(data@).len() );
            if p {
                assert( T::uniform_size() <= data@.len() );
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
        T::uniform_size()
    }

    fn exec_size(&self, value: &T) -> (sz: usize)
    {
        T::exec_uniform_size()
    }

    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        T::as_int(T::spec_from_le_bytes(data.subrange(0, T::uniform_size() as int)))
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<T>)
    {
        proof { T::as_int_ensures(); }
        // TODO(verus): shouldn't need to trigger this; it's in our (inherited) requires
        assert( slice@.valid(data@) );

        if T::exec_uniform_size() <= slice.len() {
            let sr = slice_subrange(data.as_slice(), slice.start, slice.start+T::exec_uniform_size());
            let parsed = T::from_le_bytes(sr);
            assert( sr@ == slice@.i(data@).subrange(0, T::uniform_size() as int) ); // trigger
            assert( parsed.deepv() == self.parse(slice@.i(data@)) );
            Some(parsed)
        } else {
            assert( !self.parsable(slice@.i(data@)) );
            None
        }
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: T)
    {
        assume( false );    // I think there's instability here
        
        proof { T::as_int_ensures(); }
        let sr = slice_subrange(data.as_slice(), slice.start, slice.start+T::exec_uniform_size());
        assert( sr@ == slice@.i(data@).subrange(0, T::uniform_size() as int) ); // trigger
        T::from_le_bytes(sr)
    }

    exec fn exec_marshall(&self, value: &T, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        proof { T::as_int_ensures(); }

        let s = T::to_le_bytes(*value);
        assert( s@.subrange(0, T::uniform_size() as int) =~= s@ ); // need a little extensionality? Do it by hand!
        let end = Self::install_bytes(&s, data, start);

        assert( data@.subrange(start as int, end as int) == s@ );   // trigger
        assert( T::spec_from_le_bytes(T::spec_to_le_bytes(*value)) == *value )
            by { T::lemma_auto_spec_to_from_le_bytes(); }

        end
    }
}

impl<T: IntFormattable> UniformSized for IntFormat<T> {
    open spec fn uniform_size(&self) -> (sz: usize)
    {
        T::uniform_size()
    }

    proof fn uniform_size_ensures(&self)
    ensures 0 < T::uniform_size()
    {
        T::uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    ensures sz == T::uniform_size()
    {
        T::exec_uniform_size()
    }
}

} // verus!
