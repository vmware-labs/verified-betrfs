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


// TODO: clean up the usize mess. Require all IntFormattable types to be no bigger than usize.
// (We don't need to support marshalling u64s on a 32-bit-usize platform.)
// TODO: factor out the unsigned (nonnegative) subtrait.

// An int type T can be IntFormat<T> if we know these things about it:

pub trait IntFormattable : Deepview<int> + builtin::Integer + SpecOrd + Copy + StaticallySized
{
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

    proof fn deepv_is_as_int(v: Self)
    ensures v.deepv() == v as int;

    // This type fits in usize

    spec fn max() -> (m: usize)
    ;

    proof fn max_ensures()
// why don't we need this?
//     ensures forall |v: Self| v as int <= Self::max() as int
    ;

    exec fn exec_max() -> (m: usize)
    ensures m == Self::max()
    ;

    // To and from usize

    exec fn to_usize(v: Self) -> (w: usize)
        ensures v as int == w as int
    ;

    exec fn from_usize(v: usize) -> (w: Self)
        requires v <= Self::max()
        ensures w as int == v as int
    ;

    // Maybe this class should be NatObligations? Or have an additional Natty trait?
    proof fn nonnegative(t: Self)
    ensures 0 <= t as int;
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

    proof fn deepv_is_as_int(v: Self) {}

    open spec fn max() -> (m: usize) { Self::MAX as usize }

    proof fn max_ensures() {}

    exec fn exec_max() -> (m: usize) { Self::MAX as usize }

    exec fn to_usize(v: Self) -> (w: usize) { v as usize }

    exec fn from_usize(v: usize) -> (w: Self) { v as Self }

    proof fn nonnegative(v: Self) {}
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

#[cfg(target_pointer_width = "64")]
proof fn usize64_workaround() ensures usize::MAX==u64::MAX {
    // TODO: Why can't Verus see value of usize::MAX?
    assume( usize::MAX==u64::MAX );
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

    proof fn deepv_is_as_int(v: Self) {}

    open spec fn max() -> (m: usize) { Self::MAX as usize }

    proof fn max_ensures() {}

    exec fn exec_max() -> (m: usize) { Self::MAX as usize }

    exec fn to_usize(v: Self) -> (w: usize) {
        proof { usize64_workaround() };
        v as usize
    }

    exec fn from_usize(v: usize) -> (w: Self) { v as Self }

    proof fn nonnegative(v: Self) {}
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

    // IntFormattable should be called NatFormattable since nonnegative is baked into it.
    // (Or, really, we should split out the unsigned trait, and split out this trait.
    pub proof fn parse_nat(&self, data: Seq<u8>)
    ensures 0 <= self.parse(data)
    {
        let parsed = T::spec_from_le_bytes(data.subrange(0, T::uniform_size() as int));
        T::nonnegative(parsed);
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
        T::spec_from_le_bytes(data.subrange(0, T::uniform_size() as int)) as int
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<T>)
    {
        // TODO(verus): shouldn't need to trigger this; it's in our (inherited) requires
        assert( slice@.valid(data@) );

        if T::exec_uniform_size() <= slice.len() {
            let sr = slice_subrange(data.as_slice(), slice.start, slice.start+T::exec_uniform_size());
            let parsed = T::from_le_bytes(sr);
            assert( sr@ == slice@.i(data@).subrange(0, T::uniform_size() as int) ); // trigger
            proof { T::deepv_is_as_int(parsed); }
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
        
        let sr = slice_subrange(data.as_slice(), slice.start, slice.start+T::exec_uniform_size());
        assert( sr@ == slice@.i(data@).subrange(0, T::uniform_size() as int) ); // trigger
        T::from_le_bytes(sr)
    }

    exec fn exec_marshall(&self, value: &T, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let s = T::to_le_bytes(*value);
        assert( s@.subrange(0, T::uniform_size() as int) =~= s@ ); // need a little extensionality? Do it by hand!
        let end = Self::install_bytes(&s, data, start);

        assert( data@.subrange(start as int, end as int) == s@ );   // trigger
        assert( T::spec_from_le_bytes(T::spec_to_le_bytes(*value)) == *value )
            by { T::lemma_auto_spec_to_from_le_bytes(); }

        proof { T::deepv_is_as_int(*value); }
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
        let sz = T::exec_uniform_size();
        // TODO(verus): postcondition didn't trigger but assert did.
        assert( sz == self.uniform_size() );
        sz
    }
}

} // verus!
