// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::StaticallySized_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::VariableSizedElementSeq_v::*;

verus! {

pub struct SpecKVPair {
    pub key: Seq<int>,
    pub value: Seq<int>,
}

// TODO: Generalize from Vec<u8> to some Deepviewable types.
pub struct KVPair {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

impl Deepview<SpecKVPair> for KVPair {
    open spec fn deepv(&self) -> SpecKVPair
    {
        SpecKVPair{key: self.key.deepv(), value: self.value.deepv()}
    }
}

struct KVPairFormat {
    keylen_fmt: IntFormat::<u16>,
    data_fmt: UniformSizedElementSeqFormat<IntFormat::<u8>>,
}

impl KVPairFormat {
    exec fn new() -> Self
    {
        KVPairFormat {
            keylen_fmt: IntFormat::<u16>::new(),
            data_fmt: UniformSizedElementSeqFormat::new(IntFormat::<u8>::new()),
        }
    }

    closed spec fn get_keylen_slice(&self) -> SpecSlice
    {
        SpecSlice{start: 0, end: self.keylen_fmt.uniform_size() as int}
    }

    closed spec fn get_keylen_elt_parsable(&self, data: Seq<u8>) -> bool
    {
        // slice is big enough
        &&& self.get_keylen_slice().valid(data)
        // keylen parser can parse the contents
        &&& self.keylen_fmt.parsable(self.get_keylen_slice().i(data))
    }

    closed spec fn get_keylen_elt(&self, data: Seq<u8>) -> int
    {
        self.keylen_fmt.parse(self.get_keylen_slice().i(data))
    }

    closed spec fn get_key_slice(&self, keylen: int) -> SpecSlice
    {
        SpecSlice{
            start: self.keylen_fmt.uniform_size() as int,
            end: self.keylen_fmt.uniform_size() + keylen }
    }

    // Value slice info depends on knowing the overall slice length allocated to the marshalled KVPair
    closed spec fn get_value_subslice(&self, slice: SpecSlice, keylen: int) -> SpecSlice
    {
        slice.drop(self.get_key_slice(keylen).end)
    }

    // TODO(refactor): in SeqMarshalling, rename _get -> _get_slice
    exec fn exec_get_keylen_subslice(&self, slice: &Slice) -> (out: Slice)
    requires
        slice@.wf(),
        self.keylen_fmt.uniform_size() <= slice@.len(),
    ensures
        out@.wf(),
        out@.is_subslice(slice@),
        out@ == slice@.subslice(self.get_keylen_slice().start, self.get_keylen_slice().end),
    {
        slice.subslice(0, self.keylen_fmt.exec_uniform_size())
    }

    exec fn exec_get_keylen_elt(&self, slice: &Slice, data: &Vec<u8>) -> u16
    requires
        self.keylen_fmt.uniform_size() <= slice@.len(), // TODO move to wf
        slice@.valid(data@),
        self.keylen_fmt.parsable(self.get_keylen_slice().i(data@)),
    {
        let keylen_slice = self.exec_get_keylen_subslice(slice);
        self.keylen_fmt.exec_parse(&keylen_slice, data)
    }

    exec fn exec_try_get_keylen_elt(&self, slice: &Slice, data: &Vec<u8>) -> (out: Option<u16>)
    requires
        self.keylen_fmt.uniform_size() <= slice@.len(), // TODO move to wf
        slice@.valid(data@),
    ensures
        out is Some <==> self.get_keylen_elt_parsable(slice@.i(data@)),
        out is Some ==> out.unwrap() == self.get_keylen_elt(slice@.i(data@)),
    {
        if slice.len() < self.keylen_fmt.exec_uniform_size() { return None }
        let keylen_slice = self.exec_get_keylen_subslice(slice);
        let out = self.keylen_fmt.try_parse(&keylen_slice, data);
        proof {
            u16::deepv_is_as_int_forall();
            if out is Some {
//                 assert(
//                     self.keylen_fmt.parsable(keylen_slice@.i(data@)) ==> out.unwrap().deepv() == self.keylen_fmt.parse(keylen_slice@.i(data@)) );
                assert( out.unwrap().deepv() == self.keylen_fmt.parse(keylen_slice@.i(data@)) );
//                 assert( out.unwrap()
//         self.parsable(slice@.i(data@)) ==> ov.unwrap().deepv() == self.parse(slice@.i(data@))

//                 assert( keylen_slice@ == self.get_keylen_slice() );
//                 assert( self.get_keylen_elt(keylen_slice@.i(data@))
//                     == self.keylen_fmt.parse(keylen_slice@.i(data@)) );
//                 
//                 assert( self.get_keylen_elt(slice@.i(data@))
//                     == self.keylen_fmt.parse(keylen_slice@.i(data@)) );

                assert( self.get_keylen_elt(slice@.i(data@)) == 
                    self.keylen_fmt.parse(self.get_keylen_slice().i(slice@.i(data@))) );
                assert( out.unwrap().deepv() ==
                    self.keylen_fmt.parse(keylen_slice@.i(data@)) );
                assert( self.get_keylen_slice().i(slice@.i(data@)) == keylen_slice@.i(data@) );

                assert( out.unwrap() == self.get_keylen_elt(slice@.i(data@)) );
            }
        }
        out
    }
}

impl Marshal for KVPairFormat {
    type DV = SpecKVPair;
    type U = KVPair;

    open spec fn valid(&self) -> bool
    {
        true
    }

    closed spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.get_keylen_elt_parsable(data)
        &&& { let keylen = self.get_keylen_elt(data);
        &&& self.data_fmt.parsable(self.get_key_slice(keylen).i(data))
        &&& self.data_fmt.parsable(self.get_value_subslice(SpecSlice::all(data), keylen).i(data))
        }
    }

    closed spec fn marshallable(&self, kvpair: Self::DV) -> bool
    {
        self.keylen_fmt.uniform_size()
            + self.data_fmt.spec_size(kvpair.key)
            + self.data_fmt.spec_size(kvpair.value) <= usize::MAX
    }

    closed spec fn spec_size(&self, kvpair: Self::DV) -> usize
    {
        (
            self.keylen_fmt.uniform_size()
            + self.data_fmt.spec_size(kvpair.key)
            + self.data_fmt.spec_size(kvpair.value)
        ) as usize
    }

    exec fn exec_size(&self, kvpair: &Self::U) -> (sz: usize)
    {
        self.keylen_fmt.exec_uniform_size()
        + self.data_fmt.exec_size(&kvpair.key)
        + self.data_fmt.exec_size(&kvpair.value)
    }

    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let keylen = self.get_keylen_elt(data);
        let key = self.data_fmt.parse(self.get_key_slice(keylen).i(data));
        let value = self.data_fmt.parse(self.get_value_subslice(SpecSlice::all(data), keylen).i(data));
        SpecKVPair{ key, value }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        let ghost idata = slice@.i(data@);
        if slice.len() < self.keylen_fmt.exec_uniform_size() { return None }

        let keylen_u16 = self.exec_try_get_keylen_elt(slice, data);
        if keylen_u16.is_none() {
            assert( !self.keylen_fmt.parsable(self.get_keylen_slice().i(idata)) );
            return None
        }

        assume( false );

        let keylen = keylen_u16.unwrap() as usize;
        let key_slice = slice.subslice(self.keylen_fmt.exec_uniform_size(), self.keylen_fmt.exec_uniform_size() + keylen );
        let key = self.data_fmt.try_parse(&key_slice, data);
        if key.is_none() { return None }

        // value is whatever is left over
        let value_slice = slice.drop( key_slice.end );
        let value = self.data_fmt.try_parse(&value_slice, data);
        if value.is_none() { return None }

        let kvpair = KVPair{key: key.unwrap(), value: value.unwrap()};
        proof {
//             assert( kvpair.deepv() == self.get_elt(slice@.i(data@)) );
        }
        Some(kvpair)
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (kvpair: Self::U)
    {
        self.try_parse(slice, data).unwrap()
    }

    // jonh skipping translation of Parse -- does it ever save more than
    // a cheap if condition?

    exec fn exec_marshall(&self, kvpair: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        0
    }
}

}
