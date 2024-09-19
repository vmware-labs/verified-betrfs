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
        assert( self.get_keylen_slice().i(slice@.i(data@)) == keylen_slice@.i(data@) );
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
            let key_slice = self.get_key_slice(keylen);
            let value_slice = self.get_value_subslice(SpecSlice::all(data), keylen);

        &&& self.data_fmt.parsable(key_slice.i(data))
        &&& value_slice.wf()    // can't have a negative-length value
        &&& self.data_fmt.parsable(value_slice.i(data))
        }
    }

    closed spec fn marshallable(&self, kvpair: Self::DV) -> bool
    {
        &&& self.keylen_fmt.uniform_size()
            + self.data_fmt.spec_size(kvpair.key)
            + self.data_fmt.spec_size(kvpair.value) <= usize::MAX
        &&& self.data_fmt.spec_size(kvpair.key) <= u16::MAX
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
        if slice.len() < self.keylen_fmt.exec_uniform_size() { return None }

        let keylen_u16 = self.exec_try_get_keylen_elt(slice, data);
        if keylen_u16.is_none() { return None }

        let keylen = keylen_u16.unwrap() as usize;
        if slice.len() < keylen + self.keylen_fmt.exec_uniform_size() { return None }

        let key_slice = slice.subslice(self.keylen_fmt.exec_uniform_size(), self.keylen_fmt.exec_uniform_size() + keylen );
        let key = self.data_fmt.try_parse(&key_slice, data);
        if key.is_none() { return None }

        // value is whatever is left over
        let value_slice = Slice{ start: key_slice.end, end: slice.end };
        let value = self.data_fmt.try_parse(&value_slice, data);
        if value.is_none() { return None }

        let kvpair = KVPair{key: key.unwrap(), value: value.unwrap()};

        proof {
            let idata = slice@.i(data@);
            // trigger slice extn equality
            assert( key_slice@.i(data@) == self.get_key_slice(keylen as int).i(idata) );
            // trigger slice extn equality
            assert( value_slice@.i(data@)
                == self.get_value_subslice(SpecSlice::all(idata), keylen as int).i(idata) );

            // trigger KVPair extn equality (not triggered automatically because it's hiding in an
            // implication?)
            assert( kvpair.deepv() == self.parse(idata) );
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
        let keylen: u16 = self.data_fmt.exec_size(&kvpair.key) as u16;
        let keylen_end = self.keylen_fmt.exec_marshall(&keylen, data, start);

        let ghost keylendata = data@.subrange(start as int, keylen_end as int);
        proof {
            // trigger slice extn equality
            assert( self.get_keylen_slice().i(keylendata) == data@.subrange(start as int, keylen_end as int) );
//             assert( self.get_keylen_elt(keylendata) == keylen as int );
        }

//         assert( keylen_end == start + self.keylen_fmt.uniform_size() );

        let key_end = self.data_fmt.exec_marshall(&kvpair.key, data, keylen_end);

        let ghost rawdata2 = data@;
        let ghost keydata = rawdata2.subrange(start as int, key_end as int);
        proof {
            let keylen_specparsed = self.get_keylen_elt(keydata);
            // trigger extn equality
            assert( self.get_keylen_slice().i(keydata) == self.get_keylen_slice().i(keylendata) );
            // trigger extn equal
            assert( rawdata2.subrange(keylen_end as int, key_end as int)
                == self.get_key_slice(keylen_specparsed).i(keydata) );
            assert( self.data_fmt.parse(self.get_key_slice(keylen_specparsed).i(keydata)) ==
                kvpair.key.deepv() );
        }

        let end = self.data_fmt.exec_marshall(&kvpair.value, data, key_end);

        proof {
            let idata = data@.subrange(start as int, end as int);
            let keylen = self.get_keylen_elt(idata);
            let key_slice = self.get_key_slice(keylen);
            let value_slice = self.get_value_subslice(SpecSlice::all(idata), keylen);

            assert( self.get_keylen_slice().i(idata) == self.get_keylen_slice().i(keylendata) );  // trigger extn equality

//             assert( self.data_fmt.parsable(key_slice.i(idata)) );
//             assert( value_slice.wf() );
//             assert( self.data_fmt.parsable(value_slice.i(idata)) );

//             assert( self.parsable(data@.subrange(start as int, end as int)) );

            assert( self.parse(idata).key ==
                self.data_fmt.parse(self.get_key_slice(keylen).i(idata)) );

            assert( self.data_fmt.parse(self.get_key_slice(keylen).i(keydata)) ==
                kvpair.key.deepv() );

            let valuedata = data@.subrange(start as int, end as int);
            assert( key_slice.end <= keydata.len() );
            assert( keydata.len() <= valuedata.len() );
            assert( key_slice.end <= valuedata.len() );
            assert( key_slice.i(valuedata).len() == key_slice.i(keydata).len() );
            assert( key_slice.i(valuedata) == key_slice.i(keydata) );
            assert( self.data_fmt.parse(self.get_key_slice(keylen).i(valuedata)) ==
                kvpair.key.deepv() );

            assert( self.parse(idata).value ==
                self.data_fmt.parse(self.get_value_subslice(SpecSlice::all(idata), keylen).i(idata)) );

            assert( self.data_fmt.parse(data@.subrange(key_end as int, end as int)) ==
                kvpair.value.deepv() );
            // trigger extn equality for slice math on value.
            assert( data@.subrange(key_end as int, end as int) ==
                self.get_value_subslice(SpecSlice::all(idata), keylen).i(idata) );

            assert(
                self.data_fmt.parse(self.get_value_subslice(SpecSlice::all(idata), keylen).i(idata)) ==
                kvpair.value.deepv() );

            assert( self.parse(data@.subrange(start as int, end as int)).key == kvpair.key.deepv() );
            assert( self.parse(data@.subrange(start as int, end as int)).value == kvpair.value.deepv() );

            assert( self.parse(data@.subrange(start as int, end as int)) == kvpair.deepv() );
        }
        end
    }
}

}
