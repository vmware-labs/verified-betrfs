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

pub struct KeyedMessageFormat {
    vfmt: VariableSizedElementSeqFormat<UniformSizedElementSeqFormat<IntFormat<u8>>, u16, u16>,
}

const KEY_SLOT: usize = 0;
const VALUE_SLOT: usize = 1;

impl KeyedMessageFormat {
    pub closed spec fn internal_valid(&self) -> bool
    {
        &&& self.vfmt.seq_valid()
    }

    pub closed spec fn internal_marshallable(&self, key_len: usize, value_len: usize) -> bool
    {
        &&& self.internal_valid()
        &&& Self::fits(key_len + value_len)
        &&& self.vfmt.total_size() == Self::required_size(key_len + value_len)
    }

    // A data container capable of receiving key and value of this len
    pub closed spec fn is_container(&self, data: Seq<u8>, key_len: usize, value_len: usize) -> bool
    {
        &&& self.internal_marshallable(key_len, value_len)
//         &&& self.vfmt.total_size() <= data.len()
    }

    // A data container capable of supplying a key and a value
    pub closed spec fn filled(&self, data: Seq<u8>) -> bool
    {
        &&& self.internal_valid()
//         &&& self.vfmt.total_size() <= data.len()
        &&& self.vfmt.gettable(data, KEY_SLOT as int)
        &&& self.vfmt.elt_parsable(data, KEY_SLOT as int)
        &&& self.vfmt.gettable(data, VALUE_SLOT as int)
        &&& self.vfmt.elt_parsable(data, VALUE_SLOT as int)
    }

    pub open spec fn spec_overhead() -> int
    {
         u16::uniform_size() + u16::uniform_size() + u16::uniform_size()
    }

    pub open spec fn required_size(kv_capacity: int) -> int
    {
        Self::spec_overhead() + kv_capacity
    }

    pub open spec fn fits(kv_capacity: int) -> bool
    {
        Self::required_size(kv_capacity) <= u16::MAX
    }

    pub exec fn exec_overhead() -> usize
    {
         u16::exec_uniform_size() + u16::exec_uniform_size() + u16::exec_uniform_size()
    }

    pub exec fn exec_required_size(key_len: usize, value_len: usize) -> (out: usize)
    requires
        Self::fits(key_len + value_len),
    ensures
        out as int == Self::required_size(key_len + value_len)
    {
        Self::exec_overhead() + key_len + value_len
    }

    pub closed spec fn size(&self) -> int
    {
        self.vfmt.total_size() as int
    }

    pub exec fn exec_size(&self) -> usize
    {
        self.vfmt.exec_total_size()
    }

    // Construct a formatter for key and value of known size
    pub exec fn new(backing_capacity: usize) -> (s: Self)
    requires
        backing_capacity <= u16::MAX,
    ensures
        s.internal_valid(),
        s.size() == backing_capacity,
        // TODO ensures we can store_key_value() it with this key and data
    {
        // Sneaky knowledge of how VariableSizedElementSeq works
        let u16size = u16::exec_uniform_size();
        let elt_format = UniformSizedElementSeqFormat::new(IntFormat::<u8>::new());
        let bdy_int_fmt = IntFormat::<u16>::new();
        let lenf = IntFormat::<u16>::new();
        let vfmt = VariableSizedElementSeqFormat::new(elt_format, bdy_int_fmt, lenf, backing_capacity);
        let s = KeyedMessageFormat{vfmt};
        s
    }

    // TOOD silly placeholder
        exec fn prealloc(len: usize) -> (out: Vec<u8>)
            ensures
                out.len() == len,
        {
            let mut out = Vec::new();
            let mut i = 0;
            while i < len
                invariant
                    i <= len,
                    out.len() == i,
            {
                out.push(0);
                i += 1;
            }
            out
        }

    pub exec fn construct(kvpair: &KVPair) -> (out: Vec<u8>)
    requires
        Self::fits(kvpair.key.len() + kvpair.value.len()),
    ensures
        out.len() == Self::required_size(kvpair.key.len() + kvpair.value.len()),
    {
        let kmf = Self::new(Self::exec_required_size(kvpair.key.len(), kvpair.value.len()));
        let len = kmf.vfmt.exec_total_size();
        let mut data = Self::prealloc(len);
        kmf.store_key_value(&Slice::all(&data), &mut data, &kvpair);
        data
    }

    // inner part of marshal
    pub exec fn store_key_value(&self, slice: &Slice, data: &mut Vec<u8>, kvpair: &KVPair)
    requires
        self.is_container(slice@.i(old(data)@), kvpair.key.len(), kvpair.value.len()),
        slice@.valid(old(data)@),
    ensures
        self.filled(slice@.i(data@)),
        data@.len() == old(data)@.len(),
        slice@.agree_beyond_slice(old(data)@, data@),
        self.parse(slice@.i(data@)) == kvpair.deepv(),
    {
        // zero the array in this slice
        self.vfmt.initialize(&slice, data);

        // install the key
        self.vfmt.exec_append(&slice, data, &kvpair.key);

        let ghost middle = slice@.i(data@);

        // install the value
        self.vfmt.exec_append(&slice, data, &kvpair.value);

        // trigger: value append didn't stomp the key
        assert( self.vfmt.preserves_entry(middle, KEY_SLOT as int, slice@.i(data@)) );
    }

    // TODO Want to borrow the data! Read it in-place, let caller copy as needed.
    pub exec fn exec_parse_key(&self, slice: &Slice, data: &Vec<u8>) -> (key: Vec<u8>)
    requires
        slice@.valid(data@),
        self.filled(slice@.i(data@)),
    {
        self.vfmt.exec_get_elt(slice, data, KEY_SLOT)
    }

    pub exec fn exec_parse_value(&self, slice: &Slice, data: &Vec<u8>) -> (value: Vec<u8>)
    requires
        slice@.valid(data@),
        self.filled(slice@.i(data@)),
    {
        self.vfmt.exec_get_elt(slice, data, VALUE_SLOT)
    }
}

impl Marshal for KeyedMessageFormat {
    type DV = SpecKVPair;
    type U = KVPair;

    open spec fn valid(&self) -> bool
    {
        self.internal_valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.filled(data)
    }

    // TODO rename filled->parsable, is_container -> marshallable?
    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        self.internal_marshallable(value.key.len() as usize, value.value.len() as usize)
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        Self::required_size(value.key.len() + value.value.len() as int) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        Self::exec_required_size(value.key.len(), value.value.len())
    }

    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let key = self.vfmt.get_elt(data, KEY_SLOT as int);
        let value = self.vfmt.get_elt(data, VALUE_SLOT as int);
        SpecKVPair{key, value}
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        let key = self.vfmt.try_get_elt(slice, data, KEY_SLOT);
        let value = self.vfmt.try_get_elt(slice, data, VALUE_SLOT);
        if key.is_none() || value.is_none() {
            None
        } else {
            let kv = KVPair{key: key.unwrap(), value: value.unwrap()};
            assert( kv.deepv() == self.parse(slice@.i(data@)) );    // trigger -- should have come from trait? #1239 resurrected?
            Some(kv)
        }
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: Self::U)
    {
        self.try_parse(slice, data).unwrap()
    }

    // jonh skipping translation of Parse -- does it ever save more than
    // a cheap if condition?

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let len = Self::exec_required_size(value.key.len(), value.value.len());
        let slice = Slice{start: start, end: start + len};
        self.store_key_value(&slice, data, value);
        let end = start + len;
        assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
        end
    }
}

struct FlexibleKeyFmt {
}

impl FlexibleKeyFmt {
    pub exec fn new(key_data: &Vec<u8>, value_data: &Vec<u8>) -> (s: Self)
    {
        FlexibleKeyFmt{}
    }

    pub open spec fn spec_get_kmf(len: int) -> KeyedMessageFormat
    {
        KeyedMessageFormat::new(KeyedMessageFormat::required_size(len) as usize)
    }

    exec fn exec_get_kmf(len: usize) -> KeyedMessageFormat
    {
        KeyedMessageFormat::new(KeyedMessageFormat::exec_overhead() + len)
    }
}

impl Marshal for FlexibleKeyFmt {
    type DV = SpecKVPair;
    type U = KVPair;

    open spec fn valid(&self) -> bool
    {
        true
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        Self::spec_get_kmf(data.len() as int).filled(data)
    }

    // TODO rename filled->parsable, is_container -> marshallable?
    open spec fn marshallable(&self, kvpair: Self::DV) -> bool
    {
        KeyedMessageFormat::fits(kvpair.key.len() + kvpair.value.len() as int)
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        KeyedMessageFormat::required_size(value.key.len() + value.value.len() as int) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        KeyedMessageFormat::exec_required_size(value.key.len(), value.value.len())
    }

    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let kmf = Self::spec_get_kmf(data.len() as int);
        kmf.parse(data)
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        let kmf = Self::exec_get_kmf(data.len());
        kmf.try_parse(slice, data)
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: Self::U)
    {
        self.try_parse(slice, data).unwrap()
    }

    // jonh skipping translation of Parse -- does it ever save more than
    // a cheap if condition?

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let kmf = Self::exec_get_kmf(data.len());
        kmf.exec_marshall(value, data, start)
    }
}


}