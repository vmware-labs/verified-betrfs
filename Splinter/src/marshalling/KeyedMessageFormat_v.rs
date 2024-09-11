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
    pub key: Seq<u8>,
    pub value: Seq<u8>,
}

pub struct KVPair {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

impl Deepview<SpecKVPair> for KVPair {
    open spec fn deepv(&self) -> SpecKVPair
    {
        SpecKVPair{key: self.key@, value: self.value@}
    }
}

pub struct KeyedMessageFormat {
    vfmt: VariableSizedElementSeqFormat<UniformSizedElementSeqFormat<IntFormat<u8>>, u16, u16>,
}

const KEY_SLOT: usize = 0;
const VALUE_SLOT: usize = 1;

impl KeyedMessageFormat {
    pub closed spec fn valid(&self) -> bool
    {
        &&& self.vfmt.seq_valid()
    }

    // A data container capable of receiving key and value of this len
    pub closed spec fn is_container(&self, data: Seq<u8>, key_len: usize, value_len: usize) -> bool
    {
        &&& self.valid()
        &&& self.vfmt.total_size() <= data.len()
        &&& Self::fits(key_len, value_len)
        &&& self.vfmt.total_size() == Self::required_size(key_len, value_len)
    }

    // A data container capable of supplying a key and a value
    pub closed spec fn filled(&self, data: Seq<u8>) -> bool
    {
        &&& self.valid()
        &&& self.vfmt.total_size() <= data.len()
        &&& self.vfmt.gettable(data, KEY_SLOT as int)
        &&& self.vfmt.elt_parsable(data, KEY_SLOT as int)
        &&& self.vfmt.gettable(data, VALUE_SLOT as int)
        &&& self.vfmt.elt_parsable(data, VALUE_SLOT as int)
    }

    pub open spec fn required_size(key_len: usize, value_len: usize) -> int
    {
         u16::uniform_size() + u16::uniform_size() + key_len + u16::uniform_size() + value_len
    }

    pub open spec fn fits(key_len: usize, value_len: usize) -> bool
    {
        Self::required_size(key_len, value_len) <= u16::MAX
    }

    pub exec fn exec_required_size(key_len: usize, value_len: usize) -> (out: usize)
    requires
        Self::fits(key_len, value_len),
    ensures
        out as int == Self::required_size(key_len, value_len)
    {
         u16::exec_uniform_size() + u16::exec_uniform_size() + key_len + u16::exec_uniform_size() + value_len
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
    pub exec fn new(key_data: &Vec<u8>, value_data: &Vec<u8>) -> (s: Self)
    requires
        Self::fits(key_data.len(), value_data.len()),
    ensures
        s.valid(),
        s.size() == Self::required_size(key_data.len(), value_data.len()),
        // TODO ensures we can store_key_value() it with this key and data
    {
        // Sneaky knowledge of how VariableSizedElementSeq works
        let u16size = u16::exec_uniform_size();
        let total_size = u16size + u16size + key_data.len() + u16size + value_data.len();
        let elt_format = UniformSizedElementSeqFormat::new(IntFormat::<u8>::new());
        let bdy_int_fmt = IntFormat::<u16>::new();
        let lenf = IntFormat::<u16>::new();
        let vfmt = VariableSizedElementSeqFormat::new(elt_format, bdy_int_fmt, lenf, total_size);
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

    pub exec fn construct(key_data: &Vec<u8>, value_data: &Vec<u8>) -> (out: Vec<u8>)
    requires
        Self::fits(key_data.len(), value_data.len()),
    ensures
        out.len() == Self::required_size(key_data.len(), value_data.len()),
    {
        let kmf = Self::new(key_data, value_data);
        let len = kmf.vfmt.exec_total_size();
        let mut data = Self::prealloc(len);
        kmf.store_key_value(&mut data, key_data, value_data);
        data
    }

    pub exec fn store_key_value(&self, data: &mut Vec<u8>, key_data: &Vec<u8>, value_data: &Vec<u8>)
    requires
        self.is_container(old(data)@, key_data.len(), value_data.len()),
    ensures
        self.filled(data@),
        data@.len() == old(data)@.len(),
    {
        let slice = Slice::all(data);
        proof{ SpecSlice::all_ensures::<u8>() };
        self.vfmt.initialize(&slice, data);
        self.vfmt.exec_append(&slice, data, key_data);

        assert( self.vfmt.gettable(slice@.i(data@), KEY_SLOT as int) ); // trigger
        assert( self.vfmt.appendable(slice@.i(data@), value_data.deepv()) );    // trigger
        self.vfmt.exec_append(&slice, data, value_data);

        assert( slice@.i(data@) == data@ );  // extn equality trigger
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

}
