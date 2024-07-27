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

pub struct KeyedMessageFormat {
    vfmt: VariableSizedElementSeqFormat<UniformSizedElementSeqFormat<IntFormat<u8>>, u8, u8>,
}

const KEY_SLOT: usize = 0;
const VALUE_SLOT: usize = 0;

impl KeyedMessageFormat {
    // Construct a formatter for key and value of known size
    pub exec fn new(key_data: &Vec<u8>, value_data: &Vec<u8>) -> Self
        // TODO ensures we can store_key_value() it with this key and data
    {
        assume(false);
        // Sneaky knowledge of how VariableSizedElementSeq works
        let u32size = u32::exec_uniform_size();
        let total_size = u32size + u32size + key_data.len() + u32size + value_data.len();
        let elt_format = UniformSizedElementSeqFormat::new(IntFormat::<u8>::new());
        let vfmt = VariableSizedElementSeqFormat::new(elt_format, IntFormat::<u8>::new(), IntFormat::<u8>::new(), total_size);
        KeyedMessageFormat{vfmt}
    }

    pub exec fn construct(key_data: &Vec<u8>, value_data: &Vec<u8>) -> Vec<u8>
    {
        let kmf = Self::new(key_data, value_data);
        let mut data = Vec::with_capacity(kmf.vfmt.exec_total_size());
        kmf.store_key_value(&Slice::all(&data), &mut data, key_data, value_data);
        data
    }

    pub exec fn store_key_value(&self, slice: &Slice, data: &mut Vec<u8>, key_data: &Vec<u8>, value_data: &Vec<u8>)
    {
        assume(false);
        self.vfmt.exec_append(slice, data, key_data);
        self.vfmt.exec_append(slice, data, value_data);
    }

    // TODO Want to borrow the data! Read it in-place, let caller copy as needed.
    pub exec fn exec_parse_key(&self, slice: &Slice, key_data: &Vec<u8>) -> (key: Vec<u8>)
    {
        assume(false);
        self.vfmt.exec_get_elt(slice, key_data, KEY_SLOT)
    }

    pub exec fn exec_parse_value(&self, slice: &Slice, value_data: &Vec<u8>) -> (value: Vec<u8>)
    {
        assume(false);
        self.vfmt.exec_get_elt(slice, value_data, VALUE_SLOT)
    }
}

}
