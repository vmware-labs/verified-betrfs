// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
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

pub trait KVTrait {
//     type KDV;
//     type K: Deepview<Self::KDV>;
//     type VDV;
//     type V: Deepview<Self::VDV>;

    // This trait bundles both the deepv relationships
    // (above) and the formatter decisions (below).
    // I'm okay with that, because I don't think we're ever
    // going to care to decouple those decisions.
    type LenType: IntFormattable;
    type KeyFormat: Marshal;
    type DataFormat: Marshal;

    exec fn key_format_new() -> Self::KeyFormat;
    exec fn data_format_new() -> Self::DataFormat;
}

pub struct SpecKVPair<KVTypes: KVTrait> {
    pub key: <KVTypes::KeyFormat as Marshal>::DV,
    pub value: <KVTypes::DataFormat as Marshal>::DV,
}

// TODO: Generalize from Vec<u8> to some Deepviewable types.
pub struct KVPair<KVTypes: KVTrait> {
    pub key: <KVTypes::KeyFormat as Marshal>::U,
    pub value: <KVTypes::DataFormat as Marshal>::U,
}

impl<KVTypes: KVTrait> Deepview<SpecKVPair<KVTypes>> for KVPair<KVTypes> {
    open spec fn deepv(&self) -> SpecKVPair<KVTypes>
    {
        SpecKVPair{key: self.key.deepv(), value: self.value.deepv()}
    }
}

pub struct KVPairFormat<KVTypes: KVTrait> {
    pub keylen_fmt: IntFormat::<KVTypes::LenType>,
    pub key_fmt: KVTypes::KeyFormat,
    pub data_fmt: KVTypes::DataFormat,
}

impl<KVTypes: KVTrait> KVPairFormat<KVTypes> {
    pub exec fn new() -> Self
    {
        KVPairFormat {
            keylen_fmt: IntFormat::<KVTypes::LenType>::new(),
            key_fmt: KVTypes::key_format_new(),
            data_fmt: KVTypes::data_format_new(),
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

    closed spec fn key_fits(&self, base_slice: SpecSlice, keylen: int) -> bool
    {
        &&& self.keylen_fmt.uniform_size() + keylen <= usize::MAX
        &&& self.keylen_fmt.uniform_size() + keylen <= base_slice.len()
    }

    exec fn exec_key_fits(&self, base_slice: &Slice, keylen: usize) -> (out: bool)
    requires
        base_slice@.wf(),
        self.keylen_fmt.uniform_size() + keylen <= usize::MAX,
    ensures out == self.key_fits(base_slice@, keylen as int)
    {
        self.keylen_fmt.exec_uniform_size() + keylen <= base_slice.len()
    }

    exec fn exec_get_key_slice(&self, base_slice: &Slice, keylen: usize) -> (out: Slice)
    requires self.key_fits(base_slice@, keylen as int)
    ensures out@ == base_slice@.xslice(self.get_key_slice(keylen as int))
    {
        let keylenlen = self.keylen_fmt.exec_uniform_size();
        base_slice.xslice(&Slice{ start: keylenlen, end: keylenlen + keylen })
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
        out@ == slice@.subslice(self.get_keylen_slice().start, self.get_keylen_slice().end),
    {
        slice.xslice(&Slice{start: 0, end: self.keylen_fmt.exec_uniform_size()})
    }

    exec fn exec_get_keylen_elt(&self, slice: &Slice, data: &Vec<u8>) -> KVTypes::LenType
    requires
        self.keylen_fmt.uniform_size() <= slice@.len(), // TODO move to wf
        slice@.valid(data@),
        self.keylen_fmt.parsable(self.get_keylen_slice().i(data@)),
    {
        let keylen_slice = self.exec_get_keylen_subslice(slice);
        self.keylen_fmt.exec_parse(&keylen_slice, data)
    }

    exec fn exec_try_get_keylen_elt(&self, slice: &Slice, data: &Vec<u8>) -> (out: Option<KVTypes::LenType>)
    requires
        self.keylen_fmt.uniform_size() <= slice@.len(), // TODO move to wf
        slice@.valid(data@),
    ensures
        out is Some <==> self.get_keylen_elt_parsable(slice@.i(data@)),
        out is Some ==> out.unwrap().deepv() == self.get_keylen_elt(slice@.i(data@)),
    {
        if slice.len() < self.keylen_fmt.exec_uniform_size() { return None }
        let keylen_slice = self.exec_get_keylen_subslice(slice);
        let out = self.keylen_fmt.try_parse(&keylen_slice, data);
        assert( self.get_keylen_slice().i(slice@.i(data@)) == keylen_slice@.i(data@) );
        proof { KVTypes::LenType::deepv_is_as_int(out.unwrap()) };
        out
    }
}

impl<KVTypes: KVTrait> Marshal for KVPairFormat<KVTypes> {
    type DV = SpecKVPair<KVTypes>;
    type U = KVPair<KVTypes>;

    open spec fn valid(&self) -> bool
    {
        // The biggest possible parsed keylen plus the keylen field must fit in a usize
        // so we can do exec math on it.
        // TODO: This definition excludes LenType==u64. I guess we'd need to change the
        // math in try_parse to enable u64 LenTypes.
        &&& KVTypes::LenType::max() + self.keylen_fmt.uniform_size() <= usize::MAX
        &&& self.key_fmt.valid()
        &&& self.data_fmt.valid()
    }

    closed spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.get_keylen_elt_parsable(data)
        &&& { let keylen = self.get_keylen_elt(data);
            let key_slice = self.get_key_slice(keylen);
            let value_slice = self.get_value_subslice(SpecSlice::all(data), keylen);

        &&& self.key_fmt.parsable(key_slice.i(data))
        &&& value_slice.wf()    // can't have a negative-length value
        &&& self.data_fmt.parsable(value_slice.i(data))
        }
    }

    open spec fn marshallable(&self, kvpair: Self::DV) -> bool
    {
        &&& self.key_fmt.marshallable(kvpair.key)
        &&& self.data_fmt.marshallable(kvpair.value)
        &&& self.keylen_fmt.uniform_size()
            + self.key_fmt.spec_size(kvpair.key)
            + self.data_fmt.spec_size(kvpair.value) <= usize::MAX
        &&& self.key_fmt.spec_size(kvpair.key) <= KVTypes::LenType::max()
    }

    open spec fn spec_size(&self, kvpair: Self::DV) -> usize
    {
        (
            self.keylen_fmt.uniform_size()
            + self.key_fmt.spec_size(kvpair.key)
            + self.data_fmt.spec_size(kvpair.value)
        ) as usize
    }

    exec fn exec_size(&self, kvpair: &Self::U) -> (sz: usize)
    {
        self.keylen_fmt.exec_uniform_size()
        + self.key_fmt.exec_size(&kvpair.key)
        + self.data_fmt.exec_size(&kvpair.value)
    }

    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let keylen = self.get_keylen_elt(data);
        let key = self.key_fmt.parse(self.get_key_slice(keylen).i(data));
        let value = self.data_fmt.parse(self.get_value_subslice(SpecSlice::all(data), keylen).i(data));
        SpecKVPair{ key, value }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < self.keylen_fmt.exec_uniform_size() { return None }

        let keylen_lentype = self.exec_try_get_keylen_elt(slice, data);
        if keylen_lentype.is_none() { return None }

        assert( keylen_lentype.unwrap().deepv() == self.get_keylen_elt(slice@.i(data@)) );

        let keylen = KVTypes::LenType::to_usize(keylen_lentype.unwrap());

        proof { KVTypes::LenType::deepv_is_as_int_forall(); }
//         assert( keylen as int == keylen_lentype.unwrap().deepv() ); //tidy

        proof { KVTypes::LenType::max_ensures(keylen_lentype.unwrap()); }
        if !self.exec_key_fits(slice, keylen) {
            // keylen describes more data than we have in the slice
            return None
        }

        let key_slice = self.exec_get_key_slice(slice, keylen);

        assert( key_slice@.wf() );
        assert( key_slice.start <= key_slice.end );
        assert( key_slice.end <= slice.end );

        let ghost l_data = slice@.i(data@);
        let ghost l_keylen = self.get_keylen_elt(l_data);
        let ghost l_key_slice = self.get_key_slice(l_keylen);
        assert( l_key_slice.i(l_data) == key_slice@.i(data@) ); // extn

        if !self.key_fmt.exec_parsable(&key_slice, data) {
            return None
        }

        let key_slice = slice.subslice(self.keylen_fmt.exec_uniform_size(), self.keylen_fmt.exec_uniform_size() + keylen );
        let key = self.key_fmt.try_parse(&key_slice, data);
        if key.is_none() {
            return None
        }

        // value is whatever is left over
        let value_slice = Slice{ start: key_slice.end, end: slice.end };
        let value = self.data_fmt.try_parse(&value_slice, data);
        let ghost l_value_slice = self.get_value_subslice(SpecSlice::all(l_data), l_keylen);
        assert( l_value_slice.i(l_data) == value_slice@.i(data@) ); // extn
        if value.is_none() {
            return None
        }

        let kvpair = KVPair{key: key.unwrap(), value: value.unwrap()};

        proof {
            let idata = slice@.i(data@);
            // trigger slice extn equality
            assert( key_slice@.i(data@) == self.get_key_slice(keylen as int).i(idata) );
            // trigger slice extn equality
            assert( value_slice@.i(data@)
                == self.get_value_subslice(SpecSlice::all(idata), keylen as int).i(idata) );
            assert( kvpair.deepv() == self.parse(idata) );  // extn
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
        // ** Learn the key len
        let keylen: KVTypes::LenType = KVTypes::LenType::from_usize(self.key_fmt.exec_size(&kvpair.key));

        // ** Marshall the key len
        let keylen_end = self.keylen_fmt.exec_marshall(&keylen, data, start);

        let ghost data_after_keylen = data@.subrange(start as int, keylen_end as int);
        // trigger slice extn equality
        assert( self.get_keylen_slice().i(data_after_keylen) == data@.subrange(start as int, keylen_end as int) );

        // ** Marshall the key
        let key_end = self.key_fmt.exec_marshall(&kvpair.key, data, keylen_end);

        let ghost data_after_key = data@.subrange(start as int, key_end as int);
        proof {
            KVTypes::LenType::deepv_is_as_int(keylen);

            // trigger extn equality
            assert( self.get_keylen_slice().i(data_after_key) == self.get_keylen_slice().i(data_after_keylen) );

            // trigger extn equal
            assert( data@.subrange(keylen_end as int, key_end as int)
                == self.get_key_slice(self.get_keylen_elt(data_after_key)).i(data_after_key) );

            // goal
//             assert( self.data_fmt.parse(self.get_key_slice(self.get_keylen_elt(data_after_key)).i(data_after_key)) ==
//                 kvpair.key.deepv() );
        }

        // ** Marshall the value
        let end = self.data_fmt.exec_marshall(&kvpair.value, data, key_end);

        proof {
            let data_after_value = data@.subrange(start as int, end as int);
            let keylen = self.get_keylen_elt(data_after_value);
            let key_slice = self.get_key_slice(keylen);

            assert( self.get_keylen_slice().i(data_after_value) == self.get_keylen_slice().i(data_after_keylen) );  // trigger extn equality

            // trigger extn equality: we didn't touch key_slice since we got it to parse correctly
            assert( key_slice.i(data@.subrange(start as int, end as int)) == key_slice.i(data_after_key) );
            // trigger extn equality for slice math on value.
            assert( data@.subrange(key_end as int, end as int) ==
                self.get_value_subslice(SpecSlice::all(data_after_value), keylen).i(data_after_value) );

            // goal
//             assert( self.parse(data@.subrange(start as int, end as int)) == kvpair.deepv() );
        }
        end
    }
}

}
