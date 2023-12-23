// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use crate::marshalling::Slice_v::*;

verus! {

trait Marshalling<U> {
    spec fn valid(&self) -> bool;

    spec fn parsable(&self, data: Seq<u8>) -> bool
    recommends self.valid()
    ;

    spec fn parse(&self, data: Seq<u8>) -> U
    recommends 
        self.valid(),
        self.parsable(data)
    ;

    // Should this be slices? in verus-ironfleet, jayb used Vec<u8> + start
    fn try_parse(&self, data: &Vec<u8>) -> (ov: Option<U>)
    requires
        self.valid(),
    ensures
        self.parsable(data@) <==> ov is Some,
        self.parsable(data@) ==> ov.unwrap() == self.parse(data@)
    ;

    fn exec_parsable(&self, data: &Vec<u8>) -> (p: bool)
    requires
        self.valid(),
    ensures
        p == self.parsable(data@)
    ;

    // jonh skipping translation of Parse -- does it ever save more than
    // a cheap if condition?

    spec fn marshallable(&self, value: &U) -> bool
    ;

    spec fn size(&self, value: &U) -> u64
    recommends 
        self.valid(),
        self.marshallable(value)
    ;

    fn exec_size(&self, value: &U) -> (sz: u64)
    requires 
        self.valid(),
        self.marshallable(value),
    ensures
        sz == self.size(value)
    ;

    fn marshall(&self, value: &U, data: &mut Vec<u8>, start: u64) -> (end: u64)
    requires 
        self.valid(),
        self.marshallable(value),
        start as int + self.size(value) as int <= old(data).len(),
    ensures
        end == start + self.size(value),
        data.len() == old(data).len(),
        forall |i| 0 <= i < start ==> data[i] == old(data)[i],
        forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        self.parsable(data@.subrange(start as int, end as int)),
        self.parse(data@.subrange(start as int, end as int)) == value
    ;
}

// trait<I> NativePackedInt<I> {
//     spec fn spec_len() -> int;
// 
//     exec fn exec_len() -> (sz: usize)
//     ensures
//         sz as int == spec_len()
//     ;
// 
//     spec fn spec_parse_int(data: Seq<u8>) -> I
//     ;
// 
//     exec fn exec_parse_int(data: Vec<u8>) -> I
//     ensures
// 
//     ;
// }
// 
// impl NPI64 for NativePackedInt<u64> {
// u64_from_le_bytes
// 

struct IntegerMarshalling<I> {
    dummy: I,   // parameter I is never used
}

impl Marshalling<u32> for IntegerMarshalling<u32> {
    spec fn valid(&self) -> bool
    {
        true
    }

    spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        /*std::mem::size_of<u32>()*/
        4 <= data.len()
    }

    spec fn parse(&self, data: Seq<u8>) -> u32
    {
        spec_u32_from_le_bytes(data.subrange(0, 4))
    }

    // Should this be slices? in verus-ironfleet, jayb used Vec<u8> + start
    fn try_parse(&self, data: &Vec<u8>) -> (ov: Option<u32>)
    {
        if 4 <= data.len() {
            Some(u32_from_le_bytes(slice_subrange(data.as_slice(), 0, 4)))
        } else {
            None
        }
    }

    fn exec_parsable(&self, data: &Vec<u8>) -> (p: bool)
    {
        4 <= data.len()
    }

    spec fn marshallable(&self, value: &u32) -> bool
    {
        true
    }

    spec fn size(&self, value: &u32) -> u64
    {
        4
    }

    fn exec_size(&self, value: &u32) -> (sz: u64)
    {
        4
    }

    fn marshall(&self, value: &u32, data: &mut Vec<u8>, start: u64) -> (end: u64)
    {
        // TODO this interface from verus pervasive bytes.rs can't be fast...
        let s = u32_to_le_bytes(*value);
        proof { lemma_auto_spec_u32_to_from_le_bytes(); }
        assert( s@.subrange(0, 4) =~= s@ ); // need a little extensionality? Do it by hand!

        let end = start + 4;
        let mut k:usize = 0;
        while k < 4
        invariant
            end == start + self.size(value),
            end <= data.len(),  // manual-every-effing-invariant blows
            data.len() == old(data).len(),  // manual-every-effing-invariant blows
            s.len() == 4,  // manual-every-effing-invariant blows
            forall |i| 0 <= i < start ==> data[i] == old(data)[i],
            forall |i| 0 <= i < k ==> data[start as int + i] == s[i],
            forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        {
            //data[k] = s[k];
            // Do we want some sort of intrinsic so we don't have to copy u32s a byte at a time!?
            data.set(start as usize + k, s[k]);
            k += 1;
        }
        assert( data@.subrange(start as int, end as int) =~= s@ );  // extensionality: it's what's for ~.
        end
    }
}

impl Marshalling<u64> for IntegerMarshalling<u64> {
    spec fn valid(&self) -> bool
    {
        true
    }

    spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        /*std::mem::size_of<u64>()*/
        8 <= data.len()
    }

    spec fn parse(&self, data: Seq<u8>) -> u64
    {
        spec_u64_from_le_bytes(data.subrange(0, 8))
    }

    // Should this be slices? in verus-ironfleet, jayb used Vec<u8> + start
    fn try_parse(&self, data: &Vec<u8>) -> (ov: Option<u64>)
    {
        if 8 <= data.len() {
            Some(u64_from_le_bytes(slice_subrange(data.as_slice(), 0, 8)))
        } else {
            None
        }
    }

    fn exec_parsable(&self, data: &Vec<u8>) -> (p: bool)
    {
        8 <= data.len()
    }

    spec fn marshallable(&self, value: &u64) -> bool
    {
        true
    }

    spec fn size(&self, value: &u64) -> u64
    {
        8
    }

    fn exec_size(&self, value: &u64) -> (sz: u64)
    {
        8
    }

    fn marshall(&self, value: &u64, data: &mut Vec<u8>, start: u64) -> (end: u64)
    {
        // TODO this interface from verus pervasive bytes.rs can't be fast...
        let s = u64_to_le_bytes(*value);
        proof { lemma_auto_spec_u64_to_from_le_bytes(); }
        assert( s@.subrange(0, 8) =~= s@ ); // need a little extensionality? Do it by hand!

        let end = start + 8;
        let mut k:usize = 0;
        while k < 8
        invariant
            end == start + self.size(value),
            end <= data.len(),  // manual-every-effing-invariant blows
            data.len() == old(data).len(),  // manual-every-effing-invariant blows
            s.len() == 8,  // manual-every-effing-invariant blows
            forall |i| 0 <= i < start ==> data[i] == old(data)[i],
            forall |i| 0 <= i < k ==> data[start as int + i] == s[i],
            forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        {
            //data[k] = s[k];
            // Do we want some sort of intrinsic so we don't have to copy u64s a byte at a time!?
            data.set(start as usize + k, s[k]);
            k += 1;
        }
        assert( data@.subrange(start as int, end as int) =~= s@ );  // extensionality: it's what's for ~.
        end
    }
}

// trait SeqMarshalling<C: Config, U, Elt: Marshalling<C, U>> : Marshalling<DefaultConfig, Vec<U>> {
//     spec fn spec_elt_cfg(cfg: &DefaultConfig) -> (elt_cfg: C)
//     recommends
//         cfg.valid()
// //     ensures
// //         elt_cfg.valid()
//     ;
// 
//     // sure can't stand those spec ensures. Such a hassle!
//     proof fn spec_elt_cfg_ensures(cfg: &DefaultConfig) -> (elt_cfg: C)
//     requires
//         cfg.valid(),
//     ensures
//         elt_cfg.valid()
//     ;
// 
//     /////////////////////////////////////////////////////////////////////////
//     // observing sequence length (count of elements, not bytes)
//     /////////////////////////////////////////////////////////////////////////
// 
//     // True if the sequence length (count of elements) in data can be determined from data.
//     spec fn lengthable(cfg: &DefaultConfig, data: Seq<u8>) -> bool
//     recommends
//         cfg.valid()
//     ;
// 
//     spec fn length(cfg: &DefaultConfig, data: Seq<u8>) -> int
//     recommends
//         cfg.valid(),
//         Self::lengthable(cfg, data)
//     ;
// 
//     fn try_length(cfg: &DefaultConfig, data: &Vec<u8>) -> (out: Option<u64>)
//     requires
//         cfg.valid(),
//     ensures
//         out is Some <==> Self::lengthable(cfg, data@),
//         out is Some ==> out.unwrap() as int == Self::length(cfg, data@)
//     ;
// 
//     /////////////////////////////////////////////////////////////////////////
//     // getting individual elements
//     /////////////////////////////////////////////////////////////////////////
//     spec fn gettable(cfg: &DefaultConfig, data: Seq<u8>, idx: int) -> bool
//     recommends
//         cfg.valid()
//     ;
// 
//     spec fn get(cfg: &DefaultConfig, slice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
//     recommends
//         cfg.valid(),
//         slice.valid(data),
//         Self::gettable(cfg, slice.i(data), idx)
//     ;
// 
//     proof fn get_ensures(cfg: &DefaultConfig, slice: Slice, data: Seq<u8>, idx: int)
//     requires
//         cfg.valid(),
//         slice.valid(data),
//         Self::gettable(cfg, slice.i(data), idx),
//     ensures
//         Self::get(cfg, slice, data, idx).valid(data)
//     ;
// 
//     spec fn get_data(cfg: &DefaultConfig, slice: Slice, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
//     recommends
//         cfg.valid(),
//         Self::gettable(cfg, slice.i(data), idx)
//     ;
// //     Wants to be a default method
// //     {
// //         Self::get(cfg, Slice::all(data), data, idx).i(data)
// //     }
// 
//     spec fn elt_parsable(cfg: &DefaultConfig, data: Seq<u8>, idx: int) -> bool
//     recommends
//         cfg.valid(),
//         Self::gettable(cfg, data, idx)
// //     Wants to be a default method
// //     {
// //         Elt.parsable(Self::spec_elt_cfg(cfg), Self::get_data(cfg, slic, data, idx))
// //     }
//     ;
// 
//     spec fn get_elt(cfg: &DefaultConfig, data: Seq<u8>, idx: int) -> (elt: U)
//     recommends
//         cfg.valid(),
//         Self::gettable(cfg, data, idx),
//         Self::elt_parsable(cfg, data, idx)
// //     Wants to be a default method
// //     {
// //         Elt.parse(Self::spec_elt_cfg(cfg), Self::get_data(cfg, slic, data, idx))
// //     }
//     ;
// 
//     fn try_get(cfg: &DefaultConfig, slice: Slice, data: Seq<u8>, idx: int) -> (oeslice: Option<Slice>)
//     requires
//         cfg.valid(),
//         slice.valid(data),
//     ensures
//         oeslice is Some <==> Self::gettable(cfg, slice.i(data), idx as int),
//         oeslice is Some ==> oeslice.unwrap() == Self::get(cfg, slice, data, idx as int)
//     ;
// 
//     // jonh skipped over the `exec fn get` that requires gettable, perhaps a useful optimization
//     // for some other day..
// 
//     fn try_get_elt(cfg: &DefaultConfig, slice: Slice, data: Seq<u8>, idx: int) -> (oelt: Option<U>)
//     requires
//         cfg.valid(),
//     ensures
//         oelt is Some <==> {
//                 &&& Self::gettable(cfg, slice.i(data), idx as int)
//                 &&& Self::elt_parsable(cfg, data, idx as int)
//         },
//         oelt is Some ==> oelt.unwrap() == Self::get_elt(cfg, slice.i(data), idx as int)
// //     Wants to be a default method
// //     {
// //         match Self::try_get(cfg, slice, data, idx) {
// //            None => None,
// //            Some(slice) => {
// //              Elt::try_parse(Self::exec_elt_cfg(cfg), slice, data)
// //            }
// //         }
// //     }
//     ;
// 
//     /////////////////////////////////////////////////////////////////////////
//     // setting individual elements
//     /////////////////////////////////////////////////////////////////////////
//     spec fn settable(cfg: &DefaultConfig, data: Seq<u8>, idx: int, value: U) -> bool
//     recommends
//         cfg.valid(),
//         Elt::marshallable(&Self::spec_elt_cfg(cfg), &value)
//     ;
// 
//     spec fn preserves_entry(cfg: &DefaultConfig, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
//     recommends
//         cfg.valid()
// //     Wants to be a default method
// //     {
// //         &&& Self::gettable(cfg, data, idx) ==> Self::gettable(cfg, new_data, idx)
// //         &&& (Self::gettable(cfg, data, idx) && Self::elt_parsable(cfg, new_data, idx)) ==> {
// //             &&& Self::elt_parsable(cfg, new_data, idx)
// //             &&& Self::get_elt(cfg, new_data, idx) == Self::get_elt(cfg, new_data, idx)
// //             }
// //     }
//     ;
// 
//     // if preserves_entry(data, middle) && preserves_entry(middle, new_data), then preserves_entry(data, new_data)
// //  proof fn preserves_entry_transitive(cfg: &DefaultConfig, data: Seq<u8>, idx: int, middle: Seq<u8>, new_data: Seq<u8>) -> bool
// 
//     spec fn sets(cfg: &DefaultConfig, data: Seq<u8>, idx: int, value: U, new_data: Seq<u8>) -> bool
//     recommends
//         cfg.valid(),
//         Elt::marshallable(&Self::spec_elt_cfg(cfg), &value),
//         Self::settable(cfg, data, idx, value)
// //     {
// //         &&& new_data.len() == data.len()
// //         &&& Self::lengthable(cfg, data) ==> {
// //             &&& Self::lengthable(cfg, new_data)
// //             &&& Self::length(cfg, new_data) == Self::length(cfg, data)
// //             }
// //         &&& forall |i| i!=idx ==> Self::preserves_entry(cfg, data, i, new_data)
// //         &&& Self::gettable(cfg, new_data, idx)
// //         &&& Self::elt_parsable(cfg, new_data, idx)
// //         &&& Self::get_elt(cfg, new_data, idx) == value
// //     }
//        ;
//     
//     fn is_settable(cfg: &DefaultConfig, slice: Slice, data: &Vec<u8>, idx: int, value: U) -> (s: bool)
//     requires
//         cfg.valid(),
//         Elt::marshallable(&Self::spec_elt_cfg(cfg), &value),
//     ensures
//         s == Self::settable(cfg, slice.i(data@), idx, value)
//     ;
//     
//     fn exec_set(cfg: &DefaultConfig, slice: Slice, data: &mut Vec<u8>, idx: u64, value: U)
//     requires
//         cfg.valid(),
//         slice.valid(old(data)@),
//         Elt::marshallable(&Self::spec_elt_cfg(cfg), &value),
//         Self::settable(cfg, slice.i(old(data)@), idx as int, value),
//     ensures
//         slice.agree_beyond_slice(old(data)@, data@),
//         Self::sets(cfg, slice.i(old(data)@), idx as int, value, slice.i(data@))
//     ;
// 
//     /////////////////////////////////////////////////////////////////////////
//     // resizing
//     /////////////////////////////////////////////////////////////////////////
//     spec fn resizable(cfg: &DefaultConfig, data: Seq<u8>, newlen: int) -> bool
//     recommends
//         cfg.valid()
//     ;
// 
//     spec fn resizes(cfg: &DefaultConfig, data: Seq<u8>, newlen: int, new_data: Seq<u8>) -> bool
//     recommends
//         cfg.valid(),
//         Self::resizable(cfg, data, newlen)
// //     {
// //         &&& new_data.len() == data.len()
// //         &&& Self::lengthable(cfg, new_data)
// //         &&& Self::length(cfg, new_data) == newlen
// //         &&& forall |i| Self::preserves_entry(cfg, data, i, new_data)
// //     }
//     ;
//     
//     fn is_resizable(cfg: &DefaultConfig, data: Seq<u8>, newlen: int) -> (r: bool)
//     requires
//         cfg.valid(),
//     ensures
//         r == Self::resizable(cfg, data, newlen)
//     ;
// 
//     
//     fn exec_resize(cfg: &DefaultConfig, slice: Slice, data: &mut Vec<u8>, newlen: int)
//     requires
//         cfg.valid(),
//         slice.valid(old(data)@),
//         Self::resizable(cfg, old(data)@, newlen),
//     ensures
//         slice.agree_beyond_slice(old(data)@, data@),
//         Self::resizes(cfg, slice.i(old(data)@), newlen as int, slice.i(data@))
//     ;
// 
//     /////////////////////////////////////////////////////////////////////////
//     // append
//     /////////////////////////////////////////////////////////////////////////
//     // postponing for now because we can just resize+set, right?
// 
//     /////////////////////////////////////////////////////////////////////////
//     // parse_to_len
//     /////////////////////////////////////////////////////////////////////////
//     // postponing for now
// }
// 
// // Marshalling of sequences of uniform-sized elements, with a length
// // field up front so we can resize it.
// 
// struct ResizableUniformSizedElementSeqMarshallingConfig<C: Config, U, Elt: Marshalling<C, U>>
// {
//     totalSize: u64,
//     lengthCfg: IntegerMarshalling,
//     eltCfg: C,
// }
// 
// struct ResizableUniformSizedElementSeqMarshalling<C: Config, U, Elt: Marshalling<C, U>>
// {
// }
// 
// impl<C, U, Elt> SeqMarshalling<DefaultConfig, u64, IntegerMarshalling> for ResizableUniformSizedElementSeqMarshalling<C, U, Elt> {
// }
// 
// // struct ResizableIntegerSeqMarshalling {
// // }
// // 
// // impl Marshalling<DefaultConfig, u64> for ResizableIntegerSeqMarshalling {
// // }
// // 
// // // jonh is reifing this with LengthInt==u32, BoundaryInt==u32
// // // Oh I can't defer ResizableIntegerSeqMarshalling because I need it for the boundary table.
// // // Or can I recurse?
// // struct VariableSizedElementSeqMarshallingConfig {
// //     bsmCfg: VariableSizedElementSeqMarshalling<DefaultConfig, u64, IntegerMarshalling>,
// //     eltCfg: 
// // }
// // 
// // struct VariableSizedElementSeqMarshalling<C: Config, U, Elt: Marshalling<C, U>>
// // {
// // }
// 
// // Man we need some associated types to cut down this template type burden.
// // impl<C, U, Elt> SeqMarshalling<C, U, Elt> for VariableSizedElementSeqMarshalling<C, U, Elt> {
// // }
// 
// /*
// Roadmap: Here is the module plan Rob laid out in MarshalledAccessors.i.dfy
// https://github.com/vmware-labs/verified-betrfs/blob/marshalled-accessors-4/lib/Marshalling/MarshalledAccessors.i.dfy#L354
// 
// ResizableUniformSizedElementSeqMarshalling
//     Marshalling of sequences of uniform-sized elements, with a length
//     field up front so we can resize it.
// 
// UniformSizedElementSeqMarshalling
//     Common parts of implementation of marshalling a sequence of items
//     that all have the same marshalled size.
//     We omit the actual parsing and marshalling implementations so that
//     we can use the optimized integer packing code.
// 
// IntegerSeqMarshalling
//     Implementation for marshalling a sequence of packable integers
// 
//     We could just use the UniformSized marshalling code further below,
//     but that would marshall each integer one at a time, which would
//     (presumably) be slower.
// 
// Uint32SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint32
// Uint64SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint64
// 
// ResizableUniformSizedElementSeqMarshalling
//     Marshalling of sequences of uniform-sized elements, with a length
//     field up front so we can resize it.
// 
// ResizableIntegerSeqMarshalling
//     Implementation for marshalling a sequence of packable integers
// 
//     We could just use the UniformSized marshalling code further below,
//     but that would marshall each integer one at a time, which would
//     (presumably) be slower.
// 
// VariableSizedElementSeqMarshalling
//     Implementation of marshalling a general sequence of items
// */

} // verus!
