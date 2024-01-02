// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use crate::marshalling::Slice_v::*;

verus! {

pub trait Marshalling<U> {
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

// TODO(jonh): Is there a way to templatize the (4,u32)/(8,u64) cases?
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

pub trait SeqMarshalling<U, Elt: Marshalling<U>> : Marshalling<Vec<U>> {
    spec fn elt_valid(&self) -> bool
    recommends
        self.valid()
    ;

    spec fn elt_marshalling(&self) -> (elt: Elt)
    recommends
        self.valid()
    ;

    // sure can't stand those spec ensures. Such a hassle!
    proof fn elt_marshalling_ensures(&self)
    requires
        self.valid(),
    ensures
        self.elt_marshalling().valid()
    ;

    /////////////////////////////////////////////////////////////////////////
    // observing sequence length (count of elements, not bytes)
    /////////////////////////////////////////////////////////////////////////

    // True if the sequence length (count of elements) in data can be determined from data.
    spec fn lengthable(&self, data: Seq<u8>) -> bool
    recommends
        self.valid()
    ;

    spec fn length(&self, data: Seq<u8>) -> int
    recommends
        self.valid(),
        self.lengthable(data)
    ;

    fn try_length(&self, data: &Vec<u8>) -> (out: Option<u64>)
    requires
        self.valid(),
    ensures
        out is Some <==> self.lengthable(data@),
        out is Some ==> out.unwrap() as int == self.length(data@)
    ;

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////
    spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid()
    ;

    spec fn get(&self, slice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    recommends
        self.valid(),
        slice.valid(data),
        self.gettable(slice.i(data), idx)
    ;

    proof fn get_ensures(&self, slice: Slice, data: Seq<u8>, idx: int)
    requires
        self.valid(),
        slice.valid(data),
        self.gettable(slice.i(data), idx),
    ensures
        self.get(slice, data, idx).valid(data)
    ;

    spec fn get_data(&self, slice: Slice, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.valid(),
        self.gettable(slice.i(data), idx)
    ;
//     Wants to be a default method
//     {
//         self.get(Slice::all(data), data, idx).i(data)
//     }

    spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid(),
        self.gettable(data, idx)
//     Wants to be a default method
//     {
//         Elt.parsable(self.spec_elt_cfg), self.get_data(slic, data, idx))
//     }
    ;

    spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: U)
    recommends
        self.valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
//     Wants to be a default method
//     {
//         Elt.parse(self.spec_elt_cfg), self.get_data(slic, data, idx))
//     }
    ;

    fn try_get(&self, slice: Slice, data: Seq<u8>, idx: int) -> (oeslice: Option<Slice>)
    requires
        self.valid(),
        slice.valid(data),
    ensures
        oeslice is Some <==> self.gettable(slice.i(data), idx as int),
        oeslice is Some ==> oeslice.unwrap() == self.get(slice, data, idx as int)
    ;

    // jonh skipped over the `exec fn get` that requires gettable, perhaps a useful optimization
    // for some other day..

    fn try_get_elt(&self, slice: Slice, data: Seq<u8>, idx: int) -> (oelt: Option<U>)
    requires
        self.valid(),
    ensures
        oelt is Some <==> {
                &&& self.gettable(slice.i(data), idx as int)
                &&& self.elt_parsable(data, idx as int)
        },
        oelt is Some ==> oelt.unwrap() == self.get_elt(slice.i(data), idx as int)
//     Wants to be a default method
//     {
//         match self.try_get(slice, data, idx) {
//            None => None,
//            Some(slice) => {
//              Elt::try_parse(self.exec_elt_cfg(cfg), slice, data)
//            }
//         }
//     }
    ;

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////
    spec fn settable(&self, data: Seq<u8>, idx: int, value: U) -> bool
    recommends
        self.valid(),
        self.elt_marshalling().marshallable(&value)
    ;

    spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    recommends
        self.valid()
//     Wants to be a default method
//     {
//         &&& self.gettable(data, idx) ==> self.gettable(new_data, idx)
//         &&& (self.gettable(data, idx) && self.elt_parsable(new_data, idx)) ==> {
//             &&& self.elt_parsable(new_data, idx)
//             &&& self.get_elt(new_data, idx) == self.get_elt(new_data, idx)
//             }
//     }
    ;

    // if preserves_entry(data, middle) && preserves_entry(middle, new_data), then preserves_entry(data, new_data)
//  proof fn preserves_entry_transitive(&self, data: Seq<u8>, idx: int, middle: Seq<u8>, new_data: Seq<u8>) -> bool

    spec fn sets(&self, data: Seq<u8>, idx: int, value: U, new_data: Seq<u8>) -> bool
    recommends
        self.valid(),
        self.elt_marshalling().marshallable(&value),
        self.settable(data, idx, value)
//     {
//         &&& new_data.len() == data.len()
//         &&& self.lengthable(data) ==> {
//             &&& self.lengthable(new_data)
//             &&& self.length(new_data) == self.length(data)
//             }
//         &&& forall |i| i!=idx ==> self.preserves_entry(data, i, new_data)
//         &&& self.gettable(new_data, idx)
//         &&& self.elt_parsable(new_data, idx)
//         &&& self.get_elt(new_data, idx) == value
//     }
       ;
    
    fn is_settable(&self, slice: Slice, data: &Vec<u8>, idx: int, value: U) -> (s: bool)
    requires
        self.valid(),
        self.elt_marshalling().marshallable(&value)
    ensures
        s == self.settable(slice.i(data@), idx, value)
    ;
    
    fn exec_set(&self, slice: Slice, data: &mut Vec<u8>, idx: u64, value: U)
    requires
        self.valid(),
        slice.valid(old(data)@),
        self.elt_marshalling().marshallable(&value),
        self.settable(slice.i(old(data)@), idx as int, value),
    ensures
        slice.agree_beyond_slice(old(data)@, data@),
        self.sets(slice.i(old(data)@), idx as int, value, slice.i(data@))
    ;

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////
    spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool
    recommends
        self.valid()
    ;

    spec fn resizes(&self, data: Seq<u8>, newlen: int, new_data: Seq<u8>) -> bool
    recommends
        self.valid(),
        self.resizable(data, newlen)
//     {
//         &&& new_data.len() == data.len()
//         &&& self.lengthable(new_data)
//         &&& self.length(new_data) == newlen
//         &&& forall |i| self.preserves_entry(data, i, new_data)
//     }
    ;
    
    fn is_resizable(&self, data: Seq<u8>, newlen: int) -> (r: bool)
    requires
        self.valid(),
    ensures
        r == self.resizable(data, newlen)
    ;

    
    fn exec_resize(&self, slice: Slice, data: &mut Vec<u8>, newlen: int)
    requires
        self.valid(),
        slice.valid(old(data)@),
        self.resizable(old(data)@, newlen),
    ensures
        slice.agree_beyond_slice(old(data)@, data@),
        self.resizes(slice.i(old(data)@), newlen as int, slice.i(data@))
    ;

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////
    // postponing for now because we can just resize+set, right?

    /////////////////////////////////////////////////////////////////////////
    // parse_to_len
    /////////////////////////////////////////////////////////////////////////
    // postponing for now
}

//TODO find the relevant verus defn
pub open spec fn uint64_upper_bound() -> int {
    0x1_0000_0000_0000_0000
}

struct SeqMarshallingDef<U, Elt: Marshalling<U>, Selff: SeqMarshalling<U, Elt>> {
    dummy_u: U,
    dummy_e: Elt,
    dummy_s: Selff,
}

impl<U, Elt: Marshalling<U>, Selff: SeqMarshalling<U, Elt>>
    SeqMarshallingDef<U, Elt, Selff> {

    pub open spec fn gettable_to_len(selff: Selff, data: Seq<u8>, len: int) -> bool {
        forall |i: int| 0 <= i < len ==> selff.gettable(data, len)
    }

    pub open spec fn elt_parsable_to_len(selff: Selff, data: Seq<u8>, len: int) -> bool {
        forall |i: int| 0 <= i < len ==> selff.elt_parsable(data, i)
    }

    pub open spec fn parsable_to_len(selff: Selff, data: Seq<u8>, len: u64) -> bool {
        &&& Self::gettable_to_len(selff, data, len as int)
        &&& Self::elt_parsable_to_len(selff, data, len as int)
    }

    pub open spec fn parsable(selff: Selff, data: Seq<u8>) -> bool {
        &&& selff.lengthable(data)
        &&& selff.length(data) < uint64_upper_bound()
        &&& Self::parsable_to_len(selff, data, selff.length(data) as u64)
    }
}


// In the original this module is derived through a chain from
// ResizableUniformSizedElementSeqMarshalling, which would make sense if we
// had trait default methods. I'm going to compile them together.
struct ResizableIntegerSeqMarshalling<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>> {
    total_size: u64,
    length_marshalling: LM,
    elt_marshalling: EM,

    dummy_l: LT,    // TODO(jonh): phantom something something?
    dummy_e: ET,
}

impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
    ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {

    // Maybe we don't want function methods, but maybe we do
    // want some cheap syntax for things that should define exec fn u64
    // and spec fn int at the same time.
    spec fn size_of_length_field(&self) -> u64 {
        self.length_marshalling.size()
    }
}

// impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
//     Marshalling<Vec<ET>> for
//     ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
// 
//     spec fn valid(&self) -> bool {
//         &&& self.size_of_length_field() <= self.total_size
//         &&& self.length_marshalling.valid()
//         &&& self.elt_marshalling.valid()
//     }
// 
//     spec fn parsable(&self, data: Seq<u8>) -> bool
//     recommends self.valid()
//     {
//         SeqMarshallingDef::parsable(*self, data)
//     }
// 
// //     spec fn parse(&self, data: Seq<u8>) -> U
// //     recommends 
// //         self.valid(),
// //         self.parsable(data)
// //     ;
// // 
// //     // Should this be slices? in verus-ironfleet, jayb used Vec<u8> + start
// //     fn try_parse(&self, data: &Vec<u8>) -> (ov: Option<U>)
// //     requires
// //         self.valid(),
// //     ensures
// //         self.parsable(data@) <==> ov is Some,
// //         self.parsable(data@) ==> ov.unwrap() == self.parse(data@)
// //     ;
// // 
// //     fn exec_parsable(&self, data: &Vec<u8>) -> (p: bool)
// //     requires
// //         self.valid(),
// //     ensures
// //         p == self.parsable(data@)
// //     ;
// // 
// //     // jonh skipping translation of Parse -- does it ever save more than
// //     // a cheap if condition?
// // 
// //     spec fn marshallable(&self, value: &U) -> bool
// //     ;
// // 
// //     spec fn size(&self, value: &U) -> u64
// //     recommends 
// //         self.valid(),
// //         self.marshallable(value)
// //     ;
// // 
// //     fn exec_size(&self, value: &U) -> (sz: u64)
// //     requires 
// //         self.valid(),
// //         self.marshallable(value),
// //     ensures
// //         sz == self.size(value)
// //     ;
// // 
// //     fn marshall(&self, value: &U, data: &mut Vec<u8>, start: u64) -> (end: u64)
// //     requires 
// //         self.valid(),
// //         self.marshallable(value),
// //         start as int + self.size(value) as int <= old(data).len(),
// //     ensures
// //         end == start + self.size(value),
// //         data.len() == old(data).len(),
// //         forall |i| 0 <= i < start ==> data[i] == old(data)[i],
// //         forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
// //         self.parsable(data@.subrange(start as int, end as int)),
// //         self.parse(data@.subrange(start as int, end as int)) == value
// //     ;
// }

impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
    SeqMarshalling<ET, EM> for
    ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
}

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
