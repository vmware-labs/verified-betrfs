// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::MarshalledAccessors_v::*;

verus! {

//////////////////////////////////////////////////////////////////////////////
// Sequence marshalling
//////////////////////////////////////////////////////////////////////////////

pub trait SeqMarshalling<U, Elt: Marshalling<U>> : Marshalling<Vec<U>> {
    spec fn spec_elt(&self) -> Elt
    ;

    // sure can't stand those spec ensures. Such a hassle!
    proof fn spec_elt_ensures(&self)
    requires
        self.valid(),
    ensures
        self.spec_elt().valid()
    ;

    exec fn exec_elt(&self) -> (elt: Elt)
    ensures
        elt == self.spec_elt(),
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

    // TODO(robj): Why do these spec fns take slices?
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

    spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    recommends
        self.valid(),
        self.gettable(data, idx)
    {
        self.get(Slice::all(data), data, idx).i(data)
    }

    spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    recommends
        self.valid(),
        self.gettable(data, idx)
    {
        self.spec_elt().parsable(self.get_data(data, idx))
    }

    spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: U)
    recommends
        self.valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
    {
        self.spec_elt().parse(self.get_data(data, idx))
    }

    fn try_get(&self, slice: Slice, data: &Vec<u8>, idx: int) -> (oeslice: Option<Slice>)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        oeslice is Some <==> self.gettable(slice.i(data@), idx as int),
        oeslice is Some ==> oeslice.unwrap() == self.get(slice, data@, idx as int)
    ;

    // jonh skipped over the `exec fn get` that requires gettable, perhaps a useful optimization
    // for some other day..

    fn try_get_elt(&self, slice: Slice, data: &Vec<u8>, idx: int) -> (oelt: Option<U>)
    requires
        self.valid(),
        slice.valid(data@),
    ensures
        oelt is Some <==> {
                &&& self.gettable(slice.i(data@), idx as int)
                &&& self.elt_parsable(data@, idx as int)
        },
        oelt is Some ==> oelt.unwrap() == self.get_elt(slice.i(data@), idx as int),
    {
        assume( false );
        assert( slice.valid(data@) );
        proof { self.spec_elt_ensures(); }
        assert( slice.valid(data@) );
        let oelt = 
            match self.try_get(slice, data, idx) {
                None => None,
                Some(slice) => {
                    //assert( slice == old(slice) );
                    //assert( data@ == old(data)@ );
                    assert( slice.valid(data@) );   // Whoah, neither slice nor data is mutable. How could this fail?
                    assert( self.gettable(slice.i(data@), idx as int) );
                    self.exec_elt().try_parse(slice, data)
                }
            };
        assert( oelt is Some <==> {
             &&& self.gettable(slice.i(data@), idx as int)
             &&& self.elt_parsable(data@, idx as int)
        } );
        assert( oelt is Some ==> oelt.unwrap() == self.get_elt(slice.i(data@), idx as int) );
        oelt
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////
    spec fn settable(&self, data: Seq<u8>, idx: int, value: U) -> bool
    recommends
        self.valid(),
        self.spec_elt().marshallable(&value)
    ;

    spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    recommends
        self.valid()
    {
        &&& self.gettable(data, idx) ==> self.gettable(new_data, idx)
        &&& (self.gettable(data, idx) && self.elt_parsable(new_data, idx)) ==> {
            &&& self.elt_parsable(new_data, idx)
            &&& self.get_elt(new_data, idx) == self.get_elt(new_data, idx)
            }
    }

    // if preserves_entry(data, middle) && preserves_entry(middle, new_data), then preserves_entry(data, new_data)
//  proof fn preserves_entry_transitive(&self, data: Seq<u8>, idx: int, middle: Seq<u8>, new_data: Seq<u8>) -> bool

    spec fn sets(&self, data: Seq<u8>, idx: int, value: U, new_data: Seq<u8>) -> bool
    recommends
        self.valid(),
        self.spec_elt().marshallable(&value),
        self.settable(data, idx, value)
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(data) ==> {
            &&& self.lengthable(new_data)
            &&& self.length(new_data) == self.length(data)
            }
        &&& forall |i| i!=idx ==> self.preserves_entry(data, i, new_data)
        &&& self.gettable(new_data, idx)
        &&& self.elt_parsable(new_data, idx)
        &&& self.get_elt(new_data, idx) == value
    }
    
    fn is_settable(&self, slice: Slice, data: &Vec<u8>, idx: int, value: U) -> (s: bool)
    requires
        self.valid(),
        self.spec_elt().marshallable(&value)
    ensures
        s == self.settable(slice.i(data@), idx, value)
    ;
    
    fn exec_set(&self, slice: Slice, data: &mut Vec<u8>, idx: u64, value: U)
    requires
        self.valid(),
        slice.valid(old(data)@),
        self.spec_elt().marshallable(&value),
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
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(new_data)
        &&& self.length(new_data) == newlen
        &&& forall |i| self.preserves_entry(data, i, new_data)
    }
    
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

// //TODO find the relevant verus defn
// pub open spec fn uint64_upper_bound() -> int {
//     0x1_0000_0000_0000_0000
// }
// 
// struct SeqMarshallingDef<U, Elt: Marshalling<U>, Selff: SeqMarshalling<U, Elt>> {
//     dummy_u: U,
//     dummy_e: Elt,
//     dummy_s: Selff,
// }
// 
// impl<U, Elt: Marshalling<U>, Selff: SeqMarshalling<U, Elt>>
//     SeqMarshallingDef<U, Elt, Selff> {
// 
//     pub open spec fn gettable_to_len(selff: Selff, data: Seq<u8>, len: int) -> bool {
//         forall |i: int| 0 <= i < len ==> selff.gettable(data, len)
//     }
// 
//     pub open spec fn elt_parsable_to_len(selff: Selff, data: Seq<u8>, len: int) -> bool {
//         forall |i: int| 0 <= i < len ==> selff.elt_parsable(data, i)
//     }
// 
//     pub open spec fn parsable_to_len(selff: Selff, data: Seq<u8>, len: u64) -> bool {
//         &&& Self::gettable_to_len(selff, data, len as int)
//         &&& Self::elt_parsable_to_len(selff, data, len as int)
//     }
// 
//     pub open spec fn parsable(selff: Selff, data: Seq<u8>) -> bool {
//         &&& selff.lengthable(data)
//         &&& selff.length(data) < uint64_upper_bound()
//         &&& Self::parsable_to_len(selff, data, selff.length(data) as u64)
//     }
// }
// 
// ////////////////////////////////////////////////////////////////////
// // Marshalling of sequences of uniform-sized elements, with a length
// // field up front so we can resize it.
// ////////////////////////////////////////////////////////////////////
// 
// trait ResizableUniformSizedElementSeqMarshalling<LT, ET, Elt: Marshalling<ET>>
//     : SeqMarshalling<ET, Elt>
// {
//     exec fn size_of_length_field() -> u64 {
//         NativePackedInt::<LT>::size()
//     }
// 
//     spec fn spec_total_size() -> u64;
//     //spec fn spec_length_marshalling() -> IntegerMarshalling<LT>;
// 
//     spec fn valid(&self) -> bool {
//         &&& Self::size_of_length_field() <= Self::cfg().total_size()
//         &&& Self::cfg().length_marshalling.valid()
//         &&& Self::cfg().spec_elt.valid()
//     }
// 
//     spec fn uniform_size(&self) -> u64
//     recommends
//         self.valid(),
//     ;
//     
//     proof fn uniform_size_ensures(&self)
//     requires
//         self.valid(),
//     ensures
//         0 < self.uniform_size(),
//     ;
// 
//     exec fn max_length(self) -> u64
//     requires
//         self.valid(),
//     {
//         (self.total_size - Self::size_of_length_field()) / self.uniform_size()
//     }
// 
//     spec fn lengthable(self, data: Seq<u8>) -> bool
//     {
//         self.total_size as nat <= data.len()
//     }
// 
//     spec fn length(self, data: Seq<u8>) -> int
//     {
//         self.length_marshalling.parse(data.subrange(0, Self::size_of_length_field()))
//     }
// 
//     // Stuff I'm deferring until the proof breaks
//     // proof fn length_ensures
//     // proof fn index_bounds_facts
// 
//     exec fn try_length(self, data:Vec<u8>) -> (olen: Option<u64>)
//     {
//         if data.len() < self.total_size {
//             None
//         } else {
//             // original was Parse, so we may be leaving perf on the floor here since we know it's
//             // parsable. Or maybe we should just try_parse instead of testing the length?
//             let len = self.length_marshalling.try_parse(data.subrange(0, Self::size_of_length_field()));
//                 // yeah that's gonna need to be a slice
//             Some(len)
//         }
//     }
// }
// 
// struct ResizableIntegerSeqMarshalling<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>> {
//     total_size: u64,
//     length_marshalling: LM,
//     spec_elt: EM,
// 
//     dummy_l: LT,    // TODO(jonh): phantom something something?
//     dummy_e: ET,
// }
// 
// impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
//     ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
// 
//     // Maybe we don't want function methods, but maybe we do
//     // want some cheap syntax for things that should define exec fn u64
//     // and spec fn int at the same time.
//     spec fn size_of_length_field(&self) -> u64 {
//         self.length_marshalling.size()
//     }
// }
// 
// impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
//     Marshalling<Vec<ET>> for
//     ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
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
// 
// impl<LT, LM: Marshalling<LT>, ET, EM: Marshalling<ET>>
//     SeqMarshalling<ET, EM> for
//     ResizableIntegerSeqMarshalling<LT, LM, ET, EM> {
// }
// 
// // // Marshalling of sequences of uniform-sized elements, with a length
// // // field up front so we can resize it.
// // 
// // struct ResizableUniformSizedElementSeqMarshallingConfig<C: Config, U, Elt: Marshalling<C, U>>
// // {
// //     totalSize: u64,
// //     lengthCfg: IntegerMarshalling,
// //     eltCfg: C,
// // }
// // 
// // struct ResizableUniformSizedElementSeqMarshalling<C: Config, U, Elt: Marshalling<C, U>>
// // {
// // }
// // 
// // impl<C, U, Elt> SeqMarshalling<DefaultConfig, u64, IntegerMarshalling> for ResizableUniformSizedElementSeqMarshalling<C, U, Elt> {
// // }
// // 
// // // struct ResizableIntegerSeqMarshalling {
// // // }
// // // 
// // // impl Marshalling<DefaultConfig, u64> for ResizableIntegerSeqMarshalling {
// // // }
// // // 
// // // // jonh is reifing this with LengthInt==u32, BoundaryInt==u32
// // // // Oh I can't defer ResizableIntegerSeqMarshalling because I need it for the boundary table.
// // // // Or can I recurse?
// // // struct VariableSizedElementSeqMarshallingConfig {
// // //     bsmCfg: VariableSizedElementSeqMarshalling<DefaultConfig, u64, IntegerMarshalling>,
// // //     eltCfg: 
// // // }
// // // 
// // // struct VariableSizedElementSeqMarshalling<C: Config, U, Elt: Marshalling<C, U>>
// // // {
// // // }
// // 
// // // Man we need some associated types to cut down this template type burden.
// // // impl<C, U, Elt> SeqMarshalling<C, U, Elt> for VariableSizedElementSeqMarshalling<C, U, Elt> {
// // // }
// // 
// // /*
// // Roadmap: Here is the module plan Rob laid out in MarshalledAccessors.i.dfy
// // https://github.com/vmware-labs/verified-betrfs/blob/marshalled-accessors-4/lib/Marshalling/MarshalledAccessors.i.dfy#L354
// // 
// // ResizableUniformSizedElementSeqMarshalling
// //     Marshalling of sequences of uniform-sized elements, with a length
// //     field up front so we can resize it.
// // 
// // UniformSizedElementSeqMarshalling
// //     Common parts of implementation of marshalling a sequence of items
// //     that all have the same marshalled size.
// //     We omit the actual parsing and marshalling implementations so that
// //     we can use the optimized integer packing code.
// // 
// // IntegerSeqMarshalling
// //     Implementation for marshalling a sequence of packable integers
// // 
// //     We could just use the UniformSized marshalling code further below,
// //     but that would marshall each integer one at a time, which would
// //     (presumably) be slower.
// // 
// // Uint32SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint32
// // Uint64SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint64
// // 
// // ResizableUniformSizedElementSeqMarshalling
// //     Marshalling of sequences of uniform-sized elements, with a length
// //     field up front so we can resize it.
// // 
// // ResizableIntegerSeqMarshalling
// //     Implementation for marshalling a sequence of packable integers
// // 
// //     We could just use the UniformSized marshalling code further below,
// //     but that would marshall each integer one at a time, which would
// //     (presumably) be slower.
// // 
// // VariableSizedElementSeqMarshalling
// //     Implementation of marshalling a general sequence of items
// // */

} // verus!
