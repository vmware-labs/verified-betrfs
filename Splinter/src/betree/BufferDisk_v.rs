// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::{map::*,seq::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v;
use crate::betree::LinkedSeq_v::*;
use crate::betree::OffsetMap_v::*;
use crate::disk::GenericDisk_v::{Address};

verus! {
#[verifier::ext_equal]
pub struct BufferDisk<T> {
    pub entries: Map<Address, T>
}

impl<T> BufferDisk<T> {
    pub open spec fn repr(&self) -> Set<Address> 
    {
        self.entries.dom()
    }

    pub open spec(checked) fn valid_buffers(&self, buffers: LinkedSeq) -> bool
    {
        buffers.addrs.to_set() <= self.repr()
        // forall |i| 0 <= i < buffers.len() ==> self.repr().contains(#[trigger] buffers.addrs[i])
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool 
    {
        self.entries.dom().disjoint(addrs)
    }

    pub open spec(checked) fn is_sub_disk(self, bigger: BufferDisk<T>) -> bool
    {
        self.entries <= bigger.entries
    }

    pub open spec(checked) fn empty_disk() -> Self
    {
        Self{ entries: Map::empty() }
    }

    pub open spec(checked) fn modify_disk(self, addr: Address, buffer: T) -> Self
    {
        Self{ entries: self.entries.insert(addr, buffer) }
    }

    pub open spec(checked) fn merge_disk(self, other: Self) -> Self
    {
        Self{ entries: self.entries.union_prefer_right(other.entries) }
    }
} // end of BufferDisk<T> impl

impl<T: AbstractBuffer> BufferDisk<T> {
    pub open spec fn query(&self, addr: Address, k: Key) -> Message
    {
        self.entries[addr].query(k)
    }

    pub open spec(checked) fn query_from(self, buffers: LinkedSeq, k: Key, start: int) -> Message 
        recommends self.valid_buffers(buffers), 0 <= start <= buffers.len()
        decreases buffers.len() - start when start <= buffers.len()
    {
        if start == buffers.len() {
            Message::Update{delta: nop_delta()}
        } else {
            self.query(buffers[start], k).merge(self.query_from(buffers, k, start+1))
        }
    }

    // true if address is present and key is present within the queryable structure
    pub open spec fn queryable_contains(&self, addr: Address, k: Key) -> bool
    {
        &&& self.entries.contains_key(addr)
        &&& self.entries[addr].contains(k)
    }

    pub open spec(checked) fn key_in_buffer_filtered(self, buffers: LinkedSeq, offset_map: OffsetMap, from_idx: int, k: Key, idx: int) -> bool
        recommends 0 <= from_idx, offset_map.is_total()
    {
        &&& from_idx <= idx < buffers.len()
        &&& self.queryable_contains(buffers[idx], k)
        &&& offset_map.offsets[k] <= idx
    }
}

// pub open spec(checked) fn i_buffer_seq(addrs: LinkedSeq<BufferDisk>, dv: BufferDisk) -> BufferSeq_v::BufferSeq
// {
//     let buffers = Seq::new(addrs.len(), |i| 
//         if dv.entries.contains_key(addrs[i]) { 
//             dv.entries[addrs[i]] 
//         } else { Buffer::empty() });

//     BufferSeq_v::BufferSeq{ buffers: buffers }
// }

// pub proof fn subdisk_implies_same_i(addrs: LinkedSeq<BufferDisk>, small: BufferDisk, big: BufferDisk)
//     requires
//         addrs.valid(small),
//         small.is_sub_disk(big),
//     ensures 
//         i_buffer_seq(addrs, small) == i_buffer_seq(addrs, big)
// {
//     let i_small = i_buffer_seq(addrs, small);
//     let i_big = i_buffer_seq(addrs, big);

//     // assert forall |i| 0 <= i < addrs.len()
//     // implies i_small[i] == i_big[i]
//     // by {
//     //     if small.entries.contains_key(addrs[i]) {
//     //         assert(big.entries.contains_key(addrs[i])); // trigger
//     //     }
//     // }
//     assert(i_small =~= i_big);
// }

// pub proof fn query_from_commutes_with_i(addrs: LinkedSeq<BufferDisk>, dv: BufferDisk, k: Key, start: int)
//     requires 
//         addrs.valid(dv),
//         0 <= start <= addrs.len(),
//     ensures 
//         addrs.query_from(dv, k, start) == i_buffer_seq(addrs, dv).query_from(k, start)
//     decreases addrs.len() - start
// {
//     if start < addrs.len() {
//         query_from_commutes_with_i(addrs, dv, k, start+1);
//     }    
// }
}  // end verus!
