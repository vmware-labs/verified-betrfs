// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
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

    pub open spec(checked) fn agrees_with(self, bigger: BufferDisk<T>) -> bool
    {
        self.entries.agrees(bigger.entries)
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

impl<T: Buffer> BufferDisk<T> {
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

    pub open spec(checked) fn key_in_buffer(self, buffers: LinkedSeq, from_idx: int, k: Key, idx: int) -> bool
        recommends 0 <= from_idx
    {
        &&& from_idx <= idx < buffers.len()
        &&& self.queryable_contains(buffers[idx], k)
    }

    pub open spec(checked) fn key_in_buffer_filtered(self, buffers: LinkedSeq, offset_map: OffsetMap, from_idx: int, k: Key, idx: int) -> bool
        recommends 0 <= from_idx, offset_map.is_total()
    {
        &&& self.key_in_buffer(buffers, from_idx, k, idx)
        &&& offset_map.offsets[k] <= idx
    }

    pub open spec(checked) fn i_buffer_seq(self, addrs: LinkedSeq) -> BufferSeq_v::BufferSeq
        recommends self.valid_buffers(addrs)
    {
        let buffers = Seq::new(addrs.len(), |i| self.entries[addrs[i]].i());    
        BufferSeq_v::BufferSeq{ buffers: buffers }
    }

    pub proof fn query_from_commutes_with_i(self, addrs: LinkedSeq, k: Key, start: int)
        requires 
            self.valid_buffers(addrs),
            0 <= start <= addrs.len(),
        ensures 
            self.query_from(addrs, k, start) == self.i_buffer_seq(addrs).query_from(k, start)
        decreases addrs.len() - start
    {
        broadcast use Buffer::query_refines;
        if start < addrs.len() {
            self.query_from_commutes_with_i(addrs, k, start+1);
        }
    }

    pub broadcast proof fn agrees_implies_same_i(self, other: Self, addrs: LinkedSeq)
        requires
            self.valid_buffers(addrs),
            other.valid_buffers(addrs),
            self.agrees_with(other),
        ensures 
            self.i_buffer_seq(addrs) == other.i_buffer_seq(addrs)
    {
        let i_this = self.i_buffer_seq(addrs);
        let i_other = other.i_buffer_seq(addrs);

//        assert forall |i| 0 <= i < addrs.len()
//        implies i_this[i] == i_other[i]
//        by {
//            if self.entries.contains_key(addrs[i]) {
////                assert(other.entries.contains_key(addrs[i])); // trigger
//            }
//        }
        assert(i_this =~= i_other);
    }
}
}  // end verus!
