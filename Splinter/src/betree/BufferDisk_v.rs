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
use crate::disk::GenericDisk_v::{Address};

verus! {
#[verifier::ext_equal]
pub struct BufferDisk {
    pub entries: Map<Address, Buffer>
}

impl QueryableDisk for BufferDisk {
    open spec fn wf(&self) -> bool
    {
        true
    }

    open spec fn repr(&self) -> Set<Address> 
    {
        self.entries.dom()
    }

    // query queryable structure at address addr
    open spec fn query(&self, addr: Address, k: Key) -> Message
    {
        self.entries[addr].query(k)
    }

    // true if address is present and key is present within the queryable structure
    open spec fn queryable_contains(&self, addr: Address, k: Key) -> bool
    {
        &&& self.entries.contains_key(addr)
        &&& self.entries[addr].map.contains_key(k)
    }

    open spec fn is_sub_disk(&self, bigger: &Self) -> bool
    {
        &&& self.entries <= bigger.entries
    }

    proof fn sub_disk_implies_sub_repr(&self, bigger: &Self) { }
}

impl BufferDisk {
    pub open spec(checked) fn modify_disk(self, addr: Address, buffer: Buffer) -> BufferDisk
    {
        BufferDisk{ entries: self.entries.insert(addr, buffer) }
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool 
    {
        self.entries.dom().disjoint(addrs)
    }

    pub open spec(checked) fn is_sub_disk(self, bigger: BufferDisk) -> bool
    {
        self.entries <= bigger.entries
    }

    pub open spec(checked) fn merge_disk(self, other: BufferDisk) -> BufferDisk
    {
        BufferDisk{ entries: self.entries.union_prefer_right(other.entries) }
    }
} // end of BufferDisk impl

pub open spec(checked) fn empty_disk() -> BufferDisk
{
    BufferDisk{ entries: Map::empty() }
}

pub open spec(checked) fn i_buffer_seq(addrs: LinkedSeq<BufferDisk>, dv: BufferDisk) -> BufferSeq_v::BufferSeq
    recommends addrs.valid(dv)
{
    let buffers = Seq::new(addrs.len(), |i| dv.entries[addrs[i]]);
    BufferSeq_v::BufferSeq{ buffers: buffers }
}

pub proof fn subdisk_implies_same_i(addrs: LinkedSeq<BufferDisk>, small: BufferDisk, big: BufferDisk)
    requires addrs.valid(small), small.is_sub_disk(big)
    ensures addrs.valid(big), i_buffer_seq(addrs, small) == i_buffer_seq(addrs, big)
{
    let i_small = i_buffer_seq(addrs, small);
    let i_big = i_buffer_seq(addrs, big);

    assert forall |i| 0 <= i < addrs.len()
    implies i_small[i] == i_big[i]
    by {
        assert(big.entries.dom().contains(addrs[i])); // trigger
    }
    assert(i_small =~= i_big);
}

pub proof fn query_from_commutes_with_i(addrs: LinkedSeq<BufferDisk>, dv: BufferDisk, k: Key, start: int)
    requires 
        addrs.valid(dv),
        0 <= start <= addrs.len(),
    ensures 
        addrs.query_from(dv, k, start) == i_buffer_seq(addrs, dv).query_from(k, start)
    decreases addrs.len() - start
{
    if start < addrs.len() {
        query_from_commutes_with_i(addrs, dv, k, start+1);
    }    
}
}  // end verus!
