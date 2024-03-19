// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::{seq::*,set::*, prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::OffsetMap_v::*;
use crate::disk::GenericDisk_v::{Address};

verus! {
#[verifier::ext_equal]
pub struct LinkedSeq<T> {
    pub addrs: Seq<Address>,
    pub _p: std::marker::PhantomData<(T,)>, // required by template
}

impl<T> LinkedSeq<T> {
    pub open spec(checked) fn empty() -> LinkedSeq<T>
    {
        LinkedSeq{ addrs: seq![], _p: arbitrary() }
    }

    pub open spec(checked) fn len(self) -> nat {
        self.addrs.len()
    }

    #[verifier(inline)]
    pub open spec(checked) fn spec_index(self, i: int) -> Address
        recommends 0 <= i < self.len()
    {
        self.addrs[i]
    }

    pub open spec(checked) fn contains(self, addr: Address) -> bool
    {
        self.addrs.contains(addr)
    }

    pub open spec(checked) fn slice(self, start: int, end: int) -> LinkedSeq<T>
        recommends 0 <= start <= end <= self.len()
    {
        LinkedSeq{ addrs: self.addrs.subrange(start, end), ..self }
    }

    pub open spec(checked) fn extend(self, new_addrs: Self) -> LinkedSeq<T>
    {
        LinkedSeq{ addrs: self.addrs + new_addrs.addrs, ..self }
    }

    pub open spec(checked) fn update_subrange(self, start: int, end: int, new_addr: Address) -> LinkedSeq<T> 
        recommends 0 <= start < end <= self.len()
    {
        let addrs = self.addrs.subrange(0, start) + seq![new_addr] + self.addrs.subrange(end, self.len() as int);
        LinkedSeq{ addrs: addrs, ..self  }
    }
} // end impl<T> LinkedSeq

pub trait QueryableDisk {
    spec fn wf(&self) -> bool;

    spec fn repr(&self) -> Set<Address>;

    // query queryable structure at address addr
    spec fn query(&self, addr: Address, k: Key) -> Message
        recommends self.repr().contains(addr)
    ;

    // true if address is present and key is present within the queryable structure
    spec fn queryable_contains(&self, addr: Address, k: Key) -> bool;

    spec fn is_sub_disk(&self, bigger: &Self) -> bool;

    proof fn sub_disk_implies_sub_repr(&self, bigger: &Self)
        requires self.is_sub_disk(bigger)
        ensures self.repr() <= bigger.repr()
    ;
}

impl<T: QueryableDisk> LinkedSeq<T> {
    pub open spec(checked) fn valid(self, dv: T) -> bool
    {
        forall |i| 0 <= i < self.len() ==> dv.repr().contains(#[trigger] self.addrs[i])
    }

    pub open spec(checked) fn query_from(self, dv: T, k: Key, start: int) -> Message 
        recommends 
            self.valid(dv),
            0 <= start <= self.len()
        decreases self.len() - start when start <= self.len()
    {
        if start == self.len() {
            Message::Update{delta: nop_delta()}
        } else {
            dv.query(self[start], k).merge(self.query_from(dv, k, start+1))
        }
    }

    pub open spec fn key_in_buffer(self, dv: T, from_idx: int, k: Key, idx: int) -> bool
    {
        &&& from_idx <= idx < self.len()
        &&& dv.queryable_contains(self[idx], k)
    }

    pub open spec(checked) fn key_in_buffer_filtered(self, dv: T, offset_map: OffsetMap, 
            from_idx: int, k: Key, idx: int) -> bool
        recommends 0 <= from_idx, offset_map.is_total()
    {
        &&& self.key_in_buffer(dv, from_idx, k, idx)
        &&& offset_map.offsets[k] <= idx
    }
} // end impl<T:QueryableDisk> LinkedSeq
}  // end verus!
