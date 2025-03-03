// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin_macros::*;
use vstd::{map::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::BufferDisk_v::*;

verus! {

pub trait Buffer : Sized {
    spec fn linked_wf(self, dv: BufferDisk<Self>) -> bool;

    spec fn linked_contains(self, dv: BufferDisk<Self>, key: Key) -> bool;

    spec fn is_empty(self) -> bool;

    spec(checked) fn linked_query(self, dv: BufferDisk<Self>, key: Key) -> Message
        recommends self.linked_wf(dv)
    ;

    spec fn i(self, dv: BufferDisk<Self>) -> SimpleBuffer
        recommends self.linked_wf(dv)
    ;

    broadcast proof fn linked_contains_refines(self, dv: BufferDisk<Self>, key: Key) 
        ensures #[trigger] self.linked_contains(dv, key) == self.i(dv).map.contains_key(key)
    ;

    broadcast proof fn linked_query_refines(self, dv: BufferDisk<Self>, key: Key)
        ensures  #[trigger] self.linked_query(dv, key) == self.i(dv).query(key)
    ;

    proof fn linked_empty_refines(self, dv: BufferDisk<Self>)
        ensures  #[trigger] self.is_empty() ==> self.i(dv) == SimpleBuffer::empty()
    ;

    broadcast proof fn wf_agreeable_ensures(self, dv: BufferDisk<Self>, other_dv: BufferDisk<Self>) 
        requires self.linked_wf(dv), self.linked_wf(other_dv), dv.agrees_with(other_dv),
        ensures 
            self.i(dv) == self.i(other_dv),
            forall |k: Key| true ==> {
                &&& self.linked_query(dv, k) == self.linked_query(other_dv, k)
                &&& self.linked_contains(dv, k) == self.linked_contains(other_dv, k)
            }
    ;
}

// rename to Simple SimpleBuffer
#[verifier::ext_equal]
pub struct SimpleBuffer {
    pub map: Map<Key, Message>
}

impl Buffer for SimpleBuffer {
    open spec fn linked_wf(self, dv: BufferDisk<SimpleBuffer>) -> bool
    {
        true
    }

    open spec(checked) fn linked_contains(self, dv: BufferDisk<Self>, key: Key) -> bool {
        self.map.contains_key(key)
    }

    open spec(checked) fn linked_query(self, dv: BufferDisk<Self>, key: Key) -> Message {
        self.query(key)
    }

    open spec(checked) fn is_empty(self) -> bool {
        self == SimpleBuffer::empty()
    }

    open spec(checked) fn i(self, dv: BufferDisk<Self>) -> SimpleBuffer {
        self
    }

    proof fn linked_contains_refines(self, dv: BufferDisk<Self>, key: Key) {}

    proof fn linked_query_refines(self, dv: BufferDisk<Self>, key: Key) {}

    proof fn linked_empty_refines(self, dv: BufferDisk<Self>) {}

    proof fn wf_agreeable_ensures(self, dv: BufferDisk<Self>, other_dv: BufferDisk<Self>) {}
}

// A SimpleBuffer is a map from keys to messages.
impl SimpleBuffer {
    pub open spec(checked) fn query(self, key: Key) -> Message {
        self.query_internal(key)
    }

    pub open spec(checked) fn query_internal(self, key: Key) -> Message {
        if self.map.contains_key(key) {
            self.map[key]
        } else {
            Message::Update{ delta: nop_delta() }
        }
    }

    pub open spec(checked) fn contains(self, key: Key) -> bool {
        self.map.contains_key(key)
    }

    pub open spec(checked) fn apply_filter(self, accept: Set<Key>) -> SimpleBuffer {
        SimpleBuffer{ map: Map::new( |k| accept.contains(k) && self.map.contains_key(k), |k| self.map[k] ) }
    }

    pub open spec(checked) fn merge(self, new_Buffer: SimpleBuffer) -> SimpleBuffer {
        SimpleBuffer{ map: Map::new( 
            |k| self.map.contains_key(k) || new_Buffer.map.contains_key(k), 
            |k| if new_Buffer.map.contains_key(k) && self.map.contains_key(k) { 
                    self.map[k].merge(new_Buffer.map[k]) 
                } else if new_Buffer.map.contains_key(k) { 
                    new_Buffer.map[k] 
                } else { 
                    self.map[k]
                })
        }
    }

    pub open spec(checked) fn empty() -> SimpleBuffer {
        SimpleBuffer{ map: Map::empty() }
    }

    pub open spec(checked) fn insert(self, key: Key, msg: Message) -> SimpleBuffer {
        SimpleBuffer { map: self.map.insert(key, msg) }
    }
} // end impl SimpleBuffer

/// utility functions

pub open spec(checked) fn all_keys() -> Set<Key> {
    Set::new( |k| true )
}

pub open spec(checked) fn total_keys(keys: Set<Key>) -> bool {
    forall |k| keys.contains(k)
}

}  // end verus!
