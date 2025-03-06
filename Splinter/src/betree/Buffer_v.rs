// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin_macros::*;
use vstd::{map::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::BufferDisk_v::*;
use crate::disk::GenericDisk_v::{Address};

verus! {

pub trait Buffer : Sized {
    spec(checked) fn linked_contains(self, dv: BufferDisk<Self>, addr: Address, key: Key) -> bool
        recommends dv.repr().contains(addr) && dv.entries[addr] == self
    ;

    spec(checked) fn linked_query(self, dv: BufferDisk<Self>, addr: Address, key: Key) -> Message
        recommends dv.repr().contains(addr) && dv.entries[addr] == self
    ;

    spec fn i(self, dv: BufferDisk<Self>, addr: Address) -> SimpleBuffer
        recommends dv.repr().contains(addr) && dv.entries[addr] == self
    ;
}

// rename to Simple SimpleBuffer
#[verifier::ext_equal]
pub struct SimpleBuffer {
    pub map: Map<Key, Message>
}

impl Buffer for SimpleBuffer {
    open spec(checked) fn linked_contains(self, dv: BufferDisk<Self>, addr: Address, key: Key) -> bool {
        self.map.contains_key(key)
    }

    open spec(checked) fn linked_query(self, dv: BufferDisk<Self>, addr: Address, key: Key) -> Message {
        self.query(key)
    }

    open spec(checked) fn i(self, dv: BufferDisk<Self>, addr: Address) -> SimpleBuffer {
        self
    }
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
