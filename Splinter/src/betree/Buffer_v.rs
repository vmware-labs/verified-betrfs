// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin_macros::*;
use vstd::{map::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;

verus! {

pub trait AbstractBuffer {
    spec fn contains(&self, key: Key) -> bool;

    spec fn query(&self, key: Key) -> Message;

    spec fn insert_ref(&self, key: Key, msg: Message) -> &Self;

    spec fn is_empty(&self) -> bool;

    // spec fn meow() -> &Self;

    spec fn i(&self) -> Buffer;
}

#[verifier::ext_equal]
pub struct Buffer { 
    pub map: Map<Key, Message>
}

impl AbstractBuffer for Buffer {
    open spec(checked) fn contains(&self, key: Key) -> bool {
        self.map.contains_key(key)
    }

    open spec(checked) fn query(&self, key: Key) -> Message {
        if self.contains(key) {
            self.map[key]
        } else {
            Message::Update{ delta: nop_delta() }
        }
    }
    
    // this is not ok but insert_ref is allowed???
    // spec fn meow() -> &Self {
    //     Buffer::empty()
    // }

    open spec(checked) fn insert_ref(&self, key: Key, msg: Message) -> &Self {
        &self.insert(key, msg)
    }

    open spec(checked) fn is_empty(&self) -> bool {
        *self == Buffer::empty()
    }

    open spec(checked) fn i(&self) -> Buffer {
        *self
    }

}

// A Buffer is a map from keys to messages.
impl Buffer {
    pub open spec(checked) fn apply_filter(self, accept: Set<Key>) -> Buffer {
        Buffer{ map: Map::new( |k| accept.contains(k) && self.map.contains_key(k), |k| self.map[k] ) }
    }

    pub open spec(checked) fn merge(self, new_Buffer: Buffer) -> Buffer {
        Buffer{ map: Map::new( 
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

    pub open spec(checked) fn empty() -> Buffer {
        Buffer{ map: Map::empty() }
    }

    pub open spec(checked) fn insert(self, key: Key, msg: Message) -> Buffer {
        Buffer { map: self.map.insert(key, msg) }
    }
} // end impl Buffer

/// utility functions

pub open spec(checked) fn all_keys() -> Set<Key> {
    Set::new( |k| true )
}

pub open spec(checked) fn total_keys(keys: Set<Key>) -> bool {
    forall |k| keys.contains(k)
}

}  // end verus!
