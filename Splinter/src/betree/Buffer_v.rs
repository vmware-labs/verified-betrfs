// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin_macros::*;
use vstd::{map::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;

verus! {

pub trait Buffer {
    // NOTE: & shouldn't really exist in spec land

    spec fn contains(&self, key: Key) -> bool;

    spec fn query(&self, key: Key) -> Message;

    spec fn insert_ref(&self, key: Key, msg: Message) -> &Self;

    spec fn is_empty(&self) -> bool;

    spec fn i(&self) -> SimpleBuffer;

    broadcast proof fn contains_refines(&self, key: Key) 
        ensures #[trigger] self.contains(key) == self.i().map.contains_key(key)
    ;

    broadcast proof fn query_refines(&self, key: Key)
        ensures  #[trigger] self.query(key) == self.i().query_internal(key)
    ;

    broadcast proof fn insert_refines(&self, key: Key, msg: Message) 
        ensures self.insert_ref(key, msg).i() == self.i().insert(key, msg)
    ;

    proof fn empty_refines(&self) 
        ensures  #[trigger] self.is_empty() ==> self.i() == SimpleBuffer::empty()
    ;
}

// rename to Simple SimpleBuffer
#[verifier::ext_equal]
pub struct SimpleBuffer { 
    pub map: Map<Key, Message>
}

impl Buffer for SimpleBuffer {
    open spec(checked) fn contains(&self, key: Key) -> bool {
        self.map.contains_key(key)
    }

    open spec(checked) fn query(&self, key: Key) -> Message {
        self.query_internal(key)
    }
    
    // 'a = any life time provided
    // open spec fn meow() -> &'static Self {
    //     &SimpleBuffer::empty()
    // }

    // &self for traits in spec land doesn't make sense
    open spec(checked) fn insert_ref(&self, key: Key, msg: Message) -> &Self {
        &self.insert(key, msg)
    }

    open spec(checked) fn is_empty(&self) -> bool {
        *self == SimpleBuffer::empty()
    }

    open spec(checked) fn i(&self) -> SimpleBuffer {
        *self
    }

    proof fn contains_refines(&self, key: Key) {}

    proof fn query_refines(&self, key: Key) {}

    proof fn insert_refines(&self, key: Key, msg: Message) {}

    proof fn empty_refines(&self) {}
}

// A SimpleBuffer is a map from keys to messages.
impl SimpleBuffer {
    pub open spec(checked) fn query_internal(&self, key: Key) -> Message {
        if self.map.contains_key(key) {
            self.map[key]
        } else {
            Message::Update{ delta: nop_delta() }
        }
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
