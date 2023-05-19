#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use vstd::{*,map::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;

verus! {

pub open spec fn all_keys() -> Set<Key> {
    Set::new( |k| true )
}

pub open spec fn total_keys(keys: Set<Key>) -> bool {
    forall |k| keys.contains(k)
}

pub struct Buffer { 
    pub map: Map<Key, Message>
}

impl Buffer {
    pub open spec fn query(self, key: Key) -> Message {
        if self.map.contains_key(key) {
            self.map[key]
        } else {
            Message::Update{ delta: nop_delta() }
        }
    }

    pub open spec fn apply_filter(self, accept: Set<Key>) -> Buffer {
        Buffer{ map: Map::new( |k| accept.contains(k) && self.map.contains_key(k), |k| self.map[k] ) }
    }

    pub open spec fn merge(self, older: Buffer) -> Buffer {
        Buffer{ map: Map::new( |k| self.map.contains_key(k) || older.map.contains_key(k), 
            |k| if self.map.contains_key(k) && older.map.contains_key(k) 
                { older.map[k].merge(self.map[k]) }
                else if self.map.contains_key(k) { self.map[k] } 
                else { older.map[k] }) }
    }

    pub open spec fn empty_buffer() -> Buffer {
        Buffer{ map: Map::empty() }
    }
} // end impl Buffer
}  // end verus!
