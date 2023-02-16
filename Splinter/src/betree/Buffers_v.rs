#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::prelude::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;

verus! {

pub open spec fn all_keys() -> Set<Key> {
    Set::new( |k| true )
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
} // end impl Buffer

pub struct BufferStack {
    pub buffers: Seq<Buffer>
}

impl BufferStack {
    pub open spec fn len(self) -> nat {
        self.buffers.len()
    }

    pub open spec fn slice(self, start: int, end: int) -> BufferStack 
        recommends 0 <= start <= end <= self.len()
    {
        BufferStack{ buffers: self.buffers.subrange(start, end) }
    }

    pub open spec fn query_up_to(self, key: Key, count: nat) -> Message 
        recommends count <= self.len()
        decreases count
    {
        if count == 0 {
            Message::Update{ delta: nop_delta() }
        } else {
            self.query_up_to(key, (count - 1) as nat).merge(self.buffers[count-1].query(key))
        }
    }

    pub open spec fn query(self, key: Key) -> Message {
        self.query_up_to(key, self.len())
    }

    pub open spec fn apply_filter(self, accept: Set<Key>) -> BufferStack {
        BufferStack{ buffers: Seq::new(self.len(), |i: int| self.buffers[i].apply_filter(accept)) }
    }

    pub open spec fn push_buffer_stack(self, new_buffers: BufferStack) -> BufferStack {
        BufferStack{ buffers: new_buffers.buffers + self.buffers}
    }

    pub open spec fn equivalent(self, other: BufferStack) -> bool {
        forall |k| self.query(k) == other.query(k)
    }
} // end impl BufferStack
}  // end verus!