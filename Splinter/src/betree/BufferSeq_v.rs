#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use vstd::{*,map::*,seq::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::OffsetMap_v::*;

verus! {

pub struct BufferSeq {
    pub buffers: Seq<Buffer>
}

impl BufferSeq {
    pub open spec fn len(self) -> nat {
        self.buffers.len()
    }

    pub open spec fn slice(self, start: int, end: int) -> BufferSeq 
        recommends 0 <= start <= end <= self.len()
    {
        BufferSeq{ buffers: self.buffers.subrange(start, end) }
    }

    pub open spec fn drop_first(self) -> BufferSeq
        recommends 0 < self.len()
    {
        self.slice(1, self.len() as int)
    }

    pub open spec fn query_from(self, key: Key, start: int) -> Message 
        recommends 0 <= start <= self.len()
        decreases self.len() - start
    {
        decreases_when(start <= self.len());
        if start == self.len() {
            Message::Update{ delta: nop_delta() }
        } else {
            self.query_from(key, start+1).merge(self.buffers[start].query(key))
        }
    }

    pub open spec fn query(self, key: Key) -> Message {
        self.query_from(key, 0)
    }

    pub open spec fn apply_filter(self, accept: Set<Key>) -> BufferSeq {
        BufferSeq{ buffers: Seq::new(self.len(), |i: int| self.buffers[i].apply_filter(accept)) }
    }

    pub open spec fn extend(self, new_buffers: BufferSeq) -> BufferSeq {
        BufferSeq{ buffers: self.buffers + new_buffers.buffers }
    }

    pub open spec fn i(self) -> Buffer 
        decreases self.buffers.len()
    {
        if self.buffers.len() == 0 {
            Buffer::empty_buffer()
        } else {
            self.drop_first().i().merge(self.buffers[0])
        }
    }

    pub open spec fn i_bottom(self, offset_map: OffsetMap) -> Buffer
        recommends 
        offset_map.is_total(), 
            0 < self.buffers.len()
    {
        self.buffers[0].apply_filter(offset_map.filter_for_bottom())
    }

    pub open spec fn i_filtered(self, offset_map: OffsetMap) -> Buffer 
      recommends offset_map.is_total()
      decreases self.buffers.len()
    {
        if self.buffers.len() == 0 {
            Buffer::empty_buffer()
        } else {
            let new_offset_map = offset_map.decrement(1);
            self.drop_first().i_filtered(new_offset_map).merge(self.i_bottom(offset_map))
        }
    }
} // end impl BufferSeq
}  // end verus!