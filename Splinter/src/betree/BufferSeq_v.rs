use builtin::*;

use builtin_macros::*;

use vstd::{*,seq::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::OffsetMap_v::*;

verus! {

#[verifier::ext_equal]
pub struct BufferSeq {
    pub buffers: Seq<Buffer>
}

pub open spec fn empty_buffer_seq() -> BufferSeq
{
    BufferSeq{buffers: seq![]}
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
            Message::Update{delta: nop_delta()}
        } else {
            // merge message from old buffer to new result
            self.buffers[start].query(key).merge(self.query_from(key, start+1))
        }
    }

    pub open spec fn query(self, key: Key) -> Message {
        self.query_from(key, 0)
    }

    pub proof fn query_singleton(self, key: Key)
        requires self.len() == 1
        ensures self.query(key) == self.buffers[0].query(key)
    {
        assert(self.query_from(key, 1) == Message::Update{delta: nop_delta()});
    }

    pub open spec fn apply_filter(self, accept: Set<Key>) -> BufferSeq {
        BufferSeq{ buffers: Seq::new(self.len(), |i: int| self.buffers[i].apply_filter(accept)) }
    }

    pub open spec fn extend(self, new_buffers: BufferSeq) -> BufferSeq {
        BufferSeq{ buffers: self.buffers + new_buffers.buffers }
    }

    pub open spec fn update_subrange(self, start: int, end: int, new_buffer: Buffer) -> BufferSeq 
        recommends 0 <= start < end <= self.len()
    {
        let s = seq![new_buffer];
        BufferSeq{ buffers: self.buffers.subrange(0, start) + s + self.buffers.subrange(end, self.len() as int) }
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

    pub proof fn common_buffer_seqs(a: BufferSeq, b: BufferSeq, a_start: int, b_delta: int, key: Key)
        requires 0 <= a_start <= a.len(), 0 <= a_start+b_delta <= b.len(), 
            a.len()-a_start == b.len()-a_start-b_delta,
            forall |i:int| a_start <= i < a.len() ==> a.buffers[i] == b.buffers[i+b_delta]
        ensures a.query_from(key, a_start) == b.query_from(key, a_start+b_delta)
        decreases a.len()-a_start
    {
        if a_start < a.len() {
            Self::common_buffer_seqs(a, b, a_start+1, b_delta, key);
        }
    }

    pub proof fn extend_buffer_seq_lemma(top: BufferSeq, bottom: BufferSeq, key: Key, start: int)
        requires 0 <= start <= bottom.len()
        ensures bottom.extend(top).query_from(key, start) == bottom.query_from(key, start).merge(top.query(key)) 
        decreases bottom.len()-start
    {
        if start == bottom.len() {
            Self::common_buffer_seqs(bottom.extend(top), top, start, 0-start, key);
        } else {
            assert(bottom.extend(top).buffers[start] == bottom.buffers[start]);
            Self::extend_buffer_seq_lemma(top, bottom, key, start+1);
        }
    }

    pub proof fn filtered_buffer_seq_query_lemma(self, filter: Set<Key>, key: Key, start: int)
        requires 0 <= start <= self.len()
        ensures self.apply_filter(filter).query_from(key, start)
            == if filter.contains(key) { self.query_from(key, start) } 
                else { Message::Update{delta: nop_delta()} }
        decreases self.len() - start
    {
        if start < self.len() {
            self.filtered_buffer_seq_query_lemma(filter, key, start+1);
        }
    }

} // end impl BufferSeq
}  // end verus!