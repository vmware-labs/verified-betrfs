// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::{seq::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::OffsetMap_v::*;

verus! {

#[verifier::ext_equal]
pub struct BufferSeq {
    pub buffers: Seq<SimpleBuffer>
}

impl BufferSeq {
    pub open spec(checked) fn empty() -> BufferSeq
    {
        BufferSeq{ buffers: seq![] }
    }

    pub open spec(checked) fn len(self) -> nat {
        self.buffers.len()
    }

    #[verifier(inline)]
    pub open spec(checked) fn spec_index(self, i: int) -> SimpleBuffer
        recommends 0 <= i < self.len()
    {
        self.buffers[i]
    }

    pub open spec(checked) fn slice(self, start: int, end: int) -> BufferSeq 
        recommends 0 <= start <= end <= self.len()
    {
        BufferSeq{ buffers: self.buffers.subrange(start, end) }
    }

    pub open spec(checked) fn drop_first(self) -> BufferSeq
        recommends 0 < self.len()
    {
        self.slice(1, self.len() as int)
    }

    pub open spec(checked) fn query_from(self, key: Key, start: int) -> Message 
        recommends 0 <= start <= self.len()
        decreases self.len() - start when start <= self.len()
    {
        if start == self.len() {
            Message::Update{delta: nop_delta()}
        } else {
            // merge message from old buffer to new result
            self.buffers[start].query(key).merge(self.query_from(key, start+1))
        }
    }

    pub open spec(checked) fn query(self, key: Key) -> Message {
        self.query_from(key, 0)
    }

    pub open spec(checked) fn apply_filter(self, accept: Set<Key>) -> BufferSeq {
        BufferSeq{ buffers: Seq::new(self.len(), |i: int| self.buffers[i].apply_filter(accept)) }
    }

    pub open spec(checked) fn extend(self, new_buffers: BufferSeq) -> BufferSeq {
        BufferSeq{ buffers: self.buffers + new_buffers.buffers }
    }

    pub open spec(checked) fn update_subrange(self, start: int, end: int, new_buffer: SimpleBuffer) -> BufferSeq 
        recommends 0 <= start < end <= self.len()
    {
        let s = seq![new_buffer];
        BufferSeq{ buffers: self.buffers.subrange(0, start) + s + self.buffers.subrange(end, self.len() as int) }
    }

    pub open spec(checked) fn i_from(self, idx: int) -> SimpleBuffer
        recommends 0 <= idx <= self.len()
        decreases self.len() - idx when 0 <= idx <= self.len()
    {
        if self.len() == idx {
            SimpleBuffer::empty()
        } else {
            self[idx].merge(self.i_from(idx+1))
        }
    }

    pub open spec(checked) fn i(self) -> SimpleBuffer
    {
        self.i_from(0)
    }

    pub open spec fn key_in_buffer(self, from_idx: int, k: Key, buffer_idx: int) -> bool
    {
        &&& from_idx <= buffer_idx < self.len()
        &&& self[buffer_idx].map.contains_key(k)
    }

    pub open spec /*XXX (checked)*/ fn i_filtered_from(self, offset_map: OffsetMap, idx: int) -> SimpleBuffer
        recommends offset_map.is_total(), 0 <= idx <= self.len() 
        decreases self.len() - idx when 0 <= idx <= self.len()
    {
        if self.len() == idx {
            SimpleBuffer::empty()
        } else {
            let bottom_buffer = self[idx].apply_filter(offset_map.active_keys(idx as nat));
//            let _ = assert(new_offset_map.is_total());   // XXX: aargh what was the way to add proof text?
            bottom_buffer.merge(self.i_filtered_from(offset_map, idx+1))
        }
    }

    pub open spec(checked) fn i_filtered(self, offset_map: OffsetMap) -> SimpleBuffer 
      recommends offset_map.is_total()
    {
        self.i_filtered_from(offset_map, 0)
    }

    pub open spec(checked) fn key_in_buffer_filtered(self, offset_map: OffsetMap, from_idx: int, k: Key, buffer_idx: int) -> bool
    recommends
        offset_map.is_total(),
        0 <= from_idx,
    {
        &&& self.key_in_buffer(from_idx, k, buffer_idx)
        &&& offset_map.offsets[k] <= buffer_idx
    }

    pub proof fn query_agrees_with_i(self, k: Key, start: int)
        requires 0 <= start <= self.len(), 
        ensures 
            self.i_from(start).map.contains_key(k) ==> self.query_from(k, start) == self.i_from(start).map[k],
            !self.i_from(start).map.contains_key(k) ==> self.query_from(k, start) == (Message::Update{delta: nop_delta()})
        decreases self.len() - start
    {
        if start < self.len() {
            self.query_agrees_with_i(k, start+1);
        }
    }

    pub proof fn i_from_domain(self, idx: int)
        requires 0 <= idx <= self.len()
        ensures forall |k| self.i_from(idx).map.contains_key(k) <==> exists |buffer_idx| self.key_in_buffer(idx, k, buffer_idx)
        decreases self.len() - idx
    {
        assert forall |k| #[trigger] self.i_from(idx).map.contains_key(k) <==> exists |buffer_idx| self.key_in_buffer(idx, k, buffer_idx)
        by {
            if self.i_from(idx).map.contains_key(k) {
//                assert(idx < self.len()); // trigger
                if self.key_in_buffer(idx, k, idx) {
                } else {
                    self.i_from_domain(idx+1);
                    assert(self.i_from(idx+1).map.contains_key(k));

                    let next_idx = idx + 1; // TODO(verus): temp measure before forall_arith pr is merged
                    let buffer_idx = choose |buffer_idx| self.key_in_buffer(next_idx, k, buffer_idx);
                    assert(self.key_in_buffer(idx, k, buffer_idx));
                }
            }
            if exists |buffer_idx| self.key_in_buffer(idx, k, buffer_idx) {
                let buffer_idx = choose |buffer_idx| self.key_in_buffer(idx, k, buffer_idx);
                if buffer_idx == idx {
//                    assert(self.i_from(idx).map.contains_key(k));
                } else {
                    self.i_from_domain(idx+1);
                    assert(self.key_in_buffer(idx+1, k, buffer_idx)); // trigger
                    assert(self.i_from(idx+1).map.contains_key(k)); // trigger
                }
            }
        }
    }

    pub proof fn i_filtered_from_domain(self, offset_map: OffsetMap, idx: int)
        requires offset_map.is_total(), 0 <= idx <= self.len()
        ensures forall |k| self.i_filtered_from(offset_map, idx).map.contains_key(k)
            <==> exists |buffer_idx| self.key_in_buffer_filtered(offset_map, idx, k, buffer_idx)
        decreases self.len() - idx
    {
        let result = self.i_filtered_from(offset_map, idx);
        assert forall |k| #[trigger] result.map.contains_key(k)
            <==> exists |buffer_idx| self.key_in_buffer_filtered(offset_map, idx, k, buffer_idx)
        by {
            if result.map.contains_key(k) {
//                assert(idx < self.len()); // trigger
                if self.key_in_buffer_filtered(offset_map, idx, k, idx) {
                } else {
                    let sub_result = self.i_filtered_from(offset_map, idx+1);
                    self.i_filtered_from_domain(offset_map, idx+1);
//                    assert(sub_result.map.contains_key(k));

                    let next_idx = idx + 1; // TODO(verus): temp measure before forall_arith pr is merged
                    let buffer_idx = choose |buffer_idx| self.key_in_buffer_filtered(offset_map, next_idx, k, buffer_idx);
                    assert(self.key_in_buffer_filtered(offset_map, idx, k, buffer_idx));
                }
            } 
            if exists |buffer_idx| self.key_in_buffer_filtered(offset_map, idx, k, buffer_idx) {
                let buffer_idx = choose |buffer_idx| self.key_in_buffer_filtered(offset_map, idx, k, buffer_idx);
                if buffer_idx == idx {
//                    assert(result.map.contains_key(k));
                } else {
                    let sub_result = self.i_filtered_from(offset_map, idx+1);
                    self.i_filtered_from_domain(offset_map, idx+1);
                    assert(self.key_in_buffer_filtered(offset_map, idx+1, k, buffer_idx)); // trigger
                }
            }
        }
    }

    pub proof fn query_from_same_as_i_filtered(self, k: Key, buffer_idx: int, offset_map: OffsetMap)
        requires
            offset_map.is_total(),
            0 <= buffer_idx <= self.len(),
            offset_map.offsets[k] <= self.len(),
        ensures ({
            let start = offset_map.offsets[k] as int;
            &&& start <= buffer_idx ==> 
                self.i_filtered_from(offset_map, buffer_idx).query(k) == self.query_from(k, buffer_idx)
            &&& start > buffer_idx ==> 
                self.i_filtered_from(offset_map, buffer_idx).query(k) == self.query_from(k, start)
        })
        decreases self.len() - buffer_idx
    {
        if buffer_idx < self.len() {
            self.query_from_same_as_i_filtered(k, buffer_idx+1, offset_map);
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

    pub proof fn extend_buffer_seq_query_ensures(top: BufferSeq, bottom: BufferSeq, key: Key, start: int)
        requires 0 <= start <= bottom.len()
        ensures bottom.extend(top).query_from(key, start) == bottom.query_from(key, start).merge(top.query(key)) 
        decreases bottom.len()-start
    {
        if start == bottom.len() {
            Self::common_buffer_seqs(bottom.extend(top), top, start, 0-start, key);
        } else {
//            assert(bottom.extend(top).buffers[start] == bottom.buffers[start]);
            Self::extend_buffer_seq_query_ensures(top, bottom, key, start+1);
        }
    }

    pub proof fn not_present_query_lemma(self, k: Key, start: int)
        requires 0 <= start <= self.len(),
            forall |i| #![auto] start <= i < self.len() ==> !self[i].map.contains_key(k)
        ensures self.query_from(k, start) == (Message::Update{ delta: nop_delta() })
        decreases self.len()-start
    {
        if start < self.len() {
            self.not_present_query_lemma(k, start+1);
        }
    }
} // end impl BufferSeq
}  // end verus!