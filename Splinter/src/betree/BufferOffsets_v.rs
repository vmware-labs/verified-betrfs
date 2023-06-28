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

pub struct BufferOffsets {
    pub offsets: Seq<nat>
}

pub open spec fn empty_bufer_offsets() -> BufferOffsets
{
    BufferOffsets{offsets: seq![]}
}

impl BufferOffsets {
    pub open spec fn len(self) -> nat {
        self.offsets.len()
    }

    pub open spec fn slice(self, start: int, end: int) -> BufferOffsets 
        recommends 0 <= start <= end <= self.len()
    {
        BufferOffsets{ offsets: self.offsets.subrange(start, end) }
    }

    pub open spec fn dup(self, idx: int) -> BufferOffsets
        recommends 0 <= idx < self.len()
    {
        BufferOffsets{ offsets: self.offsets.insert(idx, self.offsets[idx]) }
    }

    pub open spec fn update(self, idx: int, value: nat) -> BufferOffsets
        recommends 0 <= idx < self.len()
    {
        BufferOffsets{ offsets: self.offsets.update(idx, value) }
    }

    pub open spec fn all_lte(self, target: nat) -> bool 
    {
        forall |i:int| 0 <= i < self.len() ==> self.offsets[i] <= target
    }

    pub open spec fn all_gte(self, target: nat) -> bool
    {
        forall |i:int| 0 <= i < self.len() ==> self.offsets[i] >= target
    }

    pub open spec fn shift_left(self, target: nat) -> BufferOffsets
        recommends self.all_gte(target)
    {
        BufferOffsets{ offsets: Seq::new(self.len(), |i:int| (self.offsets[i]-target) as nat) }
    }

    pub open spec fn adjust_compact(self, start: int, end: int) -> BufferOffsets
        recommends 0 <= start <= end <= self.len()
    {
        BufferOffsets{ offsets: Seq::new(self.len(), |i:int| 
            if self.offsets[i] <= start {
                self.offsets[i]
            } else if self.offsets[i] < end {
                start as nat
            } else {
                (self.offsets[i] - (end - start) + 1) as nat
            }
        )}
    }
} // end impl BufferOffsets
}  // end verus!