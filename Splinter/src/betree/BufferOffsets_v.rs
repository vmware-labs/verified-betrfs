// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;
use vstd::seq::*;

verus! {

pub struct BufferOffsets {
    pub offsets: Seq<nat>
}

pub open spec(checked) fn empty_bufer_offsets() -> BufferOffsets
{
    BufferOffsets{offsets: seq![]}
}

impl BufferOffsets {
    pub open spec(checked) fn len(self) -> nat {
        self.offsets.len()
    }

    pub open spec(checked) fn slice(self, start: int, end: int) -> BufferOffsets 
        recommends 0 <= start <= end <= self.len()
    {
        BufferOffsets{ offsets: self.offsets.subrange(start, end) }
    }

    pub open spec(checked) fn dup(self, idx: int) -> BufferOffsets
        recommends 0 <= idx < self.len()
    {
        BufferOffsets{ offsets: self.offsets.insert(idx, self.offsets[idx]) }
    }

    pub open spec(checked) fn update(self, idx: int, value: nat) -> BufferOffsets
        recommends 0 <= idx < self.len()
    {
        BufferOffsets{ offsets: self.offsets.update(idx, value) }
    }

    pub open spec(checked) fn all_lte(self, target: nat) -> bool 
    {
        forall |i:int| 0 <= i < self.len() ==> self.offsets[i] <= target
    }

    pub open spec(checked) fn all_gte(self, target: nat) -> bool
    {
        forall |i:int| 0 <= i < self.len() ==> self.offsets[i] >= target
    }

    pub open spec(checked) fn shift_left(self, target: nat) -> BufferOffsets
        recommends self.all_gte(target)
    {
        BufferOffsets{ offsets: Seq::new(self.len(), |i:int| (self.offsets[i]-target) as nat) }
    }

    pub proof fn shift_left_preserves_lte(self, target: nat, limit: nat)
        requires self.all_gte(target), self.all_lte(limit), limit >= target
        ensures self.shift_left(target).all_lte((limit-target) as nat)
    {
    } 

    pub open spec(checked) fn adjust_compact(self, start: int, end: int) -> BufferOffsets
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