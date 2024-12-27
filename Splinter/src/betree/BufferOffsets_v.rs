// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;
use vstd::seq::*;

verus! {
#[verifier::ext_equal]
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

    // compacting buffers from [start..end) and shifting the corresponding offsets
    pub open spec(checked) fn adjust_compact(self, start: int, end: int) -> BufferOffsets
        recommends 0 <= start < end
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

    // closed spec(checked) fn min_ofs_recur(self, i: nat) -> nat 
    //     recommends i <= self.len()
    //     decreases self.len() - i when i <= self.len()
    // {
    //     if i == self.len() { 
    //         if self.len() == 0 {
    //             0
    //         } else {
    //             self.offsets[i-1]
    //         }
    //     } else {
    //         let sub_min = self.min_ofs_recur(i+1);
    //         if self.offsets[i as int] <= sub_min {
    //             self.offsets[i as int]
    //         } else {
    //             sub_min
    //         }
    //     }
    // }

    // pub closed spec(checked) fn min_ofs(self) -> nat 
    // {
    //     self.min_ofs_recur(0)
    // }

    // proof fn min_ofs_recur_ensures(self, i: nat)
    //     requires i <= self.len()
    //     ensures 
    //         i < self.len() ==> self.offsets.contains(self.min_ofs_recur(i)),
    //         forall |idx: int| i <= idx < self.len() ==> 
    //             self.offsets[idx] >= self.min_ofs_recur(i) 
    //     decreases  self.len() - i
    // {
    //     if i < self.len() {
    //         self.min_ofs_recur_ensures(i + 1);
    //     }
    // }

    // pub proof fn min_ofs_ensures(self) 
    //     ensures 
    //         self.all_gte(self.min_ofs()),
    //         self.len() > 0 ==> self.offsets.contains(self.min_ofs()),
    //         self.len() == 0 ==> self.min_ofs() == 0,
    // {
    //     self.min_ofs_recur_ensures(0);
    // }

    // pub proof fn all_gte_is_min_ofs(self, ofs: nat)
    //     requires
    //         self.all_gte(ofs),
    //         self.offsets.contains(ofs),
    //     ensures 
    //         ofs == self.min_ofs(),
    // {
    //     self.min_ofs_ensures();
    //     if ofs != self.min_ofs() {
    //         let idx_ofs = self.offsets.index_of(ofs);
    //         let idx_other = self.offsets.index_of(self.min_ofs());
    //         assert(self.offsets[idx_ofs] >= self.min_ofs());
    //         assert(self.offsets[idx_other] >= ofs);
    //         assert(false);
    //     }
    // }

    // pub proof fn dup_ensures(self, idx: int)
    //     requires 0 <= idx < self.len()
    //     ensures forall |ofs| self.offsets.contains(ofs) 
    //         ==> #[trigger] self.dup(idx).offsets.contains(ofs)
    // {
    //     let result = self.dup(idx);
    //     self.offsets.insert_ensures(idx, self.offsets[idx]);
    //     assert forall |i| 0 <= i < self.offsets.len()
    //     implies #[trigger] result.offsets.contains(self.offsets[i])
    //     by {
    //         let _ = result.offsets[i]; // trigger
    //     }
    // }

    // pub proof fn adjust_compact_ensures(self, start: int, end: int)
    //     requires
    //         0 <= start < end,
    //     ensures
    //         self.adjust_compact(start, end).min_ofs() <= self.min_ofs()
    // {
    //     let result = self.adjust_compact(start, end);
    //     let result_ofs = result.min_ofs();

    //     result.min_ofs_ensures();
    //     self.min_ofs_ensures();

    //     if result.offsets.len() > 0 {
    //         let idx = result.offsets.index_of(result_ofs);
    //         assert forall |i:int| 0 <= i < self.len()
    //         implies self.offsets[i] >= result_ofs
    //         by {
    //             if self.offsets[i] <= start {
    //                 assert(self.offsets[i] == result.offsets[i]);
    //             } else if self.offsets[i] >= end {
    //                 assert(result.offsets[i] <= self.offsets[i]);
    //             }
    //         }

    //         if self.offsets.contains(result_ofs) {
    //             assert(self.all_gte(result_ofs));
    //             self.all_gte_is_min_ofs(result_ofs);
    //         } else {
    //             assert(result_ofs <= self.min_ofs());
    //         }
    //     }
    // }

} // end impl BufferOffsets
}  // end verus!