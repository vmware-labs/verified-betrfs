// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::{seq::*};
use crate::disk::GenericDisk_v::{Address};

verus! {
#[verifier::ext_equal]
pub struct LinkedSeq {
    pub addrs: Seq<Address>,
}

impl LinkedSeq {
    pub open spec(checked) fn empty() -> LinkedSeq
    {
        LinkedSeq{ addrs: seq![] }
    }

    pub open spec(checked) fn len(self) -> nat {
        self.addrs.len()
    }

    #[verifier(inline)]
    pub open spec(checked) fn spec_index(self, i: int) -> Address
        recommends 0 <= i < self.len()
    {
        self.addrs[i]
    }

    pub open spec(checked) fn contains(self, addr: Address) -> bool
    {
        self.addrs.contains(addr)
    }

    pub open spec(checked) fn slice(self, start: int, end: int) -> LinkedSeq
        recommends 0 <= start <= end <= self.len()
    {
        LinkedSeq{ addrs: self.addrs.subrange(start, end), ..self }
    }

    pub open spec(checked) fn extend(self, new_addrs: Self) -> LinkedSeq
    {
        LinkedSeq{ addrs: self.addrs + new_addrs.addrs, ..self }
    }

    pub open spec(checked) fn update_subrange(self, start: int, end: int, new_addr: Address) -> LinkedSeq
        recommends 0 <= start < end <= self.len()
    {
        let addrs = self.addrs.subrange(0, start) + seq![new_addr] + self.addrs.subrange(end, self.len() as int);
        LinkedSeq{ addrs: addrs, ..self  }
    }
} // end impl<T> LinkedSeq
}  // end verus!
