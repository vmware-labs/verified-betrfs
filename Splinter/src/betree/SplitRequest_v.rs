// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use crate::spec::KeyType_t::*;

verus! {
pub enum SplitRequest {
    SplitLeaf{child_idx: nat, split_key: Key},
    SplitIndex{child_idx: nat, child_pivot_idx: nat}
}

impl SplitRequest{
    pub open spec(checked) fn xxxget_child_idx(self) -> nat
    {
        match self {
            Self::SplitLeaf{child_idx, ..} => child_idx,
            Self::SplitIndex{child_idx, ..} => child_idx 
        }
    }
}
} // end verus!
