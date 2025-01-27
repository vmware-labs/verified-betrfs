// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;

verus!{

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
struct Implementation {
}

impl Implementation {
}

impl KVStoreTrait for Implementation {
    type Proof = KVStoreTokenized::State;   // Supplied in implementation/ModelRefinement_v


}

}
