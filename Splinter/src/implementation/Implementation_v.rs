// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;
use vstd::{pervasive::*};
use vstd::tokens::InstanceId;

use crate::trusted::ClientAPI_t::*;
use crate::trusted::KVStoreTrait_t::*;
use crate::trusted::KVStoreTokenized_v::*;

verus!{

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    state: Tracked<KVStoreTokenized::atomic_state>,
    instance: Tracked<KVStoreTokenized::Instance>,
}

impl Implementation {
}

impl KVStoreTrait for Implementation {
    type Proof = KVStoreTokenized::State;   // Supplied in implementation/ModelRefinement_v

    closed spec fn wf(self) -> bool {
        true
    }

    closed spec fn instance(self) -> InstanceId
    {
        self.instance@.id()
    }

    fn new() -> (out: Self)
        ensures out.wf()
    {
        let tracked (
            Tracked(instance),
            Tracked(atomic_state),  // non sharded state
            Tracked(requests),      // request perm map (multiset), empty
            Tracked(replies),       // reply perm map (multiset), empty
        ) = KVStoreTokenized::Instance::initialize();

        Implementation{
            state: Tracked(atomic_state),
            instance: Tracked(instance)
        }
    }

    fn kvstore_main(self, api: ClientAPI)
    {
        print_u64(1);
    }
}

}
