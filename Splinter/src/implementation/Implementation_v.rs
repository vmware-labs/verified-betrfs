// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;
use vstd::{pervasive::*};
use vstd::prelude::*;
use vstd::modes::*;
use vstd::tokens::InstanceId;
use vstd::hash_map::*;

use crate::trusted::ClientAPI_t::*;
use crate::trusted::KVStoreTrait_t::*;
use crate::trusted::KVStoreTokenized_v::*;
use crate::spec::MapSpec_t::{Request, Reply, Output};
// use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;

verus!{

pub type Key = usize;

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    store: HashMapWithView<Key, Value>,
    state: Tracked<KVStoreTokenized::atomic_state>,
    instance: Tracked<KVStoreTokenized::Instance>,
}


impl Implementation {
    pub exec fn handle(&mut self, req: Request, tracked req_shard: Tracked<KVStoreTokenized::requests>)
            -> (out: (Reply, Tracked<KVStoreTokenized::replies>))
    requires
        req_shard@.instance_id() == old(self).instance_id(),
        req_shard@.element() == req
    ensures
        out.1@.instance_id() == self.instance_id(),
        out.1@.element() == out.0
    {
        assert(req.input is NoopInput);

        let reply = Reply{output: Output::NoopOutput, id: req.id};

        let ghost post_state: AtomicState = self.state@.value(); // noop!
        let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
        //let tracked mut state = &self.state;
        proof {
            tracked_swap(self.state.borrow_mut(), &mut atomic_state);
        }

        let tracked new_reply_token = self.instance.borrow().transition(
            KVStoreTokenized::Label::ExecuteOp{req, reply},
            post_state,
            &mut atomic_state,
            req_shard.get(),
        );
        self.state = Tracked(atomic_state);

        (reply, Tracked(new_reply_token))
    }
}

impl KVStoreTrait for Implementation {
    type Proof = KVStoreTokenized::State;   // Supplied in implementation/ModelRefinement_v

    closed spec fn wf(self) -> bool {
        true
    }

    closed spec fn instance_id(self) -> InstanceId
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
            store: HashMapWithView::new(),
            state: Tracked(atomic_state),
            instance: Tracked(instance)
        }
    }

    fn kvstore_main(&mut self, api: ClientAPI)
    {
        let debug_print = true;
        loop {
            let (req, req_shard) = api.receive_request(debug_print);
            let (reply, reply_shard) = self.handle(req, req_shard);
        }
    }
}

}
