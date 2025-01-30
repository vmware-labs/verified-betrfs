// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;
use vstd::{pervasive::*};
use vstd::prelude::*;
use vstd::modes::*;
use vstd::tokens::InstanceId;
use vstd::hash_map::*;
use vstd::std_specs::hash::*;

use crate::trusted::ClientAPI_t::*;
use crate::trusted::KVStoreTrait_t::*;
use crate::trusted::KVStoreTokenized_v::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::MapSpec_t::{Request, Reply, Output, Input};
use crate::spec::MapSpec_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;

verus!{

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    store: HashMapWithView<Key, Value>,
    state: Tracked<KVStoreTokenized::atomic_state>,
    instance: Tracked<KVStoreTokenized::Instance>,
}

impl Implementation {
    // The View hos HashMapWithView isn't what we need.
    // Gotta transform Key -> Key (by way of the darn int from the HashMapWithView @ :v)
    // and Value -> Message.
    pub closed spec fn i_hashmap(store: Map<int, Value>) -> Map<Key, Message>
    {
        Map::new(
            |k: Key| store.contains_key(k.0 as int),
            |k: Key| Message::Define{value: store[k.0 as int]}
        )
    }

    pub closed spec fn i(self) -> AtomicState {
        AtomicState{
            store: CrashTolerantAsyncMap::State {
                versions: FloatingSeq {
                    start: 0, entries: Seq::empty().push(
                        PersistentState{
                            appv: MapSpec::State {
                                kmmap: TotalKMMap(Self::i_hashmap(self.store@)),
                            }

                        }
                   ),
                },
                async_ephemeral: EphemeralState{ requests: Set::empty(), replies: Set::empty(), },
                sync_requests: Map::empty(),
            }
        }
    }

    pub open spec fn good_req(self, req: Request, req_shard: KVStoreTokenized::requests) -> bool
    {
        &&& self.wf()
        &&& req_shard.instance_id() == self.instance_id()
        &&& req_shard.element() == req
    }

    pub open spec fn good_reply(self, pre: Self, reply: Reply, reply_shard: KVStoreTokenized::replies) -> bool
    {
        &&& self.wf()
        &&& self.instance_id() == pre.instance_id()
        &&& reply_shard.instance_id() == self.instance_id()
        &&& reply_shard.element() == reply
    }

    pub exec fn handle_noop(&mut self, req: Request, req_shard: Tracked<KVStoreTokenized::requests>)
            -> (out: (Reply, Tracked<KVStoreTokenized::replies>))
    requires old(self).good_req(req, req_shard@),
        req.input is NoopInput,
    ensures self.good_reply(*old(self), out.0, out.1@),
    {
        match req.input {
            Input::NoopInput => {
                let reply = Reply{output: Output::NoopOutput, id: req.id};

                let ghost post_state = AtomicState {
                    store: CrashTolerantAsyncMap::State {
                        async_ephemeral: EphemeralState {
                            requests: self.state@.value().store.async_ephemeral.requests.remove(req),
                            replies: self.state@.value().store.async_ephemeral.replies.remove(reply),
                        },
                        .. self.state@.value().store
                    }
                };
                let ghost post_state: AtomicState = self.state@.value(); // noop!

                let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
                proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

                proof {
                    let ctam = atomic_state.value().store;
                    let async_label = AsyncMap::Label::RequestOp{ req: req };
                    let ctam_label = CrashTolerantAsyncMap::Label::OperateOp{ base_op: async_label };
                    let async_state_pre = AsyncMap::State {
                        persistent: ctam.versions.last(),
                        ephemeral: ctam.async_ephemeral
                    };
                    let async_state_post = AsyncMap::State {
                        persistent: post_state.store.versions.last(),
                        ephemeral: post_state.store.async_ephemeral
                    };

                    assume( ctam.async_ephemeral.requests.contains(req) );
                    assume( !ctam.async_ephemeral.replies.contains(reply) );
                    reveal(CrashTolerantAsyncMap::State::next);
                    reveal(CrashTolerantAsyncMap::State::next_by);
                    reveal(AsyncMap::State::next);
                    reveal(AsyncMap::State::next_by);
                    reveal(MapSpec::State::next);
                    reveal(MapSpec::State::next_by);

                    assert( AsyncMap::State::next_by(
                            async_state_pre,
                            async_state_post,
                            async_label,
                            AsyncMap::Step::execute(
                                MapSpec::Label::Noop{input: req.input, output: reply.output},
                                post_state.store.versions.last()
                            ),
                        )
                    );
                    assert( CrashTolerantAsyncMap::State::next_by(
                            ctam, post_state.store, ctam_label,
                            CrashTolerantAsyncMap::Step::operate(post_state.store.versions, post_state.store.async_ephemeral)
                            )
                    );
                    assert( CrashTolerantAsyncMap::State::next(
                            ctam, post_state.store,
                            CrashTolerantAsyncMap::Label::OperateOp{ base_op: AsyncMap::Label::RequestOp{ req: req } },
                            )
                    );
                    assert( AtomicState::execute_transition(atomic_state.value(), post_state, req, reply) );
                }

                let tracked new_reply_token = self.instance.borrow().execute_transition(
                    KVStoreTokenized::Label::ExecuteOp{req, reply},
                    post_state,
                    &mut atomic_state,
                    req_shard.get(),
                );
                self.state = Tracked(atomic_state);

                (reply, Tracked(new_reply_token))
            },
            _ => unreached(),
        }
    }

    pub exec fn handle_put(&mut self, req: Request, req_shard: Tracked<KVStoreTokenized::requests>)
            -> (out: (Reply, Tracked<KVStoreTokenized::replies>))
    requires old(self).good_req(req, req_shard@),
        req.input is PutInput,
    ensures self.good_reply(*old(self), out.0, out.1@),
    {
        match req.input {
        Input::PutInput{key, value} => {
            self.store.insert(key, value);

            let reply = Reply{output: Output::PutOutput, id: req.id};

            let ghost post_state: AtomicState = self.i();
            let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
            proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut atomic_state,
                req_shard.get(),
            );
            self.state = Tracked(atomic_state);

            (reply, Tracked(new_reply_token))
        },
            _ => unreached(),
        }
    }

    pub exec fn handle_query(&mut self, req: Request, req_shard: Tracked<KVStoreTokenized::requests>)
            -> (out: (Reply, Tracked<KVStoreTokenized::replies>))
    requires old(self).good_req(req, req_shard@),
        req.input is QueryInput,
    ensures self.good_reply(*old(self), out.0, out.1@),
    {
        match req.input {
        Input::QueryInput{key} => {
            let value = match self.store.get(&key) {
                Some(v) => *v,
                None => Value(0),
            };

            let reply = Reply{output: Output::QueryOutput{value: value}, id: req.id};

            let ghost post_state: AtomicState = self.i();
            let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
            proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut atomic_state,
                req_shard.get(),
            );
            self.state = Tracked(atomic_state);

            (reply, Tracked(new_reply_token))
        },
            _ => unreached(),
        }
    }

    pub exec fn handle(&mut self, req: Request, req_shard: Tracked<KVStoreTokenized::requests>)
            -> (out: (Reply, Tracked<KVStoreTokenized::replies>))
    requires old(self).good_req(req, req_shard@),
    ensures self.good_reply(*old(self), out.0, out.1@),
    {
        match req.input {
            Input::NoopInput => self.handle_noop(req, req_shard),
            Input::PutInput{..} => self.handle_put(req, req_shard),
            Input::QueryInput{..} => self.handle_query(req, req_shard),
        }
    }
}

impl KVStoreTrait for Implementation {
    type Proof = KVStoreTokenized::State;   // Supplied in implementation/ModelRefinement_v

    closed spec fn wf(self) -> bool {
        &&& self.state@.instance_id() == self.instance@.id()
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

        // axiom_usize_obeys_hash_table_key_model isn't firing!?
        assume( obeys_key_model::<Key>() );

        Implementation{
            store: HashMapWithView::new(),
            state: Tracked(atomic_state),
            instance: Tracked(instance)
        }
    }

    fn kvstore_main(&mut self, mut api: ClientAPI)
    {
        let debug_print = true;
        loop
        invariant
            self.wf(),
            self.instance_id() == api.instance_id(),
        {
            let (req, req_shard) = api.receive_request(debug_print);
            let (reply, reply_shard) = self.handle(req, req_shard);
            api.send_reply(reply, reply_shard, true);
        }
    }
}

}
