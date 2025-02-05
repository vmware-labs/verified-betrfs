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
use crate::spec::MapSpec_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::implementation::ConcreteProgramModel_v::*;

verus!{

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    store: HashMapWithView<Key, Value>,
    state: Tracked<KVStoreTokenized::atomic_state>,
    instance: Tracked<KVStoreTokenized::Instance>,
}

impl Implementation {
    pub closed spec(checked) fn view_store_as_kmmap(self) -> TotalKMMap
     {
        TotalKMMap(Map::new(
                |k: Key| true,
                |k: Key| if self.store@.contains_key(k@) { Message::Define{value: self.store@[k@]} }
                         else { Message::empty() }))
    }

    // The View hos HashMapWithView isn't what we need.
    // Gotta transform Key -> Key (by way of the darn int from the HashMapWithView @ :v)
    // and Value -> Message.
    pub closed spec fn i_hashmap(store: Map<int, Value>) -> Map<Key, Message>
    {
        Map::new(
            |k: Key| true,
            |k: Key| if store.contains_key(k.0 as int) { Message::Define{value: store[k.0 as int] } }
                    else { Message::empty() }
        )
    }

    pub closed spec fn i(self) -> AtomicState {
        self.state@.value()
//         TODO deleteme
//         AtomicState{
//             store: MapSpec::State {
//                 kmmap: TotalKMMap(Self::i_hashmap(self.store@)),
//             }
//         }
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

                let ghost pre_state = self.state@.value();
                let ghost post_state = self.state@.value(); // noop!

                let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
                proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

                let ghost map_lbl = MapSpec::Label::Noop{input: req.input, output: reply.output};
                proof {
                    reveal(MapSpec::State::next);
                    reveal(MapSpec::State::next_by);
                    assert( MapSpec::State::next_by(post_state.history.last().appv, post_state.history.last().appv,
                            map_lbl, MapSpec::Step::noop())); // witness to step
                    assert( post_state.history.get_prefix(pre_state.history.len()) == pre_state.history );  // extn
                    assert( AtomicState::map_transition(pre_state, post_state, map_lbl) );
                }

                let tracked new_reply_token = self.instance.borrow().execute_transition(
                    KVStoreTokenized::Label::ExecuteOp{req, reply},
                    post_state,
                    map_lbl,
                    &mut atomic_state,
                    req_shard.get()
                );
                self.state = Tracked(atomic_state);

                (reply, Tracked(new_reply_token))
            },
            _ => unreached(),
        }
    }

    pub exec fn handle_put(&mut self, req: Request, req_shard: Tracked<KVStoreTokenized::requests>)
            -> (out: (Reply, Tracked<KVStoreTokenized::replies>))
    requires
        old(self).wf(),
        old(self).good_req(req, req_shard@),
        req.input is PutInput,
    ensures
        self.wf(),
        self.good_reply(*old(self), out.0, out.1@),
    {
        let out = match req.input {
        Input::PutInput{key, value} => {
            let ghost pre_state: AtomicState = self.i();
            self.store.insert(key, value);

            let reply = Reply{output: Output::PutOutput, id: req.id};

            let ghost store = MapSpec::State {
                kmmap: pre_state.mapspec().kmmap.insert(key, Message::Define{value})
            };

            // TODO(jonh): I find it sad that the implementation has to track the history
            // value. It'd be nice if the implementation could just take local valid steps,
            // and have a proof at a higher layer carry the ghost history along. But .i() makes
            // that difficult. Hmm.
            let ghost post_state = AtomicState {
                history: self.state@.value().history.append(seq![ PersistentState{appv: store} ]),
            };

            let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
            proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

            let ghost map_lbl = MapSpec::Label::Put{input: req.input, output: reply.output};
            proof {
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.mapspec(), post_state.mapspec(),
                        map_lbl, MapSpec::Step::put())); // witness to step
                assert( post_state.history.get_prefix(pre_state.history.len()) == pre_state.history );  // extn
                assert( AtomicState::map_transition(pre_state, post_state, map_lbl) );
            }

//             assert( pre_state == atomic_state.value() );
            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                map_lbl,
                &mut atomic_state,
                req_shard.get(),
            );
            self.state = Tracked(atomic_state);

            (reply, Tracked(new_reply_token))
        },
            _ => unreached(),
        };
        assert( self.i().mapspec().kmmap == self.view_store_as_kmmap() ); // trigger extn equality
//         assert( self.wf() );
        out
    }

    pub exec fn handle_query(&mut self, req: Request, req_shard: Tracked<KVStoreTokenized::requests>)
            -> (out: (Reply, Tracked<KVStoreTokenized::replies>))
    requires
        old(self).wf(),
        old(self).good_req(req, req_shard@),
        req.input is QueryInput,
    ensures
        self.wf(),
        self.good_reply(*old(self), out.0, out.1@),
    {
        match req.input {
        Input::QueryInput{key} => {
            let value = match self.store.get(&key) {
                Some(v) => *v,
                None => { Value(0) },
            };

            let ghost pre_state: AtomicState = self.i();
            let ghost post_state = pre_state;

            let reply = Reply{output: Output::QueryOutput{value: value}, id: req.id};

            let ghost post_state: AtomicState = self.i();
            let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
            proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

            let ghost map_lbl = MapSpec::Label::Query{input: req.input, output: reply.output};
            proof {
                assert( old(self).wf() );
                if pre_state.mapspec().kmmap.0.contains_key(key) {
                    assume( pre_state.mapspec().kmmap[key]->value == value );
                } else {
                    // TODO jonh left off here
//                     assert( old(self).store@ == old(self).i().store );

                    assert( !pre_state.mapspec().kmmap.0.contains_key(key) );
                    assert( !old(self).store@.contains_key(key@) );
                    assert( pre_state.mapspec().kmmap[key]->value == value );
                }
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.mapspec(), post_state.mapspec(),
                        map_lbl, MapSpec::Step::query())); // witness to step
                assert( post_state.history.get_prefix(pre_state.history.len()) == pre_state.history );  // extn
                assert( AtomicState::map_transition(pre_state, post_state, map_lbl) );
            }
            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                map_lbl,
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
    type Proof = ConcreteProgramModel;

    closed spec fn wf(self) -> bool {
        &&& self.state@.instance_id() == self.instance@.id()
        &&& self.i().mapspec().kmmap == self.view_store_as_kmmap()
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

        let selff = Implementation{
            store: HashMapWithView::new(),
            state: Tracked(atomic_state),
            instance: Tracked(instance)
        };
//         assert( selff.i() == selff.state@.value() );   // trigger extn equality
        assert( selff.i().mapspec().kmmap == selff.view_store_as_kmmap() ); // trigger extn equality
//         assert( selff.wf() );
        selff
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
