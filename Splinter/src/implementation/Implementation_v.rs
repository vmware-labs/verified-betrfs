// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;
use vstd::pervasive::*;
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
use crate::implementation::AtomicState_v::*;
use crate::implementation::MultisetMapRelation_v::*;
use crate::spec::FloatingSeq_t::*;

#[allow(unused_imports)]
use vstd::multiset::*;
#[allow(unused_imports)]
use vstd::tokens::*;
#[allow(unused_imports)]
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
#[allow(unused_imports)]
use crate::implementation::DiskLayout_v::*;

verus!{

pub closed spec(checked) fn view_store_as_kmmap(store: HashMapWithView<Key, Value>) -> TotalKMMap
{
    TotalKMMap(Map::new(
            |k: Key| true,
            |k: Key| if store@.contains_key(k@) { Message::Define{value: store@[k@]} }
                     else { Message::empty() }))
}

pub closed spec(checked) fn view_store_as_singleton_floating_seq(at_index: nat, store: HashMapWithView<Key, Value>) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index+1,
          |i| Version{ appv: MapSpec::State{ kmmap: view_store_as_kmmap(store) } } )
}

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
        view_store_as_kmmap(self.store)
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
    }

    closed spec fn inv(self) -> bool {
        &&& self.state@.instance_id() == self.instance@.id()
        &&& self.state@.value().recovery_state is RecoveryComplete
        &&& self.i().mapspec().kmmap == self.view_store_as_kmmap()
    }

    pub closed spec fn good_req(self, req: Request, req_shard: KVStoreTokenized::requests) -> bool
    {
        &&& self.inv()
        &&& req_shard.instance_id() == self.instance_id()
        &&& req_shard.element() == req
    }

    pub closed spec fn good_reply(self, pre: Self, reply: Reply, reply_shard: KVStoreTokenized::replies) -> bool
    {
        &&& self.inv()
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
        old(self).good_req(req, req_shard@),
        req.input is PutInput,
    ensures
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
                ..self.state@.value()
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
        old(self).good_req(req, req_shard@),
        req.input is QueryInput,
    ensures
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
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.mapspec(), post_state.mapspec(),
                        map_lbl, MapSpec::Step::query())); // witness to step
                assert( post_state.history.get_prefix(pre_state.history.len()) == pre_state.history );  // extn
//                 assert( AtomicState::map_transition(pre_state, post_state, map_lbl) );
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
    requires
        old(self).good_req(req, req_shard@),
    ensures
        self.good_reply(*old(self), out.0, out.1@),
    {
        match req.input {
            Input::NoopInput => self.handle_noop(req, req_shard),
            Input::PutInput{..} => self.handle_put(req, req_shard),
            Input::QueryInput{..} => self.handle_query(req, req_shard),
        }
    }

    fn recover(&mut self, api: &mut ClientAPI)
    requires
        old(self).wf_init(),
        old(self).instance_id() == old(api).instance_id()
    ensures
        self.inv(),
        self.instance_id() == api.instance_id()
    {
        {
            let ghost pre_state: AtomicState = self.i();
            let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
            proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

            let disk_req = IDiskRequest::ReadReq{from: superblock_addr() };
            let tracked empty_disk_responses = MultisetToken::empty(self.instance_id());

            let ghost post_state = AtomicState { recovery_state: RecoveryState::AwaitingSuperblock, ..pre_state };

            let req_id_perm = Tracked( api.send_disk_request_predict_id() );

            let ghost disk_event_lbl = DiskEventLabel::InitiateRecovery{};
            let ghost disk_lbl = AsyncDisk::Label::DiskOps{
                        requests: Map::empty().insert(req_id_perm@, disk_req@),
                        responses: Map::empty()
                    };
            let ghost disk_req_id = req_id_perm@;
            let ghost disk_response_tuples = Multiset::empty();

            let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
            proof { multiset_map_singleton_ensures(req_id_perm@, disk_req@); }

//             assert( disk_response_tuples <= empty_disk_responses.multiset() );
//             assert( empty_disk_responses.instance_id() == self.instance@.id() );
            assert( disk_lbl->responses == multiset_to_map(disk_response_tuples) ); // extn equality
//             assert( AtomicState::disk_transition(
//                 atomic_state.value(), post_state, disk_event_lbl, disk_lbl, disk_req_id) );
            // I needed an awful lot of tedious debugging-in-the-dark to figure out which
            // VerusSync require clause I'd violated. :v(
//             assert( disk_lbl->requests == multiset_to_map(disk_request_tuples) );
            let tracked disk_request_tokens = self.instance.borrow().disk_transition(
                KVStoreTokenized::Label::DiskOp{
                    disk_event_lbl,
                    disk_request_tuples,
                    disk_response_tuples,
                    disk_lbl,
                    disk_req_id,
                },
                post_state,
                &mut atomic_state,
                empty_disk_responses,
            );
            assert( atomic_state.value() == post_state );

            let disk_req_id = api.send_disk_request(disk_req, req_id_perm, Tracked(disk_request_tokens));
            self.state = Tracked(atomic_state);
        }

        ////////////////////////////////////////
        assert( self.state@.value().recovery_state is AwaitingSuperblock );
        ////////////////////////////////////////

        {
            let ghost pre_state: AtomicState = self.i();
            let tracked mut atomic_state = KVStoreTokenized::atomic_state::arbitrary();
            proof { tracked_swap(self.state.borrow_mut(), &mut atomic_state); }

            let disk_resp = IDiskRequest::ReadReq{from: superblock_addr() };
            let (disk_req_id, i_disk_response, disk_response_token) = api.receive_disk_response();
            let (from,raw_page) = match i_disk_response {
                IDiskResponse::ReadResp{from, data} => (from,data),
                IDiskResponse::WriteResp{to} => {
                    // TODO This assert-false should be an assumption we pull down from the system:
                    // whenever state is AwaitingSuperblock, the only possible responses in the
                    // disk bus buffer are ReadResps.
                    assume(false);
                    unreached()
                }
            };
            // TODO likewise, by system-level invariant, the from address in the response can only
            // be the superblock addr. (Although this we should fix by removing addresses from disk
            // responses.)
            assume( from@ == spec_superblock_addr() );

            let superblock = unmarshall(raw_page);
            let ghost post_state = AtomicState {
                recovery_state: RecoveryState::RecoveryComplete,
                history: view_store_as_singleton_floating_seq(superblock.version_index, superblock.store),
                in_flight_version: None,
                persistent_version: superblock.version_index,
            };

            let ghost disk_response_tuples = multiset_map_singleton(disk_req_id, i_disk_response@);
            proof { multiset_map_singleton_ensures(disk_req_id, i_disk_response@); }

            let ghost disk_event_lbl = DiskEventLabel::CompleteRecovery{raw_page};
            let ghost disk_lbl = AsyncDisk::Label::DiskOps{
                        requests: Map::empty(),
                        responses: Map::empty().insert(disk_req_id, i_disk_response@),
                    };
            let ghost disk_request_tuples = Multiset::empty();

            // extn; why isn't it triggered by requires in macro output?
            // (Might also make a nice broadcast lemma, if that was usable.)
            assert( disk_lbl->requests == multiset_to_map(disk_request_tuples) );

            let tracked disk_request_tokens = self.instance.borrow().disk_transition(
                KVStoreTokenized::Label::DiskOp{
                    disk_event_lbl,
                    disk_request_tuples,
                    disk_response_tuples,
                    disk_lbl,
                    disk_req_id,
                },
                post_state,
                &mut atomic_state,
                disk_response_token.get(),
            );

            self.state = Tracked(atomic_state);
        }

        assert( self.state@.value().recovery_state is RecoveryComplete );

        assert( self.i().mapspec().kmmap == self.view_store_as_kmmap() );
        assert( self.inv() );
    }
}

impl KVStoreTrait for Implementation {
    type Proof = ConcreteProgramModel;

    closed spec fn wf_init(self) -> bool {
        &&& self.state@.instance_id() == self.instance@.id()
        &&& self.state@.value().recovery_state is Begin
    }

    closed spec fn instance_id(self) -> InstanceId
    {
        self.instance@.id()
    }

    fn new() -> (out: Self)
        ensures out.wf_init()
    {
        let tracked (
            Tracked(instance),
            Tracked(atomic_state),  // non sharded state
            Tracked(requests),      // request perm map (multiset), empty
            Tracked(replies),       // reply perm map (multiset), empty
            Tracked(sync_requests), // sync req map (multiset), empty
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize();

        // verus/source/vstd/std_specs/hash.rs says the best we can do right now is assume this.
        assume( obeys_key_model::<Key>() );

        let selff = Implementation{
            store: HashMapWithView::new(),
            state: Tracked(atomic_state),
            instance: Tracked(instance)
        };
//         assert( selff.i() == selff.state@.value() );   // trigger extn equality
//         assert( selff.i().mapspec().kmmap == selff.view_store_as_kmmap() ); // trigger extn equality
//         assert( selff.wf() );
        selff
    }

    fn kvstore_main(&mut self, mut api: ClientAPI)
    {
        self.recover(&mut api);

        let debug_print = true;
        loop
        invariant
            self.inv(),
            self.state@.value().recovery_state is RecoveryComplete,
            self.instance_id() == api.instance_id(),
        {
            let (req, req_shard) = api.receive_request(debug_print);
            let (reply, reply_shard) = self.handle(req, req_shard);
            api.send_reply(reply, reply_shard, true);
        }
    }
}

}
