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
use crate::trusted::KVStoreTokenized_t::*;
use crate::trusted::ProgramModelTrait_t::*;

use crate::spec::MapSpec_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::implementation::ModelRefinement_v::*;
use crate::implementation::ConcreteProgramModel_v::*;
use crate::implementation::AtomicState_v::*;
use crate::implementation::MultisetMapRelation_v::*;

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

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    store: HashMapWithView<Key, Value>,
    model: Tracked<KVStoreTokenized::model<ConcreteProgramModel>>,
    instance: Tracked<KVStoreTokenized::Instance<ConcreteProgramModel>>,
}

pub type RequestShard = KVStoreTokenized::requests<ConcreteProgramModel>;
pub type ReplyShard =  KVStoreTokenized::replies<ConcreteProgramModel>;

pub type DiskRespShard = KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>;
pub type DiskReqShard =  KVStoreTokenized::disk_requests_multiset<ConcreteProgramModel>;

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
        self.model@.value().state
    }

    closed spec fn inv(self) -> bool {
        &&& self.model@.instance_id() == self.instance@.id()
        &&& self.model@.value().state.recovery_state is RecoveryComplete
        &&& self.i().mapspec().kmmap == self.view_store_as_kmmap()
    }

    pub closed spec fn good_req(self, req: Request, req_shard: RequestShard) -> bool
    {
        &&& self.inv()
        &&& req_shard.instance_id() == self.instance_id()
        &&& req_shard.element() == req
    }

    pub closed spec fn good_reply(self, pre: Self, reply: Reply, reply_shard: ReplyShard) -> bool
    {
        &&& self.inv()
        &&& self.instance_id() == pre.instance_id()
        &&& reply_shard.instance_id() == self.instance_id()
        &&& reply_shard.element() == reply
    }

    pub exec fn handle_noop(&mut self, req: Request, req_shard: Tracked<RequestShard>)
            -> (out: (Reply, Tracked<ReplyShard>))
    requires old(self).good_req(req, req_shard@),
        req.input is NoopInput,
    ensures self.good_reply(*old(self), out.0, out.1@),
    {
        match req.input {
            Input::NoopInput => {
                let reply = Reply{output: Output::NoopOutput, id: req.id};

                let ghost pre_state = self.model@.value();
                let ghost post_state = self.model@.value(); // noop!

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                proof {
                    let ghost map_lbl = MapSpec::Label::Noop{input: req.input, output: reply.output};
                    reveal(MapSpec::State::next);
                    reveal(MapSpec::State::next_by);
                    assert( MapSpec::State::next_by(post_state.state.history.last().appv, post_state.state.history.last().appv,
                            map_lbl, MapSpec::Step::noop())); // witness to step
                    assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
                    assert( AtomicState::map_transition(pre_state.state, post_state.state, req, reply) );
                    assert( ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::UserIO{op: ProgramUserOp::Execute{req, reply}}) );
                }

                let tracked new_reply_token = self.instance.borrow().execute_transition(
                    KVStoreTokenized::Label::ExecuteOp{req, reply},
                    post_state,
                    &mut model,
                    req_shard.get()
                );
                self.model = Tracked(model);

                (reply, Tracked(new_reply_token))
            },
            _ => unreached(),
        }
    }

    pub exec fn handle_put(&mut self, req: Request, req_shard: Tracked<RequestShard>)
            -> (out: (Reply, Tracked<ReplyShard>))
    requires
        old(self).good_req(req, req_shard@),
        req.input is PutInput,
    ensures
        self.good_reply(*old(self), out.0, out.1@),
    {
        let out = match req.input {
        Input::PutInput{key, value} => {
            let ghost pre_state = self.model@.value();
            self.store.insert(key, value);

            let reply = Reply{output: Output::PutOutput, id: req.id};

            let ghost store = MapSpec::State {
                kmmap: pre_state.state.mapspec().kmmap.insert(key, Message::Define{value})
            };

            // TODO(jonh): I find it sad that the implementation has to track the history
            // value. It'd be nice if the implementation could just take local valid steps,
            // and have a proof at a higher layer carry the ghost history along. But .i() makes
            // that difficult. Hmm.
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                history: self.model@.value().state.history.append(seq![ PersistentState{appv: store} ]),
                ..self.model@.value().state
            }};

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            proof {
                let ghost map_lbl = MapSpec::Label::Put{input: req.input, output: reply.output};
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.state.mapspec(), post_state.state.mapspec(),
                        map_lbl, MapSpec::Step::put())); // witness to step
                assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
                assert( AtomicState::map_transition(pre_state.state, post_state.state, req, reply) );
                assert( ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::UserIO{op: ProgramUserOp::Execute{req, reply}}) );
            }

//             assert( pre_state == model.value() );
            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut model,
                req_shard.get(),
            );
            self.model = Tracked(model);

            (reply, Tracked(new_reply_token))
        },
            _ => unreached(),
        };
        assert( self.i().mapspec().kmmap == self.view_store_as_kmmap() ); // trigger extn equality
//         assert( self.wf() );
        out
    }

    proof fn cannot_receive_write_response_during_recovery(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.i().recovery_state is AwaitingSuperblock,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
        i_disk_response is WriteResp,
    ensures
        false,
    {
        open_system_invariant::<Self>(self.model, disk_response_token);
        multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
        assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
        
        // assert(full_model.program.state.recovery_state is AwaitingSuperblock);
        // assert(full_model.inv());
        // assert(full_model.no_writes_till_recovery_complete());
        // assert(full_model.disk.responses.contains_key(disk_req_id));

        // assert(!(full_model.disk.responses[disk_req_id] is WriteResp));
        // forall |id| #[trigger] self.disk.responses.contains_key(id) ==> !(self.disk.responses[id] is WriteResp)

        // TODO This assert-false should be an assumption we pull down from the system:
        // whenever model is AwaitingSuperblock, the only possible responses in the
        // disk bus buffer are ReadResps.
        // assume( false );
    }

    pub exec fn handle_query(&mut self, req: Request, req_shard: Tracked<RequestShard>)
            -> (out: (Reply, Tracked<ReplyShard>))
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

            let ghost pre_state = self.model@.value();
            let ghost post_state = pre_state;

            let reply = Reply{output: Output::QueryOutput{value: value}, id: req.id};

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            proof {
                let ghost map_lbl = MapSpec::Label::Query{input: req.input, output: reply.output};
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.state.mapspec(), post_state.state.mapspec(),
                        map_lbl, MapSpec::Step::query())); // witness to step
                assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
//                 assert( AtomicState::map_transition(pre_state, post_state, map_lbl) );
                assert( ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::UserIO{op: ProgramUserOp::Execute{req, reply}}) );
            }

            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut model,
                req_shard.get(),
            );
            self.model = Tracked(model);

            (reply, Tracked(new_reply_token))
        },
            _ => unreached(),
        }
    }

    pub exec fn handle(&mut self, req: Request, req_shard: Tracked<RequestShard>)
            -> (out: (Reply, Tracked<ReplyShard>))
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

    fn recover(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).wf_init(),
        old(self).instance_id() == old(api).instance_id()
    ensures
        self.inv(),
        self.instance_id() == api.instance_id()
    {
        { // braces to scope variables used in this step
            let ghost pre_state = self.model@.value();
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let disk_req = IDiskRequest::ReadReq{from: superblock_addr() };
            let tracked empty_disk_responses = MultisetToken::empty(self.instance_id());

            let ghost post_state = ConcreteProgramModel{state: AtomicState { recovery_state: RecoveryState::AwaitingSuperblock, ..pre_state.state }};

            let req_id_perm = Tracked( api.send_disk_request_predict_id() );

            let ghost disk_event = DiskEvent::InitiateRecovery{req_id: req_id_perm@};
            // let ghost disk_req_id = req_id_perm@;
            let ghost disk_response_tuples = Multiset::empty();
            let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
            // proof { multiset_map_singleton_ensures(req_id_perm@, disk_req@); }
            proof {
                let info = ProgramDiskInfo{
                    reqs: disk_request_tuples, 
                    resps: disk_response_tuples, 
                };
                assert(AtomicState::disk_transition(
                    pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
                assert(ConcreteProgramModel::valid_disk_transition(pre_state, post_state, info));
                assert(ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::DiskIO{info}));
            }

            let tracked disk_request_tokens = self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp{
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                empty_disk_responses,
            );

            assert( model.value() == post_state );

            // this way of composition feels like it can be easily cheated?
            // if we really want to we can try to 
            // let ghost disk_lbl = AsyncDisk::Label::DiskOps{
            //         requests: Map::empty().insert(req_id_perm@, disk_req@),
            //         responses: Map::empty()
            // };
            // assert( disk_lbl->responses == multiset_to_map(disk_response_tuples) ); // extn equality

            // this models external_diskop with the disk label  
            let disk_req_id = api.send_disk_request(disk_req, req_id_perm, Tracked(disk_request_tokens));
            self.model = Tracked(model);
        }

        ////////////////////////////////////////
        assert( self.model@.value().state.recovery_state is AwaitingSuperblock );
        ////////////////////////////////////////
        { // braces to scope variables used in this step
            let ghost pre_state = self.model@.value();
            let disk_resp = IDiskRequest::ReadReq{from: superblock_addr() };
            let (disk_req_id, i_disk_response, disk_response_token) = api.receive_disk_response();
            let raw_page = match i_disk_response {
                IDiskResponse::ReadResp{data} => data,
                IDiskResponse::WriteResp{} => {
                    proof { self.cannot_receive_write_response_during_recovery(disk_req_id, i_disk_response, disk_response_token); };
                    unreached()
                }
            };

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let superblock = unmarshall(raw_page);
            // Record our learnings in the physical model.
            self.store = superblock.store;

            // Compute the next ghost model and transition our token
            let ghost post_state = ConcreteProgramModel{state: AtomicState {
                recovery_state: RecoveryState::RecoveryComplete,
                history: view_store_as_singleton_floating_seq(superblock.version_index, superblock.store),
                in_flight: None,
                persistent_version: superblock.version_index,
                sync_req_map: Map::empty(),
            }};

            let ghost disk_response_tuples = multiset_map_singleton(disk_req_id, i_disk_response@);
            // proof { multiset_map_singleton_ensures(disk_req_id, i_disk_response@); }

            let ghost disk_event = DiskEvent::CompleteRecovery{req_id: disk_req_id, raw_page: raw_page};
            // let ghost disk_lbl = AsyncDisk::Label::DiskOps{
            //             requests: Map::empty(),
            //             responses: Map::empty().insert(disk_req_id, i_disk_response@),
            //         };
            let ghost disk_request_tuples = Multiset::empty();

            // extn; why isn't it triggered by requires in macro output?
            // (Might also make a nice broadcast lemma, if that was usable.)
            // assert( disk_lbl->requests == multiset_to_map(disk_request_tuples) );   // extn
            proof {
                let info = ProgramDiskInfo{
                    reqs: disk_request_tuples, 
                    resps: disk_response_tuples, 
                };
                // TODO: this is crazy, I have to use info.reqs otherwise it doesn't match for 
                // valid disk transition
                assert(AtomicState::disk_transition(
                    pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
                assert(ConcreteProgramModel::valid_disk_transition(pre_state, post_state, info));
                assert(ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::DiskIO{info}));
            }

            let tracked disk_request_tokens = self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp{
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                disk_response_token.get(),
            );
            self.model = Tracked(model);
        }
    }
}

impl KVStoreTrait for Implementation {
    type ProgramModel = ConcreteProgramModel; 
    type Proof = RefinementProof;

    closed spec fn wf_init(self) -> bool {
        &&& self.model@.instance_id() == self.instance@.id()
        &&& self.model@.value().state.recovery_state is Begin
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
            Tracked(model),         // non sharded model
            Tracked(requests),      // request perm map (multiset), empty
            Tracked(replies),       // reply perm map (multiset), empty
            Tracked(sync_requests), // sync req map (multiset), empty
            Tracked(sync_replies),  // sync reply map (multiset), empty
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(ConcreteProgramModel{state: AtomicState::init()});

        // verus/source/vstd/std_specs/hash.rs says the best we can do right now is assume this.
        assume( obeys_key_model::<Key>() );

        let selff = Implementation{
            store: HashMapWithView::new(),
            model: Tracked(model),
            instance: Tracked(instance)
        };
//         assert( selff.i() == selff.model@.value() );   // trigger extn equality
//         assert( selff.i().mapspec().kmmap == selff.view_store_as_kmmap() ); // trigger extn equality
//         assert( selff.wf() );
        selff
    }

    fn kvstore_main(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        // self.recover(&mut api);

        // let debug_print = true;
        // loop
        // invariant
        //     self.inv(),
        //     self.model@.value().recovery_state is RecoveryComplete,
        //     self.instance_id() == api.instance_id(),
        // {
        //     let (req, req_shard) = api.receive_request(debug_print);
        //     let (reply, reply_shard) = self.handle(req, req_shard);
        //     api.send_reply(reply, reply_shard, true);
        // }
    }
}

}
