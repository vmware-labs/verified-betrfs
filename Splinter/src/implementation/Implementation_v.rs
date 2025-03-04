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
use crate::trusted::ReqReply_t::*;
use crate::trusted::KVStoreTrait_t::*;
use crate::trusted::KVStoreTokenized_t::*;
use crate::trusted::ProgramModelTrait_t::*;

use crate::spec::MapSpec_t::{ID, MapSpec, PersistentState};
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

pub closed spec fn good_req(instance_id: InstanceId, req: Request, req_shard: RequestShard) -> bool
{
    &&& req_shard.instance_id() == instance_id
    &&& req_shard.element() == req
}

// requests that can be satisfied when this superblock lands
// TODO(jonh): in sync_request: need to consume request shard to get
// atomic state; then just store atomic state ids here.
// That also suggests we will have version numbers handy, which will
// further simplify this data structure.
struct SyncRequestBuffer {
    satisfied_reqs: Vec<Request>,
    deferred_reqs: Vec<Request>,
}

impl SyncRequestBuffer {
    closed spec fn wf(self, instance_id: InstanceId) -> bool
    {
        &&& forall |r| #![auto] self.satisfied_reqs@.contains(r) ==> {
            &&& r.input is SyncInput
        }
        &&& forall |r| #![auto] self.deferred_reqs@.contains(r) ==> {
            &&& r.input is SyncInput
        }
    }

    fn new_empty() -> (out: Self)
    ensures
        !out.in_flight(),
        out.deferred_reqs@.len() == 0,
    {
        SyncRequestBuffer{ satisfied_reqs: vec![], deferred_reqs: vec![] }
    }

    closed spec fn in_flight(self) -> bool {
        &&& self.satisfied_reqs.len() > 0
    }

    fn exec_in_flight(&self) -> (out: bool)
    ensures self.in_flight() == out
    {
        &&& self.satisfied_reqs.len() > 0
    }
}

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    store: HashMapWithView<Key, Value>,
    model: Tracked<KVStoreTokenized::model<ConcreteProgramModel>>,
    instance: Tracked<KVStoreTokenized::Instance<ConcreteProgramModel>>,

    sync_requests: SyncRequestBuffer,
}

pub type RequestShard = KVStoreTokenized::requests<ConcreteProgramModel>;
pub type ReplyShard = KVStoreTokenized::replies<ConcreteProgramModel>;

pub type DiskRespShard = KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>;
pub type DiskReqShard = KVStoreTokenized::disk_requests_multiset<ConcreteProgramModel>;

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

    closed spec fn state(&self) -> AtomicState
    {
        self.model@.value().state
    }

    closed spec fn inv(self) -> bool {
        let state = self.state();

        &&& self.model@.instance_id() == self.instance@.id()
        &&& state.recovery_state is RecoveryComplete
        &&& self.i().mapspec().kmmap == self.view_store_as_kmmap()
        &&& (state.in_flight is Some
            <==> self.sync_requests.in_flight())
        &&& self.sync_requests.wf(self.instance@.id())

        &&& (state.in_flight is Some ==> {
            // The in-flight version stays active so get_suffix doesn't choke on it when it's time
            // to handle the disk response
            &&& state.history.is_active(state.in_flight.get_Some_0().version as int)
            // The in-flight 'satisfied requests' can indeed be satisfied by the in-flight version
            &&& self.sync_reqs_in_version(self.sync_requests.satisfied_reqs@, state.in_flight.get_Some_0().version as int)
        })
    }

    pub closed spec fn good_req(self, req: Request, req_shard: RequestShard) -> bool
    {
        good_req(self.instance_id(), req, req_shard)
    }

    // `api` should really just be part of the state, and this property maintained in inv, except
    // that we have a construction order mess between constructing the instancea and model and then
    // getting an api from the trusted main. Probably should expose a builder pattern.
    pub closed spec fn inv_api(self, api: &ClientAPI<ConcreteProgramModel>) -> bool
    {
        &&& self.inv()
        &&& api.instance_id() == self.instance_id()
    }

    pub closed spec fn good_disk_response(self, id: ID, disk_response: IDiskResponse, response_shard: DiskRespShard) -> bool
    {
        &&& response_shard.instance_id() == self.instance_id()
        &&& response_shard.multiset() == multiset_map_singleton(id, disk_response)
    }

    pub exec fn handle_noop(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is NoopInput,
    ensures
        self.inv_api(api),
    {
        match req.input {
            Input::NoopInput => {
                let reply = Reply{output: Output::NoopOutput, id: req.id};

                let ghost pre_state = self.model@.value();
                let ghost post_state = self.model@.value(); // noop!

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                proof {
                    let map_req = req.mapspec_req();
                    let map_reply = reply.mapspec_reply();
                    let ghost map_lbl = MapSpec::Label::Noop{input: map_req.input, output: map_reply.output};
                    reveal(MapSpec::State::next);
                    reveal(MapSpec::State::next_by);
                    assert( MapSpec::State::next_by(post_state.state.history.last().appv, post_state.state.history.last().appv,
                            map_lbl, MapSpec::Step::noop())); // witness to step
                    assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
                    assert( AtomicState::map_transition(pre_state.state, post_state.state, map_req, map_reply) );
                    assert( ConcreteProgramModel::next(pre_state, post_state, 
                        ProgramLabel::UserIO{op: ProgramUserOp::Execute{req: map_req, reply: map_reply}}) );
                }

                let tracked new_reply_token = self.instance.borrow().execute_transition(
                    KVStoreTokenized::Label::ExecuteOp{req, reply},
                    post_state,
                    &mut model,
                    req_shard.get()
                );
                self.model = Tracked(model);

                api.send_reply(reply, Tracked(new_reply_token), true);
            },
            _ => unreached(),
        }
    }

    pub exec fn handle_put(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is PutInput,
    ensures
        self.inv_api(api),
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
                let map_req = req.mapspec_req();
                let map_reply = reply.mapspec_reply();
                let ghost map_lbl = MapSpec::Label::Put{input: map_req.input, output: map_reply.output};
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.state.mapspec(), post_state.state.mapspec(),
                        map_lbl, MapSpec::Step::put())); // witness to step
                assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
                assert( AtomicState::map_transition(pre_state.state, post_state.state, map_req, map_reply) );
                assert( ConcreteProgramModel::next(pre_state, post_state, 
                    ProgramLabel::UserIO{op: ProgramUserOp::Execute{req: map_req, reply: map_reply}}) );
            }

//             assert( pre_state == model.value() );
            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut model,
                req_shard.get(),
            );
            self.model = Tracked(model);

            assert( self.i().mapspec().kmmap == self.view_store_as_kmmap() ); // trigger extn equality
            api.send_reply(reply, Tracked(new_reply_token), true);
        },
            _ => unreached(),
        };
    }

    proof fn system_inv_cannot_receive_write_response_during_recovery(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.i().recovery_state is AwaitingSuperblock,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
        i_disk_response is WriteResp,
    ensures
        false,
    {
        open_system_invariant::<ConcreteProgramModel, RefinementProof>(self.model, disk_response_token);
        multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
        assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
    }

    pub exec fn handle_query(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is QueryInput,
    ensures
        self.inv_api(api),
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
                let map_req = req.mapspec_req();
                let map_reply = reply.mapspec_reply();
                let ghost map_lbl = MapSpec::Label::Query{input: map_req.input, output: map_reply.output};
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.state.mapspec(), post_state.state.mapspec(),
                        map_lbl, MapSpec::Step::query())); // witness to step
                assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
//                 assert( AtomicState::map_transition(pre_state, post_state, map_lbl) );
                assert( ConcreteProgramModel::next(pre_state, post_state, 
                    ProgramLabel::UserIO{op: ProgramUserOp::Execute{req: map_req, reply: map_reply}}) );
            }

            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut model,
                req_shard.get(),
            );
            self.model = Tracked(model);

            api.send_reply(reply, Tracked(new_reply_token), true);
        },
            _ => unreached(),
        }
    }

    pub exec fn handle_sync_request(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is SyncInput,
    ensures
        self.inv_api(api),
    {
        // Consume the shard to convert into model state
        let ghost pre_state = self.model@.value();
        let ghost version = (pre_state.state.history.len()-1) as nat;
        let ghost post_state = ConcreteProgramModel {
            state: AtomicState{
                sync_req_map: pre_state.state.sync_req_map.insert(req.id, version),
                ..pre_state.state}
        };

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        let tracked new_reply_token = self.instance.borrow().accept_sync_request(
            KVStoreTokenized::Label::RequestSyncOp{sync_req_id: req.id},
            post_state,
            &mut model,
            req_shard.get(),
        );
        self.model = Tracked(model);

        self.sync_requests.deferred_reqs.push(req);

        // trigger prior inv, element by element
        assert forall |r| #![auto] self.sync_requests.deferred_reqs@.contains(r) implies r.input is SyncInput by {
            if r != req { assert( old(self).sync_requests.deferred_reqs@.contains(r) ); }
        }

        // We didn't change the satisfied requests!
        assert( self.sync_reqs_in_version(self.sync_requests.satisfied_reqs@, self.state().in_flight.get_Some_0().version as int) ) by {
            let reqs = self.sync_requests.satisfied_reqs@;
            let version_num = self.state().in_flight.get_Some_0().version as int;
            assert forall |i| #![auto] 0<=i<reqs.len() implies self.sync_req_in_version(reqs[i].id, version_num) by {
                assert( reqs[i].id != req.id ) by {
                    assume( false );    // apply auditor promise about unique ids and maybe a system invariant?
                }
            }
        }

        self.maybe_launch_superblock(api);
    }

    pub exec fn maybe_launch_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
    ensures
        self.inv_api(api),
    {
        if self.sync_requests.deferred_reqs.len() == 0 {
            // nobody is waiting for a superblock send.
        } else if self.sync_requests.satisfied_reqs.len() == 0 {
            self.send_superblock(api);
        } else {
            // Someone is waiting to start a sync, but a superblock is already in-flight; we'll
            // consider this again when the disk response lands back here.
        }
    }

    pub exec fn send_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
    ensures
        self.inv_api(api),
    {
        assume(false);  // TODO missing code here
    }

    exec fn deliver_inflight_replies(&mut self, ready_reqs: &mut Vec<Request>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).sync_reqs_in_version(old(ready_reqs)@, old(self).state().history.first_active_index()),
        // can't break in-flight inv because there aren't any satisfied_reqs during this call
        old(self).sync_requests.satisfied_reqs@.len()==0,
    ensures
        self.inv_api(api),
    {
        loop
        invariant
            self.inv_api(api),
            self.sync_reqs_in_version(ready_reqs@, self.state().history.first_active_index()),
            self.sync_requests.satisfied_reqs@.len()==0,
        {
            match ready_reqs.pop()
            {
                Some(req) => { self.send_sync_response(req, api) },
                None => break,
            }
        }
    }

    closed spec fn sync_reqs_in_version(&self, reqs: Seq<Request>, version_num: int) -> bool
    {
        &&& forall |i| #![auto] 0<=i<reqs.len() ==> {
            &&& reqs[i].input is SyncInput
            &&& self.sync_req_in_version(reqs[i].id, version_num)
        }
        &&& forall |i,j| #![auto] 0 <= i < reqs.len() && 0 <= j < reqs.len() && i!=j ==> reqs[i].id != reqs[j].id
    }

    closed spec fn sync_req_in_version(&self, id: ID, version_num: int) -> bool
    {
        self.state().sync_req_map[id] <= version_num
    }

    closed spec fn no_matching_sync_req_id(self, id: ID) -> bool
    {
        forall |j| #![auto] 0<=j<self.sync_requests.satisfied_reqs@.len() ==> self.sync_requests.satisfied_reqs@[j].id!=id
    }

    exec fn send_sync_response(&mut self, req: Request, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        req.input is SyncInput,
        old(self).sync_req_in_version(req.id, old(self).state().history.first_active_index()),
        old(self).no_matching_sync_req_id(req.id),
    ensures
        self.inv_api(api),
//         self.store == old(self).store,
//         self.sync_requests == old(self).sync_requests,
        (self.state() == AtomicState{
            sync_req_map: old(self).state().sync_req_map.remove(req.id),
            ..old(self).state()
        }),
    {
        // Convert the model state back into a shard
        let ghost pre_state = self.model@.value();

//         proof {
// //             assert( pre_state.state.sync_req_map[req.id] <= pre_state.state.history.first_active_index() );
//         }

        let ghost post_state = ConcreteProgramModel {
            state: AtomicState{
                sync_req_map: pre_state.state.sync_req_map.remove(req.id),
                ..pre_state.state}
        };

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        let tracked reply_shard = self.instance.borrow().deliver_sync_reply(
            KVStoreTokenized::Label::ReplySyncOp{sync_req_id: req.id},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);

        let reply = Reply{output: Output::SyncOutput, id: req.id};

        api.send_reply(reply, Tracked(reply_shard), true);

        proof {
            let reqs = self.sync_requests.satisfied_reqs@;
            let version_num = self.state().in_flight.get_Some_0().version as int;

            assert forall |i| #![auto] 0<=i<reqs.len() implies {
                &&& self.sync_req_in_version(reqs[i].id, version_num)
            } by {
                if reqs[i].id == req.id {
                    assert( self.sync_req_in_version(reqs[i].id, version_num) );
                } else {
                    assert( self.sync_req_in_version(reqs[i].id, version_num) );
                }
            }
        }

        assert( self.sync_reqs_in_version(self.sync_requests.satisfied_reqs@, self.state().in_flight.get_Some_0().version as int) );
    }

    pub exec fn handle_user_request(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
    ensures
        self.inv_api(api),
    {
        match req.input {
            Input::NoopInput => self.handle_noop(req, req_shard, api),
            Input::PutInput{..} => self.handle_put(req, req_shard, api),
            Input::QueryInput{..} => self.handle_query(req, req_shard, api),
            Input::SyncInput{} =>  self.handle_sync_request(req, req_shard, api),
        }
    }

    proof fn system_inv_response_implies_in_flight(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.i().recovery_state is RecoveryComplete,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
    ensures
        i_disk_response is WriteResp,   // when RecoveryComplete, we never read again
        self.i().in_flight is Some,
        self.i().in_flight->0.req_id == disk_req_id,
    {
        open_system_invariant::<ConcreteProgramModel, RefinementProof>(self.model, disk_response_token);
        multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
        assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
    }

    pub exec fn handle_disk_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
    ensures
        self.inv_api(api),
    {
        let mut ready_reqs = vec![];
        std::mem::swap(&mut self.sync_requests.satisfied_reqs, &mut ready_reqs);
//         (ready_reqs,self.sync_requests.satisfied_reqs) = (self.sync_requests.satisfied_reqs,ready_reqs);

        // take a tokenized transition to mark disk response receipt

        // we just took out all the in-flights; need to simultaneously change model.value().state to
        // restore self.inv
        // TODO(jialin): why do these Noop requests have ids? :v/
        let ghost req = Request{input: Input::NoopInput, id: 0};
        let reply = Reply{output: Output::NoopOutput, id: 0};

        let ghost pre_state = self.model@.value();
        let ghost new_persistent_version = pre_state.state.in_flight.get_Some_0().version;
        let ghost post_state = ConcreteProgramModel{ state: AtomicState{
            in_flight: None,
            history: pre_state.state.history.get_suffix(new_persistent_version as int),
            persistent_version: new_persistent_version,
            ..pre_state.state
        }};

        proof {
            // Learn this before we yoink model out of self
            assert( self.i().recovery_state is RecoveryComplete );
            self.system_inv_response_implies_in_flight(id, disk_response, response_shard);
        }

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        proof {
            let info = ProgramDiskInfo{ reqs: Multiset::empty(), resps: response_shard@.multiset() };
            let disk_event = DiskEvent::ExecuteSyncEnd{};

            assert( response_shard@.multiset() == Multiset::singleton((pre_state.state.in_flight.get_Some_0().req_id, DiskResponse::WriteResp{})) );    // extn

            assert( AtomicState::disk_transition(
                pre_state.state, post_state.state, disk_event, info.reqs, info.resps) );    // witness
//             assert( ConcreteProgramModel::next(pre_state, post_state, 
//                     ProgramLabel::DiskIO{ info }) );
        }

        let tracked empty_disk_requests:KVStoreTokenized::disk_requests_multiset<ConcreteProgramModel>
            = KVStoreTokenized::disk_requests_multiset::empty(self.instance_id());
        let tracked new_reply_token = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp{
                disk_request_tuples: empty_disk_requests.multiset(),
                disk_response_tuples: response_shard@.multiset()},
            post_state,
            &mut model,
            response_shard.get(),
        );
        self.model = Tracked(model);

        self.deliver_inflight_replies(&mut ready_reqs, api);

        // maybe launch another superblock
        self.maybe_launch_superblock(api);
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
                    proof { self.system_inv_cannot_receive_write_response_during_recovery(disk_req_id, i_disk_response, disk_response_token); };
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
//                 open_system_invariant::<Self>(self.model, disk_response_token);
                multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
                assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
                                                                                           //
                // assert( valid_checksum(raw_page) );
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
        &&& !self.sync_requests.in_flight()
        &&& self.sync_requests.deferred_reqs@.len() == 0
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
            Tracked(replies),       // reply perm map (multiset), empty\
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(ConcreteProgramModel{state: AtomicState::init()});

        // verus/source/vstd/std_specs/hash.rs says this is the best we can do right now
        assume( obeys_key_model::<Key>() );

        let selff = Implementation{
            store: HashMapWithView::new(),
            model: Tracked(model),
            instance: Tracked(instance),
            sync_requests: SyncRequestBuffer::new_empty(),
        };
//         assert( selff.i() == selff.model@.value() );   // trigger extn equality
//         assert( selff.i().mapspec().kmmap == selff.view_store_as_kmmap() ); // trigger extn equality
        selff
    }

    fn kvstore_main(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        self.recover(&mut api);

        let debug_print = true;
        loop
        invariant
            self.inv_api(&api),
            self.model@.value().state.recovery_state is RecoveryComplete,
        {
            let poll_result = api.poll();
            if poll_result.disk_response_ready {
                let (id, disk_response, response_shard) = api.receive_disk_response();
                self.handle_disk_response(id, disk_response, response_shard, &mut api);
            }
            if poll_result.user_input_ready {
                let (req, req_shard) = api.receive_request(debug_print);
                self.handle_user_request(req, req_shard, &mut api);
            }
        }
    }
}

}
