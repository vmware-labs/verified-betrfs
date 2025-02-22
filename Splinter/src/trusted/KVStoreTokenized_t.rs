// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*, multiset::*};
use state_machines_macros::tokenized_state_machine;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::implementation::MultisetMapRelation_v::*;
use crate::trusted::ProgramModelTrait_t::*;

verus! {

tokenized_state_machine!{KVStoreTokenized<ProgramModel: ProgramModelTrait>{
    fields {
        // NOTE: this strategy work well for embedding an atomic
        // program model, it could potentially work just as well as 
        // for a sharded SM? as the composed sharded SM might be seen
        // as an abstract model at the layer above
        #[sharding(variable)]
        pub model: ProgramModel,

        // Auditor defined shards

        #[sharding(multiset)]
        pub requests: Multiset<Request>,

        #[sharding(multiset)]
        pub replies: Multiset<Reply>,

        // NOTE: this might be ok to support now, but not changing it cause we don't have to
        // right now => Jon tried sharding(map), but that's not the right model. 
        // To "fill in" a map slot, you need to have the resource that proves it's presently empty. 
        // In this case, you'd need to somehow know that you're about to receive a SyncReqId that has never
        // been supplied before. That's a promise the auditor will make, but not at this level.
        // So the multiset lets us receive a possibly-non-unique token.
        #[sharding(multiset)]
        pub sync_requests: Multiset<SyncReqId>,

        #[sharding(multiset)]
        pub sync_replies: Multiset<SyncReqId>,

        #[sharding(multiset)]
        pub disk_requests: Multiset<(ID, DiskRequest)>,

        #[sharding(multiset)]
        pub disk_responses: Multiset<(ID, DiskResponse)>,
    }

    pub enum Label{
        ExecuteOp { req: Request, reply: Reply },
        InternalOp,
        RequestSyncOp { sync_req_id: SyncReqId },
        ReplySyncOp { sync_req_id: SyncReqId },
        DiskOp{
            disk_request_tuples: Multiset<(ID, DiskRequest)>,
            disk_response_tuples: Multiset<(ID, DiskResponse)>,
        },
    }

    init!{ initialize(model: ProgramModel) {
        require ProgramModel::init(model);
        init model = model;

        init requests = Multiset::empty();
        init replies = Multiset::empty();
        init sync_requests = Multiset::empty();
        init sync_replies = Multiset::empty();
        init disk_requests = Multiset::empty();
        init disk_responses = Multiset::empty();
    }}

    // question is in this model should we omit the steps taken in the 

    transition!{ internal(lbl: Label, post_atomic_state: ProgramModel) {
        require lbl is InternalOp;
        require ProgramModel::next(pre.model, post_atomic_state, ProgramLabel::Internal{});
        update model = post_atomic_state;
    }}

    transition!{ execute_transition(lbl: Label, post_atomic_state: ProgramModel) {
        require let Label::ExecuteOp{ req, reply } = lbl;

        remove requests -= { req };
        require ProgramModel::next(pre.model, post_atomic_state, 
            ProgramLabel::UserIO{op: ProgramUserOp::Execute{req, reply}});
        add replies += {reply};

        update model = post_atomic_state;
    }}

    // program actions that generate disk requests and consume delivered disk responses
    transition!{ disk_transitions(lbl: Label, post_atomic_state: ProgramModel) {
        require lbl is DiskOp;

        remove disk_responses -= (lbl->disk_response_tuples);   
        require ProgramModel::next(pre.model, post_atomic_state, 
            ProgramLabel::DiskIO{info: ProgramDiskInfo{
                reqs: lbl->disk_request_tuples, 
                resps: lbl->disk_response_tuples, 
            }});
        add disk_requests += (lbl->disk_request_tuples);

        update model = post_atomic_state;
    }}

    // remove a request of type sync req, creates a token of sync req with the current version #
    // remove must consume that token, and generate a reply with a corresponding id
    transition!{ accept_sync_request(lbl: Label, post_atomic_state: ProgramModel) {
        require let Label::RequestSyncOp{sync_req_id} = lbl;

        // have sync_requests >= { sync_req_id };
        remove sync_requests -= { sync_req_id };
        require ProgramModel::next(pre.model, post_atomic_state, 
            ProgramLabel::UserIO{op: ProgramUserOp::AcceptSyncRequest{sync_req_id}});

        update model = post_atomic_state;
    }}

    transition!{ deliver_sync_reply(lbl: Label, post_atomic_state: ProgramModel) {
        require let Label::ReplySyncOp{sync_req_id} = lbl;

        require ProgramModel::next(pre.model, post_atomic_state, 
            ProgramLabel::UserIO{op: ProgramUserOp::DeliverSyncReply{sync_req_id}});
        add sync_replies += { sync_req_id };

        update model = post_atomic_state;
    }}
}}
}

