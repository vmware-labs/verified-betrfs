// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*, multiset::*};
//use vstd::pervasive::print_u64;
use state_machines_macros::tokenized_state_machine;
use crate::spec::MapSpec_t::*;
use crate::implementation::AtomicState_v::*;    // apologies for auditor _t code calling impl _v code
use crate::spec::AsyncDisk_t::*;
use crate::implementation::MultisetMapRelation_v::*;

verus! {

// This tokenized SM is partly implemented by the implementer with atomic state
// and partly defined by the auditor to model client api and disk api tokens.
// Transitions here only model the program side actions, the auditor enabled transitions
// are left blank on purpose to prevent implementer from generating tokens themselves.
tokenized_state_machine!{KVStoreTokenized{
    fields {
 
        // This Tokenized machine doesn't admit any interesting
        // concurrency; it's just a wrapper for an atomic state machine.
        // We're using tokens just for correspondence: to enforce
        // that the implementation sends client IOs that match the
        // claims it makes in its SystemModel.
        #[sharding(variable)]
        pub atomic_state: AtomicState,

        // ======== BEGIN AUDITOR STATES ===========

        #[sharding(multiset)]
        pub requests: Multiset<Request>,

        #[sharding(multiset)]
        pub replies: Multiset<Reply>,

        // Jon tried sharding(map), but that's not the right model. To "fill in" a map slot,
        // you need to have the resource that proves it's presently empty. In this case,
        // you'd need to somehow know that you're about to receive a SyncReqId that has never
        // been supplied before. That's a promise the auditor will make, but not at this level.
        // So the multiset lets us receive a possibly-non-unique token.
        #[sharding(multiset)]
        pub sync_requests: Multiset<(SyncReqId, nat)>,

        #[sharding(multiset)]
        pub disk_requests: Multiset<(ID, DiskRequest)>,

        #[sharding(multiset)]
        pub disk_responses: Multiset<(ID, DiskResponse)>,

        // ======== BEGIN AUDITOR STATES ===========
    }

    pub enum Label{
        ExecuteOp { req: Request, reply: Reply },
        InternalOp,
        // TODO: 
        RequestSyncOp { sync_req_id: SyncReqId },
        ReplySyncOp { sync_req_id: SyncReqId },
        DiskOp{
            disk_request_tuples: Multiset<(ID, DiskRequest)>,
            disk_response_tuples: Multiset<(ID, DiskResponse)>,
        },
    }

    init!{ initialize() {
        init atomic_state = AtomicState::init();
        init requests = Multiset::empty();
        init replies = Multiset::empty();
        init sync_requests = Multiset::empty();
        init disk_requests = Multiset::empty();
        init disk_responses = Multiset::empty();
    }}

    transition!{ internal(lbl: Label, post_atomic_state: AtomicState) {
        require lbl is InternalOp;
        require AtomicState::internal_transitions(pre.atomic_state, post_atomic_state);
        update atomic_state = post_atomic_state;
    }}

    transition!{ execute_transition(lbl: Label, post_atomic_state: AtomicState) {
        require let Label::ExecuteOp{ req, reply } = lbl;

        remove requests -= { req };
        require AtomicState::map_transition(pre.atomic_state, post_atomic_state, req, reply);
        add replies += {reply};

        update atomic_state = post_atomic_state;
    }}

    // program actions that generate disk requests and consume delivered disk responses
    transition!{ disk_transitions(lbl: Label, post_atomic_state: AtomicState, disk_event: DiskEvent) {
        require lbl is DiskOp;

        remove disk_responses -= (lbl->disk_response_tuples);
        require AtomicState::disk_transition(pre.atomic_state, post_atomic_state, 
            disk_event, lbl->disk_request_tuples, lbl->disk_response_tuples);
        add disk_requests += (lbl->disk_request_tuples);

        update atomic_state = post_atomic_state;
    }}

    // remove a request of type sync req, creates a token of sync req with the current version #
    // remove must consume that token, and generate a reply with a corresponding id
    transition!{ valid_sync_request(lbl: Label, version: nat) {
        require let Label::RequestSyncOp{sync_req_id} = lbl;
        // TODO: integrate sync into input 
        // remove -= Request{sync_req_id, SyncInput};
        require AtomicState::valid_sync_request(pre.atomic_state, pre.atomic_state, version);
        add sync_requests += {(sync_req_id, version)};
    }}

    // TODO: this looks weird I know
    transition!{ deliver_sync_reply(lbl: Label, version: nat) {
        require let Label::ReplySyncOp{sync_req_id} = lbl;

        remove sync_requests -= {(sync_req_id, version)};
        require AtomicState::valid_sync_reply(pre.atomic_state, pre.atomic_state, version); 
        // TODO: integrate sync into output
        // add += Reply{id: sync_req_id, SyncOutput} 
    }}

    #[invariant]
    pub open spec fn wf(&self) -> bool {
        &&& !(self.atomic_state.recovery_state is RecoveryComplete)
            ==> {
                &&& self.requests.len() == 0
                &&& self.replies.len() == 0
                &&& self.sync_requests.len() == 0
            }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }
   
    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState) { }
   
    #[inductive(execute_transition)]
    fn execute_transition_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState) { }
   
    #[inductive(disk_transitions)]
    fn disk_transitions_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState, disk_event: DiskEvent) { }
   
    #[inductive(valid_sync_request)]
    fn valid_sync_request_inductive(pre: Self, post: Self, lbl: Label, version: nat) { }
   
    #[inductive(deliver_sync_reply)]
    fn deliver_sync_reply_inductive(pre: Self, post: Self, lbl: Label, version: nat) { }
}}
}

