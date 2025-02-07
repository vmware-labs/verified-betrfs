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

tokenized_state_machine!{KVStoreTokenized{
    fields {
        // This Tokenized machine doesn't admit any interesting
        // concurrency; it's just a wrapper for an atomic state machine.
        // We're using tokens just for correspondence: to enforce
        // that the implementation sends client IOs that match the
        // claims it makes in its SystemModel.
        #[sharding(variable)]
        pub atomic_state: AtomicState,

        #[sharding(multiset)]
        pub requests: Multiset<Request>,

        #[sharding(multiset)]
        pub replies: Multiset<Reply>,

        // Jon tried sharding(map), but:
        // error: unable to prove inherent safety condition: the given key must be absent from the map before the update
        // Not sure how to think about this; this isn't an invariant we have at the
        // KVStoreTokenized level; we only get it higher in the stack.
//         #[sharding(map)]
//         pub sync_requests: Map<SyncReqId, nat>,
        #[sharding(multiset)]
        pub sync_requests: Multiset<(SyncReqId, nat)>,

        #[sharding(multiset)]
        pub disk_requests: Multiset<(ID, DiskRequest)>,

        #[sharding(multiset)]
        pub disk_responses: Multiset<(ID, DiskResponse)>,
    }

    pub enum Label{
        RequestOp { req: Request },
        ExecuteOp { req: Request, reply: Reply },
        ReplyOp { reply: Reply },
        InternalOp,
        RequestSyncOp { sync_req_id: SyncReqId },
        ReplySyncOp { sync_req_id: SyncReqId },

        DiskOp{
            disk_event_lbl: DiskEventLabel,
            disk_request_tuples: Multiset<(ID, DiskRequest)>,
            disk_response_tuples: Multiset<(ID, DiskResponse)>,
            disk_lbl: AsyncDisk::Label,
            disk_req_id: ID },
    }

    init!{ initialize() {
        init atomic_state = AtomicState::init();
        init requests = Multiset::empty();
        init replies = Multiset::empty();
        init sync_requests = Multiset::empty();
        init disk_requests = Multiset::empty();
        init disk_responses = Multiset::empty();
    }}

    transition!{ disk_transition(lbl: Label, post_atomic_state: AtomicState) {
        require let Label::DiskOp{ disk_event_lbl, disk_request_tuples, disk_response_tuples, disk_lbl, disk_req_id } = lbl;

        require disk_lbl is DiskOps;
        remove disk_responses -= (disk_response_tuples);
        require disk_lbl->responses == multiset_to_map(disk_response_tuples);

        require AtomicState::disk_transition(
            pre.atomic_state, post_atomic_state, disk_event_lbl, disk_lbl, disk_req_id);
        update atomic_state = post_atomic_state;

        require disk_lbl->requests == multiset_to_map(disk_request_tuples);
        add disk_requests += (disk_request_tuples);
    }}

    transition!{ request(lbl: Label) {
        require pre.atomic_state.client_ready();
        require let Label::RequestOp{ req } = lbl;
        add requests += { req };
    }}

    // execute transition takes a versiosn 
    transition!{ execute_transition(lbl: Label, post_atomic_state: AtomicState, map_lbl: MapSpec::Label) {
        require pre.atomic_state.client_ready();
        require let Label::ExecuteOp{ req, reply } = lbl;
        require req.id == reply.id;

        remove requests -= { req };

        require getInput(map_lbl) == req.input;
        require getOutput(map_lbl) == reply.output;
        require AtomicState::map_transition(pre.atomic_state, post_atomic_state, map_lbl);
        update atomic_state = post_atomic_state;

        add replies += {reply};
    }}

    transition!{ reply(lbl: Label, post_atomic_state: AtomicState) {
        require pre.atomic_state.client_ready();
        require let Label::ReplyOp{ reply } = lbl;
        remove replies -= { reply };
    }}

    transition!{ accept_sync_request(lbl: Label) {
        require pre.atomic_state.client_ready();
        require let Label::RequestSyncOp{sync_req_id} = lbl;
        let cur_version = (pre.atomic_state.history.len() - 1) as nat;
        add sync_requests += {(sync_req_id, cur_version)};
    }}

    transition!{ deliver_sync_reply(lbl: Label, version: nat) {
        require pre.atomic_state.client_ready();
        require let Label::ReplySyncOp{sync_req_id} = lbl;
        let stable_version = pre.atomic_state.history.first_active_index();
        remove sync_requests -= {(sync_req_id, version)};
        require version <= stable_version;
    }}

    transition!{ internal(lbl: Label) {
        require pre.atomic_state.client_ready();
        require lbl is InternalOp;
    }}


    #[invariant]
    pub open spec fn wf(&self) -> bool {
        &&& self.atomic_state.wf()
        &&& !(self.atomic_state.recovery_state is RecoveryComplete)
            ==> {
                &&& self.requests.len() == 0
                &&& self.replies.len() == 0
                &&& self.sync_requests.len() == 0
            }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { 
    }

    #[inductive(request)]
    fn request_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(execute_transition)]
    pub fn execute_transition_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState, map_lbl: MapSpec::Label) { 
        MapSpec::State::inv_next(pre.atomic_state.mapspec(), post.atomic_state.mapspec(), map_lbl);
        // TODO(jialin): we should be getting MapSpec::invariant here; how do we invoke it?
        // I don't see *anything* in the expand file that summarizes pre.inv & next(pre,post) => post.inv.
        // Is this a known hole in the macro? => Yup! 

        let ghost pre_history = pre.atomic_state.history;
        let ghost post_history = post.atomic_state.history;
        assert forall |i| #[trigger] post_history.is_active(i) implies post_history[i].appv.invariant() by {
            if i < post_history.len() - 1 {
                assert( pre_history.is_active(i) ); // trigger AtomicState::wf forall
            }
        }
//         assert( post.atomic_state.wf() );
//         assert( post.wf() );
    }

    #[inductive(disk_transition)]
    fn disk_transition_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState) {
        assume( false );
//         AtomicState::disk_transition_preserves_wf(... pre, post, disk_event_lbl, disk_lbl, disk_req_id),
    }

    #[inductive(reply)]
    fn reply_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState) { 
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(accept_sync_request)]
    fn accept_sync_request_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(deliver_sync_reply)]
    fn deliver_sync_reply_inductive(pre: Self, post: Self, lbl: Label, version: nat) {
    }
}}
}

