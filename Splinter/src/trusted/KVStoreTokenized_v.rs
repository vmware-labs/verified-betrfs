// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*, multiset::*};
//use vstd::pervasive::print_u64;
use state_machines_macros::tokenized_state_machine;
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::implementation::MultisetMapRelation_v::unique_keys;    // more trusted apology

verus! {

#[verifier::ext_equal]
pub struct AtomicState {
    pub history: FloatingSeq<PersistentState>,
}

impl AtomicState {
    pub open spec fn init() -> Self
    {
        AtomicState{ history: SingletonVersions(my_init()) }
    }

    pub open spec fn map_transition(pre: Self, post: Self, map_lbl: MapSpec::Label) -> bool
    {
        // new thing appends no more than one map
        &&& pre.history.len() <= post.history.len() <= pre.history.len() + 1
        // new thing appends to the history
        &&& post.history.get_prefix(pre.history.len()) == pre.history
        &&& MapSpec::State::next(pre.history.last().appv, post.history.last().appv, map_lbl)
    }

    pub open spec fn wf(self) -> bool {
      &&& self.history.is_active(self.history.len()-1)
      &&& forall |i| #[trigger] self.history.is_active(i) ==> self.history[i].appv.invariant()

      // In this silly version, we never persist, so stable_index cannot be allowed to advance;
      // that's what will allow us to crash because it lets us forget everything.
      &&& self.history.first_active_index() == 0
      // ...and of course the beginning version had better stay stuck at state 0, so we know
      // where the crash is going to return to.
      &&& self.history[0] == SingletonVersions(my_init())[0]
    }

    pub open spec fn mapspec(self) -> MapSpec::State {
        self.history.last().appv
    }
}

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
    }

    pub enum Label{
        RequestOp { req: Request },
        ExecuteOp { req: Request, reply: Reply },
        ReplyOp { reply: Reply },
        InternalOp,
        RequestSyncOp { sync_req_id: SyncReqId },
        ReplySyncOp { sync_req_id: SyncReqId },
    }

    init!{ initialize() {
        init atomic_state = AtomicState::init();
        init requests = Multiset::empty();
        init replies = Multiset::empty();
        init sync_requests = Multiset::empty();
    }}

    transition!{ request(lbl: Label) {
        require let Label::RequestOp{ req } = lbl;
        add requests += { req };
    }}

    // execute transition takes a versiosn 
    transition!{ execute_transition(lbl: Label, post_atomic_state: AtomicState, map_lbl: MapSpec::Label) {
        require let Label::ExecuteOp{ req, reply } = lbl;
        require req.id == reply.id;

        remove requests -= {req};
        require getInput(map_lbl) == req.input;
        require getOutput(map_lbl) == reply.output;
        require AtomicState::map_transition(pre.atomic_state, post_atomic_state, map_lbl);
        update atomic_state = post_atomic_state;

        add replies += {reply};
    }}

    transition!{ reply(lbl: Label, post_atomic_state: AtomicState) {
        require let Label::ReplyOp{ reply } = lbl;
        remove replies -= { reply };
    }}

    transition!{ accept_sync_request(lbl: Label) {
        require let Label::RequestSyncOp{sync_req_id} = lbl;
        let cur_version = (pre.atomic_state.history.len() - 1) as nat;
        add sync_requests += {(sync_req_id, cur_version)};
    }}

    transition!{ deliver_sync_reply(lbl: Label, version: nat) {
        require let Label::ReplySyncOp{sync_req_id} = lbl;
        let stable_version = pre.atomic_state.history.first_active_index();
        remove sync_requests -= {(sync_req_id, version)};
        require version <= stable_version;
    }}

    transition!{ internal(lbl: Label) {
        require lbl is InternalOp;
    }}

    #[invariant]
    pub open spec fn wf(&self) -> bool {
        &&& self.atomic_state.wf()
        &&& unique_keys(self.sync_requests)
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

    #[inductive(reply)]
    fn reply_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState) { 
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(accept_sync_request)]
    fn accept_sync_request_inductive(pre: Self, post: Self, lbl: Label) {

// We can't maintain the invariant in KVStoreTok, because we don't have the
// promise from the auditor.
// 
// We can't maintain the invariant in ModelRefinement, because we're already
// assuming that the GSM state space of KVStoreTok is established by its invariant.
// We can't rule out the possibility that some race condition in the concurrent
// system moves us from a all_elems_single state to a !all_elems_single state,
// since both are within the inductive region.
// 
// This sort of defeats the idea that we don't have to track the singleness in
// the tok machine and can introduce that promise higher in the stack.
// 
// One possible origin for this problem is our inability to split the tok machine
// into a trusted and untrusted composition. If we had that, the trusted half
// could assert the invariant and assume-false it here, moving the assumption
// down in the stack to the tok layer.
        
        assume( false ); // auditor supplies unique IDs
    }
   
    #[inductive(deliver_sync_reply)]
    fn deliver_sync_reply_inductive(pre: Self, post: Self, lbl: Label, version: nat) {
        assume( false ); // auditor supplies unique IDs
    }
}}
}

