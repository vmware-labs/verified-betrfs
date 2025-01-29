// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*, multiset::*};
//use vstd::pervasive::print_u64;
use state_machines_macros::tokenized_state_machine;
use crate::spec::MapSpec_t::{Request, Reply};
use crate::spec::Messages_t::Value;

verus! {

pub struct AtomicState {
    // TODO This eventually becomes a CTAMMap; until then,
    // the implementation/ModelRefinement_v will have to assume false.
    pub store: Map<int, Value>,
}

impl AtomicState {
    pub open spec fn init() -> Self
    {
        AtomicState{
            store: Map::empty()
        }
    }

    pub open spec fn transition(pre: Self, post: Self, req: Request, reply: Reply) -> bool
    {
        true
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
    }

    pub enum Label{
        RequestOp { req: Request },
        ExecuteOp { req: Request, reply: Reply },
        ReplyOp { reply: Reply },
    }

    init!{ initialize() {
        init atomic_state = AtomicState::init();
        init requests = Multiset::empty();
        init replies = Multiset::empty();
    }}

    transition!{ request(lbl: Label) {
        require let Label::RequestOp{ req } = lbl;
        add requests += { req };
    }}

    transition!{ transition(lbl: Label, post_atomic_state: AtomicState) {
        // TODO admit noops and req-only, reply-only ops, and disk IOs
        require let Label::ExecuteOp{ req, reply } = lbl;
        remove requests -= {req};
        require AtomicState::transition(pre.atomic_state, post_atomic_state, req, reply);
        update atomic_state = post_atomic_state;
        add replies += {reply};
    }}

    transition!{ reply(lbl: Label) {
        require let Label::ReplyOp{ reply } = lbl;
        remove replies -= { reply };
    }}

    #[invariant]
    pub open spec fn wf(&self) -> bool {
        true
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { 
    }

    #[inductive(request)]
    fn request_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(transition)]
    fn transition_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState) { 
    }

    #[inductive(reply)]
    fn reply_inductive(pre: Self, post: Self, lbl: Label) { 
    }
}}
}

