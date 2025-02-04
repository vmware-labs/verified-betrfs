// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*, multiset::*};
//use vstd::pervasive::print_u64;
use state_machines_macros::tokenized_state_machine;
use crate::spec::MapSpec_t::*;
use crate::spec::TotalKMMap_t::*;
// use crate::spec::Messages_t::Value;

verus! {

#[verifier::ext_equal]
pub struct AtomicState {
    pub store: MapSpec::State,
    // pub ghost_snapshots: Seq<AtomicState>,
}

impl AtomicState {
    pub open spec fn init() -> Self
    {
        AtomicState{ store: my_init() }
    }

    pub open spec fn map_transition(pre: Self, post: Self, map_lbl: MapSpec::Label) -> bool
    {
        MapSpec::State::next(pre.store, post.store, map_lbl)
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
        InternalOp,
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

    // execute transition takes a versiosn 
    transition!{ execute_transition(lbl: Label, post_atomic_state: AtomicState, map_lbl: MapSpec::Label) {
        require let Label::ExecuteOp{ req, reply } = lbl;

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

    transition!{ internal(lbl: Label) {
        require lbl is InternalOp;
    }}

    // #[invariant]
    // pub open spec fn wf(&self) -> bool {
    //     true
    // }

    // #[inductive(initialize)]
    // fn initialize_inductive(post: Self) { 
    // }

    // #[inductive(request)]
    // fn request_inductive(pre: Self, post: Self, lbl: Label) {
    // }
   
    // #[inductive(transition)]
    // fn transition_inductive(pre: Self, post: Self, lbl: Label, post_atomic_state: AtomicState) { 
    // }

    // #[inductive(reply)]
    // fn reply_inductive(pre: Self, post: Self, lbl: Label) { 
    // }

    // #[inductive(internal)]
    // fn internal_inductive(pre: Self, post: Self, lbl: Label) {
    // }
}}
}

