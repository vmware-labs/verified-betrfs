// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*, multiset::*};
//use vstd::pervasive::print_u64;
use state_machines_macros::tokenized_state_machine;
use crate::spec::FloatingSeq_t::*;
use crate::spec::MapSpec_t::*;
// use crate::spec::Messages_t::Value;

verus! {

pub struct AtomicState {
    // TODO This eventually becomes a CTAMMap; until then,
    // the implementation/ModelRefinement_v will have to assume false.

    //pub store: Map<int, Value>,
    pub store: CrashTolerantAsyncMap::State,
}

impl AtomicState {
    pub open spec fn init() -> Self
    {
        AtomicState{
            // TODO These types should get `exec fn new`s
            store: CrashTolerantAsyncMap::State {
                versions: FloatingSeq { start: 0, entries: seq![PersistentState{appv: my_init()}], },
                async_ephemeral: AsyncMap::State::init_ephemeral_state(), 
                sync_requests: Map::empty(),
            }
        }
    }

    pub open spec fn request_transition(pre: Self, post: Self, req: Request) -> bool
    {
        let lbl = CrashTolerantAsyncMap::Label::OperateOp{
            base_op: AsyncMap::Label::RequestOp{ req: req }
        };
        CrashTolerantAsyncMap::State::next(pre.store, post.store, lbl)
    }

    pub open spec fn execute_transition(pre: Self, post: Self, req: Request, reply: Reply) -> bool
    {
        let lbl = CrashTolerantAsyncMap::Label::OperateOp{
            base_op: AsyncMap::Label::ExecuteOp{
                req: req,
                reply: reply,
            }
        };
        CrashTolerantAsyncMap::State::next(pre.store, post.store, lbl)
    }

    pub open spec fn reply_transition(pre: Self, post: Self, reply: Reply) -> bool
    {
        let lbl = CrashTolerantAsyncMap::Label::OperateOp{
            base_op: AsyncMap::Label::ReplyOp{ reply: reply }
        };
        CrashTolerantAsyncMap::State::next(pre.store, post.store, lbl)
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

    transition!{ request(lbl: Label, post_atomic_state: AtomicState) {
        require let Label::RequestOp{ req } = lbl;

        // Keep atomic state req list in sync with sharded reqs.
        // This is a silly detour because we're trying to reuse the CTAM as
        // our AtomicState, and CTAM tracks the requests & replies.
        require AtomicState::request_transition(pre.atomic_state, post_atomic_state, req);
        update atomic_state = post_atomic_state;

        add requests += { req };
    }}

    transition!{ execute_transition(lbl: Label, post_atomic_state: AtomicState) {
        // TODO admit noops and req-only, reply-only ops, and disk IOs
        require let Label::ExecuteOp{ req, reply } = lbl;
        remove requests -= {req};
        require AtomicState::execute_transition(pre.atomic_state, post_atomic_state, req, reply);
        update atomic_state = post_atomic_state;
        add replies += {reply};
    }}

    transition!{ reply(lbl: Label, post_atomic_state: AtomicState) {
        require let Label::ReplyOp{ reply } = lbl;

        // Keep atomic state reply list in sync with sharded replys.
        // This is a silly detour because we're trying to reuse the CTAM as
        // our AtomicState, and CTAM tracks the requests & replies.
        require AtomicState::reply_transition(pre.atomic_state, post_atomic_state, reply);
        update atomic_state = post_atomic_state;

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

