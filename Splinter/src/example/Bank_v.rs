// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use vstd::{prelude::*, map::*, multiset::*};
use vstd::pervasive::print_u64;
use state_machines_macros::tokenized_state_machine;
use crate::BankSpec_t::{Request, Reply, Input, Output, ReqID};

verus! {

type AccID = nat;

tokenized_state_machine!{Bank{
    fields {
        #[sharding(constant)]
        pub total_accounts: nat,

        #[sharding(constant)]
        pub total_amount: nat,

        #[sharding(map)]
        pub account_map: Map<AccID, nat>,

        // NOTE: use multiset as sharding strategy
        // to allow threads to make independent decisions
        // conditional refinement on request AccID being unique

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

    init!{ initialize(total_accounts: nat, initial_amount: nat) {
        init total_accounts = total_accounts;
        init total_amount = initial_amount * total_accounts;
        init account_map = Map::new(|acc: AccID| acc < total_accounts, |acc| initial_amount);
        init requests = Multiset::empty();
        init replies = Multiset::empty();
    }}

    transition!{ request(lbl: Label) {
        require let Label::RequestOp{ req } = lbl;
        add requests += { req };
    }}

    transition!{ transfer(lbl: Label) {
        require let Label::ExecuteOp{ req, reply } = lbl;
        remove requests -= {req};

        require req.id == reply.id;
        require reply.output.succeeded;

        let from = req.input.from as nat;
        let to = req.input.to as nat;
        let amt = req.input.amt as nat;

        // generated Instance transfer fn will take in 2 account_tokens
        remove account_map -= [from => let from_amt];
        remove account_map -= [to => let to_amt];
        require from_amt >= amt;

        // generated Instance transfer fn will return 2 account_tokens
        add account_map += [from => (from_amt - amt) as nat];
        add account_map += [to  => (to_amt + amt) as nat];
        add replies += {reply};
    }}

    transition!{ failed_transfer(lbl: Label) {
        require let Label::ExecuteOp{ req, reply } = lbl;
        remove requests -= {req};

        require req.id == reply.id;
        require !reply.output.succeeded;

        add replies += {reply};
    }}

    transition!{ reply(lbl: Label) {
        require let Label::ReplyOp{ reply } = lbl;
        remove replies -= { reply };
    }}

    pub open spec(checked) fn range_sum(self, start: AccID, end: AccID) -> nat
        recommends self.wf(), start <= end <= self.total_accounts
        decreases end - start when start <= end
    {
        if start == end {
            0
        } else {
            self.account_map[start] + self.range_sum(start+1, end)
        }
    }

    #[invariant]
    pub open spec fn wf(&self) -> bool {
        forall |acc: AccID| acc < self.total_accounts ==> self.account_map.contains_key(acc)
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, total_accounts: nat, initial_amount: nat) { 
    }

    #[inductive(request)]
    fn request_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(transfer)]
    fn transfer_inductive(pre: Self, post: Self, lbl: Label) { 
    }

    #[inductive(failed_transfer)]
    fn failed_transfer_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(reply)]
    fn reply_inductive(pre: Self, post: Self, lbl: Label) { 
    }
}}
}