// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use vstd::{prelude::*, map::*, multiset::*};
use vstd::pervasive::print_u64;
use state_machines_macros::tokenized_state_machine;
use crate::spec::BankSpec_t::{Request, Reply, Input, Output, ReqID};

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

        #[sharding(multiset)]
        pub id_history: Multiset<ReqID>,
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
        init id_history = Multiset::empty();
    }}

    transition!{ request(lbl: Label) {
        require let Label::RequestOp{ req } = lbl;
        add requests += { req };
        add id_history += { req.id };
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

    // #[invariant]
    // pub open spec fn preserves_total_amt(&self) -> bool {
    //     self.range_sum(0, self.total_accounts) == self.total_amount
    // }

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

// TODO: Trusted API should not in its own _t file

// external body to prevent unprotected construction
#[verifier::external_body]
pub struct TrustedAPI{
    id: AtomicU64
}

impl TrustedAPI{
    #[verifier::external_body]
    pub closed spec fn instance(&self) -> Bank::Instance;

    #[verifier::external_body]
    pub fn new(instance: Ghost<Bank::Instance>) -> (out: Self)
        ensures
            out.instance() == instance@
    {
        TrustedAPI{id: AtomicU64::new(0)}
    }

    // NOTE: this is a tightly coupled API, we cannot ensure that the result is 
    // comes from the tokenized state machine instance transition due to it being in proof mode
    // we want (out.1, out.2) == self.instance().request(Bank::Label::RequestOp{req})
    // but this ensure is rolling out the result of the ensure
    #[verifier::external_body]
    pub fn receive_request(&self, print: bool)
        -> (out: (Request, Tracked<Bank::requests>, Tracked<Bank::id_history>))
    ensures
        out.1@@.instance == self.instance(),
        out.1@@.key == out.0,
        out.1@@.count == 1,
        out.2@@.instance == self.instance(),
        out.2@@.key == out.0.id,
        out.2@@.count == 1,
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let amt = (id % 20) as u32;

        let input = if id % 3 == 0 {
            Input { from: id as usize, to: (id + 1) as usize, amt}
        } else {
            Input { from: (id + 1) as usize, to: id as usize, amt}
        };

        if print {
            println!("request {}: transfer ${} from {} to {}", 
            id, input.amt, input.from, input.to,);
        }
        (Request {input, id}, Tracked::assume_new(), Tracked::assume_new())
    }

    // NOTE: corresponds to a tokenized state machine reply step
    // consumes the reply shard
    #[verifier::external_body]
    pub fn send_reply(&self, reply: Reply,  reply_shard: Tracked<Bank::replies>, print: bool)
        requires 
            reply_shard@@.instance == self.instance(),
            reply_shard@@.key == reply
    {
        if print {
            let result = if reply.output.succeeded { "succeeded" } else { "failed" };
            println!("reply {}: {}", reply.id, result);
        }
    }
}
} 