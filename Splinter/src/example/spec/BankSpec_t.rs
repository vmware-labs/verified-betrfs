// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, set::*};
use state_machines_macros::state_machine;

verus! {

pub type ReqID = u64;

pub struct Input { 
    pub from: usize,
    pub to: usize, 
    pub amt: u32
}

pub struct Output { 
    pub succeeded: bool 
}

pub struct Request {
    pub input: Input,
    pub id: ReqID,
}

pub struct Reply {
    pub output: Output,
    pub id: ReqID,
}

state_machine!{ BankSpec {
    fields {
        pub accounts: Map<nat, nat>,
        pub requests: Set<Request>,
        pub replies: Set<Reply>,
    }

    pub enum Label{
        RequestOp { req: Request },
        ExecuteOp { req: Request, reply: Reply },
        ReplyOp { reply: Reply },
    }

    init!{ initialize(total_accounts: nat, initial_value: nat) {
        init accounts = Map::new(|acc: nat| acc < total_accounts, |acc| initial_value);
        init requests = Set::empty();
        init replies = Set::empty();
    }}

    transition!{ request(lbl: Label) {
        require let Label::RequestOp{ req } = lbl;
        require forall |r| #[trigger] pre.requests.contains(r) ==> r.id != req.id;
        update requests = pre.requests.insert(req);
    }}

    transition!{ transfer(lbl: Label) {
        require let Label::ExecuteOp{req, reply} = lbl;
        require req.id == reply.id;
        require reply.output.succeeded;

        require pre.requests.contains(req);
        require forall |r| #[trigger] pre.replies.contains(r) ==> r.id != reply.id;

        let from = req.input.from as nat;
        let to = req.input.to as nat;

        require pre.accounts.contains_key(from);
        require pre.accounts.contains_key(to);
        require pre.accounts[from] >= req.input.amt;

        let new_from_amt = (pre.accounts[from] - req.input.amt) as nat;
        let new_to_amt = (pre.accounts[to] + req.input.amt) as nat;

        update accounts = pre.accounts.insert(from, new_from_amt).insert(to, new_to_amt);
        update requests = pre.requests.remove(req);
        update replies = pre.replies.insert(reply);
    }}

    transition!{ failed_transfer(lbl: Label) {
        require let Label::ExecuteOp{req, reply} = lbl;
        require req.id == reply.id;
        require !reply.output.succeeded; // can fail for any reason (invalid request, not enough amt, etc.)

        require pre.requests.contains(req);
        require forall |r| #[trigger] pre.replies.contains(r) ==> r.id != reply.id;

        update requests = pre.requests.remove(req);
        update replies = pre.replies.insert(reply);
    }}

    transition!{ reply(lbl: Label) {
        require let Label::ReplyOp{ reply } = lbl;
        require pre.replies.contains(reply);
        update replies = pre.replies.remove(reply);
    }}
}}

fn main() {}
} // verus!