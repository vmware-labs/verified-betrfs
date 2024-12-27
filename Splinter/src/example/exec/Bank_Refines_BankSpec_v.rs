// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::{prelude::*, map::*, multiset::*};
use crate::spec::BankSpec_t::{Request, Reply, Input, Output, ReqID};
use crate::spec::BankSpec_t;
use crate::exec::Bank_v;

verus! {
// invariants & conditional refinement
use BankSpec_t::BankSpec as BankModel;
use Bank_v::Bank as Bank;

pub open spec(checked) fn all_elems_single<V>(m: Multiset<V>) -> bool
{
    forall |e| #[trigger] m.contains(e) ==> m.count(e) == 1
}

broadcast proof fn insert_new_preserves_cardinality<V>(m: Multiset<V>, new: V)
    requires all_elems_single(m), !m.contains(new)
    ensures #[trigger] all_elems_single(m.insert(new))
{
    let post_m = m.insert(new);
    assert forall |e| #[trigger] post_m.contains(e)
    implies post_m.count(e) == 1
    by {
        if e != new {
            assert(m.contains(e)); // trigger
        }
    }
}

impl Bank::Label{
    pub open spec(checked) fn i(self) -> BankModel::Label
    {
        match self {
            Self::RequestOp{req} => BankModel::Label::RequestOp{req},
            Self::ExecuteOp{req, reply} => BankModel::Label::ExecuteOp{req, reply},
            Self::ReplyOp{reply} => BankModel::Label::ReplyOp{reply},
        }
    }
}

impl Bank::State {
    pub open spec(checked) fn i(self) -> BankModel::State
    {
        BankModel::State{
            accounts: self.account_map,
            requests: self.requests.dom(),
            replies: self.replies.dom(),
        }
    }

    pub open spec(checked) fn requests_have_unique_ids(self) -> bool 
    {
        &&& all_elems_single(self.requests)
        &&& forall |req1, req2| self.requests.contains(req1) 
            && self.requests.contains(req2) 
            && #[trigger] req1.id == #[trigger] req2.id
            ==> req1 == req2
    }

    pub open spec(checked) fn replies_have_unique_ids(self) -> bool 
    {
        &&& all_elems_single(self.replies)
        &&& forall |reply1, reply2| self.replies.contains(reply1) 
            && self.replies.contains(reply2) 
            && #[trigger] reply1.id == #[trigger] reply2.id
            ==> reply1 == reply2
    }
 
    pub open spec(checked) fn inv(self) -> bool
    {
        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& all_elems_single(self.id_history)

        &&& forall |req| self.requests.contains(req) ==> #[trigger] self.id_history.contains(req.id)
        &&& forall |reply| #[trigger] self.replies.contains(reply) ==> self.id_history.contains(reply.id)
        &&& forall |req, reply| self.requests.contains(req) && self.replies.contains(reply) 
            ==> #[trigger] req.id != #[trigger] reply.id
    }

    pub open spec(checked) fn strong_label(self, lbl: Bank::Label) -> bool
    {
        if let Bank::Label::RequestOp{req} = lbl {
            !self.id_history.contains(req.id)
        } else {
            true
        }
    }

    proof fn init_refines(self, total_accounts: nat, initial_amount: nat)
        requires 
            Self::initialize(self, total_accounts, initial_amount)
        ensures 
            self.inv(),
            BankModel::State::initialize(self.i(), total_accounts, initial_amount), 
    {
        assert(self.requests.dom() =~= Set::empty());
        assert(self.replies.dom() =~= Set::empty());
    }

    proof fn request_strong_refines(self, post: Self, lbl: Bank::Label)
        requires self.inv(), self.strong_label(lbl), Self::request(self, post, lbl)
        ensures post.inv(), BankModel::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(BankModel::State::next);
        reveal(BankModel::State::next_by);

        broadcast use insert_new_preserves_cardinality;

        let request = lbl.arrow_RequestOp_req();
        assert(post.id_history.contains(request.id));
        assert(forall |req| #[trigger] post.requests.contains(req) && req != request 
            ==> self.id_history.contains(req.id));

        assert(post.inv());
        assert(post.i().requests == self.i().requests.insert(request));
        assert(BankModel::State::next_by(self.i(), post.i(), lbl.i(), BankModel::Step::request()));
    }

    proof fn execute_preserves_inv(self, post: Self, lbl: Bank::Label)
        requires 
            self.inv(), 
            Self::transfer(self, post, lbl) || Self::failed_transfer(self, post, lbl)
        ensures 
            post.inv(), 
            post.i().requests =~= self.i().requests.remove(lbl.arrow_ExecuteOp_req()),
            post.i().replies =~= self.i().replies.insert(lbl.arrow_ExecuteOp_reply()),
    {
        broadcast use insert_new_preserves_cardinality;

        let request = lbl.arrow_ExecuteOp_req();
        let reply = lbl.arrow_ExecuteOp_reply();

        assert(forall |req| #[trigger] post.requests.contains(req) 
            ==> self.requests.contains(req));
        assert(forall |rep| #[trigger] post.replies.contains(rep) && rep != reply 
            ==> post.id_history.contains(rep.id));
        assert(post.inv());
    }

    proof fn transfer_refines(self, post: Self, lbl: Bank::Label)
        requires self.inv(), Self::transfer(self, post, lbl)
        ensures post.inv(), BankModel::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(BankModel::State::next);
        reveal(BankModel::State::next_by);

        self.execute_preserves_inv(post, lbl);

        let request = lbl.arrow_ExecuteOp_req();
        let reply = lbl.arrow_ExecuteOp_reply();

        let from = request.input.from as nat;
        let to = request.input.to as nat;

        let new_from_amt = (self.account_map[from] - request.input.amt) as nat;
        let new_to_amt = (self.account_map[to] + request.input.amt) as nat;

        assert(post.account_map == self.account_map.insert(from, new_from_amt).insert(to, new_to_amt));
        assert(BankModel::State::next_by(self.i(), post.i(), lbl.i(), BankModel::Step::transfer()));
    }

    proof fn failed_transfer_refines(self, post: Self, lbl: Bank::Label)
        requires self.inv(), Self::failed_transfer(self, post, lbl)
        ensures post.inv(), BankModel::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(BankModel::State::next);
        reveal(BankModel::State::next_by);

        self.execute_preserves_inv(post, lbl);
        assert(BankModel::State::next_by(self.i(), post.i(), lbl.i(), BankModel::Step::failed_transfer()));
    }

    proof fn reply_refines(self, post: Self, lbl: Bank::Label)
        requires self.inv(), Self::reply(self, post, lbl)
        ensures post.inv(), BankModel::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(BankModel::State::next);
        reveal(BankModel::State::next_by);

        assert(forall |r| #[trigger] post.replies.contains(r) ==> self.replies.contains(r));
        assert(post.inv());

        let reply = lbl.arrow_ReplyOp_reply();
        if (post.replies.contains(reply)) {
            assert(self.replies.count(reply) > 1);
            assert(false);
        }
        assert(post.i().replies =~= self.i().replies.remove(reply));
        assert(BankModel::State::next_by(self.i(), post.i(), lbl.i(), BankModel::Step::reply()));
    }

    proof fn next_strong_refines(self, post: Self, lbl: Bank::Label)
        requires
            self.inv(),
            Self::next(self, post, lbl),
            self.strong_label(lbl),
        ensures 
            post.inv(),
            BankModel::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(Bank::State::next);
        reveal(Bank::State::next_by);

        match choose |step| Self::next_by(self, post, lbl, step)
        {
            Bank::Step::request() => { self.request_strong_refines(post, lbl); } 
            Bank::Step::transfer() => { self.transfer_refines(post, lbl); }
            Bank::Step::failed_transfer() => { self.failed_transfer_refines(post, lbl); }
            Bank::Step::reply() => { self.reply_refines(post, lbl); }
            _ => { assert(false); } 
        }
    }
}

}