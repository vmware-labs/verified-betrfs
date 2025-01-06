use builtin::*;
use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{set::*, multiset::Multiset};
use crate::Bank_v::Bank;
use crate::BankSpec_t::*;
use crate::BankContract_t::*;

verus!{

impl BankLabel{
    pub open spec fn to_bank_lbl(self) -> Bank::Label {
        match self {
            Self::AcceptRequest{req} => Bank::Label::RequestOp{req},
            Self::DeliverReply{reply} => Bank::Label::ReplyOp{reply},
            Self::Execute{req, reply} => Bank::Label::ExecuteOp{req, reply}
        }
    }
}

impl Bank::Label{
    pub open spec(checked) fn i(self) -> BankSpec::Label
    {
        match self {
            Self::RequestOp{req} => BankSpec::Label::RequestOp{req},
            Self::ExecuteOp{req, reply} => BankSpec::Label::ExecuteOp{req, reply},
            Self::ReplyOp{reply} => BankSpec::Label::ReplyOp{reply},
        }
    }
}

impl BankModel for Bank::State{
    open spec fn init(bank: &Self, total_accounts: nat, initial_value: nat) -> bool
    {
        Self::initialize(*bank, total_accounts, initial_value)
    }

    open spec fn next(pre: &Self, post: &Self, lbl: BankLabel) -> bool
    {
        Self::next(*pre, *post, lbl.to_bank_lbl())
    }
}

impl RefinementObligations for Bank::State{
    type Model = Self;

    closed spec fn inv(model: &SystemModel::State<Self::Model>) -> bool
    {
        &&& model.bank.requests_have_unique_ids()
        &&& model.bank.replies_have_unique_ids()
        &&& forall |req, reply| model.bank.requests.contains(req) 
            && model.bank.replies.contains(reply) 
            ==> #[trigger] req.id != #[trigger] reply.id

        &&& forall |req| model.bank.requests.contains(req)
            ==> #[trigger] model.id_history.contains(req.id)
        &&& forall |reply| model.bank.replies.contains(reply)
            ==> #[trigger] model.id_history.contains(reply.id)
    }
 
    closed spec fn i(model: &SystemModel::State<Self::Model>) -> BankSpec::State
    {
        model.bank._i()
    }

    closed spec fn i_lbl(lbl: SystemModel::Label) -> (result: BankSpec::Label)
    {
        lbl.to_bank_lbl().i()
    }

    proof fn i_lbl_valid(lbl: SystemModel::Label, result: BankSpec::Label)
    {}

    proof fn init_refines(pre: &SystemModel::State<Self::Model>, total_accounts: nat, initial_value: nat)
    {
        assert(pre.bank.requests.dom() =~= Set::empty());
        assert(pre.bank.replies.dom() =~= Set::empty());
    }

    proof fn next_refines(pre: &SystemModel::State<Self::Model>, post: &SystemModel::State<Self::Model>, lbl: BankLabel)
    {
        reveal(SystemModel::State::next);
        reveal(SystemModel::State::next_by);

        reveal(Bank::State::next);
        reveal(Bank::State::next_by);

        match choose |step| SystemModel::State::next_by(*pre, *post, lbl, step)
        {
            SystemModel::Step::accept_request(new_bank) => { 
                broadcast use insert_new_preserves_cardinality;
                let request = lbl.arrow_AcceptRequest_req();
                assert(Self::i(post).requests =~= Self::i(pre).requests.insert(request));
                reveal(BankSpec::State::next);
                reveal(BankSpec::State::next_by);        
                assert(BankSpec::State::next_by(Self::i(pre), Self::i(post), Self::i_lbl(lbl),BankSpec::Step::request()));
            } 
            SystemModel::Step::bank_internal(new_bank) => { 
                if lbl is Execute {
                    pre.bank.execute_refines(post.bank, lbl.to_bank_lbl());
                } else {
                    pre.bank.reply_refines(post.bank, lbl.to_bank_lbl());
                }
            }
            _ => { assert(false); } 
        }
    }
}

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

impl Bank::State {
    pub open spec fn _i(self) -> BankSpec::State
    {
        BankSpec::State{
            accounts: self.account_map,
            requests: self.requests.dom(),
            replies: self.replies.dom(),
        }
    }

    closed spec fn _inv(self) -> bool
    {
        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& forall |req, reply| self.requests.contains(req) && self.replies.contains(reply) 
            ==> #[trigger] req.id != #[trigger] reply.id
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

    proof fn execute_refines(self, post: Self, lbl: Bank::Label)
        requires 
            self._inv(), 
            Self::transfer(self, post, lbl) || Self::failed_transfer(self, post, lbl)
        ensures 
            post._inv(),
            BankSpec::State::next(self._i(), post._i(), lbl.i()),
    {
        broadcast use insert_new_preserves_cardinality;
        assert(forall |req| #[trigger] post.requests.contains(req) 
            ==> self.requests.contains(req));

        assert(post._inv());
        assert(post._i().requests =~= self._i().requests.remove(lbl.arrow_ExecuteOp_req()));
        assert(post._i().replies =~= self._i().replies.insert(lbl.arrow_ExecuteOp_reply()));

        reveal(BankSpec::State::next);
        reveal(BankSpec::State::next_by);

        if Self::failed_transfer(self, post, lbl) {
            assert(BankSpec::State::next_by(self._i(), post._i(), lbl.i(), BankSpec::Step::failed_transfer()));
        } else {
            let request = lbl.arrow_ExecuteOp_req();
            let reply = lbl.arrow_ExecuteOp_reply();

            let from = request.input.from as nat;
            let to = request.input.to as nat;

            let new_from_amt = (self.account_map[from] - request.input.amt) as nat;
            let new_to_amt = (self.account_map[to] + request.input.amt) as nat;

            assert(post.account_map == self.account_map.insert(from, new_from_amt).insert(to, new_to_amt));
            assert(BankSpec::State::next_by(self._i(), post._i(), lbl.i(), BankSpec::Step::transfer()));
        }
    }

    proof fn reply_refines(self, post: Self, lbl: Bank::Label)
        requires self._inv(), Self::reply(self, post, lbl)
        ensures post._inv(), BankSpec::State::next(self._i(), post._i(), lbl.i())
    {
        reveal(BankSpec::State::next);
        reveal(BankSpec::State::next_by);

        assert(forall |r| #[trigger] post.replies.contains(r) ==> self.replies.contains(r));
        assert(post._inv());

        let reply = lbl.arrow_ReplyOp_reply();
        if (post.replies.contains(reply)) {
            assert(self.replies.count(reply) > 1);
            assert(false);
        }
        assert(post._i().replies =~= self._i().replies.remove(reply));
        assert(BankSpec::State::next_by(self._i(), post._i(), lbl.i(), BankSpec::Step::reply()));
    }
}

}