use builtin::*;
use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{set::*};
use crate::Bank_v::Bank;
use crate::BankSpec_t::*;
use crate::ClientAPI_t::*;

verus!{

// Auditor defines externally visible actions that can be taken by a program model
pub enum BankLabel{
    // async operations with application clients
    AcceptRequest{req: Request},
    DeliverReply{reply: Reply},
    // declares the linearization point of each operation
    Execute{req: Request, reply: Reply},
}

// Auditor defines the operations that must be implemented by the bank program trait
pub trait BankModel {
    spec fn init(bank: &Self, total_accounts: nat, initial_value: nat) -> bool;
    spec fn next(pre: &Self, post: &Self, lbl: BankLabel) -> bool;
}

// trait restrained tokenized SM

// trait for bank tokenized SM

// Auditor defined system model
state_machine!{SystemModel<T: BankModel>{
    fields {
        pub bank: T,
        pub id_history: Set<ReqID>,
    }

    pub type Label = BankLabel;

    init!{ initialize(bank: T, total_accounts: nat, initial_value: nat) {
        require T::init(&bank, total_accounts, initial_value);
        init bank = bank;
        init id_history = Set::empty();
    }}

    transition!{ accept_request(lbl: Label, new_bank: T) {
        require let BankLabel::AcceptRequest{ req } = lbl;
        // promise made by the auditor, supplied by ClientAPI_t impl
        require !pre.id_history.contains(req.id);
        require T::next(&pre.bank, &new_bank, lbl);

        update bank = new_bank;
        update id_history = pre.id_history.insert(req.id);
    }}

    transition!{ bank_internal(lbl: Label, new_bank: T) {
        require !(lbl is AcceptRequest);
        require T::next(&pre.bank, &new_bank, lbl);
        update bank = new_bank;
    }}
}}

// Auditor restrict the externally visible label's correspondance to the top level spec labels
// this example is simple enough to simply provide the i_lbl, but we are writing it out in a more general form
impl SystemModel::Label {
    pub open spec fn label_correspondance(self, spec_lbl: BankSpec::Label) -> bool
    {
        &&& self is AcceptRequest <==> spec_lbl is RequestOp
        &&& self is DeliverReply <==> spec_lbl is ReplyOp
        &&& self is Execute <==> spec_lbl is ExecuteOp
        &&& match self {
            Self::AcceptRequest{req} => spec_lbl.arrow_RequestOp_req() == req,
            Self::Execute{req, reply} => spec_lbl.arrow_ExecuteOp_req() == req && spec_lbl.arrow_ExecuteOp_reply() == reply,
            Self::DeliverReply{reply} => spec_lbl.arrow_ReplyOp_reply() == reply,
        }
    }
}

pub trait RefinementObligations {
    type Model: BankModel;

    spec fn inv(model: &SystemModel::State<Self::Model>) -> bool;

    spec fn i(model: &SystemModel::State<Self::Model>) -> BankSpec::State;

    spec fn i_lbl(lbl: SystemModel::Label) -> (result: BankSpec::Label);

    // restrict i_lbl result to ensure app label correspondence 
    proof fn i_lbl_valid(lbl: SystemModel::Label, result: BankSpec::Label)
        requires result == Self::i_lbl(lbl)            
        ensures lbl.label_correspondance(result)
    ;

    proof fn init_refines(pre: &SystemModel::State<Self::Model>, total_accounts: nat, initial_value: nat)
        requires SystemModel::State::initialize(*pre, pre.bank, total_accounts, initial_value)
        ensures BankSpec::State::initialize(Self::i(pre), total_accounts, initial_value), Self::inv(pre)
    ;

    proof fn next_refines(pre: &SystemModel::State<Self::Model>, post: &SystemModel::State<Self::Model>, lbl: BankLabel)
        requires SystemModel::State::next(*pre, *post, lbl), Self::inv(pre)
        ensures BankSpec::State::next(Self::i(pre), Self::i(post), Self::i_lbl(lbl)), Self::inv(post)
    ;
}

// Auditor contracts for the program impl 
pub trait BankTrait : Sized{
    type Proof: RefinementObligations;

    spec fn wf(&self) -> bool;

    // NOTE: this must return the instance of the bank, not enforced yet
    spec fn instance(&self) -> Bank::Instance;

    fn new() -> (out: Self)
        ensures out.wf()
    ;

    fn bank_main(self, api: TrustedAPI)
        requires 
            self.wf(),
            self.instance() == api.instance()
    ;
}
}