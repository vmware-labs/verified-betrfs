use builtin::*;
use builtin_macros::*;
use std::sync::atomic::{AtomicU64};

use crate::Bank_v::Bank;
use crate::BankContract_t::*; 
use crate::ClientAPI_t::*;

verus!{
    pub open spec fn test() -> bool
    {
        true
    }

    #[verifier::external_body]
    pub fn new_api(instance: Ghost<Bank::Instance>) -> (out: TrustedAPI)
        ensures out.instance() == instance
    {
        TrustedAPI{id: AtomicU64::new(0)}
    }

    pub fn entry<T: BankTrait>() {
        let bank = T::new();
        let api = new_api(Ghost(bank.instance()));
        bank.bank_main(api);
    }
}
