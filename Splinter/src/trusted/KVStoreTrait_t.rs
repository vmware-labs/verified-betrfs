use builtin_macros::*;

use vstd::tokens::InstanceId;

use crate::spec::SystemModel_t::*;
use crate::trusted::ClientAPI_t::*;
use crate::trusted::KVStoreTokenized_v::*;

verus!{

// Auditor contracts for the program impl 
pub trait KVStoreTrait : Sized{
    type Proof: RefinementObligation;

    spec fn wf(self) -> bool;

    // NOTE: this must return the instance of the bank, not enforced yet
    spec fn instance(self) -> InstanceId;

    fn new() -> (out: Self)
        ensures out.wf()
    ;

    fn kvstore_main(self, api: ClientAPI)
        requires 
            self.wf(),
            self.instance() == api.instance()
    ;
}

}
