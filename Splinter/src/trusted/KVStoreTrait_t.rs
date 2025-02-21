use builtin_macros::*;
use builtin::*;

use vstd::tokens::InstanceId;
use crate::spec::SystemModel_t::*;
use crate::trusted::ClientAPI_t::*;

verus!{

// Auditor contracts for the program impl 
pub trait KVStoreTrait : Sized{
    type Proof: RefinementObligation;

    spec fn wf_init(self) -> bool;

    // NOTE: this must return the instance of the bank, not enforced yet
    spec fn instance_id(self) -> InstanceId;

    fn new() -> (out: Self)
        ensures out.wf_init()
    ;

    fn kvstore_main(&mut self, api: ClientAPI)
        requires 
            old(self).wf_init(),
            old(self).instance_id() == api.instance_id()
    ;
}

}
