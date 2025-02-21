use builtin_macros::*;
use builtin::*;
use vstd::prelude::arbitrary;

use vstd::tokens::InstanceId;
use crate::spec::SystemModel_t::*;
use crate::trusted::ClientAPI_t::*;
use crate::trusted::KVStoreTokenized_v::*;

verus!{

// Auditor contracts for the program impl 
pub trait KVStoreTrait : Sized{
    type Proof: RefinementObligation;

    spec fn wf_init(self) -> bool;

    // NOTE: this must return the instance of the KVStoreTokenized, not enforced yet
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

// This should only be true for the specific RefinementObligation!
// Here I'm also narrowly specializing to a particular set of available tokens.
// pub proof fn open_system_invariant<RO: RefinementObligation>(
//     atomic_state_token: Tracked<KVStoreTokenized::atomic_state>,
//     disk_responses_token: Tracked<KVStoreTokenized::disk_responses_multiset>,
//     ) -> (model: SystemModel::State<RO::Model>)
// ensures
//     RO::inv(model),
//     model.program.state == atomic_state_token@.value(),
//     forall |id,disk_response| disk_responses_token@.multiset().contains((id, disk_response))
//         ==> (model.disk.responses.dom().contains(id) && model.disk.responses[id] == disk_response),
// {
//     arbitrary()
// }

}
