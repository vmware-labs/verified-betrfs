use builtin_macros::*;
use builtin::*;
use vstd::prelude::arbitrary;
use vstd::prelude::ValueToken;

use vstd::tokens::InstanceId;
use crate::trusted::ProgramModelTrait_t::*;
use crate::trusted::RefinementObligation_t::*;
use crate::trusted::ClientAPI_t::*;
use crate::trusted::KVStoreTokenized_t::*;
use crate::trusted::SystemModel_t::*;

verus!{

// Auditor contracts for the program impl 
pub trait KVStoreTrait : Sized{

    type ProgramModel: ProgramModelTrait;
    type Proof: RefinementObligation<Self::ProgramModel>;

    spec fn wf_init(self) -> bool;

    // NOTE: this must return the instance of the KVStoreTokenized, not enforced yet
    spec fn instance_id(self) -> InstanceId;

    fn new() -> (out: Self)
        ensures out.wf_init()
    ;

    fn kvstore_main(&mut self, api: ClientAPI<Self::ProgramModel>)
        requires 
            old(self).wf_init(),
            old(self).instance_id() == api.instance_id()
    ;
}

// Auditor promise
// This should only be true for the specific RefinementObligation!
// Here I'm also narrowly specializing to a particular set of available tokens.
pub proof fn open_system_invariant<ProgramModel: ProgramModelTrait, Proof: RefinementObligation<ProgramModel>>(
    model_token: Tracked<KVStoreTokenized::model<ProgramModel>>,
    disk_responses_token: Tracked<KVStoreTokenized::disk_responses_multiset<ProgramModel>>,
    ) -> (model: SystemModel::State<ProgramModel>)
ensures
    Proof::inv(model),
    model.program == model_token@.value(),
    forall |id,disk_response| #[trigger] disk_responses_token@.multiset().contains((id, disk_response))
        ==> (model.disk.responses.dom().contains(id) && model.disk.responses[id] == disk_response),
{
    assume(false);
    arbitrary()
}


}
