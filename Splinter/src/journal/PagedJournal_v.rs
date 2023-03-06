#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::pervasive::prelude::*;
use crate::coordination_layer::StampedMap_v::LSN;
use crate::coordination_layer::MsgHistory_v::*;
use crate::coordination_layer::AbstractJournal_v::*;

verus! {

pub struct JournalRecord {
    pub message_seq: MsgHistory,
    pub prior_rec: Option<Box<JournalRecord>>,
}

impl JournalRecord {
    pub open spec fn wf(self) -> bool
    decreases self
    {
        &&& self.message_seq.wf()
        &&& match self.prior_rec {
            Some(rec) => {
                &&& rec.wf()
                &&& rec.message_seq.can_concat(self.message_seq)
            }
            None => true
        }
    }

}

// A TruncatedJournal is some long chain but which we ignore beyond the boundaryLSN
// (because we have a map telling us that part of the history).
// In the refinement layer below, we'll have some situations where the disk has extra
// journal records, but we'll ignore them in the refinement (since we never read them)
// and instead supply a None? for the interpretation at this layer.
// That's what keeps us out of trouble when those un-read pages get reclaimed -- we don't
// want to have to say we can interpret them.
pub struct TruncatedJournal {
    pub boundary_lsn: LSN,  // exclusive: lsns <= boundaryLSN are discarded
    pub freshest_rec: Option<JournalRecord>,
}

impl TruncatedJournal {

}

#[is_variant]
enum TransitionLabel
{
    ReadForRecoveryLabel{messages: MsgHistory},
    FreezeForCommitLabel{frozenJournal: TruncatedJournal},
    QueryEndLsnLabel{endLsn: LSN},
    PutLabel{messages: MsgHistory},
    DiscardOldLabel{startLsn: LSN, requireEnd: LSN},
    InternalLabel{},   // Local No-op label
}

state_machine!{ PagedJournal {
    fields {
    }
}}   // state_machine

}   // verus
