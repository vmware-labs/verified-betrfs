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
    pub prior_rec: Box<Option<JournalRecord>>,
}

impl JournalRecord {
    pub open spec fn wf(self) -> bool
    decreases self
    {
        &&& self.message_seq.wf()
        &&& match *self.prior_rec {
            Some(rec) => {
                &&& rec.wf()
                &&& rec.message_seq.can_concat(self.message_seq)
            }
            None => true
        }
    }

    pub open spec fn valid(self, boundary_lsn: LSN) -> bool
    decreases self
    {
        &&& self.wf()
        &&& boundary_lsn < self.message_seq.seq_end
        &&& {
            ||| self.message_seq.can_discard_to(boundary_lsn)
            ||| match *self.prior_rec { Some(rec) => rec.valid(boundary_lsn), _ => false }
        }
    }

    pub proof fn new_boundary_valid(self, old_lsn: LSN, new_lsn: LSN)
    requires
        self.valid(old_lsn),
        old_lsn <= new_lsn,
        new_lsn < self.message_seq.seq_end,
    ensures
        self.valid(new_lsn),
    decreases self
    {
        if new_lsn < self.message_seq.seq_start {
            self.prior_rec.get_Some_0().new_boundary_valid(old_lsn, new_lsn);
        }
    }

    pub open spec fn cropped_prior(self, boundary_lsn: LSN) -> Option<JournalRecord>
    {
        if self.message_seq.seq_start <= boundary_lsn { None } else { *self.prior_rec }
    }

    pub open spec fn can_crop_head_records(self, boundary_lsn: LSN, depth: int) -> bool
    decreases (depth, 0nat)
    {
        &&& self.valid(boundary_lsn)
        &&& if depth <= 0 { true }
            else {
                Self::opt_rec_can_crop_head_records(
                    self.cropped_prior(boundary_lsn), boundary_lsn, depth-1)
            }
    }

    pub open spec fn opt_rec_can_crop_head_records(ojr: Option<JournalRecord>, boundary_lsn: LSN, depth: int) -> bool
        decreases (depth, 1nat)
    {
        match ojr {
            None => depth==0,
            Some(rec) => rec.can_crop_head_records(boundary_lsn, depth),
        }
    }

    pub open spec fn crop_head_records(self, boundary_lsn: LSN, depth: int) -> Option<JournalRecord>
    recommends
        self.can_crop_head_records(boundary_lsn, depth)
    decreases (depth, 0nat)
    {
        // < case can't happen, but need to mention it to get termination.
        if depth <= 0 { Some(self) }
        else {
            Self::opt_rec_crop_head_records(self.cropped_prior(boundary_lsn), boundary_lsn, depth-1)
        }
    }

    pub open spec fn opt_rec_crop_head_records(ojr: Option<JournalRecord>, boundary_lsn: LSN, depth: int) -> Option<JournalRecord>
    recommends
        Self::opt_rec_can_crop_head_records(ojr, boundary_lsn, depth)
    // ensures no longer available; becomes lemma?
    decreases (depth, 1nat)
    {
        match ojr {
            None => None,
            Some(rec) => rec.crop_head_records(boundary_lsn, depth)
        }
    }

    pub proof fn can_crop_monotonic(self, boundary_lsn: LSN, depth: int, more: int)
    requires
        0 <= depth < more,
        self.can_crop_head_records(boundary_lsn, more)
    ensures
        self.can_crop_head_records(boundary_lsn, depth)
    decreases depth
    {
        if 0<depth {
            self.cropped_prior(boundary_lsn).get_Some_0().can_crop_monotonic(boundary_lsn, depth-1, more-1);
        }
    }

    pub proof fn can_crop_more_yields_some(self, boundary_lsn: LSN, depth: int, more: int)
    requires
        0 <= depth < more,
        self.can_crop_head_records(boundary_lsn, more)
    ensures
        //self.can_crop_head_records(boundary_lsn, depth) // 
        self.crop_head_records(boundary_lsn, depth).is_Some(),
    decreases depth
    {
        self.can_crop_monotonic(boundary_lsn, depth, more);
        if 0<depth {
            self.cropped_prior(boundary_lsn).get_Some_0().can_crop_more_yields_some(boundary_lsn, depth-1, more-1);
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
