#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::prelude::*;
use crate::coordination_layer::StampedMap_v::LSN;
use crate::coordination_layer::MsgHistory_v::*;
use crate::coordination_layer::AbstractJournal_v::*;
use crate::journal::PagedJournal_v::*;

verus! {

impl JournalRecord {
    pub open spec fn i(self, boundary_lsn: LSN) -> MsgHistory
    decreases self
    {
        if self.message_seq.can_discard_to(boundary_lsn)
            { self.message_seq.discard_old(boundary_lsn) } // and don't deref the prior_rec!
        else
            { Self::i_opt(*self.prior_rec, boundary_lsn).concat(self.message_seq) }
    }

    pub open spec fn i_opt(ojr: Option<Self>, boundary_lsn: LSN) -> MsgHistory
    decreases ojr
    {
        match ojr {
            None => MsgHistory::empty_history_at(boundary_lsn),
            Some(rec) => rec.i(boundary_lsn)
        }
    }

    pub proof fn cant_crop(self, bdy: LSN, depth: nat)
    requires
        self.wf(), //needed?
        0 < depth,
        self.can_crop_head_records(bdy, (depth-1) as nat),
        self.crop_head_records(bdy, (depth-1) as nat).is_Some(),
        self.crop_head_records(bdy, (depth-1) as nat).unwrap().message_seq.can_discard_to(bdy),
    ensures
        !self.can_crop_head_records(bdy, depth+1)
    decreases depth
    {
        if 1 < depth {
            if depth==2 {
                assert(self.can_crop_head_records(bdy, 1)); // requires
                assert(self.crop_head_records(bdy, 1).is_Some());   // requires
                assert(self.crop_head_records(bdy, 1)
                        == 
                    Self::opt_rec_crop_head_records(self.cropped_prior(bdy), bdy, 0));
                assert(
                    Self::opt_rec_crop_head_records(self.cropped_prior(bdy), bdy, 0)
                    == self.cropped_prior(bdy));
                assert(self.crop_head_records(bdy, 1) == self.cropped_prior(bdy));
                assert(Self::opt_rec_can_crop_head_records(
                    self.cropped_prior(bdy), bdy, 0));
//                assert(Self::opt_rec_can_crop_head_records(self.cropped_prior(bdy), bdy, 1));
//                assert(self.cropped_prior(bdy).unwrap().can_crop_head_records(bdy, 0));
//                assert(self.cropped_prior(bdy).unwrap().cropped_prior(bdy).is_Some());
//                assert(self.cropped_prior(bdy) == self.crop_head_records(bdy, 1));
                assert( self.cropped_prior(bdy).is_Some() );
            }

            assert( self.crop_head_records(bdy, (depth-1) as nat).is_Some() );
            
            assert( self.cropped_prior(bdy).is_Some() );
            assert( self.cropped_prior(bdy).unwrap().can_crop_head_records(bdy, (depth-1) as nat) );
            self.cropped_prior(bdy).unwrap().cant_crop(bdy, (depth-1) as nat);
        }
    }
}

impl TruncatedJournal {
    pub open spec fn i(self) -> MsgHistory
    {
        JournalRecord::i_opt(self.freshest_rec, self.boundary_lsn)
    }
}

impl PagedJournal::Label {
    pub open spec fn wf(self) -> bool
    {
        match self {
            PagedJournal::Label::FreezeForCommit{frozen_journal} => frozen_journal.wf(),
            _ => true,
        }
    }

    pub open spec fn i(self) -> AbstractJournal::Label
    {
        match self {
            PagedJournal::Label::ReadForRecovery{messages}
                => AbstractJournal::Label::ReadForRecoveryLabel{messages},
            PagedJournal::Label::FreezeForCommit{frozen_journal}
                => AbstractJournal::Label::FreezeForCommitLabel{frozen_journal: frozen_journal.i()},
            PagedJournal::Label::QueryEndLsn{end_lsn}
                => AbstractJournal::Label::QueryEndLsnLabel{end_lsn},
            PagedJournal::Label::Put{messages}
                => AbstractJournal::Label::PutLabel{messages},
            PagedJournal::Label::DiscardOld{start_lsn, require_end}
                => AbstractJournal::Label::DiscardOldLabel{start_lsn, require_end},
            PagedJournal::Label::Internal{}
                => AbstractJournal::Label::InternalLabel{},
        }
    }
}

impl PagedJournal::State {
    pub open spec fn i(self) -> AbstractJournal::State
    {
        AbstractJournal::State{journal: self.truncated_journal.i().concat(self.unmarshalled_tail)}
    }
}

}//verus
