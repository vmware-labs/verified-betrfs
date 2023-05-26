// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::coordination_layer::StampedMap_v::LSN;
use crate::coordination_layer::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::journal::PagedJournal_v;
use crate::journal::PagedJournal_v::PagedJournal;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::*;

verus!{

// impl JournalRecord {
//     pub open spec fn i(self) -> PagedJournal_v::JournalRecord {
//     }
// }

impl TruncatedJournal {

    pub open spec fn iptr(dv: DiskView, ptr: Pointer) -> (out: Box<Option<PagedJournal_v::JournalRecord>>)
    recommends
        dv.decodable(ptr),
        dv.acyclic(),
    // ensures
        // dv.block_in_bounds(ptr),
        // out.is_Some() ==> out.unwrape().valid(dv.boundary_lsn)
    decreases dv.the_rank_of(ptr)
    {
        decreases_when(dv.decodable(ptr) && dv.acyclic());  // can't we just use the recommends?
        match ptr {
            None => Box::new(None),
            Some(addr) => {
                let jr = dv.entries[addr];
                Box::new(Some(PagedJournal_v::JournalRecord{
                    message_seq: jr.message_seq,
                    prior_rec: Self::iptr(dv, jr.cropped_prior(dv.boundary_lsn)),
                }))
            }
        }
    }

    pub open spec fn i(self) -> (out: PagedJournal_v::TruncatedJournal)
    recommends
        self.decodable(),
    // ensures out.wf()
    {
        PagedJournal_v::TruncatedJournal{
            boundary_lsn: self.disk_view.boundary_lsn,
            freshest_rec: *Self::iptr(self.disk_view, self.freshest_rec),
        }
    }
}

impl LinkedJournal::Label {

    pub open spec fn i(self) -> PagedJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} => PagedJournal::Label::ReadForRecovery{messages},
            Self::FreezeForCommit{frozen_journal} => PagedJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.i()},
            Self::QueryEndLsn{end_lsn} => PagedJournal::Label::QueryEndLsn{end_lsn},
            Self::Put{messages} => PagedJournal::Label::Put{messages},
            Self::DiscardOld{start_lsn, require_end} => PagedJournal::Label::DiscardOld{start_lsn, require_end},
            Self::Internal{} => PagedJournal::Label::Internal{},
        }
    }

}

} // verus!
