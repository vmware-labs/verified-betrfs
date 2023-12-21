// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{LinkedJournal, DiskView, TruncatedJournal};
use crate::journal::LikesJournal_v;
use crate::journal::LikesJournal_v::*;

verus!{

impl LikesJournal::Label {
    pub open spec /*(checked)*/ fn i(self) -> LinkedJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} =>
                LinkedJournal::Label::ReadForRecovery{messages},
            Self::FreezeForCommit{frozen_journal} =>
                LinkedJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.build_tight()},
            Self::QueryEndLsn{end_lsn} =>
                LinkedJournal::Label::QueryEndLsn{end_lsn},
            Self::Put{messages} =>
                LinkedJournal::Label::Put{messages},
            Self::DiscardOld{start_lsn, require_end} =>
                LinkedJournal::Label::DiscardOld{start_lsn, require_end},
            Self::Internal{} =>
                LinkedJournal::Label::Internal{},
        }
    }
}

impl DiskView {


}

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl LikesJournal::State {
    pub open spec(checked) fn i(self) -> LinkedJournal::State
    recommends self.journal.truncated_journal.decodable()
    {
        LinkedJournal::State{ 
            truncated_journal: self.journal.truncated_journal.build_tight(), 
            unmarshalled_tail: self.journal.unmarshalled_tail 
        }
    }

    pub proof fn i_preserves_decodable(self)
    requires 
        self.journal.truncated_journal.decodable()
    ensures
        self.i().truncated_journal.decodable(),
        self.i().truncated_journal.disk_view.is_sub_disk(self.journal.truncated_journal.disk_view)
    {
        let tj = self.journal.truncated_journal;
        tj.disk_view.build_tight_is_awesome(tj.freshest_rec);
    }

    pub proof fn read_for_recovery_refines(self, post: Self, lbl: LikesJournal::Label, depth: nat)
    requires 
        self.inv(), 
        post.inv(), 
        Self::read_for_recovery(self, post, lbl, depth)
    ensures 
        LinkedJournal::State::next_by(self.i(), post.i(), lbl.i(), LinkedJournal::Step::read_for_recovery(depth))
    {
        reveal(LinkedJournal::State::next_by);

        self.i_preserves_decodable();

        // assert(self.i().wf());
        // assert(LinkedJournal::State::lbl_wf(lbl.i()));
        // assert(self.i().truncated_journal.decodable());
        let dv = self.i().truncated_journal.disk_view;

        // need to show can_crop on a non tight disk is also true on a tight disk
        assert(self.journal.truncated_journal.disk_view.can_crop(self.journal.truncated_journal.freshest_rec, depth));

        // assert(dv.can_crop(self.journal.truncated_journal.freshest_rec, depth);
        // let ptr = dv.pointer_after_crop(pre.truncated_journal.freshest_rec, depth);
        // require ptr.is_Some();
        // require dv.entries[ptr.unwrap()].message_seq.maybe_discard_old(dv.boundary_lsn) == lbl.get_ReadForRecovery_messages();


        assume(false);
    }

    pub proof fn next_refines(self, post: Self, lbl: LikesJournal::Label)
    requires
        self.inv(),
        post.inv(),
        LikesJournal::State::next(self, post, lbl),
    ensures
        LinkedJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        // unfortunate defaults
        reveal(LinkedJournal::State::next);
        reveal(LinkedJournal::State::next_by);
        reveal(LikesJournal::State::next);
        reveal(LikesJournal::State::next_by);  

        self.i_preserves_decodable();
        // post.i_preserves_decodable();

        let step = choose |step| LikesJournal::State::next_by(self, post, lbl, step);
        match step {
            LikesJournal::Step::read_for_recovery(depth) => {
                self.read_for_recovery_refines(post, lbl, depth);
            },
            LikesJournal::Step::freeze_for_commit(depth) => {
                assume( LinkedJournal::State::next_by(self.i(), post.i(), lbl.i(), LinkedJournal::Step::freeze_for_commit(depth)) );
            },
            LikesJournal::Step::query_end_lsn() => {
                assert( LinkedJournal::State::next_by(self.i(), post.i(), lbl.i(), LinkedJournal::Step::query_end_lsn()) );
            },
            LikesJournal::Step::put(new_journal) => {
                assume( LinkedJournal::State::next_by(self.i(), post.i(), lbl.i(), LinkedJournal::Step::put()) );
            },
            LikesJournal::Step::discard_old(new_journal) => {
                assume( LinkedJournal::State::next_by(self.i(), post.i(), lbl.i(), LinkedJournal::Step::discard_old()) );
            },
            LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
                assume( LinkedJournal::State::next_by(self.i(), post.i(), lbl.i(), LinkedJournal::Step::internal_journal_marshal(cut, addr)) );
            },
            _ => {
                assert( LinkedJournal::State::next_by(self.i(), post.i(), lbl.i(), LinkedJournal::Step::internal_no_op()) );
            },
        }
    }
}


} // verus!
