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
    pub proof fn sub_disk_crop_implies(self, big: DiskView, root: Pointer, depth: nat)
    requires
        self.decodable(root),
        self.block_in_bounds(root),
        self.can_crop(root, depth),
        big.decodable(root),
        self.is_sub_disk(big),
    ensures 
        big.can_crop(root, depth),
        big.pointer_after_crop(root, depth) == self.pointer_after_crop(root, depth),
    decreases depth
    {
        if 0 < depth {
            self.sub_disk_crop_implies(big, self.next(root), (depth-1) as nat);
        }
    }

    pub proof fn build_tight_preserves_crop(self, root: Pointer, depth: nat)
    requires 
        self.buildable(root),
        self.block_in_bounds(root),
        self.can_crop(root, depth),
    ensures
        self.build_tight(root).can_crop(root, depth),
        self.build_tight(root).pointer_after_crop(root, depth) == self.pointer_after_crop(root, depth)
    decreases
        depth
    {
        if 0 < depth {
            let tight_dv = self.build_tight(root);
            let tight_dv_tail = self.build_tight(self.next(root));
    
            self.build_tight_builds_sub_disks(root);
            self.build_tight_preserves_crop(self.next(root), (depth-1) as nat);

            self.build_tight_shape(root);
            if self.next(root) is Some {
                self.tight_sub_disk(self.next(root), tight_dv_tail);
                tight_dv_tail.sub_disk_crop_implies(tight_dv, self.next(root), (depth-1) as nat);
            }

            assert(tight_dv.can_crop(self.next(root), (depth-1) as nat));
            assert(tight_dv.can_crop(root, depth));
            assert(tight_dv.pointer_after_crop(root, depth) == self.pointer_after_crop(root, depth));
        }
    }
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
        let tj = self.journal.truncated_journal;
        let dv = self.i().truncated_journal.disk_view;

        tj.disk_view.build_tight_preserves_crop(tj.freshest_rec, depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);
        dv.pointer_after_crop_ensures(tj.freshest_rec, depth);
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
