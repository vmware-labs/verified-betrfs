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

impl DiskView {
}

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl LikesJournal::State {
    pub open spec(checked) fn i(self) -> LinkedJournal::State
    recommends self.journal.truncated_journal.decodable()
    {
        self.journal
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: LikesJournal::Label, new_journal: LinkedJournal_v::LinkedJournal::State)
    requires 
        self.inv(), 
        post.inv(),
        Self::discard_old(self, post, lbl, new_journal)
    ensures 
        LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), 
            LinkedJournal::Step::discard_old(new_journal.truncated_journal))
    {
        reveal(LinkedJournal::State::next_by);

        let tj_pre = self.journal.truncated_journal;
        let tj_post = post.journal.truncated_journal;

        let start_lsn = lbl.get_DiscardOld_start_lsn();
        let require_end = lbl.get_DiscardOld_require_end();

        let post_discard = tj_pre.discard_old(start_lsn);
        let post_tight = post_discard.build_tight();

        assert(tj_post.wf());
        assert(tj_post.freshest_rec == post_discard.freshest_rec);
        assert(tj_post.disk_view.is_sub_disk(post_discard.disk_view)); // new must be a subset of original

        tj_pre.discard_old_decodable(start_lsn);
        assert(post_discard.disk_view.acyclic()); 

        post_discard.disk_view.build_tight_ensures(post_discard.freshest_rec);
        post_discard.disk_view.tight_sub_disk(post_discard.freshest_rec, post_tight.disk_view);
        assert(post_tight.disk_view.acyclic()); 

        // post_tight has the same build_lsn_addr_index as post_discard and as tj_post
        post_tight.disk_view.sub_disk_repr_index(post_discard.disk_view, post_discard.freshest_rec);
        tj_post.disk_view.sub_disk_repr_index(post_discard.disk_view, post_discard.freshest_rec);
        assert(post_tight.disk_view.build_lsn_addr_index(post_discard.freshest_rec) == post.lsn_addr_index);
        assert(post.lsn_addr_index.values() <= tj_post.disk_view.entries.dom());

        post_discard.disk_view.build_tight_domain_is_build_lsn_addr_index_range(post_discard.freshest_rec);
        assert(post_tight.disk_view.entries.dom() <= tj_post.disk_view.entries.dom());
        assert(post_tight.disk_view.entries <= tj_post.disk_view.entries);
        assert(post_discard.freshest_rec == tj_post.freshest_rec);

        assert(post_tight.disk_view.is_sub_disk(tj_post.disk_view));   // tight must be fully contained by new
    }

    pub proof fn next_refines(self, post: Self, lbl: LikesJournal::Label)
    requires
        self.inv(),
        post.inv(),
        LikesJournal::State::next(self, post, lbl),
    ensures
        LinkedJournal::State::next(self.i(), post.i(), Self::lbl_i(lbl)),
    {
        // unfortunate defaults
        reveal(LinkedJournal::State::next);
        reveal(LinkedJournal::State::next_by);
        reveal(LikesJournal::State::next);
        reveal(LikesJournal::State::next_by);  

        let step = choose |step| LikesJournal::State::next_by(self, post, lbl, step);
        match step {
            LikesJournal::Step::read_for_recovery(depth) => {
                assert(LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::read_for_recovery(depth)));
            },
            LikesJournal::Step::freeze_for_commit(depth) => {
                assert( LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::freeze_for_commit(depth)) );
            },
            LikesJournal::Step::query_end_lsn() => {
                assert( LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::query_end_lsn()) );
            },
            LikesJournal::Step::put(new_journal) => {
                assert(LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::put()));
            },
            LikesJournal::Step::discard_old(new_journal) => {
                self.discard_old_refines(post, lbl, new_journal);
            },
            LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
                assert(LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), 
                    LinkedJournal::Step::internal_journal_marshal(cut, addr)));
            },
            _ => {
                assert( LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::internal_no_op()) );
            },
        }
    }
}


} // verus!
