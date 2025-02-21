// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{LinkedJournal, TruncatedJournal};
use crate::allocation_layer::LikesJournal_v::*;

verus!{

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl LikesJournal::State {
    pub open spec(checked) fn i(self) -> LinkedJournal::State
    recommends self.journal.truncated_journal.decodable()
    {
        self.journal
    }

    pub proof fn freeze_for_commit_refines(self, post: Self, lbl: LikesJournal::Label, depth: nat)
    requires 
        self.inv(), 
        post.inv(),
        Self::freeze_for_commit(self, post, lbl, depth)
    ensures 
        LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), 
            LinkedJournal::Step::freeze_for_commit(depth))
    {
        reveal(LinkedJournal::State::next_by);

        let fj = lbl->frozen_journal;
        let tj = self.journal.truncated_journal;
        let new_bdy = fj.seq_start();

        let cropped_tj = tj.crop(depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);

        let post_discard = cropped_tj.discard_old(new_bdy);
        let post_tight = post_discard.build_tight();
        
        cropped_tj.discard_old_decodable(new_bdy);
//        assert(post_discard.disk_view.acyclic()); 

        post_discard.disk_view.build_tight_ensures(post_discard.freshest_rec);
        post_discard.disk_view.build_tight_domain_is_build_lsn_addr_index_range(post_discard.freshest_rec);

        let tj_sub_index = tj.disk_view.build_lsn_addr_index(post_discard.freshest_rec);
        let post_discard_repr = post_discard.disk_view.build_lsn_addr_index(post_discard.freshest_rec);

        if post_discard.freshest_rec is Some {
            tj.disk_view.pointer_after_crop_seq_end(tj.freshest_rec, depth);
//            assert(post_discard.seq_end() <= tj.seq_end());

            let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < post_discard.seq_end());
            let frozen_index = self.lsn_addr_index.restrict(frozen_lsns);

            tj.build_lsn_addr_index_ensures();
            post_discard.build_lsn_addr_index_ensures();

            assert(post_discard_repr.dom() =~= frozen_index.dom()) by {
                reveal(TruncatedJournal::index_domain_valid); 
            }

            tj.disk_view.cropped_ptr_build_sub_index(tj.freshest_rec, post_discard.freshest_rec, depth);
//            assert(tj_sub_index <= self.lsn_addr_index);

            post_discard.disk_view.sub_disk_with_newer_lsn_repr_index(tj.disk_view, post_discard.freshest_rec);
//            assert(post_discard_repr <= tj_sub_index);

            assert forall |lsn| #[trigger] post_discard_repr.contains_key(lsn)
            implies post_discard_repr[lsn] == self.lsn_addr_index[lsn]
            by {
                assert(tj_sub_index.contains_key(lsn));
            }
//            assert(post_discard_repr <= self.lsn_addr_index);
            assert(frozen_index =~= post_discard_repr);
//            assert(cropped_tj.valid_discard_old(new_bdy, fj));
        }
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

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;

        let post_discard = tj_pre.discard_old(start_lsn);
        let post_tight = post_discard.build_tight();

//        assert(tj_post.wf());
//        assert(tj_post.freshest_rec == post_discard.freshest_rec);
//        assert(tj_post.disk_view.is_sub_disk(post_discard.disk_view)); // new must be a subset of original

        tj_pre.discard_old_decodable(start_lsn);
//        assert(post_discard.disk_view.acyclic()); 

        post_discard.disk_view.build_tight_ensures(post_discard.freshest_rec);
        post_discard.disk_view.tight_sub_disk(post_discard.freshest_rec, post_tight.disk_view);
//        assert(post_tight.disk_view.acyclic()); 

        // post_tight has the same build_lsn_addr_index as post_discard and as tj_post
        post_tight.disk_view.sub_disk_repr_index(post_discard.disk_view, post_discard.freshest_rec);
        tj_post.disk_view.sub_disk_repr_index(post_discard.disk_view, post_discard.freshest_rec);
//        assert(post_tight.disk_view.build_lsn_addr_index(post_discard.freshest_rec) == post.lsn_addr_index);
//        assert(post.lsn_addr_index.values() <= tj_post.disk_view.entries.dom());

        post_discard.disk_view.build_tight_domain_is_build_lsn_addr_index_range(post_discard.freshest_rec);
//        assert(post_tight.disk_view.entries.dom() <= tj_post.disk_view.entries.dom());
//        assert(post_tight.disk_view.entries <= tj_post.disk_view.entries);
//        assert(post_discard.freshest_rec == tj_post.freshest_rec);

//        assert(post_tight.disk_view.is_sub_disk(tj_post.disk_view));   // tight must be fully contained by new
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
            LikesJournal::Step::read_for_recovery() => {},
            LikesJournal::Step::freeze_for_commit(depth) => {
                self.freeze_for_commit_refines(post, lbl, depth);
            },
            LikesJournal::Step::query_end_lsn() => {},
            LikesJournal::Step::put(..) => {},
            LikesJournal::Step::discard_old(new_journal) => {
                self.discard_old_refines(post, lbl, new_journal);
            },
            LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
//                assert(LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::internal_journal_marshal(cut, addr)));
            },
            _ => {
                assert( LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::internal_no_op()) );
            },
        }
    }

    pub proof fn init_refines(self, truncated_journal: TruncatedJournal) 
    requires LikesJournal::State::initialize(self, truncated_journal)
    ensures LinkedJournal::State::initialize(self.i(), truncated_journal)
    {
    }
}

} // verus!
