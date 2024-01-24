// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

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
use crate::journal::LikesJournal_v::{LikesJournal};
use crate::allocation_layer::AllocationJournal_v;
use crate::allocation_layer::AllocationJournal_v::*;

verus!{

impl AllocationJournal::Step {
    proof fn i(self) -> LikesJournal::Step {
        match self {
            Self::read_for_recovery() =>
                LikesJournal::Step::read_for_recovery(),
            Self::freeze_for_commit() =>
                LikesJournal::Step::freeze_for_commit(),
            Self::query_end_lsn() =>
                LikesJournal::Step::query_end_lsn(),
            Self::put(new_journal) =>
                LikesJournal::Step::put(new_journal),
            Self::discard_old(new_journal) =>
                LikesJournal::Step::discard_old(new_journal),
            Self::internal_journal_marshal(cut, addr, new_journal) =>
                LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal),
            Self::internal_mini_allocator_fill() =>
                LikesJournal::Step::internal_no_op(),
            Self::internal_mini_allocator_prune() =>
                LikesJournal::Step::internal_no_op(),
            Self::internal_no_op() =>
                LikesJournal::Step::internal_no_op(),
            _ => { arbitrary() },   // TODO(travis): wart on the state machine language
        }
    }
}

impl AllocationJournal::Label {
    pub open spec(checked) fn i(self) -> LikesJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} =>
                LikesJournal::Label::ReadForRecovery{messages},
            Self::FreezeForCommit{frozen_journal} =>
                LikesJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.tj},
            Self::QueryEndLsn{end_lsn} =>
                LikesJournal::Label::QueryEndLsn{end_lsn},
            Self::Put{messages} =>
                LikesJournal::Label::Put{messages},
            Self::DiscardOld{start_lsn, require_end, deallocs} =>
                LikesJournal::Label::DiscardOld{start_lsn, require_end},
            Self::InternalAllocations{allocs, deallocs} =>
                LikesJournal::Label::Internal{},
        }
    }
}

impl DiskView{
    // TODO(jonh): this lemma should just be an ensures on build_lsn_au_index_page_walk.
    pub proof fn build_lsn_au_index_page_walk_consistency(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
    ensures
        self.build_lsn_addr_index(root).dom() =~= self.build_lsn_au_index_page_walk(root).dom(),
        forall |lsn| self.build_lsn_addr_index(root).contains_key(lsn) ==>
            #[trigger] self.build_lsn_addr_index(root)[lsn].au == self.build_lsn_au_index_page_walk(root)[lsn]
    decreases self.the_rank_of(root)
    {
        if root.is_Some() {
            self.build_lsn_au_index_page_walk_consistency(self.next(root));
        }
    }
}

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl AllocationJournal::State {
    pub open spec(checked) fn i(self) -> LikesJournal::State
        recommends self.tj().decodable()
    {
        LikesJournal::State{
            journal: self.journal,
            lsn_addr_index: self.tj().build_lsn_addr_index()
        }
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: AllocationJournal::Label, new_journal: LinkedJournal::State)
        requires self.inv(), post.inv(), Self::discard_old(self, post, lbl, new_journal)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::discard_old(new_journal))
    {
        reveal(LikesJournal::State::next_by);
        assert(post.i().journal == new_journal);

        let start_lsn = lbl.get_DiscardOld_start_lsn();
        let require_end = lbl.get_DiscardOld_require_end();
        let keep_addrs = Set::new(|addr: Address| addr.wf() && post.lsn_au_index.values().contains(addr.au));

        let lsn_addr_index_post = LikesJournal_v::lsn_addr_index_discard_up_to(self.i().lsn_addr_index, start_lsn);
        let i_keep_addrs = lsn_addr_index_post.values();

        reveal(TruncatedJournal::index_domain_valid);

        if self.tj().freshest_rec is Some {
            self.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }

        post.tj().disk_view.sub_disk_with_newer_lsn_repr_index(self.tj().disk_view, post.tj().freshest_rec);
        assert(post.i().lsn_addr_index <= self.i().lsn_addr_index);

        LikesJournal_v::lsn_addr_index_discard_up_to_ensures(self.i().lsn_addr_index, start_lsn);
        assert(lsn_addr_index_post <= self.i().lsn_addr_index);

        if post.tj().freshest_rec is Some {
            post.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }

        assert(post.i().lsn_addr_index =~= lsn_addr_index_post);
        assert(self.lsn_au_index == self.tj().build_lsn_au_index(self.first));

        self.tj().disk_view.build_lsn_au_index_equiv_page_walk(self.tj().freshest_rec, self.first);
        self.tj().disk_view.build_lsn_au_index_page_walk_consistency(self.tj().freshest_rec);
        self.tj().disk_view.build_lsn_addr_index_reflects_disk_view(self.tj().freshest_rec);
        assert(i_keep_addrs <= keep_addrs);

        assert(self.tj().discard_old_cond(start_lsn, i_keep_addrs, new_journal.truncated_journal));
    }

    pub proof fn internal_journal_marshal_refines(self, post: Self, lbl: AllocationJournal::Label, 
        cut: LSN, addr: Address, new_journal: LinkedJournal::State)
        requires self.inv(), post.inv(), Self::internal_journal_marshal(self, post, lbl, cut, addr, new_journal)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal))
    {
        reveal(LikesJournal::State::next_by);
        reveal(LinkedJournal::State::next_by);

        assert( LinkedJournal_v::LinkedJournal::State::next_by(self.journal, new_journal, 
            Self::linked_lbl(lbl), LinkedJournal_v::LinkedJournal::Step::internal_journal_marshal(cut, addr)) );

        let post_addr_index = LikesJournal_v::lsn_addr_index_append_record(
            self.i().lsn_addr_index,
            self.journal.unmarshalled_tail.discard_recent(cut),
            addr
        );

        self.tj().disk_view.sub_disk_repr_index(post.tj().disk_view, self.tj().freshest_rec);
        assert(post_addr_index == post.i().lsn_addr_index);
    }

    pub proof fn next_refines(self, post: Self, lbl: AllocationJournal::Label)
    requires
        self.inv(),
        post.inv(),
        AllocationJournal::State::next(self, post, lbl),
    ensures
        LikesJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(LikesJournal::State::next_by);  // unfortunate defaults
        reveal(LikesJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(AllocationJournal::State::next);

        let step = choose |step| AllocationJournal::State::next_by(self, post, lbl, step);
        match step {
            AllocationJournal::Step::read_for_recovery() => {
                assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::read_for_recovery()) );
            },
            AllocationJournal::Step::freeze_for_commit() => {
                assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::freeze_for_commit()) );
            },
            AllocationJournal::Step::query_end_lsn() => {
                assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::query_end_lsn()) );
            },
            AllocationJournal::Step::put(new_journal) => {
                reveal(LinkedJournal::State::next);
                reveal(LinkedJournal::State::next_by);
                assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::put(new_journal)) );
            },
            AllocationJournal::Step::discard_old(new_journal) => {
                self.discard_old_refines(post, lbl, new_journal);
            },
            AllocationJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
                self.internal_journal_marshal_refines(post, lbl, cut, addr, new_journal);
            },
            _ => {
                assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::internal_no_op()) );
            },
        }
    }
}


} // verus!
