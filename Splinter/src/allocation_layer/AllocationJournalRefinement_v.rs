// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin_macros::*;
use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v::{LinkedJournal, DiskView, TruncatedJournal};
use crate::allocation_layer::LikesJournal_v;
use crate::allocation_layer::LikesJournal_v::{LikesJournal};
use crate::allocation_layer::AllocationJournal_v::*;

verus!{

impl AllocationJournal::Step {
    pub open spec fn i(self) -> LikesJournal::Step {
        match self {
            Self::read_for_recovery() =>
                LikesJournal::Step::read_for_recovery(),
            Self::freeze_for_commit(depth) =>
                LikesJournal::Step::freeze_for_commit(depth),
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
        if root is Some {
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

    pub proof fn freeze_for_commit_refines(self, post: Self, lbl: AllocationJournal::Label, depth: nat)
        requires self.inv(), post.inv(), Self::freeze_for_commit(self, post, lbl, depth)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::freeze_for_commit(depth))
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(LikesJournal::State::next_by);

        let frozen_journal = lbl->frozen_journal;
        let frozen_root = frozen_journal.tj.freshest_rec;
        let new_bdy = frozen_journal.tj.seq_start();

        assert(Self::next_by(self, post, lbl, AllocationJournal::Step::freeze_for_commit(depth)));
        Self::frozen_journal_is_valid_image(self, post, lbl);
//        assert(frozen_journal.tj.decodable());

        self.tj().crop_ensures(depth);
        self.tj().disk_view.pointer_after_crop_seq_end(self.tj().freshest_rec, depth);
//        assert(frozen_journal.tj.seq_end() <= self.tj().seq_end());

        let post_discard = self.tj().crop(depth).discard_old(new_bdy);
        let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < post_discard.seq_end());
        let frozen_index = self.lsn_au_index.restrict(frozen_lsns);
        let i_frozen_index = self.i().lsn_addr_index.restrict(frozen_lsns);

        let addrs_past_new_end = Set::new(|addr: Address| frozen_root.unwrap().after_page(addr));
        let frozen_addrs = Set::new(|addr: Address| self.tj().crop(depth).disk_view.entries.contains_key(addr) 
            && frozen_index.values().contains(addr.au)) - addrs_past_new_end;
        self.tj().build_lsn_au_index_ensures(self.first);
        self.tj().disk_view.build_lsn_au_index_equiv_page_walk(self.tj().freshest_rec, self.first);
        self.tj().disk_view.build_lsn_au_index_page_walk_consistency(self.tj().freshest_rec);
        self.tj().disk_view.build_lsn_addr_index_reflects_disk_view(self.tj().freshest_rec);

        if frozen_root is Some {
            assert forall |lsn| #[trigger] i_frozen_index.contains_key(lsn)
            implies !addrs_past_new_end.contains(i_frozen_index[lsn])
            by {
                let addr = i_frozen_index[lsn];
    
                self.tj().build_lsn_addr_index_ensures();
//                assert(self.tj().disk_view.index_keys_map_to_valid_entries(self.i().lsn_addr_index));
                self.tj().disk_view.instantiate_index_keys_map_to_valid_entries(self.i().lsn_addr_index, lsn);
    
//                assert(self.i().lsn_addr_index[lsn] == addr);
//                assert(self.tj().disk_view.addr_supports_lsn(addr, lsn));
    
                if addrs_past_new_end.contains(addr) {
//                    assert(frozen_root.unwrap().after_page(addr));

                    let last_frozen_lsn = (frozen_journal.tj.seq_end()-1) as nat;
//                    assert(self.lsn_au_index.contains_key(last_frozen_lsn)); // trigger
//                    assert(self.tj().disk_view.addr_supports_lsn(frozen_root.unwrap(), last_frozen_lsn));
//                    assert(self.tj().disk_view.addr_supports_lsn(addr, lsn));
                    reveal(DiskView::pages_allocated_in_lsn_order);
//                    assert(false);
                }
            }
        }

//        assert(i_frozen_index.values() <= frozen_addrs);
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: AllocationJournal::Label, new_journal: LinkedJournal::State)
        requires self.inv(), post.inv(), Self::discard_old(self, post, lbl, new_journal)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::discard_old(new_journal))
    {
        reveal(LikesJournal::State::next_by);
//        assert(post.i().journal == new_journal);

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;
        let keep_addrs = Set::new(|addr: Address| addr.wf() && post.lsn_au_index.values().contains(addr.au));

        let lsn_addr_index_post = LikesJournal_v::lsn_addr_index_discard_up_to(self.i().lsn_addr_index, start_lsn);
        let i_keep_addrs = lsn_addr_index_post.values();

        reveal(TruncatedJournal::index_domain_valid);

        if self.tj().freshest_rec is Some {
            self.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }

        post.tj().disk_view.sub_disk_with_newer_lsn_repr_index(self.tj().disk_view, post.tj().freshest_rec);
//        assert(post.i().lsn_addr_index <= self.i().lsn_addr_index);

        LikesJournal_v::lsn_addr_index_discard_up_to_ensures(self.i().lsn_addr_index, start_lsn);
//        assert(lsn_addr_index_post <= self.i().lsn_addr_index);

        if post.tj().freshest_rec is Some {
            post.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }

        assert(post.i().lsn_addr_index =~= lsn_addr_index_post);
//        assert(self.lsn_au_index == self.tj().build_lsn_au_index(self.first));

        self.tj().disk_view.build_lsn_au_index_equiv_page_walk(self.tj().freshest_rec, self.first);
        self.tj().disk_view.build_lsn_au_index_page_walk_consistency(self.tj().freshest_rec);
        self.tj().disk_view.build_lsn_addr_index_reflects_disk_view(self.tj().freshest_rec);
//        assert(i_keep_addrs <= keep_addrs);

//        assert(self.tj().discard_old_cond(start_lsn, i_keep_addrs, new_journal.truncated_journal));
    }

    pub proof fn internal_journal_marshal_refines(self, post: Self, lbl: AllocationJournal::Label, 
        cut: LSN, addr: Address, new_journal: LinkedJournal::State)
        requires self.inv(), post.inv(), Self::internal_journal_marshal(self, post, lbl, cut, addr, new_journal)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal))
    {
        reveal(LikesJournal::State::next_by);
        reveal(LinkedJournal::State::next_by);
        self.tj().disk_view.sub_disk_repr_index(post.tj().disk_view, self.tj().freshest_rec);
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
            AllocationJournal::Step::freeze_for_commit(depth) => {
                self.freeze_for_commit_refines(post, lbl, depth);
            },
            AllocationJournal::Step::discard_old(new_journal) => {
                self.discard_old_refines(post, lbl, new_journal);
            },
            AllocationJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
                self.internal_journal_marshal_refines(post, lbl, cut, addr, new_journal);
            },
            _ => {
                reveal(LinkedJournal::State::next);
                reveal(LinkedJournal::State::next_by);
                assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), step.i()) );
            },
        }
    }

    pub proof fn init_refines(self, journal: LinkedJournal::State, image: JournalImage) 
    requires AllocationJournal::State::initialize(self, journal, image)
    ensures LikesJournal::State::initialize(self.i(), image.tj)
    {
    }
}


} // verus!
