// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// #![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;

use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{Address};
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{TruncatedJournal};
use crate::allocation_layer::AllocationJournal_v;
use crate::allocation_layer::AllocationJournal_v::{JournalImage, AllocationJournal};
use crate::allocation_layer::AllocationCrashAwareJournal_v;
use crate::allocation_layer::AllocationCrashAwareJournal_v::{AllocationCrashAwareJournal};
use crate::allocation_layer::UnifiedCrashAwareJournal_v::*;

// Refines Unified Crash Aware Journal => Allocation Crash Aware Journal

verus! {

impl UnifiedCrashAwareJournal::Label {
    pub open spec fn i(self) -> AllocationCrashAwareJournal::Label
    {
        match self {
            Self::LoadEphemeralFromPersistent => 
                AllocationCrashAwareJournal::Label::LoadEphemeralFromPersistent,
            Self::ReadForRecovery{ records } => 
                AllocationCrashAwareJournal::Label::ReadForRecovery{ records },
            Self::QueryEndLsn{ end_lsn } => 
                AllocationCrashAwareJournal::Label::QueryEndLsn{ end_lsn },
            Self::Put{ records } => 
                AllocationCrashAwareJournal::Label::Put{ records },
            Self::Internal{ allocs, deallocs } => 
                AllocationCrashAwareJournal::Label::Internal{ allocs, deallocs },
            Self::QueryLsnPersistence { sync_lsn } => 
                AllocationCrashAwareJournal::Label::QueryLsnPersistence{ sync_lsn },
            Self::CommitStart { new_boundary_lsn, max_lsn } => 
                AllocationCrashAwareJournal::Label::CommitStart{ new_boundary_lsn, max_lsn },
            Self::CommitComplete { require_end, discarded } => 
                AllocationCrashAwareJournal::Label::CommitComplete{ require_end, discarded },
            Self::Crash{ keep_in_flight } =>
                AllocationCrashAwareJournal::Label::Crash{ keep_in_flight },
        }
    }
}

impl Ephemeral {
    pub open spec(checked) fn i(self, dv: DiskView) -> AllocationCrashAwareJournal_v::Ephemeral {
        if self is Unknown {
            AllocationCrashAwareJournal_v::Ephemeral::Unknown
        } else {
            AllocationCrashAwareJournal_v::Ephemeral::Known { v: self->v.to_aj(dv) }
        }
    }
}

impl ImageState {
    pub open spec(checked) fn i(self, dv: DiskView) -> JournalImage
        recommends self.valid_image(dv)
    {
        let tight_jdv = self.tight_dv(dv).to_jdv(self.boundary_lsn);
        JournalImage {
            tj: TruncatedJournal{
                disk_view: tight_jdv,
                freshest_rec: self.freshest_rec,
            },
            first: self.first,
        }
    }

    broadcast proof fn i_valid(self, dv: DiskView) 
        requires  #[trigger] self.valid_image(dv)
        ensures self.i(dv).valid_image()
    {
        self.tight_dv_preserves_valid_image(dv);
    }

    pub proof fn new_addr_preserves_tight_dv(self, dv: DiskView, big: Self, big_dv: DiskView)
    requires
        self.valid_image(dv),
        self.valid_image(big_dv),
        big.valid_image(big_dv),
        big.freshest_rec is Some,
        dv.entries <= big_dv.entries,
        dv.entries.dom() =~= big_dv.entries.dom().difference(set![big.freshest_rec.unwrap()]),
        big.seq_start() <= self.seq_start(),
        self.seq_end(dv) <= big.seq_end(big_dv),
    ensures
        self.tight_dv(dv) == self.tight_dv(big_dv)
    {
        // 1. show index dv and big_dv are the same
        let index = self.to_tj(dv).build_lsn_au_index(self.first);
        let post_index = self.to_tj(big_dv).build_lsn_au_index(self.first);
        assert(index == post_index) by {
            self.to_tj(dv).disk_view.build_lsn_au_index_page_walk_sub_disk(self.to_tj(big_dv).disk_view, self.freshest_rec);
            self.to_tj(dv).disk_view.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);
            self.to_tj(big_dv).disk_view.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);
        }

        // 2. show big.freshest_rec does not meet tight_domain condition
        let addr = big.freshest_rec.unwrap();
        if {
            &&& index.values().contains(addr.au)
            &&& self.freshest_rec is Some 
            &&& !self.freshest_rec.unwrap().after_page(addr)
        } {
            let big_index = big.to_tj(big_dv).build_lsn_au_index(big.first);
            self.to_tj(dv).sub_disk_build_sub_lsn_au_index(self.first, big.to_tj(big_dv), big.first);
//            assert(index <= big_index);

            self.to_tj(dv).build_lsn_au_index_ensures(self.first);
            big.to_tj(big_dv).build_lsn_au_index_ensures(big.first);

            let head = self.freshest_rec.unwrap();
            if head.au == addr.au {
//                assert(addr.page < head.page);
                reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
//                assert(false);
            }

            let lsn1 = choose |lsn1| #[trigger] index.contains_key(lsn1) && index[lsn1] == addr.au;
            let lsn2 = (self.seq_end(dv) - 1) as nat;
            let lsn3 = (big.seq_end(big_dv) - 1) as nat;

            big.to_tj(big_dv).disk_view.addr_supports_lsn_consistent_with_index(big_index, lsn2, head);
            big.to_tj(big_dv).disk_view.addr_supports_lsn_consistent_with_index(big_index, lsn3, addr);
//            assert(big_index[lsn2] == head.au);
//            assert(big_index[lsn3] == addr.au);

//            assert(lsn1 <= lsn2 <= lsn3);
//            assert(big_index.contains_key(lsn1));
//            assert(big_index[lsn1] == addr.au);

            assert(AllocationJournal_v::contiguous_lsns(big_index, lsn1, lsn2, lsn3));
//            assert(big_index[lsn2] == addr.au);
//            assert(false);
        }

//        assert(self.tight_domain(dv) =~= self.tight_domain(big_dv));
        assert(self.tight_dv(dv).entries =~= self.tight_dv(big_dv).entries);
    }
}

impl UnifiedCrashAwareJournal::State {
    pub open spec fn i(self) -> AllocationCrashAwareJournal::State {
        let i_inflight = 
            if self.inflight is None { None } 
            else { Some(self.inflight.unwrap().i(self.dv)) };

        AllocationCrashAwareJournal::State{
            ephemeral: self.ephemeral.i(self.dv),
            inflight: i_inflight,
            persistent: self.persistent.i(self.dv),
        }
    }

    pub proof fn load_ephemeral_from_persistent_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareJournal::Label,
        new_ephemeral: EphemeralState,
    )
        requires
            self.inv(),
            post.inv(),
            Self::load_ephemeral_from_persistent(self, post, lbl, new_ephemeral),
        ensures
            AllocationCrashAwareJournal::State::next_by(
                self.i(),
                post.i(),
                lbl.i(),
                AllocationCrashAwareJournal::Step::load_ephemeral_from_persistent(
                    new_ephemeral.to_aj(post.dv),
                ),
            ),
    {
        reveal(AllocationCrashAwareJournal::State::next_by);
        broadcast use ImageState::i_valid;

        let i_pre_dv = self.i().persistent.tj.disk_view;
        let i_post_dv = post.i().persistent.tj.disk_view;
        assert(i_pre_dv.entries =~= i_post_dv.entries);
    }

    #[verifier::spinoff_prover]
    pub proof fn internal_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareJournal::Label,
        new_ephemeral: EphemeralState,
        new_dv: DiskView, 
    )
        requires
            self.inv(),
            post.inv(),
            Self::internal(self, post, lbl, new_ephemeral, new_dv),
        ensures
            AllocationCrashAwareJournal::State::next_by(
                self.i(),
                post.i(),
                lbl.i(),
                AllocationCrashAwareJournal::Step::internal(new_ephemeral.to_aj(new_dv)),
            ),
    {
        reveal(AllocationCrashAwareJournal::State::next_by);
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        broadcast use ImageState::i_valid;

        let v = self.ephemeral->v;
        let post_v = post.ephemeral->v;

        let allocs = lbl->allocs;
        let deallocs = lbl.arrow_Internal_deallocs();
        let aj_lbl = AllocationJournal::Label::InternalAllocations{ allocs, deallocs };

        match choose |step| AllocationJournal::State::next_by(v.to_aj(self.dv), post_v.to_aj(post.dv), aj_lbl, step)
        {
            AllocationJournal::Step::internal_journal_marshal(_, addr, _) => {
                self.persistent.new_addr_preserves_tight_dv(self.dv, post_v.image, post.dv);
                if self.inflight is Some {
                    self.inflight.unwrap().new_addr_preserves_tight_dv(self.dv, post_v.image, post.dv);
                }
            }
            _ => {  }
        }
    }

    pub proof fn commit_start_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareJournal::Label,
        frozen_journal: ImageState,
        depth: nat,
    )
        requires
            self.inv(),
            post.inv(),
            Self::commit_start(self, post, lbl, frozen_journal, depth),
        ensures
            AllocationCrashAwareJournal::State::next_by(
                self.i(),
                post.i(),
                lbl.i(),
                AllocationCrashAwareJournal::Step::commit_start(frozen_journal.i(self.dv)),
            ),
    {
        reveal(AllocationCrashAwareJournal::State::next_by);
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        broadcast use ImageState::i_valid;

        let aj = self.ephemeral->v.to_aj(self.dv);
        let new_bdy = frozen_journal.seq_start();
        let i_frozen = frozen_journal.i(self.dv);
        let frozen_index = frozen_journal.to_tj(self.dv).build_lsn_au_index(frozen_journal.first);

        frozen_journal.to_tj(self.dv).build_lsn_au_index_ensures(frozen_journal.first);
        frozen_journal.to_tj(self.dv).sub_disk_build_sub_lsn_au_index(frozen_journal.first, aj.tj(), aj.first);
//        assert(frozen_index <= aj.lsn_au_index);
//        assert(frozen_journal.freshest_rec is Some ==> frozen_index.contains_key(new_bdy)); // trigger

        let cropped_tj = aj.tj().crop(depth);
        let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < cropped_tj.discard_old(new_bdy).seq_end());
        let i_frozen_index = aj.lsn_au_index.restrict(frozen_lsns);
        let frozen_addrs = Set::new(|addr: Address| cropped_tj.disk_view.entries.contains_key(addr) 
            && i_frozen_index.values().contains(addr.au)) - AllocationJournal_v::au_addrs_past_pointer(frozen_journal.freshest_rec);

        assert(i_frozen_index.dom() =~= frozen_index.dom());
//        assert(cropped_tj.discard_old_cond(new_bdy, frozen_addrs, i_frozen.tj));
//        assert(cropped_tj.discard_old_tight(new_bdy, frozen_addrs, i_frozen.tj));

        assert(AllocationJournal::State::next_by(aj, aj,
            AllocationJournal::Label::FreezeForCommit{frozen_journal: i_frozen},
            AllocationJournal::Step::freeze_for_commit(depth),
        )); // witness
    }

    pub proof fn commit_complete_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareJournal::Label,
        new_ephemeral: EphemeralState, 
        new_dv: DiskView
    )
        requires
            self.inv(),
            post.inv(),
            Self::commit_complete(self, post, lbl, new_ephemeral, new_dv),
        ensures
            AllocationCrashAwareJournal::State::next_by(
                self.i(),
                post.i(),
                lbl.i(),
                AllocationCrashAwareJournal::Step::commit_complete(new_ephemeral.to_aj(new_dv)),
            ),
    {
        reveal(AllocationCrashAwareJournal::State::next_by);
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        
        broadcast use ImageState::i_valid;

        let post_v = post.ephemeral->v;

        let bdy = post.persistent.boundary_lsn;
        let root = post.persistent.freshest_rec;
        let first = post.persistent.first;

        let index = post.persistent.to_tj(self.dv).build_lsn_au_index(first);
        let post_index = post.persistent.to_tj(post.dv).build_lsn_au_index(first);

        assert(index == post_index) by {
            let pre_jdv = self.dv.to_jdv(bdy);
            let post_jdv = post.dv.to_jdv(bdy);
            pre_jdv.build_lsn_au_index_equiv_page_walk(root, first);
            post_jdv.build_lsn_au_index_equiv_page_walk(root, first);
            post_jdv.build_lsn_au_index_page_walk_sub_disk(pre_jdv, root);
        }

        // assert(lbl->discarded.disjoint(post_v.lsn_au_index.values()));
        assert(index <= post_v.lsn_au_index) by {
            post.persistent.to_tj(post.dv).sub_disk_build_sub_lsn_au_index(
                first, post_v.to_aj(post.dv).tj(), post_v.image.first);
        }
        assert(index.dom() <= post_v.lsn_au_index.dom());
//        assert(index.values() <= post_v.lsn_au_index.values());

        let tight_pre_jdv = post.persistent.tight_dv(self.dv).to_jdv(bdy);
        let tight_post_jdv = post.persistent.tight_dv(post.dv).to_jdv(bdy);

//        assert(tight_post_jdv.entries.dom() =~= tight_pre_jdv.entries.dom());
        assert(tight_pre_jdv.entries =~= tight_post_jdv.entries);
    }

    pub proof fn next_refines(self, post: Self, lbl: UnifiedCrashAwareJournal::Label)
        requires
            self.inv(),
            post.inv(),
            Self::next(self, post, lbl),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        broadcast use ImageState::i_valid;
        reveal(UnifiedCrashAwareJournal::State::next_by);
        reveal(UnifiedCrashAwareJournal::State::next);
        reveal(AllocationCrashAwareJournal::State::next_by);
        reveal(AllocationCrashAwareJournal::State::next);

        let step = choose|step| UnifiedCrashAwareJournal::State::next_by(self, post, lbl, step);
        match step {
            UnifiedCrashAwareJournal::Step::load_ephemeral_from_persistent(new_journal) => {
                self.load_ephemeral_from_persistent_refines(post, lbl, new_journal);
            },
            UnifiedCrashAwareJournal::Step::read_for_recovery() => {
                assert(
                    AllocationCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(),
                    AllocationCrashAwareJournal::Step::read_for_recovery())
                );
            },
            UnifiedCrashAwareJournal::Step::query_end_lsn() => {
                assert(
                    AllocationCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(),
                    AllocationCrashAwareJournal::Step::query_end_lsn())
                );
            },
            UnifiedCrashAwareJournal::Step::put(new_ephemeral) => {
                assert(
                    AllocationCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(),
                    AllocationCrashAwareJournal::Step::put(new_ephemeral.to_aj(post.dv)))
                );
            },
            UnifiedCrashAwareJournal::Step::internal(new_ephemeral, new_dv) => {
                self.internal_refines(post, lbl, new_ephemeral, new_dv);
            },
            UnifiedCrashAwareJournal::Step::query_lsn_persistence() => {
                assert(
                    AllocationCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(),
                    AllocationCrashAwareJournal::Step::query_lsn_persistence())
                );
            },
            UnifiedCrashAwareJournal::Step::commit_start(frozen_journal, depth) => {
                self.commit_start_refines(post, lbl, frozen_journal, depth);
            },
            UnifiedCrashAwareJournal::Step::commit_complete(new_ephemeral, new_dv) => {
                self.commit_complete_refines(post, lbl, new_ephemeral, new_dv);
            },
            UnifiedCrashAwareJournal::Step::crash() => {
                assert(
                    AllocationCrashAwareJournal::State::next_by(self.i(),post.i(),lbl.i(),
                    AllocationCrashAwareJournal::Step::crash(),
                ));
            },
            _ => {
//                assert(false);
            },
        }
    }

    pub proof fn init_refines(self)
        requires
            Self::initialize(self),
        ensures
            AllocationCrashAwareJournal::State::initialize(self.i()),
    {
        assert(self.i().persistent.tj.disk_view.entries =~= map![]);
    }
}

} // verus!
  // verus
