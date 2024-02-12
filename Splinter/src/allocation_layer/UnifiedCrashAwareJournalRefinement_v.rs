// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::math;
use vstd::prelude::*;

use builtin_macros::*;

// use crate::abstract_system::AbstractCrashAwareJournal_v;
// use crate::abstract_system::AbstractCrashAwareJournal_v::CrashTolerantJournal;
// use crate::abstract_system::AbstractJournal_v::AbstractJournal;
// use crate::abstract_system::MsgHistory_v::*;
// use crate::abstract_system::StampedMap_v::LSN;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{TruncatedJournal};
use crate::allocation_layer::AllocationJournal_v;
use crate::allocation_layer::AllocationJournal_v::{JournalImage, AllocationJournal};
use crate::allocation_layer::AllocationCrashAwareJournal_v;
use crate::allocation_layer::AllocationCrashAwareJournal_v::{AllocationCrashAwareJournal};
use crate::allocation_layer::UnifiedCrashAwareJournal_v;
use crate::allocation_layer::UnifiedCrashAwareJournal_v::*;

// use crate::disk::GenericDisk_v::AU;
// use crate::disk::GenericDisk_v::*;
// use crate::journal::LikesJournal_v::LikesJournal;
// use crate::journal::PagedJournal_v::JournalRecord;

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
                AllocationCrashAwareJournal::Label::CommitComplete { require_end, discarded },
            Self::Crash => AllocationCrashAwareJournal::Label::Crash,
        }
    }  
}

impl Ephemeral {
    pub open spec(checked) fn i(self, dv: DiskView) -> AllocationCrashAwareJournal_v::Ephemeral {
        if self is Unknown {
            AllocationCrashAwareJournal_v::Ephemeral::Unknown
        } else {
            AllocationCrashAwareJournal_v::Ephemeral::Known { v: self.get_Known_v().to_aj(dv) }
        }
    }
}

impl ImageState {
    pub open spec(checked) fn i(self, dv: DiskView) -> JournalImage
        recommends self.valid_image(dv)
    {
        let tight_jdv = self.tight_dv(dv).to_JournalDiskView(self.boundary_lsn);
        JournalImage {
            tj: TruncatedJournal{
                disk_view: tight_jdv,
                freshest_rec: self.freshest_rec,
            },
            first: self.first,
        }
    }

    proof fn i_valid(self, dv: DiskView) 
        requires self.valid_image(dv)
        ensures self.i(dv).valid_image()
    {
        self.tight_dv_preserves_valid_image(dv);
    }

    proof fn i_valid_auto() 
        ensures forall |image: Self, dv| 
            #[trigger] image.valid_image(dv) ==> image.i(dv).valid_image()
    {
        assert forall |image: Self, dv| #[trigger] image.valid_image(dv)
        implies image.i(dv).valid_image() by {
            image.i_valid(dv);
        }
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

        let jdv = self.to_tj(dv).disk_view;
        let big_jdv = self.to_tj(big_dv).disk_view;

        jdv.build_lsn_au_index_page_walk_sub_disk(big_jdv, self.freshest_rec);
        jdv.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);
        big_jdv.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);

        assert(index == post_index);

        // 2. show big.freshest_rec does not meet tight_domain condition
        let addr = big.freshest_rec.unwrap();
        if {
            &&& index.values().contains(addr.au)
            &&& self.freshest_rec is Some 
            &&& !self.freshest_rec.unwrap().after_page(addr)
        } {
            let big_index = big.to_tj(big_dv).build_lsn_au_index(big.first);
            self.to_tj(dv).sub_disk_build_sub_lsn_au_index(self.first, big.to_tj(big_dv), big.first);
            assert(index <= big_index);

            self.to_tj(dv).build_lsn_au_index_ensures(self.first);
            big.to_tj(big_dv).build_lsn_au_index_ensures(big.first);

            if self.freshest_rec.unwrap().au == addr.au {
                assert(addr.page < self.freshest_rec.unwrap().page);
                reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
                assert(false);
            }

            let lsn1 = choose |lsn1| #[trigger] index.contains_key(lsn1) && index[lsn1] == addr.au;
            let lsn2 = self.last_lsn(dv);
            let lsn3 = big.last_lsn(big_dv);

            assert(big_index.contains_key(lsn2));
            assert(big_index[lsn2] == self.freshest_rec.unwrap().au);

            assert(lsn1 <= lsn2 <= lsn3);
            assert(big_index.contains_key(lsn1));
            assert(big_index[lsn1] == addr.au);
            assert(big_index.contains_key(lsn3));
            assert(big_index[lsn3] == addr.au);

            assert(AllocationJournal_v::contiguous_lsns(big_index, lsn1, lsn2, lsn3));
            assert(big_index[lsn2] == addr.au);
            assert(false);
        }

        assert(self.tight_domain(dv) =~= self.tight_domain(big_dv));
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
        reveal(AllocationJournal::State::init_by);

        ImageState::i_valid_auto();

        let i_pre_dv = self.i().persistent.tj.disk_view;
        let i_post_dv = post.i().persistent.tj.disk_view;
        assert(i_pre_dv.entries =~= i_post_dv.entries);
    }

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

        ImageState::i_valid_auto();

        let v = self.ephemeral.get_Known_v();
        let post_v = post.ephemeral.get_Known_v();

        let allocs = lbl.get_Internal_allocs();
        let deallocs = lbl.get_Internal_deallocs();
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

//     pub proof fn commit_start_refines(
//         self,
//         post: Self,
//         lbl: AllocationCrashAwareJournal::Label,
//         frozen_journal: StoreImage,
//     )
//         requires
//             self.inv(),
//             post.inv(),
//             Self::commit_start(self, post, lbl, frozen_journal),
//         ensures
//             CrashTolerantJournal::State::next_by(
//                 self.i(),
//                 post.i(),
//                 lbl.i(),
//                 CrashTolerantJournal::Step::commit_start(frozen_journal.i()),
//             ),
//     {
//         reveal(CrashTolerantJournal::State::next_by);
//         assert(self.i().ephemeral is Known);
//         assert(self.i().in_flight is None);
//         frozen_journal.tj.iwf();
//         JournalRecord::i_lemma_forall();
//         assert(frozen_journal.i().wf());
//         assert(frozen_journal.tj.seq_start() == frozen_journal.i().seq_start);
//         let aj = self.ephemeral.get_Known_v();
//         let alloc_lbl = AllocationJournal::Label::FreezeForCommit { frozen_journal };
//         aj.next_refines_abstract(aj, alloc_lbl);
//     }

//     pub proof fn commit_complete_refines(
//         self,
//         post: Self,
//         lbl: AllocationCrashAwareJournal::Label,
//         new_journal: AllocationJournal::State,
//     )
//         requires
//             self.inv(),
//             post.inv(),
//             Self::commit_complete(self, post, lbl, new_journal),
//         ensures
//             CrashTolerantJournal::State::next_by(
//                 self.i(),
//                 post.i(),
//                 lbl.i(),
//                 CrashTolerantJournal::Step::commit_complete(new_journal.i_abstract()),
//             ),
//     {
//         reveal(CrashTolerantJournal::State::next_by);
//         self.inflight.unwrap().tj.iwf();
//         JournalRecord::i_lemma_forall();
//         assert(self.inflight.unwrap().tj.seq_start() == self.i().in_flight.unwrap().seq_start);
//         let aj = self.ephemeral.get_Known_v();
//         let alloc_lbl = AllocationJournal::Label::DiscardOld {
//             start_lsn: self.inflight.unwrap().tj.seq_start(),
//             require_end: lbl.get_CommitComplete_require_end(),
//             deallocs: lbl.get_CommitComplete_discarded(),
//         };
//         aj.next_refines_abstract(new_journal, alloc_lbl);
//     }

    pub proof fn next_refines(self, post: Self, lbl: UnifiedCrashAwareJournal::Label)
        requires
            self.inv(),
            post.inv(),
            Self::next(self, post, lbl),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(UnifiedCrashAwareJournal::State::next_by);
        reveal(UnifiedCrashAwareJournal::State::next);
        reveal(AllocationCrashAwareJournal::State::next_by);
        reveal(AllocationCrashAwareJournal::State::next);

        ImageState::i_valid_auto();

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
                assume(false);
                // self.commit_start_refines(post, lbl, frozen_journal);
            },
            UnifiedCrashAwareJournal::Step::commit_complete(new_ephemeral, new_dv) => {
                assume(false);
                // self.commit_complete_refines(post, lbl, new_journal);
            },
            UnifiedCrashAwareJournal::Step::crash() => {
                assert(
                    AllocationCrashAwareJournal::State::next_by(self.i(),post.i(),lbl.i(),
                    AllocationCrashAwareJournal::Step::crash(),
                ));
            },
            _ => {
                assert(false);
            },
        }
    }

//     pub proof fn init_refines(self)
//         requires
//             Self::initialize(self),
//         ensures
//             CrashTolerantJournal::State::initialize(self.i()),
//     {
//         TruncatedJournal::mkfs_ensures();
//     }
}

} // verus!
  // verus
