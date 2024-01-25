// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::math;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use vstd::map::*;
use vstd::map_lib::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::AbstractJournal_v::{AbstractJournal};
use crate::abstract_system::AbstractCrashAwareJournal_v;
use crate::abstract_system::AbstractCrashAwareJournal_v::{CrashTolerantJournal};
use crate::disk::GenericDisk_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::journal::LikesJournal_v::{LikesJournal};
use crate::allocation_layer::AllocationJournal_v::{AllocationJournal, JournalImage};
use crate::allocation_layer::AllocationCrashAwareJournal_v::*;

// Refines Allocation Journal => Abstract Journal
// Refines Allocation Crash Aware Journal => Abstract Crash Aware Journal

verus!{

impl AllocationJournal::Label{
    pub open spec fn i_abstract(self) -> AbstractJournal::Label
    {   
        LikesJournal::State::lbl_i(self.i()).i().i()
    }
}

impl AllocationJournal::State{
    pub open spec fn i_abstract(self) -> AbstractJournal::State
    {
        self.i().i().i().i()
    }

    // refines to abstract journal
    pub proof fn next_refines_abstract(self, post: Self, lbl: AllocationJournal::Label)
    requires
        self.inv(),
        post.inv(),
        AllocationJournal::State::next(self, post, lbl)
    ensures
        AbstractJournal::State::next(self.i_abstract(), post.i_abstract(), lbl.i_abstract())
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);

        self.next_refines(post, lbl); // alloc refines to likes

        let likes = self.i();
        let likes_post = post.i();
        let likes_lbl = lbl.i();

        likes.next_refines(likes_post, likes_lbl); // likes refines to linked

        let linked = likes.i();
        let linked_post = likes_post.i();
        let linked_lbl = LikesJournal::State::lbl_i(likes_lbl);

        linked.next_refines(linked_post, linked_lbl); // linked refines to paged

        linked.truncated_journal.iwf();
        linked_post.truncated_journal.iwf();
        
        let paged = linked.i();
        let paged_post = linked_post.i();
        let paged_lbl = linked_lbl.i();

        paged.next_refines(paged_post, paged_lbl); // paged refines to abstract
    }
}

impl JournalImage{
    pub open spec fn i(self) -> MsgHistory
    {
        self.tj.i().i()
    }
}

impl Ephemeral{
    pub open spec fn i(self) -> AbstractCrashAwareJournal_v::Ephemeral
    {
        if self is Unknown {
            AbstractCrashAwareJournal_v::Ephemeral::Unknown
        } else {
            AbstractCrashAwareJournal_v::Ephemeral::Known{
                v: self.get_Known_v().i_abstract()
            }
        }
    }
}

impl AllocationCrashAwareJournal::Label{
    pub open spec fn i(self) -> CrashTolerantJournal::Label
    {
        match self {
            Self::LoadEphemeralFromPersistent => 
                CrashTolerantJournal::Label::LoadEphemeralFromPersistentLabel,
            Self::ReadForRecovery{records} =>
                CrashTolerantJournal::Label::ReadForRecoveryLabel{records},
            Self::QueryEndLsn{end_lsn} =>
                CrashTolerantJournal::Label::QueryEndLsnLabel{end_lsn},
            Self::Put{records} =>
                CrashTolerantJournal::Label::PutLabel{records},
            Self::Internal{allocs, deallocs} =>
                CrashTolerantJournal::Label::InternalLabel,
            Self::QueryLsnPersistence{sync_lsn} =>
                CrashTolerantJournal::Label::QueryLsnPersistenceLabel{sync_lsn},
            Self::CommitStart{ new_boundary_lsn, max_lsn } =>
                CrashTolerantJournal::Label::CommitStartLabel{new_boundary_lsn, max_lsn},
            Self::CommitComplete{ require_end, discarded } =>
                CrashTolerantJournal::Label::CommitCompleteLabel{require_end},
            Self::Crash => CrashTolerantJournal::Label::CrashLabel,
        }
    }
}

impl AllocationCrashAwareJournal::State{
    pub open spec fn i(self) -> CrashTolerantJournal::State 
    {
        let i_in_flight = 
            if self.inflight is None { None }
            else { Some(self.inflight.unwrap().i()) };

        CrashTolerantJournal::State{
            persistent: self.persistent.i(),
            ephemeral: self.ephemeral.i(),
            in_flight: i_in_flight,
        }
    }

    pub proof fn load_ephemeral_from_persistent_refines(self, post: Self, 
        lbl: AllocationCrashAwareJournal::Label, new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::load_ephemeral_from_persistent(self, post, lbl, new_journal)
    ensures
        CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            CrashTolerantJournal::Step::load_ephemeral_from_persistent(new_journal.i_abstract()))
    {
        assume(false);
    }

    pub proof fn read_for_recovery_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires
        self.inv(),
        post.inv(),
        Self::read_for_recovery(self, post, lbl)
    ensures
        CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), CrashTolerantJournal::Step::read_for_recovery())
    {
        reveal(CrashTolerantJournal::State::next_by);

        let aj = self.ephemeral.get_Known_v();
        let alloc_lbl = AllocationJournal::Label::ReadForRecovery{messages: lbl.get_ReadForRecovery_records()};
        aj.next_refines_abstract(aj, alloc_lbl);
    }

    pub proof fn query_end_lsn_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires
        self.inv(),
        post.inv(),
        Self::query_end_lsn(self, post, lbl)
    ensures
        CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), CrashTolerantJournal::Step::query_end_lsn())
    {
        reveal(CrashTolerantJournal::State::next_by);

        let aj = self.ephemeral.get_Known_v();
        let alloc_lbl = AllocationJournal::Label::QueryEndLsn{end_lsn: lbl.get_QueryEndLsn_end_lsn() };
        aj.next_refines_abstract(aj, alloc_lbl);
    }

    pub proof fn put_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::put(self, post, lbl, new_journal)
    ensures
        CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            CrashTolerantJournal::Step::put(new_journal.i_abstract()))
    {
        reveal(CrashTolerantJournal::State::next_by);

        let aj = self.ephemeral.get_Known_v();
        let alloc_lbl = AllocationJournal::Label::Put{messages: lbl.get_Put_records() };
        aj.next_refines_abstract(new_journal, alloc_lbl);
    }

    pub proof fn internal_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::internal(self, post, lbl, new_journal)
    ensures
        CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            CrashTolerantJournal::Step::internal(new_journal.i_abstract()))
    {
        reveal(CrashTolerantJournal::State::next_by);

        let aj = self.ephemeral.get_Known_v();
        let alloc_lbl = AllocationJournal::Label::InternalAllocations{
            allocs: lbl.get_Internal_allocs(),
            deallocs: lbl.get_Internal_deallocs(),
        };
        aj.next_refines_abstract(new_journal, alloc_lbl);
    }

    pub proof fn commit_start_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        frozen_journal: StoreImage)
    requires
        self.inv(),
        post.inv(),
        Self::commit_start(self, post, lbl, frozen_journal)
    ensures
        CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            CrashTolerantJournal::Step::commit_start(frozen_journal.i()))
    {
        assume(false);
    }

    pub proof fn commit_complete_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::commit_complete(self, post, lbl, new_journal)
    ensures
        CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            CrashTolerantJournal::Step::commit_complete(new_journal.i_abstract()))
    {
        assume(false);
    }

    pub proof fn next_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires 
        self.inv(),
        post.inv(),
        Self::next(self, post, lbl)
    ensures
        CrashTolerantJournal::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AllocationCrashAwareJournal::State::next_by);  // unfortunate defaults
        reveal(AllocationCrashAwareJournal::State::next);
        reveal(CrashTolerantJournal::State::next_by);
        reveal(CrashTolerantJournal::State::next);

        let step = choose |step| AllocationCrashAwareJournal::State::next_by(self, post, lbl, step);
        match step {
            AllocationCrashAwareJournal::Step::load_ephemeral_from_persistent(new_journal) => {
                self.load_ephemeral_from_persistent_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::read_for_recovery() => {
                self.read_for_recovery_refines(post, lbl);
            },
            AllocationCrashAwareJournal::Step::query_end_lsn() => {
                self.query_end_lsn_refines(post, lbl);
            },
            AllocationCrashAwareJournal::Step::put(new_journal) => {
                self.put_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::internal(new_journal) => {
                self.internal_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::query_lsn_persistence() => {
                assert( CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), 
                    CrashTolerantJournal::Step::query_lsn_persistence()) ); // witness
            },
            AllocationCrashAwareJournal::Step::commit_start(frozen_journal) => {
                self.commit_start_refines(post, lbl, frozen_journal);
            },
            AllocationCrashAwareJournal::Step::commit_complete(new_journal) => {
                self.commit_complete_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::crash() => {
                assert( CrashTolerantJournal::State::next_by(self.i(), post.i(), lbl.i(), 
                    CrashTolerantJournal::Step::crash()) ); // witness
            },
            _ => {
                assert(false);
            },
        }
    }
}

} // verus