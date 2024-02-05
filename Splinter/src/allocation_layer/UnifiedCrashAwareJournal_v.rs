// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{AllocationJournal as AJ, *};
use crate::allocation_layer::MiniAllocator_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::JournalRecord;
use crate::journal::LinkedJournal_v::LinkedJournal;
use vstd::map::*;
use vstd::map_lib::*;
use vstd::prelude::*;

verus! {

pub type JournalDiskView = LinkedJournal_v::DiskView;

// data written to super block
pub struct ImageState {
    pub freshest_rec: Pointer,  // from LinkedJournal::TruncatedJournal
    pub boundary_lsn: LSN,  // from LinkedJournal::TruncatedJournal
    pub first:
        AU,  // from AJ::State, needed to faciliate AU recovery scan (page skip)
    // in memory Option<lsn_au_index>
}

impl ImageState {
    pub open spec(checked) fn empty() -> Self {
        ImageState { freshest_rec: None, boundary_lsn: 0, first: 0 }
    }

    pub open spec(checked) fn to_tj(self, dv: DiskView) -> LinkedJournal_v::TruncatedJournal {
        LinkedJournal_v::TruncatedJournal {
            freshest_rec: self.freshest_rec,
            disk_view: dv.to_JournalDiskView(self.boundary_lsn),
        }
    }

    pub open spec(checked) fn seq_start(self) -> LSN {
        self.boundary_lsn
    }

    pub open spec(checked) fn seq_end(self, dv: DiskView) -> LSN
        recommends
            self.to_tj(dv).disk_view.is_nondangling_pointer(self.freshest_rec),
    {
        self.to_tj(dv).seq_end()
    }

    // equivalent to AJ::valid_journal_image
    pub open spec(checked) fn valid_image(self, dv: DiskView) -> bool {
        let jdv = dv.to_JournalDiskView(self.boundary_lsn);
        &&& jdv.wf_addrs()
        &&& jdv.pointer_is_upstream(self.freshest_rec, self.first)
        &&& jdv.non_index_lsn_bounded(self.to_tj(dv).build_lsn_au_index(self.first))
    }

    pub open spec(checked) fn tight_domain(self, dv: DiskView) -> Set<Address>
        recommends
            self.valid_image(dv),
    {
        let index = self.to_tj(dv).build_lsn_au_index(self.first);
        let addrs_past_new_end = au_addrs_past_pointer(self.freshest_rec);
        Set::new(
            |addr: Address|
                dv.entries.contains_key(addr) && index.values().contains(addr.au)
                    && !addrs_past_new_end.contains(addr),
        )
    }

    pub open spec(checked) fn tight_dv(self, dv: DiskView) -> DiskView
        recommends
            self.valid_image(dv),
    {
        DiskView { entries: dv.entries.restrict(self.tight_domain(dv)) }
    }

    pub proof fn tight_dv_preserves_valid_image(self, dv: DiskView)
        requires
            self.valid_image(dv),
        ensures
            self.valid_image(self.tight_dv(dv)),
            self.to_tj(dv).build_lsn_au_index(self.first) == self.to_tj(
                self.tight_dv(dv),
            ).build_lsn_au_index(self.first),
    {
        let jdv = dv.to_JournalDiskView(self.boundary_lsn);
        let tight_jdv = self.tight_dv(dv).to_JournalDiskView(self.boundary_lsn);
        let index = self.to_tj(dv).build_lsn_au_index(self.first);
        self.to_tj(dv).build_lsn_au_index_ensures(self.first);
        if self.freshest_rec is Some {
            let last_lsn = (jdv.entries[self.freshest_rec.unwrap()].message_seq.seq_end - 1) as nat;
            assert(index.contains_key(last_lsn));
            assert(jdv.addr_supports_lsn(self.freshest_rec.unwrap(), last_lsn));
            let _ = jdv.instantiate_index_keys_exist_valid_entries(index, last_lsn);
            assert(tight_jdv.is_nondangling_pointer(self.freshest_rec));
        }
        reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
        assert forall|addr|
            #[trigger]
            tight_jdv.entries.contains_key(addr) implies tight_jdv.is_nondangling_pointer(
            tight_jdv.entries[addr].cropped_prior(self.boundary_lsn),
        ) by {
            let head = jdv.entries[addr];
            let next_ptr = head.cropped_prior(self.boundary_lsn);
            if next_ptr is Some {
                if addr.au == next_ptr.unwrap().au {
                    if addr.after_page(next_ptr.unwrap()) {
                        assert(false);
                    }
                } else {
                    let lsn1 = head.message_seq.seq_start;
                    if index.contains_key(lsn1) {
                        let lsn2 = (jdv.entries[next_ptr.unwrap()].message_seq.seq_end - 1) as nat;
                        assert(index.contains_key(lsn2));
                        assert(jdv.addr_supports_lsn(next_ptr.unwrap(), lsn2));
                        let _ = jdv.instantiate_index_keys_exist_valid_entries(index, lsn2);
                        assert(tight_jdv.is_nondangling_pointer(next_ptr));
                    } else {
                        assert(jdv.entries.dom().contains(addr));
                        assert(jdv.entries[addr].message_seq.contains(lsn1));
                        assert(lsn1 < self.boundary_lsn);
                        assert(false);
                    }
                }
            }
        }
        assert(tight_jdv.nondangling_pointers());
        assert(tight_jdv.decodable(self.freshest_rec));
        assert(tight_jdv.valid_ranking(jdv.the_ranking()));
        assert(tight_jdv.acyclic());
        assert(tight_jdv.internal_au_pages_fully_linked());
        assert(tight_jdv.has_unique_lsns()) by {
            assert(forall|lsn, addr|
                tight_jdv.addr_supports_lsn(addr, lsn) ==> jdv.addr_supports_lsn(addr, lsn));
        }
        if self.freshest_rec is Some {
            assert(index.contains_key(self.boundary_lsn));
            let addr = choose|addr: Address|
                addr.au == self.first && #[trigger]
                jdv.addr_supports_lsn(addr, self.boundary_lsn);
            let _ = jdv.instantiate_index_keys_exist_valid_entries(index, self.boundary_lsn);
            assert(tight_jdv.addr_supports_lsn(addr, self.boundary_lsn));
            assert(tight_jdv.valid_first_au(self.first));
        }
        assert(tight_jdv.pointer_is_upstream(self.freshest_rec, self.first));
        tight_jdv.build_lsn_au_index_page_walk_sub_disk(jdv, self.freshest_rec);
        tight_jdv.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);
        jdv.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);
        assert(index == self.to_tj(self.tight_dv(dv)).build_lsn_au_index(self.first));
        assert(tight_jdv.non_index_lsn_bounded(index));
    }
}

pub struct EphemeralState {
    pub image: ImageState,
    pub unmarshalled_tail: MsgHistory,  // from LinkedJournal::State
    pub lsn_au_index: Map<LSN, AU>,  // from AJ::State
    pub mini_allocator: MiniAllocator,  // from AJ::State
}

impl EphemeralState {
    // equivalent to AllocationJournal_v::initialize
    pub open spec(checked) fn init_by(self, image: ImageState, dv: DiskView) -> bool {
        let tj = self.image.to_tj(dv);
        &&& image.valid_image(dv)
        &&& self.image == image
        &&& self.unmarshalled_tail == MsgHistory::empty_history_at(
            tj.seq_end(),
        )  // LinkedJournal::initialize

        &&& self.lsn_au_index == tj.build_lsn_au_index(self.image.first)
        &&& self.mini_allocator == MiniAllocator::empty()
    }

    pub open spec(checked) fn wf(self, dv: DiskView) -> bool {
        &&& self.image.to_tj(dv).wf()
        &&& self.mini_allocator.wf()
        &&& self.unmarshalled_tail.wf()
    }

    pub open spec(checked) fn decodable(self, dv: DiskView) -> bool
        recommends
            self.wf(dv),
    {
        self.image.to_tj(dv).decodable()
    }

    pub open spec(checked) fn to_lj(self, dv: DiskView) -> LinkedJournal::State {
        LinkedJournal::State {
            truncated_journal: self.image.to_tj(dv),
            unmarshalled_tail: self.unmarshalled_tail,
        }
    }

    pub open spec(checked) fn to_aj(self, dv: DiskView) -> AllocationJournal::State {
        AllocationJournal::State {
            journal: self.to_lj(dv),
            lsn_au_index: self.lsn_au_index,
            first: self.image.first,
            mini_allocator: self.mini_allocator,
        }
    }
}

#[is_variant]
pub enum Ephemeral {
    Unknown,
    Known { v: EphemeralState },
}

pub struct DiskView {
    pub entries: Map<Address, JournalRecord>,
}

impl DiskView {
    pub open spec(checked) fn to_JournalDiskView(self, boundary_lsn: LSN) -> JournalDiskView {
        JournalDiskView { boundary_lsn: boundary_lsn, entries: self.entries }
    }
}

state_machine!{UnifiedCrashAwareJournal{
    fields {
        pub ephemeral: Ephemeral,
        pub inflight: Option<ImageState>,
        pub persistent: ImageState,
        pub dv: DiskView,  // shared disk
    }

    init!{
        initialize() {
            init persistent = ImageState::empty();
            init ephemeral = Ephemeral::Unknown;
            init inflight = Option::None;
            init dv = DiskView{entries: Map::empty()};
        }
    }

    #[is_variant]
    pub enum Label
    {
        LoadEphemeralFromPersistent,
        ReadForRecovery{ records: MsgHistory },
        QueryEndLsn{ end_lsn: LSN },
        Put{ records: MsgHistory },
        Internal{allocs: Set<AU>, deallocs: Set<AU>},
        QueryLsnPersistence{ sync_lsn: LSN },
        CommitStart{ new_boundary_lsn: LSN, max_lsn: LSN },
        CommitComplete{ require_end: LSN, discarded: Set<AU> },
        Crash,
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_ephemeral: EphemeralState) {
            require lbl is LoadEphemeralFromPersistent;
            require pre.ephemeral is Unknown;
            require new_ephemeral.init_by(pre.persistent, pre.dv);

            update ephemeral = Ephemeral::Known{ v: new_ephemeral };
            update dv = pre.persistent.tight_dv(pre.dv);
        }
    }

    transition!{
        read_for_recovery(lbl: Label) {
            require lbl is ReadForRecovery;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v().to_aj(pre.dv),
                pre.ephemeral.get_Known_v().to_aj(pre.dv),
                AllocationJournal::Label::ReadForRecovery{ messages: lbl.get_ReadForRecovery_records() }
            );
        }
    }

    transition!{
        query_end_lsn(lbl: Label) {
            require lbl is QueryEndLsn;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v().to_aj(pre.dv),
                pre.ephemeral.get_Known_v().to_aj(pre.dv),
                AllocationJournal::Label::QueryEndLsn{ end_lsn: lbl.get_QueryEndLsn_end_lsn() },
            );
        }
    }

    transition!{
        put(lbl: Label, new_ephemeral: EphemeralState) {
            require lbl is Put;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v().to_aj(pre.dv),
                new_ephemeral.to_aj(pre.dv),
                AllocationJournal::Label::Put{ messages: lbl.get_Put_records() },
            );
            update ephemeral = Ephemeral::Known{ v: new_ephemeral };
        }
    }

    transition!{
        internal(lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView) {
            require lbl is Internal;
            require pre.ephemeral is Known;

            let pre_v = pre.ephemeral.get_Known_v();
            let allocs = lbl.get_Internal_allocs();
            let deallocs = lbl.get_Internal_deallocs();

            require allocs.disjoint(pre_v.lsn_au_index.values());
            require allocs.disjoint(pre_v.mini_allocator.allocs.dom());

            require AllocationJournal::State::next(
                pre_v.to_aj(pre.dv),
                new_ephemeral.to_aj(new_dv),
                AllocationJournal::Label::InternalAllocations{ allocs, deallocs }
            );

            update ephemeral = Ephemeral::Known{ v: new_ephemeral };
            update dv = new_dv;
        }
    }

    transition!{
        query_lsn_persistence(lbl: Label) {
            require lbl is QueryLsnPersistence;
            require lbl.get_QueryLsnPersistence_sync_lsn() <= pre.persistent.seq_end(pre.dv);
        }
    }

    transition!{
        commit_start(lbl: Label, frozen_journal: ImageState, depth: nat) {
            require lbl is CommitStart;
            require pre.ephemeral is Known;
            // Can't start a commit if one is in-flight, or we'd forget to maintain the
            // invariants for the in-flight one.
            require pre.inflight is None;
            // Journal doesn't go backwards
            require pre.persistent.seq_end(pre.dv) <= frozen_journal.seq_end(pre.dv);

            let new_bdy = frozen_journal.seq_start();
            // There should be no way for the frozen journal to have passed the ephemeral map!
            require new_bdy <= lbl.get_CommitStart_max_lsn();
            // Frozen journal stitches to frozen map
            require new_bdy == lbl.get_CommitStart_new_boundary_lsn();

            // freeze for commit conditions
            let v = pre.ephemeral.get_Known_v();
            let tj = v.image.to_tj(pre.dv);

            require tj.disk_view.can_crop(v.image.freshest_rec, depth); // depth is croppable
            let cropped_tj = tj.crop(depth);
            require cropped_tj.can_discard_to(new_bdy); // new_bdy is valid after the crop

            // arbitrary if newbdy isn't present
            require frozen_journal.first == v.lsn_au_index[new_bdy];
            require frozen_journal.freshest_rec ==
                if cropped_tj.seq_end() == new_bdy { None }
                else { cropped_tj.freshest_rec };

            update inflight = Option::Some(frozen_journal);
        }
    }

    transition!{
        commit_complete(lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView) {
            require lbl is CommitComplete;
            require pre.ephemeral is Known;
            require pre.inflight is Some;

            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v().to_aj(pre.dv),
                new_ephemeral.to_aj(new_dv),
                AllocationJournal::Label::DiscardOld{
                    start_lsn: pre.inflight.unwrap().seq_start(),
                    require_end: lbl.get_CommitComplete_require_end(),
                    // where do we specify which aus are in deallocs?
                    deallocs: lbl.get_CommitComplete_discarded(),
                },
            );

            update persistent = pre.inflight.unwrap();
            update ephemeral = Ephemeral::Known{ v: new_ephemeral };
            update inflight = Option::None;
            update dv = new_dv;
        }
    }

    transition!{
        crash(lbl: Label) {
            require lbl is Crash;
            update ephemeral = Ephemeral::Unknown;
            update inflight = Option::None;
        }
    }

    pub open spec(checked) fn state_relations(self) -> bool
        recommends
            self.ephemeral is Known ==> self.ephemeral.get_Known_v().wf(self.dv),
            self.inflight is Some ==> self.inflight.unwrap().valid_image(self.dv),
            self.persistent.valid_image(self.dv)
    {
        self.ephemeral is Known ==> {
            let v = self.ephemeral.get_Known_v();
            &&& self.persistent.seq_end(self.dv) <= v.image.seq_end(self.dv)
            &&& (self.inflight is Some ==>
                self.inflight.unwrap().seq_end(self.dv) <= v.image.seq_end(self.dv))
        }
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.inflight is None
        &&& self.ephemeral is Known ==> self.ephemeral.get_Known_v().to_aj(self.dv).inv()
        &&& self.inflight is Some ==> self.inflight.unwrap().valid_image(self.dv)
        &&& self.persistent.valid_image(self.dv)
        &&& self.state_relations()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        LinkedJournal_v::TruncatedJournal::mkfs_ensures();
        reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
        assert(post.persistent.valid_image(post.dv));
    }

    #[inductive(load_ephemeral_from_persistent)]
    fn load_ephemeral_from_persistent_inductive(pre: Self, post: Self, lbl: Label,
        new_ephemeral: EphemeralState)
    {
        let v = post.ephemeral.get_Known_v();
        pre.persistent.tight_dv_preserves_valid_image(pre.dv);
        assert(v.to_aj(post.dv).inv());
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: EphemeralState)
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(LinkedJournal::State::next);
        reveal(LinkedJournal::State::next_by);
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView)
    {
        assume(false);
    }

    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label, frozen_journal: ImageState, depth: nat)
    {
        assume(false);
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView)
    {
        assume(false);
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

  }}  // state_machine


} // verus!
  // verus
