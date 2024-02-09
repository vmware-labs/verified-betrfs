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
        &&& ({
            let index = self.to_tj(dv).build_lsn_au_index(self.first);
            let tight_jdv = self.tight_dv(dv).to_JournalDiskView(self.boundary_lsn);
            &&& tight_jdv.non_index_lsn_bounded(index)
        })
    }

    pub open spec(checked) fn tight_domain(self, dv: DiskView) -> Set<Address>
        recommends
            self.to_tj(dv).disk_view.pointer_is_upstream(self.freshest_rec, self.first)
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
            self.to_tj(dv).disk_view.pointer_is_upstream(self.freshest_rec, self.first)
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

    pub proof fn sub_disk_preserves_valid_image(self, big: Self, dv: DiskView, big_dv: DiskView) 
        requires
            self.valid_image(dv),
            big.valid_image(big_dv),
            big.seq_start() <= self.seq_start(),
            self.seq_end(dv) <= big.seq_end(big_dv),
            dv.entries <= big_dv.entries,
            big_dv.entries.dom().disjoint(au_addrs_past_pointer(big.freshest_rec))
        ensures 
            self.valid_image(big_dv)
    {
        let pre_jdv = dv.to_JournalDiskView(self.boundary_lsn);
        let post_jdv = big_dv.to_JournalDiskView(self.boundary_lsn);
        let big_jdv = big_dv.to_JournalDiskView(big.boundary_lsn);

        assert(post_jdv.valid_ranking(big_jdv.the_ranking()));
        assert(post_jdv.acyclic());

        assert(post_jdv.internal_au_pages_fully_linked()) by {
            reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
        }
        assert(post_jdv.has_unique_lsns()) by {
            assert(forall |lsn, addr| post_jdv.addr_supports_lsn(addr, lsn) 
                ==> big_jdv.addr_supports_lsn(addr, lsn) );
        }

        if self.freshest_rec is Some {
            let addr = choose |addr: Address| addr.au == self.first 
                && #[trigger] pre_jdv.addr_supports_lsn(addr, self.boundary_lsn);
            
            assert(post_jdv.entries.contains_key(addr));
            assert(post_jdv.addr_supports_lsn(addr, self.boundary_lsn));
            assert(post_jdv.valid_first_au(self.first));
        }

        assert(post_jdv.decodable(self.freshest_rec));
        assert(post_jdv.pointer_is_upstream(self.freshest_rec, self.first));

        // tight dv non index lsn bounded
        let pre_index = self.to_tj(dv).build_lsn_au_index(self.first);
        let post_index = self.to_tj(big_dv).build_lsn_au_index(self.first);

        // index are the same because 
        pre_jdv.build_lsn_au_index_page_walk_sub_disk(post_jdv, self.freshest_rec);
        pre_jdv.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);
        post_jdv.build_lsn_au_index_equiv_page_walk(self.freshest_rec, self.first);
        assert(pre_index == post_index);

        // index must be a subset of the big buddy
        let big_index = big.to_tj(big_dv).build_lsn_au_index(big.first);
        self.to_tj(dv).sub_disk_build_sub_lsn_au_index(self.first, big.to_tj(big_dv), big.first);
        assert(pre_index <= big_index);

        let pre_tight_jdv = self.tight_dv(dv).to_JournalDiskView(self.boundary_lsn);
        let post_tight_jdv = self.tight_dv(big_dv).to_JournalDiskView(self.boundary_lsn);
        let big_tight_jdv = big.tight_dv(big_dv).to_JournalDiskView(big.boundary_lsn);

        assert forall|addr, lsn| ({
            &&& post_tight_jdv.entries.dom().contains(addr)
            &&& post_tight_jdv.entries[addr].message_seq.contains(lsn)
            &&& post_index.values().contains(addr.au)
            &&& !post_index.contains_key(lsn)
        }) implies lsn < self.boundary_lsn
        by {
            let valid_lsn = choose |valid_lsn| #[trigger] post_index.contains_key(valid_lsn) && post_index[valid_lsn] == addr.au;
            assert(big_index.contains_key(valid_lsn));

            if !big_tight_jdv.entries.contains_key(addr) {
                assert(au_addrs_past_pointer(big.freshest_rec).contains(addr));
                assert(false);
            }
            assert(big_tight_jdv.entries[addr].message_seq.contains(lsn)); // trigger

            self.to_tj(dv).build_lsn_au_index_ensures(self.first);
            big.to_tj(big_dv).build_lsn_au_index_ensures(big.first);

            if lsn >= self.seq_end(big_dv) {
                if big_index.contains_key(lsn) {
                    assert(self.freshest_rec is Some);
                    assert(post_jdv.entries.contains_key(self.freshest_rec.unwrap()));

                    let last_lsn = (post_jdv.entries[self.freshest_rec.unwrap()].message_seq.seq_end-1) as nat;
                    assert(post_jdv.addr_supports_lsn(self.freshest_rec.unwrap(), last_lsn));

                    assert(post_index.contains_key(last_lsn)); // trigger
                    assert(post_index[last_lsn] == self.freshest_rec.unwrap().au);
                    assert(post_index.values().contains(self.freshest_rec.unwrap().au));
                    assert(post_tight_jdv.addr_supports_lsn(self.freshest_rec.unwrap(), last_lsn));

                    assert(big_index.contains_key(last_lsn));
                    assert(big_index[last_lsn] == self.freshest_rec.unwrap().au);

                    assert(addr.au != self.freshest_rec.unwrap().au) by {
                        reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
                    }

                    assert(valid_lsn <= last_lsn <= lsn);
                    assert(big_index[valid_lsn] == addr.au);
                    assert(big_index[lsn] == addr.au) by {
                        assert(big_jdv.addr_supports_lsn(addr, lsn));
                        let _ = big_jdv.instantiate_index_keys_exist_valid_entries(big_index, lsn);
                    }
            
                    assert(contiguous_lsns(big_index, valid_lsn, last_lsn, lsn));
                    assert(big_index[valid_lsn] == big_index[last_lsn]);
                    assert(false);
                } else {
                    assert(lsn < big.boundary_lsn);
                }
            }
        }
        assert(post_tight_jdv.non_index_lsn_bounded(post_index));
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

            // captured by allocation journal already
            // require allocs.disjoint(pre_v.lsn_au_index.values());
            // require allocs.disjoint(pre_v.mini_allocator.allocs.dom());

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
        &&& self.ephemeral is Known ==> {
            let v = self.ephemeral.get_Known_v();
            &&& v.image.seq_start() <= self.persistent.seq_start()
            &&& self.persistent.seq_end(self.dv) <= v.image.seq_end(self.dv)
        }
        &&& self.ephemeral is Known && self.inflight is Some ==> {
            let v = self.ephemeral.get_Known_v();
            &&& v.image.seq_start() <= self.inflight.unwrap().seq_start()
            &&& self.inflight.unwrap().seq_end(self.dv) <= v.image.seq_end(self.dv)
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
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        let pre_aj = pre.ephemeral.get_Known_v().to_aj(pre.dv);
        let post_aj = post.ephemeral.get_Known_v().to_aj(post.dv);

        let aj_lbl = AllocationJournal::Label::InternalAllocations{
            allocs: lbl.get_Internal_allocs(), 
            deallocs: lbl.get_Internal_deallocs() 
        };

        AJ::State::inv_next(pre_aj, post_aj, aj_lbl);
        assert( post_aj.inv() );

        match choose |step| AJ::State::next_by(pre_aj, post_aj, aj_lbl, step)
        {
            AllocationJournal::Step::internal_journal_marshal(cut, addr, post_linked_journal) => {
                let v = post.ephemeral.get_Known_v();
                post.persistent.sub_disk_preserves_valid_image(v.image, pre.dv, post.dv);
                if post.inflight is Some {
                    post.inflight.unwrap().sub_disk_preserves_valid_image(v.image, pre.dv, post.dv);
                }
                assert(post.state_relations());
            }
            _ => {  assert(post.state_relations()); }
        }
    }

    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label, frozen_journal: ImageState, depth: nat)
    {
        let v = pre.ephemeral.get_Known_v();
        let tj = v.image.to_tj(pre.dv);

        tj.disk_view.pointer_after_crop_seq_end(tj.freshest_rec, depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);

        let frozen_tj = frozen_journal.to_tj(pre.dv);
        let frozen_jdv = frozen_tj.disk_view;
        assert(frozen_jdv.decodable(frozen_journal.freshest_rec));
        assert(frozen_jdv.valid_ranking(tj.disk_view.the_ranking()));
        assert(frozen_jdv.acyclic());

        reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
        assert(frozen_jdv.internal_au_pages_fully_linked());
        assert(frozen_jdv.has_unique_lsns()) by {
            assert(forall|lsn, addr| #[trigger] frozen_jdv.addr_supports_lsn(addr, lsn) 
                ==> tj.disk_view.addr_supports_lsn(addr, lsn));
        }

        tj.build_lsn_au_index_ensures(v.image.first);
        if frozen_journal.freshest_rec is Some {
            assert(frozen_jdv.upstream(frozen_journal.freshest_rec.unwrap()));
            assert(v.lsn_au_index.contains_key(frozen_journal.boundary_lsn));
            let addr = tj.disk_view.instantiate_index_keys_exist_valid_entries(v.lsn_au_index, frozen_journal.boundary_lsn);
            assert(frozen_jdv.addr_supports_lsn(addr, frozen_journal.boundary_lsn));
            assert(frozen_jdv.valid_first_au(frozen_journal.first));
        }

        assert(frozen_jdv.pointer_is_upstream(frozen_journal.freshest_rec, frozen_journal.first));

        let frozen_index = frozen_tj.build_lsn_au_index(frozen_journal.first);
        frozen_tj.build_lsn_au_index_ensures(frozen_journal.first);
        frozen_tj.sub_disk_build_sub_lsn_au_index(frozen_journal.first, tj, v.image.first);
        assert(frozen_index <= v.lsn_au_index);

        let tight_frozen_jdv = JournalDiskView{
            boundary_lsn: frozen_jdv.boundary_lsn,
            entries: frozen_journal.tight_dv(pre.dv).entries
        };

        // NOTE(JL): this is copy pasting from allocation journal 
        // maybe this shouldn't be in allocation journal in the first place
        assert forall|addr, lsn| ({
            &&& tight_frozen_jdv.entries.dom().contains(addr)
            &&& tight_frozen_jdv.entries[addr].message_seq.contains(lsn)
            &&& frozen_index.values().contains(addr.au)
            &&& !frozen_index.contains_key(lsn)
        }) implies lsn < tight_frozen_jdv.boundary_lsn 
        by {
            if v.lsn_au_index.contains_key(lsn) && lsn >= frozen_journal.to_tj(pre.dv).seq_end() {
                assert(tj.disk_view.addr_supports_lsn(addr, lsn));
                assert(frozen_journal.freshest_rec is Some);
                if addr.au == frozen_journal.freshest_rec.unwrap().au {
                    reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
                    assert(frozen_journal.freshest_rec.unwrap().after_page(addr));
                    assert(false);
                } else {
                    assert(v.lsn_au_index[lsn] == addr.au) by {
                        let _ = tj.disk_view.instantiate_index_keys_exist_valid_entries(v.lsn_au_index, lsn);
                    }

                    let valid_lsn = choose |valid_lsn| frozen_index.contains_key(valid_lsn) 
                        && #[trigger] frozen_index[valid_lsn] == addr.au;
                    let valid_addr = tj.disk_view.instantiate_index_keys_exist_valid_entries(v.lsn_au_index, valid_lsn);

                    assert(frozen_index[valid_lsn] == addr.au);
                    assert(v.lsn_au_index.contains_key(valid_lsn)); // trigger
                    assert(v.lsn_au_index[valid_lsn] == frozen_index[valid_lsn]);
                    assert(v.lsn_au_index[valid_lsn] == v.lsn_au_index[lsn]);

                    let last_frozen_lsn = (frozen_tj.seq_end()-1) as nat;
                    assert(v.lsn_au_index.contains_key(last_frozen_lsn)); // trigger
                    assert(tj.disk_view.addr_supports_lsn(frozen_journal.freshest_rec.unwrap(), last_frozen_lsn));
                    assert(v.lsn_au_index[last_frozen_lsn] == frozen_journal.freshest_rec.unwrap().au) by {
                        let _ = tj.disk_view.instantiate_index_keys_exist_valid_entries(v.lsn_au_index, last_frozen_lsn);
                    }

                    assert(contiguous_lsns(v.lsn_au_index, valid_lsn, last_frozen_lsn, lsn));
                    assert(v.lsn_au_index[valid_lsn] == v.lsn_au_index[last_frozen_lsn]);
                    assert(false);
                }
            }            
        }
        assert(tight_frozen_jdv.non_index_lsn_bounded(frozen_index));
        assert(post.inflight.unwrap().valid_image(post.dv));
        assert(post.state_relations());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView)
    {
        let pre_aj = pre.ephemeral.get_Known_v().to_aj(pre.dv);
        let post_aj = post.ephemeral.get_Known_v().to_aj(post.dv);
        let deallocs = lbl.get_CommitComplete_discarded();

        let aj_lbl = AllocationJournal::Label::DiscardOld{
            start_lsn: pre.inflight.unwrap().seq_start(),
            require_end: lbl.get_CommitComplete_require_end(),
            deallocs: deallocs,
        };

        AJ::State::inv_next(pre_aj, post_aj, aj_lbl);
        assert( post_aj.inv() );

        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        // prove persistent image still valid upon a disk truncate
        let bdy = post.persistent.boundary_lsn;
        let root = post.persistent.freshest_rec;

        let pre_jdv = pre.dv.to_JournalDiskView(bdy);
        let post_jdv = post.dv.to_JournalDiskView(bdy);

        let pre_index = post.persistent.to_tj(pre.dv).build_lsn_au_index(post.persistent.first);
        post.persistent.to_tj(pre.dv).build_lsn_au_index_ensures(post.persistent.first);
        post.persistent.to_tj(pre.dv).sub_disk_build_sub_lsn_au_index(post.persistent.first, pre_aj.tj(), pre_aj.first);
        assert(pre_index <= pre_aj.lsn_au_index);

        pre_aj.tj().build_lsn_au_index_ensures(pre_aj.first);
        assert(post_aj.lsn_au_index <= pre_aj.lsn_au_index);

        if root is Some {
            // prove root is_nondanglingly_pointer
            let last_lsn = (pre.dv.entries[root.unwrap()].message_seq.seq_end - 1) as nat;
            assert(pre_aj.tj().disk_view.addr_supports_lsn(root.unwrap(), last_lsn));
            assert(pre_aj.lsn_au_index.contains_key(last_lsn));
            assert(pre_aj.lsn_au_index[last_lsn] == root.unwrap().au) by {
                let _ = pre_aj.tj().disk_view.instantiate_index_keys_exist_valid_entries(pre_aj.lsn_au_index, last_lsn);
            }
            assert(post_aj.lsn_au_index.contains_key(last_lsn));
            assert(!deallocs.contains(root.unwrap().au));
            assert(post_jdv.is_nondangling_pointer(root));

            // prove valid_first_au
            assert(pre_index.contains_key(bdy));
            pre_jdv.first_contains_boundary(root, post.persistent.first);
            pre_jdv.build_lsn_au_index_equiv_page_walk(root, post.persistent.first);

            assert(post.persistent.first == pre_index[bdy]);
            assert(post_aj.first === post_aj.lsn_au_index[bdy]);
            assert(post.persistent.first == post_aj.first);
            assert(post_jdv.valid_first_au(post.persistent.first));
        }
        assert(post_jdv.decodable(root));
        assert(post_jdv.acyclic());

        assert(post_jdv.internal_au_pages_fully_linked());
        assert(post_jdv.has_unique_lsns());
        assert(post_jdv.pointer_is_upstream(root, post.persistent.first));

        let post_index = post.persistent.to_tj(post.dv).build_lsn_au_index(post.persistent.first);
        post.persistent.to_tj(post.dv).build_lsn_au_index_ensures(post.persistent.first);
        post_jdv.build_lsn_au_index_equiv_page_walk(root, post.persistent.first);
        post_jdv.build_lsn_au_index_page_walk_sub_disk(pre_jdv, root);
        assert(post_index == pre_index);

        post.persistent.to_tj(post.dv).sub_disk_build_sub_lsn_au_index(
            post.persistent.first, post_aj.tj(), post_aj.first);
        assert(post_index <= post_aj.lsn_au_index);
        assert(post_index.dom() <= post_aj.lsn_au_index.dom());
        assert(post_index.values() <= post_aj.lsn_au_index.values());

        let tight_pre_jdv = post.persistent.tight_dv(pre.dv).to_JournalDiskView(bdy);
        let tight_post_jdv = post.persistent.tight_dv(post.dv).to_JournalDiskView(bdy);

        assert(tight_post_jdv.entries.dom() <= tight_pre_jdv.entries.dom());
        assert(tight_pre_jdv.entries =~= tight_post_jdv.entries);

        assert(tight_pre_jdv.non_index_lsn_bounded(post_index));
        assert(tight_post_jdv.non_index_lsn_bounded(post_index));

        assert(post.persistent.valid_image(post.dv));
        assert(post.state_relations());
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

  }}  // state_machine


} // verus!
  // verus
