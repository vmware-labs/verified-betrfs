// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::map::*;
use vstd::map_lib::*;
use vstd::prelude::*;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{AllocationJournal as AJ, *};
use crate::allocation_layer::MiniAllocator_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::JournalRecord;
use crate::journal::LinkedJournal_v::LinkedJournal;

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
            disk_view: dv.to_jdv(self.boundary_lsn),
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
        let jdv = dv.to_jdv(self.boundary_lsn);
        &&& jdv.wf_addrs()
        &&& jdv.pointer_is_upstream(self.freshest_rec, self.first)
        &&& jdv.bounded_inactive_lsns(self.to_tj(dv).build_lsn_au_index(self.first), self.freshest_rec)
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
        requires self.valid_image(dv)
        ensures self.valid_image(self.tight_dv(dv)),
            self.to_tj(dv).build_lsn_au_index(self.first) == 
            self.to_tj(self.tight_dv(dv)).build_lsn_au_index(self.first),
    {
        let pre_dv = self.to_tj(dv).disk_view;
        let post_dv = self.to_tj(self.tight_dv(dv)).disk_view;
        let index = self.to_tj(dv).build_lsn_au_index(self.first);

        let sub_end = pre_dv.tj_at(self.freshest_rec).seq_end();
        let sub_lsns = Set::new(|lsn| self.seq_start() <= lsn < sub_end);

        self.to_tj(dv).build_lsn_au_index_ensures(self.first);
//        assert(index.dom() =~= sub_lsns);
        assert(index.restrict(sub_lsns) =~= index);

        let sub_dv = self.to_tj(dv).sub_disk_preserves_pointer_is_upstream(index, self.first, self.seq_start(), self.freshest_rec, self.first);
//        assert(sub_dv.pointer_is_upstream(self.freshest_rec, self.first));
//        assert(sub_dv.entries.dom() =~= self.tight_domain(dv));
//        assert(sub_dv.entries =~= post_dv.entries);

        self.to_tj(dv).sub_disk_preserves_bounded_inactive_lsns(index, self.first, self.to_tj(self.tight_dv(dv)), self.first);
    }
}

pub struct EphemeralState {
    pub image: ImageState,
    pub unmarshalled_tail: MsgHistory,  // from LinkedJournal::State
    pub lsn_au_index: Map<LSN, AU>,     // from AJ::State
    pub mini_allocator: MiniAllocator,  // from AJ::State
}

impl EphemeralState {
    // equivalent to AllocationJournal_v::initialize
    pub open spec(checked) fn init_by(self, image: ImageState, dv: DiskView) -> bool 
        recommends 
    {
        let tj = self.image.to_tj(dv);
        &&& image.valid_image(dv)
        &&& self.image == image
        &&& self.unmarshalled_tail == MsgHistory::empty_history_at(tj.seq_end()) 
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

    // NOTE(JL): contains image might be a better name?
    pub open spec(checked) fn supports_image(self, dv: DiskView, image: ImageState) -> bool
        recommends 
            self.wf(dv),
            image.valid_image(dv),
    {
        &&& self.image.seq_start() <= image.seq_start()
        &&& image.seq_end(dv) <= self.image.seq_end(dv)
        &&& image.freshest_rec is Some ==> {
            &&& self.lsn_au_index.contains_key(image.seq_start())
            &&& self.lsn_au_index[image.seq_start()] == image.first
        }
    }
}

pub enum Ephemeral {
    Unknown,
    Known { v: EphemeralState },
}

pub struct DiskView {
    pub entries: Map<Address, JournalRecord>,
}

impl DiskView {
    pub open spec(checked) fn to_jdv(self, boundary_lsn: LSN) -> JournalDiskView {
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
        Crash{ keep_in_flight: bool },
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_ephemeral: EphemeralState) {
            require lbl is LoadEphemeralFromPersistent;
            require pre.ephemeral is Unknown;
            require pre.persistent.valid_image(pre.dv); // maintained by invariant
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
                pre.ephemeral->v.to_aj(pre.dv),
                pre.ephemeral->v.to_aj(pre.dv),
                AllocationJournal::Label::ReadForRecovery{ messages: lbl.arrow_ReadForRecovery_records() }
            );
        }
    }

    transition!{
        query_end_lsn(lbl: Label) {
            require lbl is QueryEndLsn;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral->v.to_aj(pre.dv),
                pre.ephemeral->v.to_aj(pre.dv),
                AllocationJournal::Label::QueryEndLsn{ end_lsn: lbl->end_lsn },
            );
        }
    }

    transition!{
        put(lbl: Label, new_ephemeral: EphemeralState) {
            require lbl is Put;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral->v.to_aj(pre.dv),
                new_ephemeral.to_aj(pre.dv),
                AllocationJournal::Label::Put{ messages: lbl.arrow_Put_records() },
            );
            update ephemeral = Ephemeral::Known{ v: new_ephemeral };
        }
    }

    transition!{
        internal(lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView) {
            require lbl is Internal;
            require pre.ephemeral is Known;

            let pre_v = pre.ephemeral->v;
            let allocs = lbl->allocs;
            let deallocs = lbl.arrow_Internal_deallocs();

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
            require lbl->sync_lsn <= pre.persistent.seq_end(pre.dv);
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
            require new_bdy <= lbl->max_lsn;
            // Frozen journal stitches to frozen map
            require new_bdy == lbl->new_boundary_lsn;

            // freeze for commit conditions
            let v = pre.ephemeral->v;
            let tj = v.image.to_tj(pre.dv);

            require tj.disk_view.can_crop(v.image.freshest_rec, depth); // depth is croppable
            let cropped_tj = tj.crop(depth);
            require cropped_tj.can_discard_to(new_bdy); // new_bdy is valid after the crop

            // arbitrary if newbdy isn't present
            require frozen_journal.first == 
                if frozen_journal.freshest_rec is None { arbitrary() }
                else { v.lsn_au_index[new_bdy] };
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
                pre.ephemeral->v.to_aj(pre.dv),
                new_ephemeral.to_aj(new_dv),
                AllocationJournal::Label::DiscardOld{
                    // common case would be a no op (if only journal was synced)
                    // inflight.seq_start would have been the same as ephemeral seq_start
                    // unless map is actually synced as well
                    start_lsn: pre.inflight.unwrap().seq_start(), 
                    require_end: lbl->require_end,
                    // where do we specify which aus are in deallocs?
                    deallocs: lbl->discarded,
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
            update persistent = if lbl->keep_in_flight && pre.inflight is Some { pre.inflight.unwrap() } else { pre.persistent };
        }
    }

    pub open spec(checked) fn state_relations(self) -> bool
        recommends
            self.ephemeral is Known ==> self.ephemeral->v.wf(self.dv),
            self.inflight is Some ==> self.inflight.unwrap().valid_image(self.dv),
            self.persistent.valid_image(self.dv)
    {
        &&& self.ephemeral is Known ==> 
            self.ephemeral->v.supports_image(self.dv, self.persistent)
        &&& self.ephemeral is Known && self.inflight is Some ==> 
            self.ephemeral->v.supports_image(self.dv, self.inflight.unwrap())
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.inflight is None
        &&& self.ephemeral is Known ==> self.ephemeral->v.to_aj(self.dv).inv()
        &&& self.inflight is Some ==> self.inflight.unwrap().valid_image(self.dv)
        &&& self.persistent.valid_image(self.dv)
        &&& self.state_relations()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        LinkedJournal_v::TruncatedJournal::mkfs_ensures();
        assert(post.persistent.valid_image(post.dv)) by {
            reveal(LinkedJournal_v::DiskView::pages_allocated_in_lsn_order);
        }
    }

    #[inductive(load_ephemeral_from_persistent)]
    fn load_ephemeral_from_persistent_inductive(pre: Self, post: Self, lbl: Label,
        new_ephemeral: EphemeralState)
    {
        let v = post.ephemeral->v;
        pre.persistent.tight_dv_preserves_valid_image(pre.dv);
        v.image.to_tj(pre.dv).build_lsn_au_index_ensures(pre.persistent.first);

//        assert(v.to_aj(post.dv).inv());
//        assert(post.state_relations());
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
        // needed to reveal to communicate that ephemeral boundary_lsn and freshest rec did not change
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

        AJ::State::inv_next(
            pre.ephemeral->v.to_aj(pre.dv), 
            post.ephemeral->v.to_aj(post.dv), 
            AllocationJournal::Label::InternalAllocations{
                allocs: lbl->allocs, 
                deallocs: lbl.arrow_Internal_deallocs() 
            }
        );

        let post_aj = post.ephemeral->v.to_aj(post.dv);
        post_aj.subrange_preserves_valid_structure(post.persistent.seq_start(), post.persistent.freshest_rec, post.persistent.first);
        if post.inflight is Some {
            let image = post.inflight.unwrap();
            post_aj.subrange_preserves_valid_structure(image.seq_start(), image.freshest_rec, image.first);
        }
    }

    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label, frozen_journal: ImageState, depth: nat)
    {
        let v = pre.ephemeral->v;
        let tj = v.image.to_tj(pre.dv);

        tj.disk_view.pointer_after_crop_seq_end(tj.freshest_rec, depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);
        tj.build_lsn_au_index_ensures(v.image.first);
        v.to_aj(pre.dv).subrange_preserves_valid_structure(frozen_journal.seq_start(), frozen_journal.freshest_rec, frozen_journal.first);
//        assert(frozen_journal.valid_image(pre.dv));
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView)
    {
        let pre_aj = pre.ephemeral->v.to_aj(pre.dv);
        let post_aj = post.ephemeral->v.to_aj(post.dv);
        let deallocs = lbl->discarded;

        let aj_lbl = AllocationJournal::Label::DiscardOld{
            start_lsn: pre.inflight.unwrap().seq_start(),
            require_end: lbl->require_end,
            deallocs: deallocs,
        };

        AJ::State::inv_next(pre_aj, post_aj, aj_lbl);
//        assert( post_aj.inv() );

        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        // show that decodable is true post a journal truncation
        let root = post.persistent.freshest_rec;
        if root is Some {
            let bdy = post.persistent.seq_start();
            let last_lsn = (post.persistent.seq_end(pre.dv) - 1) as nat;

            pre_aj.tj().build_lsn_au_index_ensures(pre_aj.first);
            pre_aj.tj().disk_view.addr_supports_lsn_consistent_with_index(pre_aj.lsn_au_index, last_lsn, root.unwrap());
            // assert(pre_aj.lsn_au_index[last_lsn] == root.unwrap().au);
            assert(post_aj.lsn_au_index.contains_key(last_lsn));
//            assert(post_aj.lsn_au_index <= pre_aj.lsn_au_index);
//            assert(!deallocs.contains(root.unwrap().au));
            assert(post.dv.entries.contains_key(root.unwrap()));
        }

        post_aj.subrange_preserves_valid_structure(post.persistent.seq_start(), post.persistent.freshest_rec, post.persistent.first);
//        assert(post.persistent.valid_image(post.dv));
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label)
    {
    }

  }}  // state_machine


} // verus!
  // verus