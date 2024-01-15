// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// use builtin_macros::*;
// use state_machines_macros::state_machine;

// use vstd::prelude::*;
// use vstd::map::*;
// use vstd::map_lib::*;
// use crate::abstract_system::StampedMap_v::LSN;
// use crate::abstract_system::MsgHistory_v::*;
// use crate::disk::GenericDisk_v::*;
// use crate::disk::GenericDisk_v::AU;
// use crate::journal::LinkedJournal_v;
// use crate::journal::LinkedJournal_v::LinkedJournal;
// use crate::journal::LinkedJournal_v::JournalRecord;
// use crate::allocation_layer::AllocationJournal_v::*;
// use crate::allocation_layer::MiniAllocator_v::*;

// verus!{
// pub type JournalDiskView = LinkedJournal_v::DiskView;

// pub struct ImageState {
//     pub freshest_rec: Pointer,  // from LinkedJournal::TruncatedJournal
//     pub boundary_lsn: LSN,      // from LinkedJournal::TruncatedJournal
//     pub first: AU,              // from AllocationJournal::State, needed to faciliate AU recovery scan (page skip)
// }

// impl ImageState {
//     pub open spec(checked) fn empty() -> Self {
//         ImageState {
//             freshest_rec: None,
//             boundary_lsn: 0,
//             first: 0,
//         }
//     }

//     pub open spec(checked) fn dom(self, dv: DiskView) -> Set<Address>
//     {
//         if self.to_tj(dv).decodable() {
//             self.to_tj(dv).build_lsn_addr_index().values()
//         } else {
//             Set::empty() // NOT REACHED WHEN INV is true
//         }
//     }

//     pub open spec(checked) fn wf(self, dv: DiskView) -> bool {
//         self.freshest_rec is Some ==> self.dom(dv).contains(self.freshest_rec.unwrap())
//     }

//     // equivalent to AllocationJournal::valid_journal_image
//     pub open spec(checked) fn valid_image(self, dv: DiskView) -> bool
//     {
//         &&& dv.to_JournalDiskView(self.boundary_lsn).wf()
//         &&& dv.to_JournalDiskView(self.boundary_lsn).pointer_is_upstream(
//                 self.freshest_rec, 
//                 self.first
//             )
//     }

//     pub open spec(checked) fn to_tj(self, dv: DiskView) -> LinkedJournal_v::TruncatedJournal
//     {
//         LinkedJournal_v::TruncatedJournal{
//             freshest_rec: self.freshest_rec,
//             disk_view: dv.to_JournalDiskView(self.boundary_lsn)
//         }
//     }

//     pub open spec(checked) fn seq_start(self) -> LSN
//     {
//         self.boundary_lsn
//     }

//     pub open spec(checked) fn seq_end(self, dv: DiskView) -> LSN
//         recommends  dv.is_nondangling_pointer(self.freshest_rec)
//     {
//         if self.freshest_rec is None { 
//             self.boundary_lsn 
//         } else { 
//             dv.entries[self.freshest_rec.unwrap()].message_seq.seq_end 
//         }
//     }
// }

// pub struct EphemeralState {
//     pub image: ImageState,
//     pub unmarshalled_tail: MsgHistory,  // from LinkedJournal::State
//     pub lsn_au_index: Map<LSN, AU>,     // from AllocationJournal::State
//     pub mini_allocator: MiniAllocator,  // from AllocationJournal::State
// }

// impl EphemeralState {
//     // equivalent to AllocationJournal_v::initialize
//     pub open spec(checked) fn init_by(self, image: ImageState, dv: DiskView) -> bool
//         recommends image.valid_image(dv)
//     {
//         let tj = self.image.to_tj(dv);
//         &&& self.image == image
//         &&& self.unmarshalled_tail == MsgHistory::empty_history_at(tj.build_tight().seq_end()) // LikesJournal::initialize
//         &&& self.lsn_au_index == AllocationJournal::State::build_lsn_au_index(tj, self.image.first)
//         &&& self.mini_allocator == MiniAllocator::empty()
//     }

//     pub open spec(checked) fn wf(self, dv: DiskView) -> bool 
//     {
//         &&& self.image.to_tj(dv).wf()
//         &&& self.unmarshalled_tail.wf()
//     }

//     pub open spec(checked) fn decodable(self, dv: DiskView) -> bool
//         recommends self.wf(dv)
//     {
//         self.image.to_tj(dv).decodable()
//     }

//     pub open spec(checked) fn to_lj(self, dv: DiskView) -> LinkedJournal::State
//     {
//         LinkedJournal::State{
//             truncated_journal: self.image.to_tj(dv),
//             unmarshalled_tail: self.unmarshalled_tail,
//         }
//     }

//     pub open spec(checked) fn same_except_lj(self, new_state: Self) -> bool
//     {
//         new_state == EphemeralState{
//             image: ImageState{
//                 first: self.image.first,
//                 .. new_state.image
//             },
//             unmarshalled_tail: new_state.unmarshalled_tail,
//             ..self
//         }
//     }

//     pub open spec(checked) fn is_marshalled_state(self, dv: DiskView, allocs: Set<AU>, deallocs: Set<AU>,
//         cut: LSN, addr: Address, new_state: Self, new_dv: DiskView) -> bool
//     {
//         &&& self.mini_allocator.wf()
//         &&& self.to_lj(dv).wf()
//         &&& allocs == Set::<AU>::empty()
//         &&& deallocs == Set::<AU>::empty()
//         &&& self.mini_allocator.tight_next_addr(self.image.freshest_rec, addr)
//         &&& LinkedJournal::State::internal_journal_marshal(
//                 self.to_lj(dv), new_state.to_lj(new_dv),
//                 LinkedJournal::Label::Internal{}, cut, addr
//             )
//         // other image fields bounded by internal_journal_marshal
//         &&& new_state.image.first == 
//                 if self.image.freshest_rec is Some { self.image.first } else { addr.au }
//         &&& new_state.lsn_au_index == lsn_au_index_append_record(
//                 self.lsn_au_index, self.unmarshalled_tail.discard_recent(cut), addr.au)
//         &&& new_state.mini_allocator == self.mini_allocator.allocate_and_observe(addr)
//     }

//     pub open spec(checked) fn is_allocator_fill(self, dv: DiskView, allocs: Set<AU>, deallocs: Set<AU>, new_state: Self, new_dv: DiskView) -> bool
//     {
//         &&& self.mini_allocator.wf()
//         &&& self.to_lj(dv).wf()
//         &&& allocs.disjoint(self.mini_allocator.allocs.dom())
//         &&& deallocs == Set::<AU>::empty()
//         &&& new_state == EphemeralState{ mini_allocator: self.mini_allocator.add_aus(allocs), ..self}
//         &&& new_dv == dv
//     }

//     pub open spec(checked) fn is_allocator_prune(self, dv: DiskView, allocs: Set<AU>, deallocs: Set<AU>, new_state: Self, new_dv: DiskView) -> bool
//     {
//         &&& self.mini_allocator.wf()
//         &&& self.to_lj(dv).wf()
//         &&& allocs == Set::<AU>::empty()
//         &&& forall |au| #![auto] deallocs.contains(au) ==> self.mini_allocator.can_remove(au)
//         &&& new_state == EphemeralState{ mini_allocator: self.mini_allocator.prune(deallocs), ..self}
//         &&& new_dv == dv
//     }

//     pub open spec(checked) fn is_no_op(self, dv: DiskView, allocs: Set<AU>, deallocs: Set<AU>, new_state: Self, new_dv: DiskView) -> bool
//     {
//         &&& allocs == Set::<AU>::empty()
//         &&& deallocs == Set::<AU>::empty()
//         &&& new_state == self
//         &&& new_dv == dv
//     }

//     pub open spec(checked) fn is_internal_op(self, dv: DiskView, allocs: Set<AU>, deallocs: Set<AU>, new_state: Self, new_dv: DiskView) -> bool
//     {
//         ||| exists |cut, addr| self.is_marshalled_state(dv, allocs, deallocs, cut, addr, new_state, new_dv) == true
//         ||| self.is_allocator_fill(dv, allocs, deallocs, new_state, new_dv) == true
//         ||| self.is_allocator_prune(dv, allocs, deallocs, new_state, new_dv) == true
//         ||| self.is_no_op(dv, allocs, deallocs, new_state, new_dv) == true
//     }
// }

// #[is_variant]
// pub enum Ephemeral
// {
//     Unknown,
//     Known{ v: EphemeralState }
// }

// pub struct DiskView {
//     pub entries: Map<Address, JournalRecord>
// }

// impl DiskView {
//     pub open spec(checked) fn to_JournalDiskView(self, boundary_lsn: LSN) -> JournalDiskView
//     {
//         JournalDiskView{ boundary_lsn: boundary_lsn, entries: self.entries }
//     }

//     pub open spec(checked) fn entries_wf(self) -> bool
//     {
//         forall |addr| #[trigger] self.entries.contains_key(addr) ==> self.entries[addr].wf()
//     }

//     pub open spec(checked) fn is_nondangling_pointer(self, ptr: Pointer) -> bool 
//     {
//         ptr.is_Some() ==> self.entries.contains_key(ptr.unwrap())
//     }

//     pub open spec(checked) fn nondangling_pointers(self, boundary_lsn: LSN, dom: Set<Address>) -> bool 
//         recommends dom.subset_of(self.entries.dom())
//     {
//         forall |addr| #[trigger] dom.contains(addr)
//             ==> self.is_nondangling_pointer(self.entries[addr].cropped_prior(boundary_lsn))
//     }
// }

// // NOTE: should never take a step with the linked journal 
// state_machine!{UnifiedCrashAwareJournal{
//     fields {
//         pub ephemeral: Ephemeral,
//         pub persistent: ImageState,
//         pub inflight: Option<ImageState>,
//         pub dv: DiskView,  // shared disk
//     }

//     init!{
//         initialize() {
//             init persistent = ImageState::empty();
//             init ephemeral = Ephemeral::Unknown;
//             init inflight = Option::None;
//             init dv = DiskView{entries: Map::empty()};
//         }
//     }

//     #[is_variant]
//     pub enum Label
//     {
//         LoadEphemeralFromPersistent,
//         ReadForRecovery{ records: MsgHistory },
//         QueryEndLsn{ end_lsn: LSN },
//         Put{ records: MsgHistory },
//         Internal{allocs: Set<AU>, deallocs: Set<AU>},
//         QueryLsnPersistence{ sync_lsn: LSN },
//         CommitStart{ new_boundary_lsn: LSN, max_lsn: LSN },
//         CommitComplete{ require_end: LSN, discarded: Set<AU> },
//         Crash,
//     }

//     transition!{
//         load_ephemeral_from_persistent(lbl: Label, new_ephemeral: EphemeralState) {
//             require lbl is LoadEphemeralFromPersistent;
//             require pre.ephemeral is Unknown;
//             require pre.persistent.valid_image(pre.dv);
//             require new_ephemeral.init_by(pre.persistent, pre.dv);
//             update ephemeral = Ephemeral::Known{ v: new_ephemeral };
//         }
//     }

//     transition!{
//         read_for_recovery(lbl: Label) {
//             require lbl is ReadForRecovery;
//             require pre.ephemeral is Known;
//             require LinkedJournal::State::next(
//                 pre.ephemeral.get_Known_v().to_lj(pre.dv), 
//                 pre.ephemeral.get_Known_v().to_lj(pre.dv), 
//                 LinkedJournal::Label::ReadForRecovery{ messages: lbl.get_ReadForRecovery_records() }
//             );
//         }
//     }

//     transition!{
//         query_end_lsn(lbl: Label) {
//             require lbl is QueryEndLsn;
//             require pre.ephemeral is Known;
//             require LinkedJournal::State::next(
//                 pre.ephemeral.get_Known_v().to_lj(pre.dv), 
//                 pre.ephemeral.get_Known_v().to_lj(pre.dv), 
//                 LinkedJournal::Label::QueryEndLsn{ end_lsn: lbl.get_QueryEndLsn_end_lsn() },
//             );
//         }
//     }

//     transition!{
//         put(lbl: Label, new_ephemeral: EphemeralState) {
//             require lbl is Put;
//             require pre.ephemeral is Known;
//             require LinkedJournal::State::next(
//                 pre.ephemeral.get_Known_v().to_lj(pre.dv),
//                 new_ephemeral.to_lj(pre.dv), 
//                 LinkedJournal::Label::Put{ messages: lbl.get_Put_records() },
//             );
//             // NOTE (jialin): predicate and update style don't mix well here
//             require pre.ephemeral.get_Known_v().same_except_lj(new_ephemeral);
//             update ephemeral = Ephemeral::Known{ v: new_ephemeral };
//         }
//     }

//     transition!{
//         internal(lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView) {
//             require lbl is Internal;
//             require pre.ephemeral is Known;
//             require pre.ephemeral.get_Known_v().is_internal_op(
//                 pre.dv, 
//                 lbl.get_Internal_allocs(),
//                 lbl.get_Internal_deallocs(),
//                 new_ephemeral,
//                 new_dv,
//             );
//             update ephemeral = Ephemeral::Known{ v: new_ephemeral };
//             update dv = new_dv;
//         }
//     }

//     transition!{
//         query_lsn_persistence(lbl: Label) {
//             require lbl is QueryLsnPersistence;
//             require lbl.get_QueryLsnPersistence_sync_lsn() <= pre.persistent.seq_end(pre.dv);
//         }
//     }

//     transition!{
//         commit_start(lbl: Label, frozen_journal: ImageState, frozen_dv: DiskView) {
//             require lbl is CommitStart;
//             require pre.ephemeral is Known;
//             // Can't start a commit if one is in-flight, or we'd forget to maintain the
//             // invariants for the in-flight one.
//             require pre.inflight is None;
//             // Journal doesn't go backwards
//             require pre.persistent.seq_end(pre.dv) <= frozen_journal.seq_end(pre.dv);
//             // There should be no way for the frozen journal to have passed the ephemeral map!
//             require frozen_journal.seq_start() <= lbl.get_CommitStart_max_lsn();
//             // Frozen journal stitches to frozen map
//             require frozen_journal.seq_start() == lbl.get_CommitStart_new_boundary_lsn();

//             // make sure frozen journal is ready to freeze
//             let v = pre.ephemeral.get_Known_v();
//             let frozen_tj = frozen_journal.to_tj(frozen_dv);

//             // TODO: REMOVE
//             require LinkedJournal::State::next(
//                 pre.ephemeral.get_Known_v().to_lj(pre.dv),
//                 pre.ephemeral.get_Known_v().to_lj(pre.dv),
//                 LinkedJournal::Label::FreezeForCommit{ frozen_journal: frozen_tj },
//             );
//             // check first updated
//             require frozen_journal.first == AllocationJournal::State::new_first(
//                 frozen_tj, v.lsn_au_index, v.image.first, frozen_tj.seq_start());

//             update inflight = Option::Some(frozen_journal);
//         }
//     }

//     transition!{
//         commit_complete(lbl: Label, new_ephemeral: EphemeralState, new_dv: DiskView) {
//             require lbl is CommitComplete;
//             require pre.ephemeral is Known;
//             require pre.inflight is Some;

//     // TODO (Jialin)
//     //         require AllocationJournal::State::next(
//     //             pre.ephemeral.get_Known_v(), 
//     //             new_journal, 
//     //             AllocationJournal::Label::DiscardOld{ 
//     //                 start_lsn: pre.inflight.get_Some_0().tj.seq_start(), 
//     //                 require_end: lbl.get_CommitComplete_require_end(),
//     //                 deallocs: lbl.get_CommitComplete_discarded(),
//     //             },
//     //         );
            
//             update persistent = pre.inflight.get_Some_0();
//             update ephemeral = Ephemeral::Known{ v: new_ephemeral };
//             update inflight = Option::None;
//             update dv = new_dv;
//         }
//     }

//     transition!{
//         crash(lbl: Label) {
//             require lbl is Crash;
//             update ephemeral = Ephemeral::Unknown;
//             update inflight = Option::None;
//         }
//     }

// //     pub open spec(checked) fn state_relations(self) -> bool 
// //     {
// //         // persistent and ephemeral agree on values
// //         &&& self.ephemeral is Known ==> {
// //             let ephemeral_disk = self.ephemeral.get_Known_v().tj().disk_view;
// //             let persistent_disk = self.persistent.tj.disk_view;
// //             &&& Map::agrees(ephemeral_disk.entries, persistent_disk.entries)
// //         }
// //         // inflight is always a subset of ephemeral
// //         &&& self.ephemeral is Known && self.inflight is Some ==> {
// //             let ephemeral_disk = self.ephemeral.get_Known_v().tj().disk_view;
// //             let inflight_disk = self.inflight.get_Some_0().tj.disk_view;
// //             &&& inflight_disk.is_sub_disk_with_newer_lsn(ephemeral_disk)
// //         }
// //     }

// //     pub open spec(checked) fn journal_pages_not_free(self) -> bool
// //         recommends self.ephemeral is Known ==> self.ephemeral.get_Known_v().inv()
// //     {
// //         // ephemeral pages are not free as promised by the recommends
// //         &&& self.ephemeral is Known ==> {
// //             let v = self.ephemeral.get_Known_v();
// //             let persistent_disk = self.persistent.tj.disk_view;
// //             &&& AllocationJournal::State::journal_pages_not_free(persistent_disk.entries.dom(), v.mini_allocator)
// //         }
// //         &&& self.ephemeral is Known && self.inflight is Some ==> {
// //             let v = self.ephemeral.get_Known_v();
// //             let inflight_disk = self.inflight.get_Some_0().tj.disk_view;
// //             &&& AllocationJournal::State::journal_pages_not_free(inflight_disk.entries.dom(), v.mini_allocator)
// //         }
// //     }

// //     #[invariant]
// //     pub open spec(checked) fn inv(self) -> bool {
// //         &&& self.ephemeral is Unknown ==> self.inflight is None
// //         &&& self.ephemeral is Known ==> self.ephemeral.get_Known_v().inv()
// //         &&& self.inflight is Some ==> self.inflight.get_Some_0().tj.decodable()
// //         &&& self.persistent.tj.decodable()
// //         // not used here but easier to maintain here
// //         &&& self.state_relations()
// //         &&& self.journal_pages_not_free()
// //     }
           
// //     #[inductive(initialize)]
// //     fn initialize_inductive(post: Self) {
// //         assume(post.persistent.tj.decodable()); // show empty is decodable
// //     }
   
// //     #[inductive(load_ephemeral_from_persistent)]
// //     fn load_ephemeral_from_persistent_inductive(pre: Self, post: Self, lbl: Label,
// //         new_journal: AllocationJournal::State, journal_config: AllocationJournal::Config) 
// //     { 
// //         assert(pre.ephemeral is Known ==> pre.ephemeral.get_Known_v().inv());
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //         assume(post.journal_pages_not_free());
// //     }
   
// //     #[inductive(read_for_recovery)]
// //     fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) 
// //     { 
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //     }
   
// //     #[inductive(query_end_lsn)]
// //     fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) 
// //     { 
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //     }
   
// //     #[inductive(put)]
// //     fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State) 
// //     { 
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //         assume(post.journal_pages_not_free());
// //         assume(post.state_relations());
// //     }
   
// //     #[inductive(internal)]
// //     fn internal_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State) 
// //     {
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //         assume(post.journal_pages_not_free());
// //         assume(post.state_relations());
// //     }
   
// //     #[inductive(query_lsn_persistence)]
// //     fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label) 
// //     {
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //      }
   
// //     #[inductive(commit_start)]
// //     fn commit_start_inductive(pre: Self, post: Self, lbl: Label, frozen_journal: StoreImage, new_journal: AllocationJournal::State) 
// //     {
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //         assume(post.inflight is Some ==> post.inflight.get_Some_0().tj.decodable()); // should reveal inflight 
// //         assume(post.journal_pages_not_free());
// //         assume(post.state_relations());
// //     }
   
// //     #[inductive(commit_complete)]
// //     fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State) 
// //     { 
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //         assume(post.journal_pages_not_free());
// //     }
   
// //     #[inductive(crash)]
// //     fn crash_inductive(pre: Self, post: Self, lbl: Label) 
// //     {
// //         assume(post.ephemeral is Known ==> post.ephemeral.get_Known_v().inv()); // promised by submodule inv currently not accessible
// //     }

//   }} // state_machine
// } // verus
