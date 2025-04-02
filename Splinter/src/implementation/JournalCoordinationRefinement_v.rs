// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::{map::*,set::*,set_lib::*};
use vstd::math;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID};
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::JournalModel_v::*;
use crate::implementation::JournalCoordinationSystem_v::*;

verus!{

impl JournalCoordinationSystem::State {
    pub open spec fn i(self) -> LikesJournal::State
    {
        LikesJournal::State{
            journal: LinkedJournal::State{
                truncated_journal: self.ephemeral_tj(),  
                unmarshalled_tail: self.journal.unmarshalled_tail
            },
            lsn_addr_index: self.journal.lsn_addr_index,
        }
    }

    pub open spec fn tj_at(self, snapshot: JournalSnapShot) -> TruncatedJournal
    {
        let disk = self.ephemeral_disk();
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec,
            disk_view: DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: disk.entries,
            }
        }
    }
}

impl JournalCoordinationSystem::Label {
    pub open spec fn i(self, state: JournalCoordinationSystem::State) -> LikesJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} => { LikesJournal::Label::ReadForRecovery{messages} }
            Self::FreezeForCommit{frozen} => { 
                LikesJournal::Label::FreezeForCommit{frozen_journal: state.tj_at(frozen)}
            }
            Self::QueryEndLsn{end_lsn} => { LikesJournal::Label::QueryEndLsn{end_lsn} }
            Self::Put{messages} => { LikesJournal::Label::Put{messages} }
            Self::DiscardOld{start_lsn, require_end} => { LikesJournal::Label::DiscardOld{start_lsn, require_end} }
            Self::Internal{} => { LikesJournal::Label::Internal{} }
        }
    }
}

impl JournalCoordinationSystem::State {
    // TODO(JL): this almost feels like something we should have adopted in likesjournal
    pub proof fn next_index_refines(self, ptr: Pointer)
        requires 
            self.inv(), 
            ptr is Some,
            self.ephemeral_disk().is_nondangling_pointer(ptr),
        ensures ({
            let result = self.journal.next_index(ptr);
            let index = self.journal.lsn_addr_index;
            &&& result is Some ==> index.contains_value(result.unwrap())
            &&& result == self.ephemeral_disk().next(ptr)
        })
    {
        let addr = ptr.unwrap();
        let bdy = self.journal.boundary_lsn;
        let index = self.journal.lsn_addr_index;

        let record = self.ephemeral_disk().entries[addr];
        let next = record.cropped_prior(bdy);
        let lsns = addr_to_lsns(index, addr, bdy);

        // TODO: not going to prove this right now, to prove it 
        // we can maintain inv that index is finite, and show lsns is a subset of index.dom()
        assume(lsns.finite());

        self.ephemeral_tj().build_lsn_addr_index_ensures();

        // a combination of addr_supports_lsn, index_keys_map_to_valid_entries
        // instantiate_index_keys_map_to_valid_entries(lsn addr index, lsn)
        // and index_range_valid, every_lsn_at_addr_indexed_to_addr
        let start = record.message_seq.seq_start;

        if next is Some {
            assert(bdy < start);
            assert(self.ephemeral_tj().index_range_valid(index));
            assert(DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, start));
            assert(index.contains_key(start));
            assert(lsns.contains(start));
            assert(!lsns.is_empty());

            assert(min_lsn(lsns) == start) by {
                min_lsn_ensures(lsns);

                let min = min_lsn(lsns);
                if min != start {
                    assert(min < start);
                    assert(index[min] == addr);
                    self.ephemeral_disk().instantiate_index_keys_map_to_valid_entries(index, min);
                    assert(record.contains_lsn(bdy, min));
                    assert(false);
                }
            }

            assert(self.ephemeral_disk().is_nondangling_pointer(next));
            let next_record = self.ephemeral_disk().entries[next.unwrap()];
            assert(next_record.message_seq.seq_end == record.message_seq.seq_start);

            let last_lsn = (next_record.message_seq.seq_end - 1) as nat;
            assert(next_record.message_seq.contains(last_lsn));
            assert(index.contains_value(next.unwrap()));

            assert(self.ephemeral_tj().every_lsn_at_addr_indexed_to_addr(index, next.unwrap()));
            assert(DiskView::cropped_msg_seq_contains_lsn(bdy, next_record.message_seq, last_lsn));
            assert(index.contains_key(last_lsn));
            assert(index[last_lsn] == next.unwrap());
        } else {
            assert(start <= bdy);
            if lsns.is_empty() {
                assert(self.journal.next_index(ptr) is None);
            } else {
                reveal(TruncatedJournal::index_domain_valid);
                assert(forall |lsn| lsns.contains(lsn) ==> bdy <= lsn);
            
                let min = min_lsn(lsns);
                if min < 1 {
                    assert(self.journal.next_index(ptr) is None);
                    return;
                }

                // goal here is to show that it's either none or c
                let prior_lsn = (min - 1) as nat;
                min_lsn_ensures(lsns);
                if bdy >= record.message_seq.seq_end {
                    assert(index.contains_key(min));
                    assert(index[min] == ptr.unwrap());
                    self.ephemeral_disk().instantiate_index_keys_map_to_valid_entries(index, min);
                    assert(false);
                }
                assert(bdy < record.message_seq.seq_end);
                assert(min == bdy) by {
                    assert(DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, bdy));
                    assert(index.contains_key(bdy));
                    assert(lsns.contains(bdy));
                }
            }
        }
    }

    // NOTE: maybe this should have been how we define these operations in the likes layer 
    // in the first place...
    proof fn can_crop_ptr_after_index_refines(self, root: Pointer, depth: nat)
        requires 
            self.inv(), 
            self.journal.can_crop_index(root, depth),
            root is Some ==> self.journal.lsn_addr_index.contains_value(root.unwrap()),
        ensures 
            self.ephemeral_disk().can_crop(root, depth),
            self.ephemeral_disk().pointer_after_crop(root, depth)
            == self.journal.pointer_after_crop_index(root, depth),
        decreases depth
    {
        if 0 < depth {
            self.next_index_refines(root);
            self.can_crop_ptr_after_index_refines(self.journal.next_index(root), (depth-1) as nat);
        }
    }

    proof fn journal_cache_reads_ensures(self, post: Self, reads: Map<Address, RawPage>)
        requires
            self.inv(), post.inv(), 
            Cache::State::next(self.cache, post.cache, Cache::Label::Access{reads: reads, writes: Map::empty()})
        ensures 
            forall |addr| #[trigger] reads.contains_key(addr) && self.ephemeral_disk().entries.contains_key(addr)
            ==> to_journal_reads(reads)[addr] == self.ephemeral_disk().entries[addr]
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
    
        let journal_reads = to_journal_reads(reads);
        assert(journal_reads.dom() =~= reads.dom());

        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        self.cache.build_lookup_map_ensures();

        assert forall |addr| #[trigger] reads.contains_key(addr) 
            && self.ephemeral_disk().entries.contains_key(addr)
        implies journal_reads[addr] == self.ephemeral_disk().entries[addr]
        by {
            assert(journal_reads.contains_key(addr));
            journal_unmarshall_marshall(journal_reads[addr]);
            assert(raw_page_to_record(reads[addr]) == journal_reads[addr]);

            // reads match with content in the cache
            assert(cache_lbl->reads.contains_key(addr)); // trigger
            assert(self.cache.lookup_map.contains_key(addr));
    
            // connect this slot to content on ephemeral disk
            let slot = self.cache.lookup_map[addr];
            assert(self.cache.non_empty_slot(slot));
    
            assert(journal_reads[addr] == raw_page_to_record(self.cache.entries[slot]->data));
            assert(journal_reads[addr] == self.ephemeral_disk().entries[addr]) by {
                if self.cache.status_map[slot] is Clean {
                    assert(self.cache.valid_clean_slot(slot)); // trigger
                    assert(self.cache.entries[slot].get_addr() == addr);
                }
            }
        }
    }

    proof fn read_for_recovery_refines(self, post: Self, lbl: JournalCoordinationSystem::Label, reads: Map<Address, RawPage>)
        requires self.inv(), post.inv(), Self::read_for_recovery(self, post, lbl, reads)
        ensures LikesJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        let i_lbl = lbl.i(self);
        let messages = i_lbl.arrow_ReadForRecovery_messages();

        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages, reads: to_journal_reads(reads)};
        let journal_step = choose |journal_step| CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, journal_step);
        let depth = journal_step.arrow_read_for_recovery_0();

        let tj = self.ephemeral_tj();
        assert(tj.decodable());

        self.can_crop_ptr_after_index_refines(tj.freshest_rec, depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);
        let ptr = tj.disk_view.pointer_after_crop(tj.freshest_rec, depth);

        assert(ptr is Some && tj.disk_view.entries.contains_key(ptr.unwrap()));
        self.journal_cache_reads_ensures(post, reads);
        assert(messages == tj.disk_view.entries[ptr.unwrap()].message_seq.maybe_discard_old(tj.disk_view.boundary_lsn));
        assert(messages.wf());

        // read for recovery is the same
        let linked_lbl = LikesJournal::State::lbl_i(lbl.i(self));
        assert(LinkedJournal::State::next_by(self.i().journal, self.i().journal, linked_lbl, 
            LinkedJournal::Step::read_for_recovery(depth))) by {
            reveal(LinkedJournal::State::next_by);
        }
        reveal(LinkedJournal::State::next);
        reveal(LikesJournal::State::next_by);
        reveal(LikesJournal::State::next);
        assert(LikesJournal::State::next_by(self.i(), post.i(), lbl.i(self), LikesJournal::Step::read_for_recovery()));
    }

    proof fn freeze_for_commit_refines(self, post: Self, lbl: JournalCoordinationSystem::Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>)
        requires self.inv(), post.inv(), Self::freeze_for_commit(self, post, lbl, frozen_domain, reads)
        ensures LikesJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let journal_lbl = CachedJournal::Label::FreezeForCommit{frozen: lbl->frozen, frozen_domain, reads: to_journal_reads(reads)};
        let journal_step = choose |journal_step| CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, journal_step);
        let depth = journal_step.arrow_freeze_for_commit_0();

        let i_lbl = lbl.i(self);
        let i_frozen = i_lbl->frozen_journal;
        let new_bdy = i_frozen.seq_start();

        self.can_crop_ptr_after_index_refines(self.journal.freshest_rec, depth);
        assert(self.ephemeral_disk().can_crop(self.journal.freshest_rec, depth));
        assert(self.journal.boundary_lsn <= new_bdy);

        let cropped_tj = self.ephemeral_tj().crop(depth);
        let ptr = self.journal.pointer_after_crop_index(self.journal.freshest_rec, depth);
        self.ephemeral_tj().crop_ensures(depth);
        assert(cropped_tj.freshest_rec == ptr);

        assert(i_frozen.decodable()) by {
            assert(i_frozen.disk_view.entries == self.ephemeral_disk().entries);
            assert(i_frozen.disk_view.wf());
            assert(i_frozen.disk_view.is_nondangling_pointer(ptr));
            if ptr is Some {
                self.journal_cache_reads_ensures(post, reads);
                assert(i_frozen.disk_view.valid_ranking(self.ephemeral_disk().the_ranking()));
            }
        }
        assert(cropped_tj.can_discard_to(new_bdy)); 

        let post_discard = cropped_tj.discard_old(new_bdy);
        let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < post_discard.seq_end());
        let frozen_index = self.journal.lsn_addr_index.restrict(frozen_lsns);

        assert(cropped_tj.discard_old_cond(new_bdy, frozen_index.values(), i_frozen));

        reveal(LikesJournal::State::next);
        reveal(LikesJournal::State::next_by);
        assert(LikesJournal::State::next_by(self.i(), post.i(), lbl.i(self), 
            LikesJournal::Step::freeze_for_commit(depth)));
    }

    proof fn init_refines(self, disk: AsyncDisk::State, cache: Cache::State, journal: CachedJournal::State, snapshot: JournalSnapShot, reads: Map<Address, RawPage>) 
        requires self.inv(), JournalCoordinationSystem::State::initialize(self, disk, cache, journal, snapshot, reads), 
        ensures LikesJournal::State::initialize(self.i(), self.ephemeral_tj())
    {
    }

    // Skipping the rest for this exercise
}
}