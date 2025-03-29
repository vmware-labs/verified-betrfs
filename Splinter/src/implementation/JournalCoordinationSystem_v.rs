// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::{map::*,set_lib::*};
use vstd::math;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID};
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;

verus!{

pub closed spec fn record_to_raw_page(record: JournalRecord) -> (out: RawPage)
{
    arbitrary()
}

pub closed spec fn raw_page_to_record(raw_page: RawPage) -> (out: JournalRecord)
{
    arbitrary()
}

pub broadcast proof fn journal_unmarshall_marshall(record: JournalRecord)
    ensures record == #[trigger] raw_page_to_record(record_to_raw_page(record))
{
    assume(false);
}

pub open spec fn to_journal_reads(reads: Map<Address, RawPage>) -> Map<Address, JournalRecord>
{
    Map::new(
        |addr| reads.contains_key(addr), 
        |addr| raw_page_to_record(reads[addr])
    )
}

pub open spec fn to_cache_writes(writes: Map<Address, JournalRecord>) -> Map<Address, RawPage>
{
    Map::new(
        |addr| writes.contains_key(addr), 
        |addr| record_to_raw_page(writes[addr])
    )
}

impl Cache::State{
    pub open spec fn valid_clean_slot(self, slot: Slot) -> bool
    {
        &&& self.status_map.contains_key(slot)
        &&& self.status_map[slot] is Clean
    }

    pub open spec fn valid_dirty_addr(self, addr: Address) -> bool
    {
        &&& self.lookup_map.contains_key(addr)
        &&& (self.status_map[self.lookup_map[addr]] is Writeback 
            || self.status_map[self.lookup_map[addr]] is Dirty)
    }
}

state_machine!{ JournalCoordinationSystem{
    fields {
        pub journal: CachedJournal::State,
        pub cache: Cache::State,
        pub disk: AsyncDisk::State,
    }

    // label should 
    pub enum Label {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen: JournalSnapShot},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        Internal{},   // Local No-op label
    }

    transition!{ read_for_recovery(lbl: Label, reads: Map<Address, RawPage>) {
        require let Label::ReadForRecovery{messages} = lbl;

        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages, reads: to_journal_reads(reads)};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ freeze_for_commit(lbl: Label, reads: Map<Address, RawPage>) {
        require lbl is FreezeForCommit;

        let cache_lbl1 = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl1);

        // NOTE(JL): this seems weird now, but when we implement watermark (cleaned writable pages)
        // we won't need this anymore. this is fine here because we could inline lbl1 and lbl2 transition
        // as a single transition atomically
        let cache_lbl2 = Cache::Label::EvictableCheck{addrs: lbl->frozen.record_domain};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl2);

        let journal_lbl = CachedJournal::Label::FreezeForCommit{frozen: lbl->frozen, reads: to_journal_reads(reads)};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require lbl is QueryEndLsn;
        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn: lbl->end_lsn};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ put(lbl: Label) {
        require let Label::Put{messages} = lbl;
        let journal_lbl = CachedJournal::Label::Put{messages};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ discard_old(lbl: Label, new_journal: CachedJournal::State) {
        require lbl is DiscardOld;
        let journal_lbl = CachedJournal::Label::DiscardOld{require_end: lbl->require_end, start_lsn: lbl->start_lsn};
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);
        update journal = new_journal;
    }}

    // journal marshal
    transition!{ journal_marshal(lbl: Label, new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord) {
        require lbl is Internal;

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: Map::empty().insert(addr, record)};
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);

        let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes: to_cache_writes(journal_lbl->writes)};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update journal = new_journal;
        update cache = new_cache;
    }}

    transition!{ cache_disk_ops(lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State, requests: Map<ID, DiskRequest>, responses: Map<ID, DiskResponse>) {
        require lbl is Internal;

        let cache_lbl = Cache::Label::DiskOps{requests, responses};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        let disk_lbl = AsyncDisk::Label::DiskOps{requests, responses};
        require AsyncDisk::State::next(pre.disk, new_disk, disk_lbl);

        update cache = new_cache;
        update disk = new_disk;
    }}

    transition!{ cache_internal(lbl: Label, new_cache: Cache::State) {
        require lbl is Internal;
        require Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{});
        update cache = new_cache;
    }}

    transition!{ disk_internal(lbl: Label, new_disk: AsyncDisk::State) {
        require lbl is Internal;
        require AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{});
        update disk = new_disk;
    }}

    init!{ initialize(disk: AsyncDisk::State, cache: Cache::State, slots: nat, journal: CachedJournal::State) {
        require AsyncDisk::State::initialize(disk);
        require Cache::State::initialize(cache, slots);
        require CachedJournal::State::initialize(journal, Map::empty(), 0, None);

        init disk = disk;
        init cache = cache;
        init journal = journal;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool
    {
        &&& self.journal.wf()
        &&& self.cache.inv()
        &&& self.disk.inv()

        &&& self.outstanding_reqs_inv()
        &&& self.clean_cache_pages_agree_with_disk()
        &&& self.valid_journal_structure()
    }

    pub open spec fn valid_read_request(self, id: ID, addr: Address) -> bool
    {
        let slot = self.cache.outstanding_reqs[id];
        &&& self.cache.entries[slot] is Loading
        &&& self.cache.entries[slot].get_addr() == addr
    }

    pub open spec fn valid_write_request(self, id: ID, addr: Address, data: RawPage) -> bool
    {
        let slot = self.cache.outstanding_reqs[id];
        &&& self.cache.entries[slot] is Filled
        &&& self.cache.entries[slot].get_addr() == addr
        &&& self.cache.entries[slot]->data == data
        &&& self.cache.status_map[slot] is Writeback
    }

    pub open spec fn valid_read_response(self, id: ID, data: RawPage) -> bool
    {
        let slot = self.cache.outstanding_reqs[id];
        &&& self.cache.entries[slot] is Loading
        &&& data == self.disk.content[self.cache.entries[slot].get_addr()]
        // &&& self.disk.content.contains_pair(self.cache.entries[slot].get_addr(), data)
    }

    pub open spec fn valid_write_response(self, id: ID) -> bool
    {
        let slot = self.cache.outstanding_reqs[id];
        let entry = self.cache.entries[slot];

        &&& entry is Filled
        &&& self.cache.status_map[slot] is Writeback
        &&& self.disk.content.contains_pair(entry.get_addr(), entry->data)
    }

    pub open spec fn outstanding_reqs_inv(self) -> bool
    { 
        // outstanding reqs are tracked by disk reqs/replies
        // TODO(JL): doesn't include sb writes, would need to add that in
        &&& self.cache.outstanding_reqs.dom() =~= self.disk.requests.dom() + self.disk.responses.dom()

        // ensures every outstanding requests can be traced back to cache 
        &&& forall |id| #[trigger] self.disk.requests.contains_key(id) ==> {
            let req = self.disk.requests[id];
            &&& req is ReadReq ==> self.valid_read_request(id, req->from) 
            &&& req is WriteReq ==> self.valid_write_request(id, req->to, req->data)
        }

        // ensures content of each response corresponds to what's on disk
        &&& forall |id| #[trigger] self.disk.responses.contains_key(id) ==> {
            let resp = self.disk.responses[id];
            &&& resp is ReadResp ==> self.valid_read_response(id, resp->data)
            &&& resp is WriteResp ==> self.valid_write_response(id)
        }
    }

    pub open spec fn clean_cache_pages_agree_with_disk(self) -> bool
    {
        forall |slot| #[trigger] self.cache.valid_clean_slot(slot)
        ==> {
            let entry = self.cache.entries[slot];
            &&& self.disk.content.contains_pair(entry.get_addr(), entry->data)
        }
    }

    pub open spec fn persistent_journal_disk(self) -> Map<Address, JournalRecord>
    {
        Map::new(
            |addr| self.disk.content.contains_key(addr),
            |addr| raw_page_to_record(self.disk.content[addr])
        )
    }

    pub open spec fn dirty_journal_cache(self) -> Map<Address, JournalRecord>
    {
        Map::new(
            |addr| self.cache.valid_dirty_addr(addr),
            |addr| raw_page_to_record(self.cache.entries[self.cache.lookup_map[addr]]->data)
        )
    }

    // NOTE(JL): in our actual version where cache contains different types 
    // of pages we will use the domain map of each component to determine marshalled type
    pub open spec fn ephemeral_disk(self) -> DiskView
    {
        DiskView{
            boundary_lsn: self.journal.boundary_lsn,
            entries: self.persistent_journal_disk().union_prefer_right(self.dirty_journal_cache()),
        }
    }

    pub open spec fn ephemeral_tj(self) -> TruncatedJournal
    {
        TruncatedJournal{freshest_rec: self.journal.freshest_rec, disk_view: self.ephemeral_disk()}
    }

    // all relative to an ephemeral disk (cache+disk)
    pub open spec fn valid_journal_structure(self) -> bool 
    {
        &&& self.ephemeral_tj().decodable()
        &&& self.ephemeral_tj().seq_end() == self.journal.unmarshalled_tail.seq_start 
        &&& self.journal.lsn_addr_index == self.ephemeral_tj().build_lsn_addr_index()
        &&& self.journal.lsn_addr_index.values() =~= self.ephemeral_tj().disk_view.entries.dom()
    }        
    
    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) { }
   
    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) { }
   
    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State) 
    { 
        assume(false);
    }
   
    #[inductive(journal_marshal)]
    fn journal_marshal_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord) 
    { 
        assume(false);
    }
   
    #[inductive(cache_disk_ops)]
    fn cache_disk_ops_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State, requests: Map<ID, DiskRequest>, responses: Map<ID, DiskResponse>) 
    {
        assume(false);
    }
   
    #[inductive(cache_internal)]
    fn cache_internal_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State) 
    { 
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);

        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Internal{});
        assert(post.cache == new_cache);

        assert(forall |id| #[trigger] post.disk.requests.contains_key(id) 
            || post.disk.responses.contains_key(id) ==> pre.cache.outstanding_reqs.contains_key(id));
        assert(post.outstanding_reqs_inv());

        let cache_lbl = Cache::Label::Internal{};
        let cache_step = choose |cache_step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, cache_step);

        assert(post.clean_cache_pages_agree_with_disk()) by {
            assert(forall |slot| #[trigger] post.cache.valid_clean_slot(slot)
                ==> pre.cache.valid_clean_slot(slot)); // trigger
        }

        match cache_step {
            Cache::Step::reserve(new_slots_mapping) => {
                injective_map_property(new_slots_mapping);
                assert(post.dirty_journal_cache() == pre.dirty_journal_cache());
            },
            Cache::Step::evict(evicted_slots) => {
                let evicted_addrs = Map::new(|slot| evicted_slots.contains(slot), 
                    |slot| pre.cache.entries[slot].get_addr()).values();
                assert forall |addr| true
                implies pre.cache.valid_dirty_addr(addr) <==> post.cache.valid_dirty_addr(addr) 
                by {
                    pre.cache.build_lookup_map_ensures();
                    if evicted_addrs.contains(addr) {
                        let slot = choose |slot| #[trigger] evicted_slots.contains(slot) 
                                && pre.cache.entries[slot].get_addr() == addr;
                        assert(pre.cache.non_empty_slot(slot)); // trigger
                        assert(!pre.cache.valid_dirty_addr(addr));
                        assert(!post.cache.valid_dirty_addr(addr));
                    }
                }
                assert(post.dirty_journal_cache() == pre.dirty_journal_cache());
            },
            _ => { assert(post.inv()); }
        }
    }
   
    #[inductive(disk_internal)]
    fn disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State) 
    {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);

        let disk_lbl = AsyncDisk::Label::Internal{};
        let disk_step = choose |disk_step| AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, disk_step);
        assert(disk_step is process_read || disk_step is process_write);

        let processed_id = if disk_step is process_read { disk_step.get_process_read_0() } else { disk_step.get_process_write_0() };
        assert(post.cache.outstanding_reqs.contains_key(processed_id)); // trigger

        let processed_slot = post.cache.outstanding_reqs[processed_id];
        assert(post.cache.non_empty_slot(processed_slot)); // trigger

        assert forall |id| #[trigger] post.disk.responses.contains_key(id)
        implies {
            let resp = post.disk.responses[id];
            &&& resp is ReadResp ==> post.valid_read_response(id, resp->data)
            &&& resp is WriteResp ==> post.valid_write_response(id)
        } by {
            if id != processed_id {
                let slot = post.cache.outstanding_reqs[id];
                assert(post.cache.outstanding_reqs.contains_key(id)); // trigger
            }
        }

        assert(post.clean_cache_pages_agree_with_disk()) by {
            assert forall |slot| #[trigger] post.cache.valid_clean_slot(slot)
            implies {
                let entry = post.cache.entries[slot];
                &&& post.disk.content.contains_pair(entry.get_addr(), entry->data)
            } by {
                if disk_step is process_write {
                    assert(slot != processed_slot);
                    assert(post.cache.non_empty_slot(slot)); // trigger
                }
            }
        }

        if disk_step is process_write {        
            let processed_entry = post.cache.entries[processed_slot];
            let dirty_cache_entries = pre.dirty_journal_cache();
            assert(dirty_cache_entries.contains_key(processed_entry.get_addr())) by {
                pre.cache.build_lookup_map_ensures();
                assert(pre.cache.lookup_map.contains_key(processed_entry.get_addr()));
            }
            assert(pre.ephemeral_disk().entries =~= post.ephemeral_disk().entries);
            assert(post.valid_journal_structure());
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, disk: AsyncDisk::State, cache: Cache::State, slots: nat, journal: CachedJournal::State) 
    {
        Cache::State::initialize_inductive(post.cache, slots);
        assert(post.ephemeral_disk().valid_ranking(map!{}));
    }
}}

}