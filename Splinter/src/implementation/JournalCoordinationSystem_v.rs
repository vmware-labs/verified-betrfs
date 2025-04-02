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
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::JournalModel_v::*;

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

    pub open spec fn valid_read_request(self, id: ID, addr: Address) -> bool
    {
        &&& self.entries[self.outstanding_reqs[id]] is Loading
        &&& self.entries[self.outstanding_reqs[id]].get_addr() == addr
    }

    pub open spec fn valid_write_request(self, id: ID, addr: Address, data: RawPage) -> bool
    {
        let slot = self.outstanding_reqs[id];
        &&& self.entries[slot] is Filled
        &&& self.entries[slot].get_addr() == addr
        &&& self.entries[slot]->data == data
        &&& self.status_map[slot] is Writeback
    }

    // NOTE: we don't need to track whether a page read has previously been written to disk
    // in fact our cache model allows arbitrary page to be fetched and reserved, but 
    // the composition ensures that 
    pub open spec fn valid_read_response(self, id: ID, data: RawPage, disk_content: Disk) -> bool
    {
        let slot = self.outstanding_reqs[id];
        &&& self.entries[slot] is Loading
        &&& data == disk_content[self.entries[slot].get_addr()]
        // &&& disk_content.contains_pair(self.entries[slot].get_addr(), data)
    }

    pub open spec fn valid_write_response(self, id: ID, disk_content: Disk) -> bool
    {
        let slot = self.outstanding_reqs[id];
        let entry = self.entries[slot];

        &&& entry is Filled
        &&& self.status_map[slot] is Writeback
        // &&& disk_content[entry.get_addr()] == entry->data
        &&& disk_content.contains_pair(entry.get_addr(), entry->data)
    }

    pub open spec fn clean_pages_agree_with_disk(self, disk_content: Disk) -> bool
    {
        forall |slot| #[trigger] self.valid_clean_slot(slot)
        ==> disk_content[self.entries[slot].get_addr()] == self.entries[slot]->data
    }

    pub open spec fn dirty_pages_bounded_by_journal_index(self, lsn_addr_index: LsnAddrIndex) -> bool
    {
        forall |addr| #[trigger] self.valid_dirty_addr(addr) ==> lsn_addr_index.contains_value(addr)
    }

    pub open spec fn outstanding_reqs_consistent_with_disk(self, disk: AsyncDisk::State) -> bool
    { 
        // outstanding reqs are tracked by disk reqs/replies
        // TODO(JL): doesn't include sb writes, would need to add that in
        &&& self.outstanding_reqs.dom() =~= disk.requests.dom() + disk.responses.dom()

        // ensures every outstanding requests can be traced back to cache 
        &&& forall |id| #[trigger] disk.requests.contains_key(id) ==> {
            let req = disk.requests[id];
            &&& req is ReadReq ==> self.valid_read_request(id, req->from) 
            &&& req is WriteReq ==> self.valid_write_request(id, req->to, req->data)
        }

        // ensures content of each response corresponds to what's on disk
        &&& forall |id| #[trigger] disk.responses.contains_key(id) ==> {
            let resp = disk.responses[id];
            &&& resp is ReadResp ==> self.valid_read_response(id, resp->data, disk.content)
            &&& resp is WriteResp ==> self.valid_write_response(id, disk.content)
        }
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

    transition!{ freeze_for_commit(lbl: Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) {
        require lbl is FreezeForCommit;

        let cache_lbl1 = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl1);

        // NOTE(JL): this seems weird now, but when we implement watermark (cleaned writable pages)
        // we won't need this anymore. this is fine here because we could inline lbl1 and lbl2 transition
        // as a single transition atomically
        let cache_lbl2 = Cache::Label::EvictableCheck{addrs: frozen_domain};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl2);

        let journal_lbl = CachedJournal::Label::FreezeForCommit{frozen: lbl->frozen, frozen_domain, reads: to_journal_reads(reads)};
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

    transition!{ discard_old(lbl: Label, new_journal: CachedJournal::State, discard_addrs: Set<Address>) {
        require lbl is DiscardOld;

        let journal_lbl = CachedJournal::Label::DiscardOld{
                start_lsn: lbl->start_lsn, 
                require_end: lbl->require_end,
                discard_addrs: discard_addrs,
            };
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);

        // TODO: this eventually will be tracked by an internal watermark that ensures all pages 
        // below watermark are clean in cache
        let cache_lbl = Cache::Label::EvictableCheck{addrs: discard_addrs};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

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

    pub open spec fn tj_from_reads_and_snapshot(snapshot: JournalSnapShot, reads: Map<Address, RawPage>) -> TruncatedJournal
    {
        let dv = DiskView{
            boundary_lsn: snapshot.boundary_lsn,
            entries: to_journal_reads(reads),
        };
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec,
            disk_view: dv,
        }
    }

    // NOTE: 
    init!{ initialize(disk: AsyncDisk::State, cache: Cache::State, journal: CachedJournal::State, 
        snapshot: JournalSnapShot, reads: Map<Address, RawPage>) {
        // NOTE: this isn't a crash aware composed system so init does not initializes 
        // from fully empty state and looks a bit weird. The main goal is just to refine
        // page walks on cached pages to page walks over the projected disk
        require disk.inv();
        require cache.inv();

        // validate cache reads
        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(cache, cache, cache_lbl);
        require CachedJournal::State::initialize(journal, to_journal_reads(reads), snapshot);

        // require these as cache and disk are just handed to us
        require cache.outstanding_reqs_consistent_with_disk(disk);
        require cache.clean_pages_agree_with_disk(disk.content);
        // this can be satisfied prior to building the journal by not performing any writes 
        // until journal is initialized which is a reasonable decision
        require cache.dirty_pages_bounded_by_journal_index(journal.lsn_addr_index);

        // decodable property should be maintained by system across crashes
        let tj = Self::tj_from_reads_and_snapshot(snapshot, reads);
        require tj.decodable();
        require reads.dom() <= disk.content.dom();
        require reads.dom() == journal.lsn_addr_index.values();

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

        // NOTE(JL): 
        // bc this is an ephemeral composition model, the initial
        // version requires pages to be read into the supplied cache already
        // and disk cannot have any other outstanding requests 

        &&& self.cache.outstanding_reqs_consistent_with_disk(self.disk)
        &&& self.cache.clean_pages_agree_with_disk(self.disk.content)
        &&& self.cache.dirty_pages_bounded_by_journal_index(self.journal.lsn_addr_index)
        &&& self.valid_journal_structure()
    }

    pub open spec fn persistent_journal_disk(self) -> Map<Address, JournalRecord>
    {
        Map::new(
            |addr| self.disk.content.contains_key(addr)
                && self.journal.lsn_addr_index.contains_value(addr),
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
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) { }
   
    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, discard_addrs: Set<Address>) 
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);

        let cache_lbl = Cache::Label::EvictableCheck{addrs: discard_addrs};
        assert(Cache::State::evictable(pre.cache, post.cache, cache_lbl));

        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn: lbl->start_lsn, 
            require_end: lbl->require_end,
            discard_addrs: discard_addrs,
        };

        assert(post.cache.dirty_pages_bounded_by_journal_index(post.journal.lsn_addr_index));
        assert(pre.dirty_journal_cache() == post.dirty_journal_cache());

        let pre_tj = pre.ephemeral_tj();
        let post_tj = post.ephemeral_tj();

        lsn_addr_index_discard_up_to_ensures(pre.journal.lsn_addr_index, lbl->start_lsn);

        if pre_tj.freshest_rec is Some {
            let root = pre_tj.freshest_rec.unwrap();
            let last_lsn = (pre_tj.seq_end() - 1) as nat;

            assert(pre_tj.seq_end() == lbl->require_end);
            assert(pre.journal.lsn_addr_index.contains_key(last_lsn));
            assert(pre.journal.lsn_addr_index[last_lsn] == root);

            if lbl->start_lsn != lbl->require_end {
                assert(post.journal.lsn_addr_index.contains_key(last_lsn)); // witness
                assert(post.journal.lsn_addr_index.contains_value(root));
                assert(!discard_addrs.contains(root));
            }
        }
        assert(post_tj.disk_view.is_nondangling_pointer(post_tj.freshest_rec));
        assert(post_tj.wf());

        assert forall |addr| post.journal.lsn_addr_index.values().contains(addr)
        implies post_tj.disk_view.entries.contains_key(addr) 
        by {
            assert(pre.journal.lsn_addr_index.values().contains(addr)); // trigger
            if !post.dirty_journal_cache().contains_key(addr) {
                assert(pre.disk.content.contains_key(addr));
            }
        }
        assert(post.journal.lsn_addr_index.values() =~= post.ephemeral_tj().disk_view.entries.dom());
        assert(pre_tj.can_discard_to(lbl->start_lsn));
        assert(pre_tj.discard_old_cond(lbl->start_lsn, post.journal.lsn_addr_index.values(), post_tj));

        pre_tj.discard_old_preserves_acyclicity(lbl->start_lsn, post.journal.lsn_addr_index.values(), post_tj);
        assert(post_tj.disk_view.acyclic());

        pre_tj.discard_old_maintains_repr_index(lbl->start_lsn, post.journal.lsn_addr_index, post_tj);
        assert(post.journal.lsn_addr_index == post.ephemeral_tj().build_lsn_addr_index());
        assert(post.valid_journal_structure());    
        assert(post.inv());
    }
   
    #[inductive(journal_marshal)]
    fn journal_marshal_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord) 
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: Map::empty().insert(addr, record)};
        let journal_step = choose |journal_step| CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, journal_step);
        assert(post.journal.wf());

        let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes: to_cache_writes(journal_lbl->writes)};
        Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
        assert(Cache::State::access(pre.cache, post.cache, cache_lbl)) by {
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
        }

        assert(post.cache.outstanding_reqs_consistent_with_disk(post.disk)) by {
            assert(forall |id| #[trigger] pre.disk.requests.contains_key(id) || pre.disk.responses.contains_key(id) 
            ==> post.cache.non_empty_slot(post.cache.outstanding_reqs[id])); // trigger
        }

        assert(post.cache.clean_pages_agree_with_disk(post.disk.content)) by {
            assert(forall |slot| #[trigger] post.cache.valid_clean_slot(slot)
                ==> pre.cache.valid_clean_slot(slot)); // trigger
        }

        let cut = journal_step.arrow_internal_journal_marshal_0();
        let new_addr = journal_step.arrow_internal_journal_marshal_1();

        let marshalled_msgs = pre.journal.unmarshalled_tail.discard_recent(cut);
        let new_record = JournalRecord{message_seq: marshalled_msgs, prior_rec: pre.journal.freshest_rec};

        lsn_addr_index_append_record_ensures(pre.journal.lsn_addr_index, marshalled_msgs, new_addr);

        assert(lsn_disjoint(pre.journal.lsn_addr_index.dom(), marshalled_msgs)) by {
            pre.ephemeral_tj().build_lsn_addr_index_ensures();
            assert(pre.ephemeral_tj().index_domain_valid(pre.journal.lsn_addr_index));
            reveal(TruncatedJournal::index_domain_valid);
        }

        assert(post.journal.lsn_addr_index == lsn_addr_index_append_record(pre.journal.lsn_addr_index, marshalled_msgs, new_addr));
        assert(post.journal.lsn_addr_index.values() == pre.journal.lsn_addr_index.values() + set![new_addr]);

        assert(post.cache.dirty_pages_bounded_by_journal_index(post.journal.lsn_addr_index)) by {
            assert forall |addr| #[trigger] post.cache.valid_dirty_addr(addr)
            implies post.journal.lsn_addr_index.contains_value(addr)
            by {
                if addr != new_addr{
                    pre.cache.build_lookup_map_ensures();
                    assert(pre.cache.valid_dirty_addr(addr)); // trigger
                }
                assert(post.journal.lsn_addr_index.values().contains(addr)); // trigger
            }
        }

        assert(post.valid_journal_structure()) by {
            let pre_tj = pre.ephemeral_tj();
            let post_tj = post.ephemeral_tj();

            journal_unmarshall_marshall(new_record);
            assert(post_tj.disk_view.wf());

            // TODO: my marshalling sequence might be weird?
            assert(post_tj.disk_view.entries =~= pre_tj.disk_view.entries.insert(new_addr, new_record))
            by {
                assert(cache_lbl->writes.contains_key(new_addr)); // trigger
                assert(pre.cache.lookup_map.contains_key(new_addr));

                let slot = pre.cache.lookup_map[new_addr];
                assert(pre.cache.lookup_map.restrict(cache_lbl->writes.dom()) =~= map!{new_addr => slot});

                let write_slots = pre.cache.lookup_map.restrict(cache_lbl->writes.dom()).values();
                assert(write_slots =~= set!{slot});                
                assert(post.dirty_journal_cache().dom() =~= pre.dirty_journal_cache().dom() + set!{new_addr});
                assert(post.dirty_journal_cache() =~= pre.dirty_journal_cache().insert(new_addr, new_record));
            }

            assert(post_tj.decodable()) by {
                assert(post_tj.disk_view.valid_ranking(pre_tj.marshal_ranking(new_addr)) );    // witness
            }

            assert(post_tj.seq_end() == post.journal.unmarshalled_tail.seq_start);
            assert(post.journal.lsn_addr_index.values() =~= post_tj.disk_view.entries.dom());

            pre_tj.disk_view.sub_disk_repr_index(post_tj.disk_view, pre_tj.freshest_rec);
            assert(post.journal.lsn_addr_index == post_tj.build_lsn_addr_index());
        }
        assert(post.inv());
    }

    #[inductive(cache_disk_ops)]
    fn cache_disk_ops_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State, requests: Map<ID, DiskRequest>, responses: Map<ID, DiskResponse>) 
    {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        assert(post.disk.inv());

        reveal(Cache::State::next);
        reveal(Cache::State::next_by);

        let cache_lbl = Cache::Label::DiskOps{requests, responses};
        Cache::State::inv_next(pre.cache, post.cache, cache_lbl);

        let cache_step = choose |cache_step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, cache_step);

        if cache_step is load_initiate || cache_step is writeback_initiate {
            if cache_step is load_initiate {
                injective_map_property(cache_step.arrow_load_initiate_0());
                injective_map_property(requests);
            }
            assert(forall |id| #[trigger] requests.contains_key(id) ==> requests.contains_value(requests[id])); //  trigger
            assert(forall |id| #[trigger] pre.disk.requests.contains_key(id) || post.disk.responses.contains_key(id) 
                    ==> post.cache.non_empty_slot(post.cache.outstanding_reqs[id])); // trigger
            assert(post.cache.outstanding_reqs_consistent_with_disk(post.disk));

            assert(forall |slot| #[trigger] post.cache.valid_clean_slot(slot) ==> pre.cache.valid_clean_slot(slot)); // trigger
            assert(post.cache.clean_pages_agree_with_disk(post.disk.content));

            pre.cache.build_lookup_map_ensures();
            assert(forall |addr| #[trigger] post.cache.valid_dirty_addr(addr) ==> pre.cache.valid_dirty_addr(addr)); // trigger
            assert(post.cache.dirty_pages_bounded_by_journal_index(post.journal.lsn_addr_index));
            assert(pre.ephemeral_disk() == post.ephemeral_disk());
        } else {
            assert(forall |id| #[trigger] post.disk.requests.contains_key(id) ||  post.disk.responses.contains_key(id)
                    ==> post.cache.non_empty_slot(post.cache.outstanding_reqs[id])); // trigger
            assert(post.cache.outstanding_reqs_consistent_with_disk(post.disk));

            let slot_id_map = pre.cache.outstanding_reqs.restrict(responses.dom()).invert();
            let resps_slots = pre.cache.outstanding_reqs.restrict(responses.dom()).values();

            injective_map_property(pre.cache.outstanding_reqs.restrict(responses.dom()));

            assert forall |slot| #[trigger] post.cache.valid_clean_slot(slot)
            implies {
                let entry = post.cache.entries[slot];
                &&& post.disk.content[entry.get_addr()] == entry->data
            } by {
                if !resps_slots.contains(slot) {
                    assert(pre.cache.valid_clean_slot(slot)); // trigger
                }
            }
            assert(post.cache.clean_pages_agree_with_disk(post.disk.content));

            pre.cache.build_lookup_map_ensures();
            post.cache.build_lookup_map_ensures();

            assert(forall |addr| #[trigger] post.cache.valid_dirty_addr(addr) ==> pre.cache.valid_dirty_addr(addr)); // trigger
            assert(post.cache.dirty_pages_bounded_by_journal_index(post.journal.lsn_addr_index));

            injective_map_property(pre.cache.lookup_map);
            assert(pre.ephemeral_disk() == post.ephemeral_disk());

            // if cache_step is load_complete {
            //     assert(pre.dirty_journal_cache() == post.dirty_journal_cache());
            //     assert(pre.ephemeral_disk() == post.ephemeral_disk());
            // } else {
            //     assert(post.dirty_journal_cache() <= pre.dirty_journal_cache());
                // assert forall |addr| #[trigger] pre.cache.valid_dirty_addr(addr) 
                //     && !post.cache.valid_dirty_addr(addr)
                // implies {
                //    &&& post.persistent_journal_disk().contains_key(addr)
                //    &&& post.persistent_journal_disk()[addr] == pre.dirty_journal_cache()[addr]
                // } by {
                //     let id = slot_id_map[pre.cache.lookup_map[addr]];
                //     assert(pre.valid_write_response(id));
                //     // let slot = pre.cache.outstanding_reqs[id];
                //     // let entry = pre.cache.entries[slot];

                //     // assert(pre.cache.lookup_map[addr] == slot);
                //     // assert(pre.cache.non_empty_slot(slot));
                // }
            // }
        }
        assert(post.inv());
    }
   
    #[inductive(cache_internal)]
    fn cache_internal_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State) 
    { 
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);

        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Internal{});
        assert(post.cache == new_cache);

        assert(post.cache.outstanding_reqs_consistent_with_disk(post.disk)) by {
            assert forall |id| #[trigger] post.disk.requests.contains_key(id) 
                || post.disk.responses.contains_key(id)
            implies pre.cache.non_empty_slot(pre.cache.outstanding_reqs[id])
            by {}
        }

        let cache_lbl = Cache::Label::Internal{};
        let cache_step = choose |cache_step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, cache_step);

        assert(post.cache.clean_pages_agree_with_disk(post.disk.content)) by {
            assert(forall |slot| #[trigger] post.cache.valid_clean_slot(slot)
                ==> pre.cache.valid_clean_slot(slot)); // trigger
        }

        match cache_step {
            Cache::Step::reserve(new_slots_mapping) => {
                injective_map_property(new_slots_mapping);
                post.cache.build_lookup_map_ensures();
                assert(forall |addr| #[trigger] post.cache.valid_dirty_addr(addr) ==> pre.cache.valid_dirty_addr(addr)); // trigger
                assert(post.cache.dirty_pages_bounded_by_journal_index(post.journal.lsn_addr_index));
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
            &&& resp is ReadResp ==> post.cache.valid_read_response(id, resp->data, post.disk.content)
            &&& resp is WriteResp ==> post.cache.valid_write_response(id, post.disk.content)
        } by {
            if id != processed_id {
                let slot = post.cache.outstanding_reqs[id];
                assert(post.cache.non_empty_slot(slot)); // trigger
            }
        }

        assert(post.cache.clean_pages_agree_with_disk(post.disk.content)) by {
            assert forall |slot| #[trigger] post.cache.valid_clean_slot(slot)
            implies {
                let entry = post.cache.entries[slot];
                &&& post.disk.content[entry.get_addr()] == entry->data
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
    fn initialize_inductive(post: Self, disk: AsyncDisk::State, cache: Cache::State, 
        journal: CachedJournal::State, snapshot: JournalSnapShot, reads: Map<Address, RawPage>) 
    {
        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);

        CachedJournal::State::initialize_inductive(post.journal, to_journal_reads(reads), snapshot);

        let ptr = snapshot.freshest_rec;
        let tj = Self::tj_from_reads_and_snapshot(snapshot, reads);
        let seq_end = if ptr is Some { tj.disk_view.entries[ptr.unwrap()].message_seq.seq_end } else { snapshot.boundary_lsn };

        build_lsn_addr_index_from_reads_refines(tj.disk_view, ptr, seq_end);
        assert(tj.disk_view =~= post.ephemeral_tj().disk_view);
        assert(post.inv());
    }
}}

proof fn build_lsn_addr_index_from_reads_refines(dv: DiskView, root: Pointer, curr_end: LSN)
requires 
    dv.buildable(root),
    curr_end == dv.seq_end(root),
ensures 
    build_lsn_addr_index_from_reads(dv.entries, dv.boundary_lsn, root, curr_end)
    == dv.build_lsn_addr_index(root)
decreases curr_end
{
    if root is Some {
        let curr_msgs = dv.entries[root.unwrap()].message_seq;
        let start_lsn = math::max(dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let next_ptr = dv.entries[root.unwrap()].cropped_prior(dv.boundary_lsn);
        build_lsn_addr_index_from_reads_refines(dv, next_ptr, start_lsn);
    }
}

}