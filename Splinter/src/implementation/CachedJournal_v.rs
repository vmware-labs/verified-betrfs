// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::math::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v::*;
use crate::implementation::JournalModel_v::*;

// this is a version of the journal where 
// content does not live in the journal disk view but accessed through the cache

// to take just this we want to have an equivalent of crop but with lsnaddrindex

verus!{

pub open spec fn addr_to_lsns(lsn_addr_index: LsnAddrIndex, addr: Address, bdy: LSN) -> Set<LSN>
{
    Set::new(|lsn| bdy <= lsn && lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn] == addr)
}

// to sorted seq, what do we need this for?
pub open spec fn min_lsn(lsns: Set<LSN>) -> LSN
{
    lsns.find_unique_minimal(|a: LSN, b: LSN| a < b)
}

pub open spec fn cropped_prior_index(lsn_addr_index: LsnAddrIndex, addr: Address, bdy: LSN) -> Pointer
{
    let lsns = addr_to_lsns(lsn_addr_index, addr, bdy);
    if lsns.len() > 0 {
        let min = min_lsn(lsns);
        let prior_lsn = (min - 1) as nat;
        if bdy <= prior_lsn && lsn_addr_index.contains_key(prior_lsn) {
            Some(lsn_addr_index[prior_lsn])
        } else {
            None
        }
    } else {
        None
    }
}

pub open spec fn can_crop_index(lsn_addr_index: LsnAddrIndex, root: Pointer, bdy: LSN, depth: nat) -> bool
    decreases depth
{
    0 < depth ==> {
        &&& root is Some
        &&& can_crop_index(lsn_addr_index, cropped_prior_index(lsn_addr_index, root.unwrap(), bdy), bdy, (depth-1) as nat)
    }
}

pub open spec(checked) fn pointer_after_crop_index(lsn_addr_index: LsnAddrIndex, root: Pointer, bdy: LSN, depth: nat) -> Pointer
    recommends can_crop_index(lsn_addr_index, root, bdy, depth)
    decreases depth
{
    if depth == 0 { root }
    else {
        let next_ptr = cropped_prior_index(lsn_addr_index, root.unwrap(), bdy);
        pointer_after_crop_index(lsn_addr_index, next_ptr, bdy, (depth-1) as nat) 
    }
}

pub open spec(checked) fn build_lsn_addr_index_from_reads(reads: Map<Address, JournalRecord>, boundary_lsn: LSN, root: Pointer) -> LsnAddrIndex
    decreases reads.len() when reads.dom().finite()
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let curr_msgs = reads[root.unwrap()].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());

        let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);
        let sub_index = build_lsn_addr_index_from_reads(reads.remove(root.unwrap()), boundary_lsn, next_ptr);

        sub_index.union_prefer_right(update)
    } else {
        map!{}
    }
}

pub struct JournalSnapShot {
    pub boundary_lsn: LSN, 
    pub freshest_rec: Pointer,
    pub record_domain: Set<Address>,
}

state_machine!{ CachedJournal {
    fields{
        pub boundary_lsn: LSN,  // start of active entry
        pub freshest_rec: Pointer, // latest journal pointer
        pub unmarshalled_tail: MsgHistory, // in memory journal
        pub lsn_addr_index: LsnAddrIndex,
    }

    #[invariant]
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.seq_start() <= self.seq_end()
        // &&& self.freshest_rec is Some ==> self.lsn_addr_index.contains_value(self.freshest_rec.unwrap())
        &&& self.unmarshalled_tail.wf()
    }

    pub open spec(checked) fn seq_start(self) -> LSN
    {
        self.boundary_lsn
    }

    pub open spec(checked) fn marshalled_seq_end(self) -> LSN
    {
        self.unmarshalled_tail.seq_start
    }

    pub open spec(checked) fn seq_end(self) -> LSN
    {
        self.unmarshalled_tail.seq_end
    }
    
    pub open spec(checked) fn can_discard_to(self, lsn: LSN) -> bool
    {
        self.seq_start() <= lsn <= self.seq_end()
    }

    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory, reads: Map<Address, JournalRecord>},
        FreezeForCommit{frozen: JournalSnapShot, reads: Map<Address, JournalRecord>},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN, discard_addrs: Set<Address>},
        JournalMarshal{writes: Map<Address, JournalRecord>},
        Internal{}, 
    }

    // NOTE: we use depth in the following transitions to ensure we only perform operations
    // on page aligned LSNs, using depth require caller to page in all the relevant pages 
    // which seems fine for recovery but not best when we are under memory pressure, 
    // another option is to rely on the LsnAddrIndex 

    transition!{ read_for_recovery(lbl: Label, depth: nat) {
        require let Label::ReadForRecovery{messages, reads} = lbl;
        require can_crop_index(pre.lsn_addr_index, pre.freshest_rec, pre.boundary_lsn, depth);

        let ptr = pointer_after_crop_index(pre.lsn_addr_index, pre.freshest_rec, pre.boundary_lsn, depth);
        require ptr is Some && reads.contains_key(ptr.unwrap());
        require messages == reads[ptr.unwrap()].message_seq.maybe_discard_old(pre.boundary_lsn);
    }}

    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require let Label::FreezeForCommit{frozen, reads} = lbl;
        require pre.seq_start() <= frozen.boundary_lsn;
        require can_crop_index(pre.lsn_addr_index, pre.freshest_rec, pre.boundary_lsn, depth);

        let ptr = pointer_after_crop_index(pre.lsn_addr_index, pre.freshest_rec, pre.boundary_lsn, depth);

        // freeze for commit wants the cache reads 
        require ptr == frozen.freshest_rec;
        
        require ptr is Some ==> reads.contains_key(ptr.unwrap());
        let frozen_seq_end = if ptr is Some { reads[ptr.unwrap()].message_seq.seq_end } else { frozen.boundary_lsn };

        require frozen.boundary_lsn <= frozen_seq_end;
        require frozen_seq_end <= pre.marshalled_seq_end();

        let frozen_lsns = Set::new(|lsn: LSN| frozen.boundary_lsn <= lsn && lsn < frozen_seq_end);
        require frozen.record_domain == pre.lsn_addr_index.restrict(frozen_lsns).values();
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require lbl is QueryEndLsn;
        require lbl->end_lsn == pre.seq_end();
    }}

    transition!{ put(lbl: Label) {
        require let Label::Put{messages} = lbl;
        require messages.wf();
        require messages.seq_start == pre.seq_end();
        update unmarshalled_tail = pre.unmarshalled_tail.concat(messages);
    }}

    transition!{ discard_old(lbl: Label) {
        require lbl is DiscardOld;
        require lbl->require_end == pre.marshalled_seq_end();
        require pre.seq_start() <= lbl->start_lsn <= lbl->require_end;

        let new_freshest_rec = if lbl->start_lsn == lbl->require_end { None } else { pre.freshest_rec };
        let new_lsn_addr_index = lsn_addr_index_discard_up_to(pre.lsn_addr_index, lbl->start_lsn);
        require lbl->discard_addrs == pre.lsn_addr_index.values() - new_lsn_addr_index.values();

        update boundary_lsn = lbl->start_lsn;
        update freshest_rec = new_freshest_rec;
        update lsn_addr_index = new_lsn_addr_index;
    }}

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address) {
        require lbl is JournalMarshal;
        require !pre.lsn_addr_index.contains_value(addr);

        require pre.marshalled_seq_end() < cut;
        require pre.unmarshalled_tail.can_discard_to(cut);

        let marshalled_msgs = pre.unmarshalled_tail.discard_recent(cut);
        let new_record = JournalRecord{message_seq: marshalled_msgs, prior_rec: pre.freshest_rec};
        require lbl->writes == Map::empty().insert(addr, new_record);

        update freshest_rec = Some(addr);
        update unmarshalled_tail = pre.unmarshalled_tail.discard_old(cut);
        update lsn_addr_index = lsn_addr_index_append_record(pre.lsn_addr_index, marshalled_msgs, addr);
    }}

    init!{ initialize(reads: Map<Address, JournalRecord>, boundary_lsn: LSN, freshest_rec: Pointer) {
        let lsn_addr_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, freshest_rec);

        // NOTE: we need this if we want to maintain internal wf
        require freshest_rec is Some ==> {
            &&& reads.contains_key(freshest_rec.unwrap())
            &&& boundary_lsn <= reads[freshest_rec.unwrap()].message_seq.seq_end
        };

        let seq_end = if freshest_rec is Some { reads[freshest_rec.unwrap()].message_seq.seq_end } else { boundary_lsn };

        init boundary_lsn = boundary_lsn;
        init freshest_rec = freshest_rec;
        init lsn_addr_index = lsn_addr_index;
        init unmarshalled_tail = MsgHistory::empty_history_at(seq_end); 
    }}

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }
    
    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }
    
    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address) { }
    
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, reads: Map<Address, JournalRecord>, boundary_lsn: LSN, freshest_rec: Pointer) { 

        // if root is Some && reads.contains_key(root.unwrap()) {
        //     let curr_msgs = reads[root.unwrap()].message_seq;
        //     let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        //     let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
    
        //     let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);
        //     let sub_index = build_lsn_addr_index_from_reads(reads.remove(root.unwrap()), boundary_lsn, next_ptr);
    
        //     sub_index.union_prefer_right(update)
        // } else {
        //     map!{}
        // }
    }

}}
} // end of verus