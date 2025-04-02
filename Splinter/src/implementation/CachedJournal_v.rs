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
    recommends !lsns.is_empty()
    decreases lsns.len() 
{
    if !lsns.finite() {
        arbitrary()
    } else {
        let e = lsns.choose();
        if lsns.remove(e).is_empty() { e } 
        else { min(e as int, min_lsn(lsns.remove(e)) as int) as nat }
    }
}

pub proof fn min_lsn_ensures(lsns: Set<LSN>)
    requires !lsns.is_empty(), lsns.finite()
    ensures 
        lsns.contains(min_lsn(lsns)),
        forall |lsn| #[trigger] lsns.contains(lsn) ==> min_lsn(lsns) <= lsn
    decreases lsns.len()
{
    let e = lsns.choose();
    if !lsns.remove(e).is_empty() {
        let result = min_lsn(lsns);
        min_lsn_ensures(lsns.remove(e));
    }
}

pub open spec(checked) fn build_lsn_addr_index_from_reads(reads: Map<Address, JournalRecord>, 
    boundary_lsn: LSN, root: Pointer, curr_end: LSN) -> LsnAddrIndex
    decreases curr_end
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let curr_msgs = reads[root.unwrap()].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());

        let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);
        if start_lsn < curr_end {
            let sub_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr, start_lsn);
            sub_index.union_prefer_right(update)
        } else {
            // never reached if blocks can concat
            map!{}
        }
    } else {
        map!{}
    }
}

pub struct JournalSnapShot {
    pub boundary_lsn: LSN, 
    pub freshest_rec: Pointer,
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
        FreezeForCommit{frozen: JournalSnapShot, frozen_domain: Set<Address>, reads: Map<Address, JournalRecord>},
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
        require pre.can_crop_index(pre.freshest_rec, depth);

        let ptr = pre.pointer_after_crop_index(pre.freshest_rec, depth);
        require ptr is Some && reads.contains_key(ptr.unwrap());
        require messages == reads[ptr.unwrap()].message_seq.maybe_discard_old(pre.boundary_lsn);
    }}

    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require let Label::FreezeForCommit{frozen, frozen_domain, reads} = lbl;
        require pre.seq_start() <= frozen.boundary_lsn;
        require pre.can_crop_index(pre.freshest_rec, depth);

        let ptr = pre.pointer_after_crop_index(pre.freshest_rec, depth);
        require ptr == frozen.freshest_rec;
        require ptr is Some ==> reads.contains_key(ptr.unwrap());

        let frozen_seq_end = if ptr is Some { reads[ptr.unwrap()].message_seq.seq_end } else { pre.boundary_lsn };
        require frozen.boundary_lsn <= frozen_seq_end;
        require ptr is Some ==> frozen.boundary_lsn < frozen_seq_end;

        let frozen_lsns = Set::new(|lsn: LSN| frozen.boundary_lsn <= lsn && lsn < frozen_seq_end);
        require frozen_domain == pre.lsn_addr_index.restrict(frozen_lsns).values();
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

    // this makes it so that we can't really initialize everything in a single transition
    init!{ initialize(reads: Map<Address, JournalRecord>, snapshot: JournalSnapShot) {
        let ptr = snapshot.freshest_rec;
        let bdy = snapshot.boundary_lsn;

        // NOTE: we need this if we want to maintain internal wf
        require ptr is Some ==> {
            &&& reads.contains_key(ptr.unwrap())
            &&& bdy <= reads[ptr.unwrap()].message_seq.seq_end
        };
        let seq_end = if ptr is Some { reads[ptr.unwrap()].message_seq.seq_end } else { bdy };
        let lsn_addr_index = build_lsn_addr_index_from_reads(reads, bdy, ptr, seq_end);

        init boundary_lsn = bdy;
        init freshest_rec = ptr;
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
    pub fn initialize_inductive(post: Self, reads: Map<Address, JournalRecord>, snapshot: JournalSnapShot) { }

}}

impl CachedJournal::State {
    pub open spec(checked) fn next_index(self, ptr: Pointer) -> Pointer
        recommends ptr is Some
    {
        let lsns = addr_to_lsns(self.lsn_addr_index, ptr.unwrap(), self.boundary_lsn);
        if !lsns.is_empty() {
            let min = min_lsn(lsns);
            let prior_lsn = (min - 1) as nat;
            if min > 0 && self.boundary_lsn <= prior_lsn && self.lsn_addr_index.contains_key(prior_lsn) {
                Some(self.lsn_addr_index[prior_lsn])
            } else {
                None
            }        
        } else {
            None
        }
    }

    pub open spec fn can_crop_index(self, root: Pointer, depth: nat) -> bool
        decreases depth
    {
        0 < depth ==> {
            &&& root is Some
            &&& self.can_crop_index(self.next_index(root), (depth-1) as nat)
        }
    }

    pub open spec(checked) fn pointer_after_crop_index(self, root: Pointer, depth: nat) -> Pointer
        recommends self.can_crop_index(root, depth)
        decreases depth
    {
        if depth == 0 { root }
        else {
            self.pointer_after_crop_index(self.next_index(root), (depth-1) as nat)
        }
    }
}
} // end of verus