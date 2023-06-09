// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::coordination_layer::StampedMap_v::LSN;
use crate::coordination_layer::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::journal::PagedJournal_v;
use crate::journal::PagedJournal_v::PagedJournal;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::*;

verus!{

// impl JournalRecord {
//     pub open spec fn i(self) -> PagedJournal_v::JournalRecord {
//     }
// }

impl DiskView {
    pub proof fn iptr_output_valid(self, ptr: Pointer)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
    ensures
        self.iptr(ptr).is_Some() ==> self.iptr(ptr).unwrap().valid(self.boundary_lsn),
    decreases self.the_rank_of(ptr)
    {
        if ptr.is_Some() {
            self.iptr_output_valid(self.next(ptr));
        }
    }

    pub proof fn discard_interp(self, lsn: LSN, post: Self, ptr: Pointer)
    requires
        self.wf(),
        self.acyclic(),
        self.boundary_lsn <= lsn,
        post == self.discard_old(lsn),
        self.block_in_bounds(ptr),
        post.block_in_bounds(ptr),
    ensures
        post.acyclic(),
        self.iptr(ptr).is_Some() ==> self.iptr(ptr).unwrap().valid(lsn),
        post.iptr(ptr) == PagedJournal_v::JournalRecord::discard_old_journal_rec(self.iptr(ptr), lsn),
    decreases if ptr.is_Some() { self.the_ranking()[ptr.unwrap()]+1 } else { 0 }
    {
        self.iptr_output_valid(ptr);
        assert( post.valid_ranking(self.the_ranking()) );
        if ptr.is_Some() && lsn < self.entries[ptr.unwrap()].message_seq.seq_start {
            self.discard_interp(lsn, post, post.next(ptr));
        }
    }
}

impl TruncatedJournal {
    pub open spec fn iptr(dv: DiskView, ptr: Pointer) -> (out: Box<Option<PagedJournal_v::JournalRecord>>)
    recommends
        dv.decodable(ptr),
        dv.acyclic(),
    // ensures
        // dv.block_in_bounds(ptr),
        // out.is_Some() ==> out.unwrape().valid(dv.boundary_lsn)
    decreases dv.the_rank_of(ptr)
    {
        decreases_when(dv.decodable(ptr) && dv.acyclic());  // can't we just use the recommends?
        match ptr {
            None => Box::new(None),
            Some(addr) => {
                let jr = dv.entries[addr];
                Box::new(Some(PagedJournal_v::JournalRecord{
                    message_seq: jr.message_seq,
                    prior_rec: Self::iptr(dv, jr.cropped_prior(dv.boundary_lsn)),
                }))
            }
        }
    }

    pub open spec fn i(self) -> (out: PagedJournal_v::TruncatedJournal)
    recommends
        self.decodable(),
    // ensures out.wf()
    {
        PagedJournal_v::TruncatedJournal{
            boundary_lsn: self.disk_view.boundary_lsn,
            freshest_rec: *Self::iptr(self.disk_view, self.freshest_rec),
        }
    }

    pub proof fn mkfs_refines()
    ensures
        Self::mkfs().disk_view.acyclic(),
        Self::mkfs().i() =~= PagedJournal_v::mkfs(),
    {
        assert( Self::mkfs().disk_view.valid_ranking(Map::empty()) );
    }

    pub proof fn tj_discard_interp(self, lsn: LSN, post: Self)
    requires
        self.wf(),
        self.disk_view.acyclic(),
        self.seq_start() <= lsn <= self.seq_end(),
        post == self.discard_old(lsn),
    ensures
        post.disk_view.acyclic(),
        self.i().discard_old_defn(lsn) == post.i(),
    {
        assert( post.disk_view.valid_ranking(self.disk_view.the_ranking()) );
        self.disk_view.discard_interp(lsn, post.disk_view, post.freshest_rec);
        if self.i().seq_end() != lsn {
            assume(false); // LEFT OFF HERE
            assert( self.i().discard_old_defn(lsn).freshest_rec =~~=
                    PagedJournal_v::JournalRecord::discard_old_journal_rec(self.i().freshest_rec, lsn) );
            assert( post.i().freshest_rec == *Self::iptr(post.disk_view, post.freshest_rec) );

            assert( post.i().freshest_rec ==
                    PagedJournal_v::JournalRecord::discard_old_journal_rec(self.disk_view.iptr(post.freshest_rec), lsn) );
            assert( self.i().freshest_rec == self.disk_view.iptr(post.freshest_rec) );
        }
        assert( self.i().discard_old_defn(lsn).freshest_rec =~~= post.i().freshest_rec  );
        assert( self.i().discard_old_defn(lsn) =~~= post.i() );
    }
}

impl LinkedJournal::Label {
    pub open spec fn i(self) -> PagedJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} => PagedJournal::Label::ReadForRecovery{messages},
            Self::FreezeForCommit{frozen_journal} => PagedJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.i()},
            Self::QueryEndLsn{end_lsn} => PagedJournal::Label::QueryEndLsn{end_lsn},
            Self::Put{messages} => PagedJournal::Label::Put{messages},
            Self::DiscardOld{start_lsn, require_end} => PagedJournal::Label::DiscardOld{start_lsn, require_end},
            Self::Internal{} => PagedJournal::Label::Internal{},
        }
    }
}

impl LinkedJournal::State {
}

} // verus!
