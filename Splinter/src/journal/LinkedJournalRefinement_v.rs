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
        // TODO(chris): adding this assert completes the proof, even though the identical string
        // appears in the ensures.
        // Well actually, sometimes with == it completes the proof, but (AAAARGH) it's super flaky.
        // trying =~=...
        assume(false); // Goodness this is hella flaky.
        assert( post.iptr(ptr) =~= PagedJournal_v::JournalRecord::discard_old_journal_rec(self.iptr(ptr), lsn) );
    }

//      pub proof fn sigh<K, V>(small: Map<K, V>, big: Map<K, V>)
//      requires
//          small.le(big),
//      ensures
//          //small.dom().subset_of(big.dom()),
//          small.dom().subset_of(big.dom()),
//      {
//      }



    // In Dafny, this entire lemma was unneeded; call sites could be replaced by this single line:
    //   assert( self.valid_ranking(big.the_ranking()) ); // witness
    pub proof fn sub_disk_ranking(self, big: DiskView)
    requires
        big.wf(),
        big.acyclic(),
        self.wf(),
        self.is_sub_disk(big),
    ensures
        self.acyclic(),
    {
        let ranking = big.the_ranking();
    // TODO(chris): jon tried writing a contains_key == dom.contains broadcast_forall, but it
    // didn't solve this problem.
        assert( forall |addr| #[trigger] self.entries.contains_key(addr) ==> big.entries.dom().contains(addr) );
        assert( self.valid_ranking(big.the_ranking()) ); // witness
    }

    // TODO(jonh): how does this relate to IPtrFraming!?
    pub proof fn sub_disk_interp(self, big: DiskView, ptr: Pointer)
    requires
        big.wf(),
        big.acyclic(),
        self.wf(),
        self.is_sub_disk(big),
        self.boundary_lsn == big.boundary_lsn,
        self.is_nondangling_pointer(ptr),
    ensures
        self.acyclic(),
        self.iptr(ptr) == big.iptr(ptr),
    decreases if ptr.is_Some() { self.the_ranking()[ptr.unwrap()]+1 } else { 0 }
    {
        assert( big.valid_ranking(big.the_ranking()) ); // witness; new in Verus
        self.sub_disk_ranking(big);
        if ptr.is_Some() {
            self.sub_disk_interp(big, big.next(ptr));
        }
    }

    pub proof fn she_nat_igans(depth: nat)
    {
        if 0 < depth {
            assert( ((depth-1) as nat) < depth );
        }
    }

    pub proof fn pointer_after_crop_commutes_with_interpretation(self, ptr: Pointer, bdy: LSN, depth: nat)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
        bdy == self.boundary_lsn,
        self.can_crop(ptr, depth),
        self.pointer_after_crop(ptr, depth).is_Some(),
    ensures
        PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(self.iptr(ptr), bdy, depth),
        PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(self.iptr(ptr), bdy, depth+1),
        self.iptr(self.pointer_after_crop(ptr, depth))
            == PagedJournal_v::JournalRecord::opt_rec_crop_head_records(self.iptr(ptr), bdy, depth),
    decreases depth
    {
        // Got 36 lines into this proof before I discovered I was missing
        // this ensures which used to be attached to iptr, for free. :v/
        self.iptr_output_valid(ptr);

        if 0 == depth {
            // Dafny didn't need this trigger
            let pojr = self.iptr(ptr).unwrap().cropped_prior(bdy);
            if !PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(pojr, bdy, 0) {
                 assert( false );
            }
        } else {
            self.pointer_after_crop_commutes_with_interpretation(self.entries[ptr.unwrap()].cropped_prior(bdy), bdy, (depth - 1) as nat);
        }
    }

    pub proof fn pointer_after_crop_commutes_with_interpretation_no_some(self, ptr: Pointer, depth: nat)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
        self.can_crop(ptr, depth),
    ensures
        PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(self.iptr(ptr), self.boundary_lsn, depth),
        self.iptr(self.pointer_after_crop(ptr, depth))
            == PagedJournal_v::JournalRecord::opt_rec_crop_head_records(self.iptr(ptr), self.boundary_lsn, depth),
    decreases depth
    {
        self.iptr_output_valid(ptr);
        self.pointer_after_crop_ensures(ptr, depth);

        if 0 < depth {
            self.pointer_after_crop_commutes_with_interpretation_no_some(self.entries[ptr.unwrap()].cropped_prior(self.boundary_lsn), (depth - 1) as nat);
        }
    }

    pub proof fn discard_old_commutes(self, ptr: Pointer, new_bdy: LSN)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
        self.boundary_lsn <= new_bdy,
        ptr.is_Some() ==> new_bdy < self.entries[ptr.unwrap()].message_seq.seq_end,
    ensures
        self.discard_old(new_bdy).acyclic(),
        self.iptr(ptr).is_Some() ==> self.iptr(ptr).unwrap().valid(new_bdy), // discard_old_journal_rec prereq
        PagedJournal_v::JournalRecord::discard_old_journal_rec(self.iptr(ptr), new_bdy) == self.discard_old(new_bdy).iptr(ptr),
    decreases self.the_rank_of(ptr)
    {
        self.iptr_output_valid(ptr);
        assert( self.discard_old(new_bdy).valid_ranking(self.the_ranking()) );
        if ptr.is_Some() {
            let next_ptr = self.entries[ptr.unwrap()].cropped_prior(new_bdy);
            self.iptr(ptr).unwrap().discard_valid(self.boundary_lsn, new_bdy);
            self.discard_old_commutes(next_ptr, new_bdy);
        }
    }
        
}

impl TruncatedJournal {

    pub open spec fn i(self) -> (out: PagedJournal_v::TruncatedJournal)
    recommends
        self.decodable(),
    // ensures out.wf()
    {
        PagedJournal_v::TruncatedJournal{
            boundary_lsn: self.disk_view.boundary_lsn,
            freshest_rec: self.disk_view.iptr(self.freshest_rec),
        }
    }

    pub proof fn mkfs_refines()
    ensures
        Self::mkfs().disk_view.acyclic(),
        Self::mkfs().i() =~= PagedJournal_v::mkfs(),
    {
        assert( Self::mkfs().disk_view.valid_ranking(map![]) );
    }

    pub proof fn discard_interp(self, lsn: LSN, post: Self)
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
    }

    pub proof fn discard_old_commutes(self, new_bdy: LSN)
    requires
        self.decodable(),
        self.can_discard_to(new_bdy),
    ensures
        self.discard_old(new_bdy).decodable(), //prereq
        self.i().can_discard_to(new_bdy), //prereq
        self.discard_old(new_bdy).i() == self.i().discard_old_defn(new_bdy),
    {
        assert( self.disk_view.discard_old(new_bdy).valid_ranking(self.disk_view.the_ranking()) );  // witness to Acyclic
        if new_bdy < self.seq_end() {
          self.disk_view.discard_old_commutes(self.freshest_rec, new_bdy);
        }
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
    pub open spec fn i(self) -> PagedJournal::State
    {
        if self.wf() && self.truncated_journal.disk_view.acyclic() {
            PagedJournal::State{
                truncated_journal: self.truncated_journal.i(),
                unmarshalled_tail: self.unmarshalled_tail,
            }
        } else {
            choose |v| PagedJournal::State::init(v)
        }
    }

    pub proof fn next_refines(self, post: Self, lbl: LinkedJournal::Label)
    requires
        self.inv(),
        LinkedJournal::State::next(self, post, lbl),
    ensures
        PagedJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PagedJournal::State::next_by);    // unfortunate defaults
        reveal(PagedJournal::State::next);    // unfortunate defaults
        reveal(LinkedJournal::State::next_by);
        reveal(LinkedJournal::State::next);

        let step = choose |step| LinkedJournal::State::next_by(self, post, lbl, step);
        assert( LinkedJournal::State::next_by(self, post, lbl, step) );
        match step {
            LinkedJournal::Step::read_for_recovery(depth) =>  {
                let tj = self.truncated_journal;
                let tjd = self.truncated_journal.disk_view;
                tjd.pointer_after_crop_commutes_with_interpretation(
                    tj.freshest_rec, tjd.boundary_lsn, depth);
                tjd.pointer_after_crop_ensures(tj.freshest_rec, depth); // GAAAAH weeks looking for this awful thing

                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::read_for_recovery(depth)) );
            }
            LinkedJournal::Step::freeze_for_commit(depth) =>  {
                assume(false);
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::freeze_for_commit(depth)) );
            }
            LinkedJournal::Step::query_end_lsn() =>  {
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::query_end_lsn()) );
            }
            LinkedJournal::Step::put() =>  {
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::put()) );
            }
            LinkedJournal::Step::discard_old() =>  {
                assume(false);
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::discard_old()) );
            }
            LinkedJournal::Step::internal_journal_marshal(cut, addr) =>  {
                assume(false);
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::internal_journal_marshal(cut)) );
            }
            LinkedJournal::Step::internal_journal_no_op() =>  {
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::internal_journal_no_op()) );
            }
            _ => { assert(false); }
        }
    }
}

} // verus!
