// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::coordination_layer::StampedMap_v::LSN;
use crate::coordination_layer::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;

verus!{

pub struct JournalRecord {
    pub message_seq: MsgHistory,
    prior_rec: Pointer,
}

impl JournalRecord {
    pub open spec fn wf(self) -> bool {
        &&& self.message_seq.wf()
        &&& !self.message_seq.is_empty()
    }

    pub open spec fn has_link(self, boundary_lsn: LSN) -> bool {
        boundary_lsn < self.message_seq.seq_start ==> self.cropped_prior(boundary_lsn).is_Some()
    }

    pub closed spec fn cropped_prior(self, boundary_lsn: LSN) -> Pointer {
        if boundary_lsn < self.message_seq.seq_start { self.prior_rec } else { None }
    }

    pub open spec fn contains_lsn(self, boundary_lsn: LSN) -> bool {
        self.message_seq.seq_start <= boundary_lsn < self.message_seq.seq_end
    }
}

  // The DiskView in this module is a tightly-populated mapping:
  // every record the journal needs is present in the mapping,
  // and every address is "important" to the journal.
  // The boundaryLSN enables us to ignore "cropped" pointers.
  // The values in this DiskView are typed, unlike GenericDisk.DiskView.
  //
  // TODO(jonh): Jialin suggests JournalStore to avoid the way "disk" brings in too
  // many other model assumptions.

pub struct DiskView {
    pub boundary_lsn: LSN,
    pub entries: Map<Address, JournalRecord>,
}

impl DiskView {
    pub open spec fn entries_wf(self) -> bool {
        forall |addr| #[trigger] self.entries.contains_key(addr) ==> self.entries[addr].wf()
    }

    pub open spec fn is_nondangling_pointer(self, ptr: Pointer) -> bool {
        ptr.is_Some() ==> self.entries.contains_key(ptr.unwrap())
    }

    pub open spec fn nondangling_pointers(self) -> bool {
        forall |addr| #[trigger] self.entries.contains_key(addr)
            ==> self.is_nondangling_pointer(self.entries[addr].cropped_prior(self.boundary_lsn))
    }

    pub open spec fn this_block_can_concat(self, addr: Address) -> bool {
        let head = self.entries[addr];
        let next_ptr = head.cropped_prior(self.boundary_lsn);
        next_ptr.is_Some() ==> self.entries[next_ptr.unwrap()].message_seq.can_concat(head.message_seq)
    }

    pub open spec fn blocks_can_concat(self) -> bool
    recommends
        self.entries_wf(),
        self.nondangling_pointers(),
    {
        forall |addr| #[trigger] self.entries.contains_key(addr)
            ==> self.this_block_can_concat(addr)
    }

    pub open spec fn blocks_each_have_link(self) -> bool
    {
        forall |addr| #[trigger] self.entries.contains_key(addr)
            ==> self.entries[addr].has_link(self.boundary_lsn)
    }

    pub open spec fn block_in_bounds(self, ptr: Pointer) -> bool
    {
        &&& self.is_nondangling_pointer(ptr)
        &&& (ptr.is_Some() ==> self.boundary_lsn < self.entries[ptr.unwrap()].message_seq.seq_end)
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.entries_wf()
        &&& self.nondangling_pointers()
        &&& self.blocks_can_concat()
        &&& self.blocks_each_have_link()
    }

    pub open spec fn valid_ranking(self, ranking: Ranking) -> bool
    recommends
        self.wf(),
    {
        &&& self.entries.dom().subset_of(ranking.dom())
        &&& (forall |addr| #[trigger] self.entries.contains_key(addr) && self.entries[addr].cropped_prior(self.boundary_lsn).is_Some()
                ==> ranking[self.entries[addr].cropped_prior(self.boundary_lsn).unwrap()] < ranking[addr]
            )
    }

    pub open spec fn acyclic(self) -> bool
    recommends
        self.wf(),
    {
        exists |ranking| self.valid_ranking(ranking)
    }

    pub open spec fn the_ranking(self) -> Ranking
    recommends
        self.wf(),
        self.acyclic(),
    {
        choose |ranking| self.valid_ranking(ranking)
    }

    pub open spec fn decodable(self, ptr: Pointer) -> bool
    {
        &&& self.wf()
        &&& self.is_nondangling_pointer(ptr)
    }

    // NB it's interesting that LinkedBetree needs to pass rankings
    // around so it can reuse and reconstruct them, but the journal can
    // always get away with using some random old CHOOSEn ranking.
    pub open spec fn the_rank_of(self, ptr: Pointer) -> nat
    recommends
        self.decodable(ptr),
    {
        if ptr.is_Some() && self.acyclic()
            { self.the_ranking()[ptr.unwrap()] + 1 }
        else
            { 0 }
    }

    // Simply advance the boundary LSN
    pub open spec fn discard_old(self, new_boundary: LSN) -> (out: Self)
    recommends
        self.boundary_lsn <= new_boundary
    {
        Self{boundary_lsn: new_boundary, ..self}
    }

    pub open spec fn is_sub_disk(self, bigger: Self) -> bool
    {
        &&& bigger.boundary_lsn == self.boundary_lsn
        &&& self.entries.le(bigger.entries)
    }

    pub open spec fn is_sub_disk_with_newer_lsn(self, bigger: Self) -> bool
    {
        &&& bigger.boundary_lsn <= self.boundary_lsn
        &&& self.entries.le(bigger.entries)
    }

//     #[verifier(decreases_by)]
//     proof fn thing(self, root: Pointer)
//     {
// //         if self.acyclic() && root.is_Some() {
// //             let addr = root.unwrap();
// //             assert( self.valid_ranking(self.the_ranking()) );
// //             assert( self.entries.contains_key(addr) );
// //             assert( self.the_rank_of(self.entries[addr].cropped_prior(self.boundary_lsn)) < self.the_rank_of(root) );
// //         }
//     }

    pub open spec fn build_tight(self, root: Pointer) -> (out: Self)
    recommends
        self.decodable(root),
        // TODO want ensures here
    decreases
        self.the_rank_of(root),
    {
//         // TODO(chris): missing documentation for (and nice syntax for?) decreases_by.
//         // TODO(chris): Error messages should offer a function signature.
//         decreases_by(Self::thing);
        // Geez and this thing's a mess
        decreases_when(self.decodable(root));

        if !self.acyclic() { Self{boundary_lsn: 0, entries: Map::empty()} } // silly
        else if root.is_None() { Self{boundary_lsn: self.boundary_lsn, entries: Map::empty()} }
        else {
            let addr = root.unwrap();
            let tail = self.build_tight(self.entries[addr].cropped_prior(self.boundary_lsn));
            Self{
                boundary_lsn: self.boundary_lsn,
                entries: tail.entries.insert(addr, self.entries[addr]),
            }
        }
    }

    // TODO auto-generate please
    pub proof fn build_tight_inductive(self, root: Pointer, out: Self)
        // TODO(chris): really want the `let` that scopes around requires, ensures, and body here!
    requires
        self.decodable(root),
        out == self.build_tight(root),
    ensures
        forall |addr| #[trigger] out.entries.contains_key(addr) ==> self.entries.contains_key(addr),
        self.acyclic() ==> out.is_sub_disk(self),
    decreases
        self.the_rank_of(root),
    {
        if !self.acyclic() { }
        else if root.is_None() { }
        else {
            let inner_root = self.entries[root.unwrap()].cropped_prior(self.boundary_lsn);
            self.build_tight_inductive(inner_root, self.build_tight(inner_root));
        }
    }
}

}
