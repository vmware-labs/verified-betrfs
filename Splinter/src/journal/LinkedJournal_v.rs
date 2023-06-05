// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use vstd::map::*;
use crate::coordination_layer::StampedMap_v::LSN;
use crate::coordination_layer::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;

// Needed for pieces of proof pulled in here.
use crate::journal::PagedJournal_v;
use crate::journal::PagedJournal_v::PagedJournal;

verus!{

pub struct JournalRecord {
    pub message_seq: MsgHistory,

    // Never read priorRec directly; only reference it through CroppedPrior.
    // A Pointer only has meaning if its referent isn't rendered irrelevant by
    // some boundaryLSN.
    // In Verus, I'd like to make this not-pub, but I can't because spec
    // functions are written in terms of it. :v/
    pub prior_rec: Pointer,
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
    pub proof fn build_tight_ensures(self, root: Pointer, out: Self)
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
            self.build_tight_ensures(inner_root, self.build_tight(inner_root));
        }
    }

    // TODO please for the love of Z3 automate
    pub proof fn build_tight_auto(self)
    ensures
        forall |root:Pointer| #[trigger self.build_tight(root)]
            self.decodable(root) ==> ({
                &&& (forall |addr| #[trigger] self.build_tight(root).entries.contains_key(addr) ==> self.entries.contains_key(addr))
                &&& self.acyclic() ==> self.build_tight(root).is_sub_disk(self)
        })
    {
        assert forall |root:Pointer| #[trigger self.build_tight(root)]
            self.decodable(root) implies ({
                &&& (forall |addr| #[trigger] self.build_tight(root).entries.contains_key(addr) ==> self.entries.contains_key(addr))
                &&& self.acyclic() ==> self.build_tight(root).is_sub_disk(self)
        }) by {
            self.build_tight_ensures(root, self.build_tight(root));
        }
    }

//     #[verifier(decreases_by)]
//     proof fn thing(self, root: Pointer)
//     {
//          if self.decodable(root) && root.is_Some() {
//             assert( self.acyclic() );
//             let addr = root.unwrap();
//             assert( self.valid_ranking(self.the_ranking()) );
//             assert( self.entries.contains_key(addr) );
//             assert( self.the_rank_of(self.entries[addr].cropped_prior(self.boundary_lsn)) < self.the_rank_of(root) );
//         }
//     }

    pub open spec fn representation(self, root: Pointer) -> (out: Set<Address>)
    recommends
        self.decodable(root),
        self.acyclic(),
    decreases
        self.the_rank_of(root),
    {
        decreases_when(self.decodable(root) && self.acyclic());
        //decreases_by(Self::thing);    // TODO(chris): debugging these failures sucks, unlike
        //inline asserts.
        match root {
            None => Set::empty(),
            Some(addr) => self.representation(self.entries[addr].cropped_prior(self.boundary_lsn)).insert(addr)
        }
    }

    pub proof fn representation_ensures(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
    ensures
        forall |addr| self.representation(root).contains(addr) ==> self.entries.contains_key(addr)
    decreases
        self.the_rank_of(root),
    {
        match root {
            None => {},
            Some(addr) => {
                self.representation_ensures(self.entries[addr].cropped_prior(self.boundary_lsn));
            },
        }
    }

    pub proof fn representation_auto(self)
    ensures
        forall |root|
            self.decodable(root) && self.acyclic()
            ==>
            forall |addr| self.representation(root).contains(addr) ==> self.entries.contains_key(addr)
    {
        assert forall |root|
            self.decodable(root) && self.acyclic()
            implies
            forall |addr| self.representation(root).contains(addr) ==> self.entries.contains_key(addr) by
        {
            self.representation_ensures(root);
        }
    }

    pub open spec fn can_crop(self, root: Pointer, depth: nat) -> bool
    recommends
        self.decodable(root),
        self.block_in_bounds(root),
    decreases depth
    {
        0 < depth ==> {
            &&& root.is_Some()
            &&& self.can_crop(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn), (depth-1) as nat)
        }
    }

    pub open spec fn pointer_after_crop(self, root: Pointer, depth: nat) -> (out: Pointer)
    recommends
        self.decodable(root),
        self.block_in_bounds(root),
        self.can_crop(root, depth),
    decreases depth
    {
        if depth==0 { root }
        else { self.pointer_after_crop(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn), (depth-1) as nat) }
    }

    pub proof fn pointer_after_crop_ensures(self, root: Pointer, depth: nat)
    requires
        self.decodable(root),
        self.block_in_bounds(root),
        self.can_crop(root, depth),
    ensures
        self.is_nondangling_pointer(self.pointer_after_crop(root, depth)),
        self.block_in_bounds(self.pointer_after_crop(root, depth)),
    decreases depth
    {
        if depth > 0 {
            self.pointer_after_crop_ensures(
                self.entries[root.unwrap()].cropped_prior(self.boundary_lsn), (depth-1) as nat)
        }
    }

    pub proof fn pointer_after_crop_auto(self)
    requires
    ensures
        forall |root, depth| {
            &&& self.decodable(root)
            &&& self.block_in_bounds(root)
            &&& self.can_crop(root, depth)
        } ==> {
            &&& self.is_nondangling_pointer(#[trigger] self.pointer_after_crop(root, depth))
            &&& self.block_in_bounds(self.pointer_after_crop(root, depth))
        },
    {
        assert forall |root, depth| {
            &&& self.decodable(root)
            &&& self.block_in_bounds(root)
            &&& self.can_crop(root, depth)
        } implies {
            &&& self.is_nondangling_pointer(#[trigger] self.pointer_after_crop(root, depth))
            &&& self.block_in_bounds(self.pointer_after_crop(root, depth))
        } by {
            self.pointer_after_crop_ensures(root, depth);
        }
    }

    //////////////////////////////////////////////////////////////////////////
    // Proof-y stuff, pulled in here because it's required by the invariant
    // proofs which the state machine macro demands we put inline.
    //////////////////////////////////////////////////////////////////////////

    pub open spec fn iptr(self, ptr: Pointer) -> (out: Option<PagedJournal_v::JournalRecord>)
    recommends
        self.decodable(ptr),
        self.acyclic(),
    decreases self.the_rank_of(ptr)
    {
        decreases_when(self.decodable(ptr) && self.acyclic());
        if ptr.is_None() { None }
        else {
            let jr = self.entries[ptr.unwrap()];
            Some(PagedJournal_v::JournalRecord{
                message_seq: jr.message_seq,
                prior_rec: Box::new(self.iptr(jr.cropped_prior(self.boundary_lsn))),
            })
        }
    }

    pub proof fn iptr_ignores_extra_blocks(self, ptr: Pointer, big: DiskView)
    requires
        self.wf(),
        self.is_nondangling_pointer(ptr),
        big.wf(),
        big.acyclic(),
        self.is_sub_disk(big),
    ensures
        self.acyclic(),
        self.iptr(ptr) == big.iptr(ptr),
    decreases big.the_rank_of(ptr)
    {
        // TODO(verus,chris): map.le should broadcast-ensures dom.subset_of(dom)
        assert( self.entries.dom().subset_of(big.entries.dom()) );

        assert( self.valid_ranking(big.the_ranking()) ); // witness to acyclic
        if ptr.is_Some() {
            let next = big.entries[ptr.unwrap()].cropped_prior(big.boundary_lsn);
            assert( big.the_rank_of(next) < big.the_rank_of(ptr) );
            self.iptr_ignores_extra_blocks(next, big);
        }
    }

    pub open spec fn next(self, ptr: Pointer) -> Pointer
    {
        self.entries[ptr.unwrap()].cropped_prior(self.boundary_lsn)
    }

    // A direct translation of this proof was flaky; whether it proved depended on whether
    // I proc'd it down with --verify-function
    // The trigger (the if line) was needed here whereas not in Dafny; Dafny must have chosen
    // a more-generous trigger for the ensures forall?
    pub proof fn build_tight_ranks(self, ptr: Pointer)
    requires
        self.decodable(ptr),
        self.acyclic(),
        ptr.is_Some(),
    ensures ({
        forall |addr: Address| #[trigger] self.build_tight(self.next(ptr)).entries.contains_key(addr) ==> {
            &&& self.the_ranking().contains_key(addr)
            &&& self.the_ranking()[addr] < self.the_ranking()[ptr.unwrap()]
        }
    })
    decreases self.the_rank_of(ptr)
    {
        let next = self.next(ptr);
        if next.is_Some() {
            self.build_tight_ranks(next);

            assert forall |addr: Address| #[trigger] self.build_tight(self.next(ptr)).entries.contains_key(addr) implies {
                &&& self.the_ranking().contains_key(addr)
                &&& self.the_ranking()[addr] < self.the_ranking()[ptr.unwrap()]
            } by {
                if self.build_tight(self.next(next)).entries.contains_key(addr) { } // trigger
            }
        }
    }

    pub proof fn build_tight_shape(self, root: Pointer)
    requires
        root.is_Some(),
        self.decodable(root),
        self.acyclic(),
    ensures (
        self.build_tight(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn))
        == Self{entries: self.build_tight(root).entries.remove(root.unwrap()), ..self})
    {
        let next = self.entries[root.unwrap()].cropped_prior(self.boundary_lsn);
        if next.is_Some() {
            self.build_tight_ranks(root);   // proves root.value !in self.build_tight(next, ranking).entries;
        }

        assert_maps_equal!(
            self.build_tight(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn)).entries,
            self.build_tight(root).entries.remove(root.unwrap())
            );
    }

    pub open spec fn is_tight(self, root: Pointer) -> bool
    {
        &&& self.decodable(root)
        &&& self.acyclic()
        &&& forall |other: Self| {
            &&& other.decodable(root)
            &&& other.acyclic()
            &&& self.iptr(root) == other.iptr(root)
            &&& other.is_sub_disk(self)
            ==> other == self
        }
    }

    pub proof fn build_tight_builds_sub_disks(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
    ensures
        self.build_tight(root).is_sub_disk(self),
    decreases self.the_rank_of(root)
    {
        if root.is_Some() {
            let next = self.entries[root.unwrap()].cropped_prior(self.boundary_lsn);
            self.build_tight_builds_sub_disks(next);
        }
    }

    pub proof fn tight_sub_disk(self, root: Pointer, tight: Self)
    requires
        self.decodable(root),
        tight == self.build_tight(root),
        self.acyclic(),
        tight.is_sub_disk(self),
    ensures
        tight.is_tight(root),
    decreases self.the_rank_of(root)
    {
        assert( tight.valid_ranking(self.the_ranking()) ); // witness
        if root.is_Some() {
            let next = self.entries[root.unwrap()].cropped_prior(self.boundary_lsn);
            let inner = self.build_tight(next);
            self.build_tight_shape(root);
            self.tight_sub_disk(next, inner);
//             assert( tight.valid_ranking(self.the_ranking()) ); // witness
            assert forall |other: Self| {
                &&& other.decodable(root)
                &&& other.acyclic()
                &&& tight.iptr(root) == other.iptr(root)
                &&& other.is_sub_disk(tight)
            } implies other == tight by {
                // any other tighter disk implies an "other_inner" disk tighter than inner, but inner.IsTight(next).
                let other_inner = DiskView{ entries: other.entries.remove(root.unwrap()), ..other };
                assert( inner.valid_ranking( self.the_ranking()) );
                other_inner.iptr_ignores_extra_blocks(next, inner);
            }
        }
    }

    pub proof fn tight_interp(big: Self, root: Pointer, tight: Self)
    requires
        big.decodable(root),
        tight == big.build_tight(root),
        big.acyclic(),
    ensures
        tight.is_sub_disk(big),
        tight.is_tight(root),
        tight.iptr(root) == big.iptr(root),
        tight.acyclic(),
    decreases big.the_rank_of(root)
    {
        if root.is_None() {
            assert( tight.valid_ranking(big.the_ranking()) );
        } else {
            big.build_tight_builds_sub_disks(root);
            big.tight_sub_disk(root, tight);
            assert( tight.valid_ranking(big.the_ranking()) );
            tight.iptr_ignores_extra_blocks(root, big);
        }
    }
}

pub struct TruncatedJournal {
    pub freshest_rec: Pointer, // root address of journal
    pub disk_view: DiskView,
}

impl TruncatedJournal {
    pub open spec fn wf(self) -> bool {
        &&& self.disk_view.wf()
        &&& self.disk_view.is_nondangling_pointer(self.freshest_rec)
        &&& self.disk_view.block_in_bounds(self.freshest_rec)
    }

    pub open spec fn seq_start(self) -> LSN {
        self.disk_view.boundary_lsn
    }

    pub open spec fn seq_end(self) -> LSN
    recommends
        self.disk_view.is_nondangling_pointer(self.freshest_rec),   // why not just wf()?
    {
        if self.freshest_rec.is_None() // normal case with empty TJ
            { self.disk_view.boundary_lsn }
        else
            { self.disk_view.entries[self.freshest_rec.unwrap()].message_seq.seq_end }
    }

    pub open spec fn can_discard_to(self, lsn: LSN) -> bool
    recommends
        self.wf(),
    {
        self.seq_start() <= lsn <= self.seq_end()
    }

    pub open spec fn discard_old(self, lsn: LSN) -> Self
    recommends
        self.wf(),
        self.can_discard_to(lsn),
    {
      // Simply advances the boundary LSN of the diskView
       TruncatedJournal{
           freshest_rec: if self.seq_end() == lsn { None } else { self.freshest_rec },
           disk_view: self.disk_view.discard_old(lsn),
       }
    }

    pub open spec fn decodable(self) -> bool
    {
        &&& self.wf()
        &&& self.disk_view.acyclic()
    }

    pub open spec fn can_crop(self, depth: nat) -> bool
    {
        &&& self.decodable()
        &&& self.disk_view.can_crop(self.freshest_rec, depth)
    }

    pub open spec fn crop(self, depth: nat) -> Self
    recommends
        self.can_crop(depth),
    {
        let ptr = self.disk_view.pointer_after_crop(self.freshest_rec, depth);
        TruncatedJournal{ freshest_rec: ptr, ..self }
    }

    pub proof fn crop_ensures(self, depth: nat)
    requires
        self.can_crop(depth),
    ensures
        self.crop(depth).wf(),
    {
        self.disk_view.pointer_after_crop_auto();
    }

    pub proof fn crop_auto(self)
    ensures
        forall |depth| self.can_crop(depth) ==> #[trigger] self.crop(depth).wf(),
    {
        assert forall |depth| self.can_crop(depth) implies #[trigger] self.crop(depth).wf() by {
            self.disk_view.pointer_after_crop_auto();
        }
    }

    pub open spec fn append_record(self, addr: Address, msgs: MsgHistory) -> (out: Self)
    {
        Self{
            disk_view: DiskView {
                entries: self.disk_view.entries.insert(addr, JournalRecord {
                    message_seq: msgs,
                    prior_rec: self.freshest_rec,
                }),
                ..self.disk_view
            },
            freshest_rec: Some(addr),
        }
    }

// Proof is trivial, so probably never needed this ensures in Dafny.
//     pub proof fn append_record_ensures(self, addr: Address, msgs: MsgHistory)
//     ensures
//         !self.disk_view.entries.contains_key(addr)
//             ==> self.disk_view.is_sub_disk(self.append_record(addr, msgs).disk_view),
//     {
//     }

    pub open spec fn build_tight(self) -> (out: Self)
    {
        TruncatedJournal{
            disk_view: self.disk_view.build_tight(self.freshest_rec),
            ..self
        }
    }

    pub open spec fn representation(self) -> (out: Set<Address>)
    recommends
        self.disk_view.decodable(self.freshest_rec),
        self.disk_view.acyclic(),
    {
        self.disk_view.representation(self.freshest_rec)
    }

    // Yeah re-exporting this is annoying. Gonna just ask others to call 
    // self.disk_view.representation_auto();
//     pub proof fn representation_ensures(self)
//     requires
//         self.disk_view.decodable(self.freshest_rec),
//         self.disk_view.acyclic(),
//     ensures
//         forall |addr| self.representation().contains(addr)
//             ==> self.disk_view.entries.contains_key(addr)
//     {
//         self.disk_view.representation_auto();
//     }

    pub open spec fn disk_is_tight_wrt_representation(self) -> bool
    recommends
        self.disk_view.decodable(self.freshest_rec),
        self.disk_view.acyclic(),
    {
        self.disk_view.entries.dom() == self.representation()
    }

    pub open spec fn mkfs() -> (out: Self)
    {
        Self{
            freshest_rec: None,
            disk_view: DiskView { boundary_lsn: 0, entries: Map::empty() },
        }
    }

    pub proof fn mkfs_ensures()
    ensures
        Self::mkfs().decodable(),
    {
        assert( Self::mkfs().disk_view.valid_ranking(Map::empty()) );
    }

}

state_machine!{ LinkedJournal {
    fields {
        pub truncated_journal: TruncatedJournal,
        pub unmarshalled_tail: MsgHistory,
    }

    pub open spec fn wf(self) -> bool {
        &&& self.truncated_journal.wf()
        &&& self.unmarshalled_tail.wf()

        // TODO(jonh): can probably delete this conjunct, since it's proven by interp
        &&& self.truncated_journal.seq_end() == self.unmarshalled_tail.seq_start
    }

    pub open spec fn seq_start(self) -> LSN
    {
        self.truncated_journal.seq_start()
    }

    pub open spec fn seq_end(self) -> LSN
    recommends
        self.wf(),
    {
        self.unmarshalled_tail.seq_end
    }
    
    pub open spec fn unused_addr(self, addr: Address) -> bool
    {
        // TODO reaching into truncatedJournal to find the diskView feels skeezy
        !self.truncated_journal.disk_view.entries.contains_key(addr)
    }

    #[is_variant]
    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: TruncatedJournal},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        Internal{},   // Local No-op label
    }

    // unfortunate:
    // error: this item is not supported
//     impl Label {
//         pub open spec fn wf(self) -> bool {
//             self.is_FreezeForCommit() ==> self.get_FreezeForCommit().decodable()
//         }
//     }
    pub open spec fn lbl_wf(lbl: Label) -> bool
    {
        match lbl {
            Label::ReadForRecovery{messages} => messages.wf(),
            Label::FreezeForCommit{frozen_journal} => frozen_journal.decodable(),
            _ => true,
        }
    }

    transition!{ read_for_recovery(lbl: Label, depth: nat) {
        require pre.wf();
        require lbl.is_ReadForRecovery();
        require Self::lbl_wf(lbl);
        require pre.truncated_journal.decodable(); // Shown by invariant, not runtime-checked
        let dv = pre.truncated_journal.disk_view;
        require dv.can_crop(pre.truncated_journal.freshest_rec, depth);
        let ptr = dv.pointer_after_crop(pre.truncated_journal.freshest_rec, depth);
        require ptr.is_Some();
        require dv.entries[ptr.unwrap()].message_seq.maybe_discard_old(dv.boundary_lsn) == lbl.get_ReadForRecovery_messages();
    }}

    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_FreezeForCommit();
        require pre.truncated_journal.decodable(); // Shown by invariant, not runtime-checked
        let dv = pre.truncated_journal.disk_view;
        require dv.can_crop(pre.truncated_journal.freshest_rec, depth);
        let ptr = dv.pointer_after_crop(pre.truncated_journal.freshest_rec, depth);
        let cropped_tj = TruncatedJournal{
            freshest_rec: ptr,
            disk_view: pre.truncated_journal.disk_view
        };
        let label_fj = lbl.get_FreezeForCommit_frozen_journal();
        let new_bdy = label_fj.seq_start();
        require dv.boundary_lsn <= new_bdy;
        require cropped_tj.can_discard_to(new_bdy);
        require label_fj == cropped_tj.discard_old(new_bdy).build_tight();
    }}

    transition!{ query_end_lsn(lbl: Label, depth: nat) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_QueryEndLsn();
        require lbl.get_QueryEndLsn_end_lsn() == pre.seq_end();
    }}

    transition!{ put(lbl: Label, depth: nat) {
        require pre.wf();
        //require Self::lbl_wf(lbl);
        require lbl.get_Put_messages().wf();    // direct translation. TODO fold into lbl_wf
        require lbl.is_Put();
        require lbl.get_Put_messages().seq_start == pre.seq_end();
        update unmarshalled_tail = pre.unmarshalled_tail.concat(lbl.get_Put_messages());
    }}

    transition!{ discard_old(lbl: Label, depth: nat) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_DiscardOld();
        require pre.seq_start() <= lbl.get_DiscardOld_start_lsn() <= pre.seq_end();

        require lbl.get_DiscardOld_require_end() == pre.seq_end();
        require pre.truncated_journal.can_discard_to(lbl.get_DiscardOld_start_lsn());
        update truncated_journal = pre.truncated_journal.discard_old(lbl.get_DiscardOld_start_lsn()).build_tight();
        update unmarshalled_tail =
            if pre.unmarshalled_tail.seq_start <= lbl.get_DiscardOld_start_lsn()
                { pre.unmarshalled_tail.discard_old(lbl.get_DiscardOld_start_lsn()) }
            else
                { pre.unmarshalled_tail };
    }}

    // TODO: Hmm, in dfy the transition is split into partial actions
    // InternalJournalMarshalAlloc & InternalJournalMarshalRecord, for
    // reuse lower in the stack.
    // Guess we should break this up into predicates? Ew. For now
    // I'll leave them lumped together.
    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address) {
        // InternalJournalMarshalAlloc(v, addr)
        require pre.unused_addr(addr);

        // InternalJournalMarshalRecord(v, v', lbl, cut, addr)
        require pre.wf();
        require lbl.is_Internal();
        require pre.unmarshalled_tail.seq_start < cut; // Can't marshall nothing.
        require pre.unmarshalled_tail.can_discard_to(cut);
        let marshalled_msgs = pre.unmarshalled_tail.discard_recent(cut);

        update truncated_journal = pre.truncated_journal.append_record(addr, marshalled_msgs);
        update unmarshalled_tail = pre.unmarshalled_tail.discard_old(cut);
    }}

    transition!{ internal_journal_no_op(lbl: Label) {
        require pre.wf();
        require lbl.is_Internal();
    }}

    init!{ initialize(truncated_journal: TruncatedJournal) {
        require truncated_journal.decodable();  // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
        init truncated_journal = truncated_journal;
        init unmarshalled_tail = MsgHistory::empty_history_at(truncated_journal.seq_end());
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.wf()
        &&& self.truncated_journal.decodable()
        &&& self.truncated_journal.disk_view.acyclic()
    }

        #[inductive(read_for_recovery)]
        fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }

        #[inductive(freeze_for_commit)]
        fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }

        #[inductive(query_end_lsn)]
        fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, lbl: Label, depth: nat) {
        }

        #[inductive(discard_old)]
        fn discard_old_inductive(pre: Self, post: Self, lbl: Label, depth: nat) {
//             let loose = pre.truncated_journal.discard_old(lbl.get_DiscardOld_start_lsn());
//             let dv = post.truncated_journal.disk_view;
//             loose.disk_view.build_tight_ensures(loose.freshest_rec,
//                  loose.disk_view.build_tight(loose.freshest_rec));
//             //loose.disk_view.build_tight_auto(); auto couldn't guess ptr?
//             assert( post.truncated_journal.disk_view.entries_wf() );
// 
//             assert( loose.disk_view.nondangling_pointers() );
//             assert( loose.disk_view.is_nondangling_pointer(
//                     loose.freshest_rec) );

            let lsn = lbl.get_DiscardOld_start_lsn();
            let cropped_tj = pre.truncated_journal.discard_old(lsn);
            let tight_tj = cropped_tj.build_tight();
            assert( cropped_tj.disk_view.valid_ranking(
                    pre.truncated_journal.disk_view.the_ranking()) ); // witness to acyclic
            DiskView::tight_interp(cropped_tj.disk_view, cropped_tj.freshest_rec, tight_tj.disk_view);
            assert( post.truncated_journal.disk_view.nondangling_pointers() );
            assert( post.truncated_journal.disk_view.is_nondangling_pointer(
                    post.truncated_journal.freshest_rec) );
            assert( post.truncated_journal.wf() );
            assert( post.wf() );
            assert( post.truncated_journal.decodable() );
            assert( post.truncated_journal.disk_view.acyclic() );
        }

        #[inductive(internal_journal_marshal)]
        fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address) {
            assume( false );
        }

        #[inductive(internal_journal_no_op)]
        fn internal_journal_no_op_inductive(pre: Self, post: Self, lbl: Label) { }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, truncated_journal: TruncatedJournal) { }


} } // state_machine!

} // verus!
