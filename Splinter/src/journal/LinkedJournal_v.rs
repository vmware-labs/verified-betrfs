// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use vstd::map::*;
use vstd::math;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
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
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.message_seq.wf()
        &&& !self.message_seq.is_empty()
    }

    pub open spec(checked) fn has_link(self, boundary_lsn: LSN) -> bool {
        boundary_lsn < self.message_seq.seq_start ==> self.cropped_prior(boundary_lsn) is Some
    }

    pub open spec(checked) fn cropped_prior(self, boundary_lsn: LSN) -> Pointer {
        if boundary_lsn < self.message_seq.seq_start { self.prior_rec } else { None }
    }

    pub open spec(checked) fn contains_lsn(self, boundary_lsn: LSN, lsn: LSN) -> bool {
        math::max(self.message_seq.seq_start as int, boundary_lsn as int) as nat <= lsn < self.message_seq.seq_end
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
#[verifier::ext_equal]
pub struct DiskView {
    pub boundary_lsn: LSN,
    pub entries: Map<Address, JournalRecord>,
}

impl DiskView {
    pub open spec(checked) fn entries_wf(self) -> bool {
        forall |addr| #[trigger] self.entries.contains_key(addr) ==> self.entries[addr].wf()
    }

    pub open spec(checked) fn is_nondangling_pointer(self, ptr: Pointer) -> bool {
        ptr is Some ==> self.entries.contains_key(ptr.unwrap())
    }

    pub open spec(checked) fn nondangling_pointers(self) -> bool {
        forall |addr| #[trigger] self.entries.contains_key(addr)
            ==> self.is_nondangling_pointer(self.entries[addr].cropped_prior(self.boundary_lsn))
    }

    pub open spec(checked) fn this_block_can_concat(self, addr: Address) -> bool
    recommends
        self.entries_wf(),
        self.nondangling_pointers(),
        self.entries.contains_key(addr),
    {
        let head = self.entries[addr];
        let next_ptr = head.cropped_prior(self.boundary_lsn);
        next_ptr is Some ==> self.entries[next_ptr.unwrap()].message_seq.can_concat(head.message_seq)
    }

    pub open spec(checked) fn blocks_can_concat(self) -> bool
    recommends
        self.entries_wf(),
        self.nondangling_pointers(),
    {
        forall |addr| #[trigger] self.entries.contains_key(addr)
            ==> self.this_block_can_concat(addr)
    }

    pub open spec(checked) fn blocks_each_have_link(self) -> bool
    {
        forall |addr| #[trigger] self.entries.contains_key(addr)
            ==> self.entries[addr].has_link(self.boundary_lsn)
    }

    pub open spec(checked) fn block_in_bounds(self, ptr: Pointer) -> bool
    {
        &&& self.is_nondangling_pointer(ptr)
        &&& (ptr is Some ==> self.boundary_lsn < self.entries[ptr.unwrap()].message_seq.seq_end)
    }

    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.entries_wf()
        &&& self.nondangling_pointers()
        &&& self.blocks_can_concat()
        &&& self.blocks_each_have_link()
    }

    pub open spec(checked) fn valid_ranking(self, ranking: Ranking) -> bool
    recommends
        self.wf(),
    {
        &&& self.entries.dom().subset_of(ranking.dom())
        &&& (forall |addr| #[trigger] self.entries.contains_key(addr) && self.entries[addr].cropped_prior(self.boundary_lsn) is Some
                ==> ranking[self.entries[addr].cropped_prior(self.boundary_lsn).unwrap()] < ranking[addr]
            )
    }

    pub open spec(checked) fn acyclic(self) -> bool
    recommends
        self.wf(),
    {
        exists |ranking| self.valid_ranking(ranking)
    }

    pub open spec(checked) fn the_ranking(self) -> Ranking
    recommends
        self.wf(),
        self.acyclic(),
    {
        choose |ranking| self.valid_ranking(ranking)
    }

    pub open spec(checked) fn decodable(self, ptr: Pointer) -> bool
    {
        &&& self.wf()
        &&& self.is_nondangling_pointer(ptr)
    }

    // NB it's interesting that LinkedBetree needs to pass rankings
    // around so it can reuse and reconstruct them, but the journal can
    // always get away with using some random old CHOOSEn ranking.
    pub open spec(checked) fn the_rank_of(self, ptr: Pointer) -> nat
    recommends
        self.decodable(ptr),
    {
        if ptr is Some && self.acyclic()
            { self.the_ranking()[ptr.unwrap()] + 1 }
        else
            { 0 }
    }

    pub open spec(checked) fn seq_start(self) -> LSN {
        self.boundary_lsn
    }

    pub open spec(checked) fn seq_end(self, root: Pointer) -> LSN
    recommends
        self.is_nondangling_pointer(root),   // why not just wf()?
    {
        if root is None
            { self.boundary_lsn }
        else
            { self.entries[root.unwrap()].message_seq.seq_end }
    }

    // Simply advance the boundary LSN
    pub open spec(checked) fn discard_old(self, new_boundary: LSN) -> (out: Self)
    recommends
        self.boundary_lsn <= new_boundary
    {
        Self{boundary_lsn: new_boundary, ..self}
    }

    pub open spec(checked) fn is_sub_disk(self, bigger: Self) -> bool
    {
        &&& bigger.boundary_lsn == self.boundary_lsn
        &&& self.entries <= bigger.entries
    }

    // TODO: should probably promote to maps::le_transitive_auto
    pub proof fn sub_disk_transitive_auto()
    ensures forall |a:Self, b:Self, c: Self| #[trigger] a.is_sub_disk(b) && #[trigger] b.is_sub_disk(c) ==> a.is_sub_disk(c)
    {
        assert forall |a:Self, b:Self, c: Self| #[trigger] a.is_sub_disk(b) && #[trigger] b.is_sub_disk(c) implies a.is_sub_disk(c) by {
            assert forall|k: Address| #[trigger] a.entries.dom().contains(k) implies
                #[trigger] c.entries.dom().contains(k) && a.entries[k] == c.entries[k] by {
                assert( b.entries.dom().contains(k) );
//                assert( c.entries.dom().contains(k) );
            }
        }
    }

    pub open spec(checked) fn is_sub_disk_with_newer_lsn(self, bigger: Self) -> bool
    {
        &&& bigger.boundary_lsn <= self.boundary_lsn
        &&& self.entries <= bigger.entries
    }

    pub open spec(checked) fn build_tight(self, root: Pointer) -> (out: Self)
    recommends
        self.decodable(root),
        // TODO want ensures here
    decreases self.the_rank_of(root) when self.decodable(root)
    {
        if !self.acyclic() { Self{boundary_lsn: 0, entries: map![]} } // silly
        else if root is None { Self{boundary_lsn: self.boundary_lsn, entries: map![]} }
        else {
            let addr = root.unwrap();
            let tail = self.build_tight(self.next(root));
            Self{
                boundary_lsn: self.boundary_lsn,
                entries: tail.entries.insert(addr, self.entries[addr]),
            }
        }
    }

    // TODO auto-generate please
    pub proof fn build_tight_ensures(self, root: Pointer)
        // TODO(chris): really want the `let` that scopes around requires, ensures, and body here!
    requires
        self.decodable(root)
    ensures
        forall |addr| #[trigger] self.build_tight(root).entries.contains_key(addr) ==> self.entries.contains_key(addr),
        self.acyclic() ==> self.build_tight(root).is_sub_disk(self),
    decreases
        self.the_rank_of(root),
    {
        if !self.acyclic() { }
        else if root is None { }
        else {
            self.build_tight_ensures(self.next(root));
        }
    }

    pub open spec(checked) fn can_crop(self, root: Pointer, depth: nat) -> bool
    recommends
        self.decodable(root),
        self.block_in_bounds(root),
    decreases depth
    {
        0 < depth ==> {
            &&& root is Some
            &&& self.can_crop(self.next(root), (depth-1) as nat)
        }
    }

    pub open spec(checked) fn pointer_after_crop(self, root: Pointer, depth: nat) -> (out: Pointer)
    recommends
        self.decodable(root),
        self.block_in_bounds(root),
        self.can_crop(root, depth),
    decreases depth
    {
        if depth==0 { root }
        else { self.pointer_after_crop(self.next(root), (depth-1) as nat) }
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
            self.pointer_after_crop_ensures(self.next(root), (depth-1) as nat)
        }
    }

    pub proof fn pointer_after_crop_seq_end(self, root: Pointer, depth: nat)
    requires
        self.decodable(root),
        self.block_in_bounds(root),
        self.can_crop(root, depth),
    ensures
        self.seq_end(self.pointer_after_crop(root, depth)) <= self.seq_end(root)
    decreases depth
    {
        if depth > 0 {
            self.pointer_after_crop_seq_end(self.next(root), (depth-1) as nat)
        }
    }

    //////////////////////////////////////////////////////////////////////////
    // Proof-y stuff, pulled in here because it's required by the invariant
    // proofs which the state machine macro demands we put inline.
    //////////////////////////////////////////////////////////////////////////

    pub open spec(checked) fn iptr(self, ptr: Pointer) -> (out: Option<PagedJournal_v::JournalRecord>)
    recommends
        self.decodable(ptr),
        self.acyclic(),
//     ensures
//         self.block_in_bounds(ptr),
//         out is Some ==> out.unwrap().valid(self.boundary_lsn)
    decreases self.the_rank_of(ptr) when self.decodable(ptr) && self.acyclic()
    {
        if ptr is None { None }
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
        if ptr is Some {
//            assert( big.the_rank_of(self.next(ptr)) < big.the_rank_of(ptr) );
            self.iptr_ignores_extra_blocks(self.next(ptr), big);
        }
    }

    pub open spec /*XXX (checked)*/ fn next(self, ptr: Pointer) -> Pointer
    recommends
        self.wf(),
        ptr is Some,
    {
//         let _ = spec_affirm( self.entries.contains_key(ptr.unwrap()) );
//         let _ = spec_affirm( self.entries.dom().contains(ptr.unwrap()) );
//         XXX These affirms aren't triggering.
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
        ptr is Some,
    ensures ({
        forall |addr: Address| #[trigger] self.build_tight(self.next(ptr)).entries.contains_key(addr) ==> {
            &&& self.the_ranking().contains_key(addr)
            &&& self.the_ranking()[addr] < self.the_ranking()[ptr.unwrap()]
        }
    })
    decreases self.the_rank_of(ptr)
    {
        let next = self.next(ptr);
        if next is Some {
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
        root is Some,
        self.decodable(root),
        self.acyclic(),
    ensures (
        self.build_tight(self.next(root))
        == Self{entries: self.build_tight(root).entries.remove(root.unwrap()), ..self})
    {
        if self.next(root) is Some {
            self.build_tight_ranks(root);   // proves root.value !in self.build_tight(next, ranking).entries;
        }

        assert_maps_equal!(
            self.build_tight(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn)).entries,
            self.build_tight(root).entries.remove(root.unwrap())
            );
    }

    pub open spec(checked) fn is_tight(self, root: Pointer) -> bool
    {
        &&& self.decodable(root)
        &&& self.acyclic()
        &&& forall |other: Self| {
            ({
                &&& other.decodable(root)
                &&& other.acyclic()
                &&& self.iptr(root) == other.iptr(root)
                &&& #[trigger] other.is_sub_disk(self)
            }) ==> other == self
        }
    }

    // #[verifier::spinoff_prover]  // flaky proof
    // pub proof fn build_tight_builds_sub_disks(self, root: Pointer)
    // requires
    //     self.decodable(root),
    //     self.acyclic(),
    // ensures
    //     self.build_tight(root).is_sub_disk(self),
    // decreases self.the_rank_of(root)
    // {
    //     if root is Some {
    //         self.build_tight_builds_sub_disks(self.next(root));
    //     }
    //     assert( self.build_tight(root).is_sub_disk(self) ); // This line shouldn't be necessary
    // }

    // Dafny didn't need this proof
    pub proof fn tight_empty_disk(self)
    requires
        self.decodable(None),
    ensures
        self.build_tight(None).is_tight(None),
    {
        let tight = self.build_tight(None);

        //XXX need a callout to build_tight_is_awesome?
//        assert( tight.wf() );

        assert( tight.valid_ranking(map![]) ); // new witness; not needed in Dafny
        assert forall |other: Self|
        ({
            &&& other.decodable(None)
            &&& other.acyclic()
            &&& tight.iptr(None) == other.iptr(None)
            &&& #[trigger] other.is_sub_disk(tight)
        }) implies other =~= tight by {
            //assert( tight.wf() );   // new trigger when we perturb DiskView::can_crop
            //assert( forall |addr| !tight.entries.dom().contains(addr) );    // added to fight the flake
//            assert( tight.entries.dom() =~~= other.entries.dom() );
//            assert( other.entries =~~= tight.entries );  // flaky
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
        // Yikes. Dafny proof was 15 lines; this "minimized" Verus proof is 73 lines.
        self.build_tight_ensures(root); //new because not auto
        //assert(tight.wf());
        if root is Some {
            let next = self.next(root);
            let inner = self.build_tight(next);
            self.build_tight_shape(root);
            self.tight_sub_disk(next, inner);
            assert( tight.valid_ranking(self.the_ranking()) ); // witness
            assert( tight.is_tight(root) ) by {
                assert forall |other: Self| {
                    &&& other.decodable(root)
                    &&& other.acyclic()
                    &&& tight.iptr(root) == other.iptr(root)
                    &&& #[trigger] other.is_sub_disk(tight)
                } implies other == tight by {
                    // any other tighter disk implies an "other_inner" disk tighter than inner, but inner.IsTight(next).
                    let other_inner = DiskView{ entries: other.entries.remove(root.unwrap()), ..other };

//                    assert( other_inner.entries_wf() );

                    Self::sub_disk_transitive_auto();

                    assert forall |addr| #[trigger] other_inner.entries.contains_key(addr)
                        implies other_inner.is_nondangling_pointer(other_inner.entries[addr].cropped_prior(other_inner.boundary_lsn)) by {
                        let aprior = self.entries[addr].cropped_prior(self.boundary_lsn);
                        assert( self.entries.contains_key(addr) );
//                        assert( self.is_nondangling_pointer(aprior) );
//                        assert( other.wf() );
                        if aprior == root {
                            if tight.entries[addr].cropped_prior(tight.boundary_lsn) == root {
                                assert( tight.entries.contains_key(addr) );  // dayyum
//                                assert( tight.the_ranking()[tight.entries[addr].cropped_prior(tight.boundary_lsn).unwrap()] > tight.the_ranking()[root.unwrap()] ); // from valid_ranking
//                                assert( tight.the_ranking()[tight.entries[addr].cropped_prior(tight.boundary_lsn).unwrap()] < tight.the_ranking()[root.unwrap()] ); // from build_tight_ranks
                            }
//                            assert( tight.entries[addr].cropped_prior(tight.boundary_lsn) != root );
//                            assert( other_inner.is_sub_disk(tight) );
                        }
                        // frustrating, considering this is the just a repitition of the assert-forall-by
                        // conclusion
//                        assert( other_inner.is_nondangling_pointer(aprior) );
                    }
                
//                    assert( other_inner.is_nondangling_pointer(next) );    //new
//                    assert(other_inner.wf());   // wait, we needed this as a trigger?
                    assert(other_inner.is_sub_disk(inner)); // new
                    // we know by here Dafny knowns other_inner.wf()
                    other_inner.iptr_ignores_extra_blocks(next, inner);
                    // every line below here is both new and necessary
//                    assert( inner.is_tight(next) ); // new trigger holy crap how did we not get this
                                                    // calling tight_sub_disk!!!??
//                    assert( forall |a| inner.entries.contains_key(a) ==> #[trigger] other_inner.entries.contains_key(a) && other_inner.entries[a] == inner.entries[a] );
//                    assert( other_inner =~= inner );
//                    assert( other.entries =~= tight.entries );
                    assert( other =~= tight );
                }
//                assert( tight.decodable(root) );
//                assert( tight.acyclic() );  // new trigger
            }
        } else {
            self.tight_empty_disk()
        }
    }

    // pub proof fn tight_interp(big: Self, root: Pointer, tight: Self)
    // requires
    //     big.decodable(root),
    //     tight == big.build_tight(root),
    //     big.acyclic(),
    // ensures
    //     tight.is_sub_disk(big),
    //     tight.is_tight(root),
    //     tight.iptr(root) == big.iptr(root),
    //     tight.acyclic(),
    // decreases big.the_rank_of(root)
    // {
    //     if root is None {
    //         big.tight_empty_disk()
    //     } else {
    //         big.build_tight_builds_sub_disks(root);
    //         big.tight_sub_disk(root, tight);
    //         // Dafny could trigger just on valid_ranking, but we seem to need to poke at
    //         // contains_key. How many of these problems would go away with an axiom tying
    //         // dom.contains to contains_key?
    //         assert( forall |addr| tight.entries.contains_key(addr) ==> big.entries.contains_key(addr) );
    //         tight.iptr_ignores_extra_blocks(root, big);
    //     }
    // }

    pub open spec fn lsn_has_entry_at(self, lsn: LSN, addr: Address) -> bool {
        &&& self.entries.contains_key(addr)
        &&& self.entries[addr].message_seq.contains(lsn)
    }

    pub open spec fn lsn_has_entry(self, lsn: LSN) -> bool {
        exists |addr| self.lsn_has_entry_at(lsn, addr)
    }

    pub open spec fn lsns_have_entries(self, root: Pointer) -> bool {
        forall |lsn| self.boundary_lsn <= lsn < self.seq_end(root) ==> self.lsn_has_entry(lsn)
    }

    pub proof fn decodable_implies_lsns_have_entries(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
    ensures
        self.lsns_have_entries(root),
    decreases self.the_rank_of(root)
    {
        if root is Some {
            self.decodable_implies_lsns_have_entries(self.next(root));
            assert forall |lsn| self.seq_start() <= lsn < self.seq_end(root) implies self.lsn_has_entry(lsn) by {
                if self.entries[root.unwrap()].message_seq.seq_start <= lsn {
                    assert( self.lsn_has_entry_at(lsn, root.unwrap()) );
                }
            }
        }
    }
}

#[verifier::ext_equal]
pub struct TruncatedJournal {
    pub freshest_rec: Pointer, // root address of journal
    pub disk_view: DiskView,
}

impl TruncatedJournal {
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.disk_view.wf()
        &&& self.disk_view.is_nondangling_pointer(self.freshest_rec)
        &&& self.disk_view.block_in_bounds(self.freshest_rec)
    }

    pub open spec(checked) fn seq_start(self) -> LSN {
        self.disk_view.seq_start()
    }

    pub open spec(checked) fn seq_end(self) -> LSN
    recommends
        self.disk_view.is_nondangling_pointer(self.freshest_rec),   // why not just wf()?
    {
        self.disk_view.seq_end(self.freshest_rec)
    }

    pub open spec(checked) fn can_discard_to(self, lsn: LSN) -> bool
    recommends
        self.wf(),
    {
        self.seq_start() <= lsn <= self.seq_end()
    }

    pub open spec(checked) fn discard_old(self, lsn: LSN) -> Self
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

    pub open spec/*(checked)*/ fn valid_discard_old(self, lsn: LSN, new: Self) -> bool
    recommends
        self.wf(),
        self.can_discard_to(lsn)
    {
        let post_discard = self.discard_old(lsn);
        let post_tight = post_discard.build_tight();

        &&& new.wf()
        &&& new.freshest_rec == post_discard.freshest_rec
        &&& new.disk_view.is_sub_disk(post_discard.disk_view) // new must be a subset of original
        &&& post_tight.disk_view.is_sub_disk(new.disk_view)   // tight must be fully contained by new
    }

    pub open spec(checked) fn decodable(self) -> bool
    {
        &&& self.wf()
        &&& self.disk_view.acyclic()
    }

    pub open spec(checked) fn can_crop(self, depth: nat) -> bool
    {
        &&& self.decodable()
        &&& self.disk_view.can_crop(self.freshest_rec, depth)
    }

    pub open spec(checked) fn crop(self, depth: nat) -> Self
    recommends
        self.can_crop(depth),
    {
        let ptr = self.disk_view.pointer_after_crop(self.freshest_rec, depth);
        TruncatedJournal{ freshest_rec: ptr, ..self }
    }

    pub proof fn crop_ensures(self, depth: nat)
    requires self.can_crop(depth),
    ensures self.crop(depth).wf(),
    {
        self.disk_view.pointer_after_crop_ensures(self.freshest_rec, depth);
    }

    pub open spec(checked) fn append_record(self, addr: Address, msgs: MsgHistory) -> (out: Self)
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

    pub open spec(checked) fn build_tight(self) -> (out: Self)
    recommends
        self.disk_view.decodable(self.freshest_rec),
    {
        TruncatedJournal{
            disk_view: self.disk_view.build_tight(self.freshest_rec),
            ..self
        }
    }

    pub open spec(checked) fn mkfs() -> (out: Self)
    {
        Self{
            freshest_rec: None,
            disk_view: DiskView { boundary_lsn: 0, entries: map![] },
        }
    }

    pub proof fn mkfs_ensures()
    ensures
        Self::mkfs().decodable(),
    {
        assert( Self::mkfs().disk_view.valid_ranking(map![]) );
    }

    pub open spec fn lsns_have_entries(self) -> bool {
        self.disk_view.lsns_have_entries(self.freshest_rec)
    }

    pub proof fn decodable_implies_lsns_have_entries(self)
    requires
        self.decodable(),
    ensures
        self.lsns_have_entries(),
    {
        self.disk_view.decodable_implies_lsns_have_entries(self.freshest_rec);
    }

    // An acyclic()-satisyfing ranking when one adds a single addr to self.
    // TODO(chris): Rather than open, how about spec ensures?
    // TODO(chris): When (checked), I get a recommendation-not-met here, even though a
    // corresponding proof fn completes without further triggering (see below).
    pub open spec/*(checked)*/ fn marshal_ranking(self, addr: Address) -> Ranking
    recommends
        self.decodable(),
    {
        let pre_rank = self.disk_view.the_ranking();
        pre_rank.insert(addr,
                            if self.freshest_rec is None { 0 }
                            else {pre_rank[self.freshest_rec.unwrap()] + 1 })
    }

//     pub proof fn no_trigger_needed(self, addr: Address)
//     requires
//         self.decodable(),
//     {
//         let pre_rank = self.disk_view.the_ranking();
//         if self.freshest_rec is Some {
//             assert( pre_rank.contains_key(self.freshest_rec.unwrap()) );
//         }
//     }
}

impl MsgHistory {
    pub open spec fn bounded_discard(self, new_bdy: LSN) -> Self
    {
        if self.seq_start <= new_bdy { 
            self.discard_old(new_bdy) 
        } else { 
            self
        }
    }
}

state_machine!{ LinkedJournal {
    fields {
        pub truncated_journal: TruncatedJournal,
        pub unmarshalled_tail: MsgHistory,
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.truncated_journal.wf()
        &&& self.unmarshalled_tail.wf()
        &&& self.truncated_journal.seq_start() <= self.truncated_journal.seq_end()
        // TODO(jonh): can probably delete this conjunct, since it's proven by interp
        &&& self.truncated_journal.seq_end() == self.unmarshalled_tail.seq_start
    }

    pub open spec(checked) fn seq_start(self) -> LSN
    {
        self.truncated_journal.seq_start()
    }

    pub open spec(checked) fn seq_end(self) -> LSN
    recommends
        self.wf(),
    {
        self.unmarshalled_tail.seq_end
    }
    
    pub open spec(checked) fn unused_addr(self, addr: Address) -> bool
    {
        // TODO reaching into truncatedJournal to find the diskView feels skeezy
        !self.truncated_journal.disk_view.entries.contains_key(addr)
    }

    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: TruncatedJournal},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        Internal{},   // Local No-op label
    }

    pub open spec(checked) fn lbl_wf(lbl: Label) -> bool
    {
        match lbl {
            Label::ReadForRecovery{messages} => messages.wf(),
            Label::FreezeForCommit{frozen_journal} => frozen_journal.decodable(),
            _ => true,
        }
    }

    transition!{ read_for_recovery(lbl: Label, depth: nat) {
        require pre.wf();
        require lbl is ReadForRecovery;
        require Self::lbl_wf(lbl);
        require pre.truncated_journal.decodable(); // Shown by invariant, not runtime-checked
        let dv = pre.truncated_journal.disk_view;
        require dv.can_crop(pre.truncated_journal.freshest_rec, depth);
        let ptr = dv.pointer_after_crop(pre.truncated_journal.freshest_rec, depth);
        require ptr is Some;
        require dv.entries[ptr.unwrap()].message_seq.maybe_discard_old(dv.boundary_lsn) == lbl.arrow_ReadForRecovery_messages();
    }}

    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl is FreezeForCommit;
        require pre.truncated_journal.decodable(); // Shown by invariant, not runtime-checked

        let dv = pre.truncated_journal.disk_view;
        require dv.can_crop(pre.truncated_journal.freshest_rec, depth);

        let cropped_tj = pre.truncated_journal.crop(depth);
        let label_fj = lbl->frozen_journal;
        let new_bdy = label_fj.seq_start();
        require dv.boundary_lsn <= new_bdy;

        require cropped_tj.can_discard_to(new_bdy);
        require cropped_tj.valid_discard_old(new_bdy, label_fj);
        // require label_fj == cropped_tj.discard_old(new_bdy);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl is QueryEndLsn;
        require lbl->end_lsn == pre.seq_end();
    }}

    transition!{ put(lbl: Label) {
        require pre.wf();
        //require Self::lbl_wf(lbl);
        require lbl.arrow_Put_messages().wf();    // direct translation. TODO fold into lbl_wf
        require lbl is Put;
        require lbl.arrow_Put_messages().seq_start == pre.seq_end();
        update unmarshalled_tail = pre.unmarshalled_tail.concat(lbl.arrow_Put_messages());
    }}

    transition!{ discard_old(lbl: Label, new_tj: TruncatedJournal) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl is DiscardOld;

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;

        require require_end == pre.seq_end();
        require pre.truncated_journal.can_discard_to(start_lsn);

        // leaving the amount of garbage collection to new_tj.disk_view
        // as long as all reachable pages are still in scope
        require pre.truncated_journal.valid_discard_old(start_lsn, new_tj);

        update truncated_journal = new_tj;
        update unmarshalled_tail = pre.unmarshalled_tail.bounded_discard(start_lsn);
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
        require lbl is Internal;
        require pre.unmarshalled_tail.seq_start < cut; // Can't marshall nothing.
        require pre.unmarshalled_tail.can_discard_to(cut);
        let marshalled_msgs = pre.unmarshalled_tail.discard_recent(cut);

        update truncated_journal = pre.truncated_journal.append_record(addr, marshalled_msgs);
        update unmarshalled_tail = pre.unmarshalled_tail.discard_old(cut);
    }}

    transition!{ internal_no_op(lbl: Label) {
        require pre.wf();
        require lbl is Internal;
    }}

    init!{ initialize(truncated_journal: TruncatedJournal) {
        require truncated_journal.decodable();  // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
        init truncated_journal = truncated_journal;
        init unmarshalled_tail = MsgHistory::empty_history_at(truncated_journal.seq_end());
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.truncated_journal.decodable()
        // &&& self.truncated_journal.disk_view.acyclic() // covered by tj.decodable
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(discard_old)]
    pub fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_tj: TruncatedJournal) {
        let lsn = lbl->start_lsn;
        let post_discard = pre.truncated_journal.discard_old(lsn);

        pre.truncated_journal.discard_old_decodable(lsn);
        new_tj.disk_view.sub_disk_ranking(post_discard.disk_view); // lemma that triggers
    }

    #[inductive(internal_journal_marshal)]
    pub fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address) {
        assert( post.truncated_journal.disk_view.valid_ranking(pre.truncated_journal.marshal_ranking(addr)) );    // witness
    }

    #[inductive(internal_no_op)]
    fn internal_no_op_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, truncated_journal: TruncatedJournal) { }

} } // state_machine!

} // verus!
