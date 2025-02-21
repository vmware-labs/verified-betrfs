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

use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::TruncatedJournal;
use crate::journal::LinkedJournal_v::DiskView;
use crate::disk::GenericDisk_v::*;
use crate::allocation_layer::Likes_v::*;
use crate::allocation_layer::Likes_v::*;

verus!{

impl TruncatedJournal {
}

//////////////////////////////////////////////////////////////////////////////
type LsnAddrIndex = Map<LSN, Address>;

pub open spec(checked) fn lsn_disjoint(lsn_index: Set<LSN>, msgs: MsgHistory) -> bool
{
    forall |lsn| msgs.seq_start <= lsn < msgs.seq_end
        ==> !lsn_index.contains(lsn)
}

pub open spec fn lsn_addr_index_discard_up_to(lsn_addr_index: LsnAddrIndex, bdy: LSN) -> (out: LsnAddrIndex)
{
    Map::new(
        |k| lsn_addr_index.contains_key(k) && bdy <= k,
        |k| lsn_addr_index[k])
}

pub proof fn lsn_addr_index_discard_up_to_ensures(lsn_addr_index: LsnAddrIndex, bdy: LSN)
ensures ({
    let out = lsn_addr_index_discard_up_to(lsn_addr_index, bdy);
    &&& out <= lsn_addr_index
    &&& forall |k| out.contains_key(k) ==> bdy <= k
    &&& forall |k| lsn_addr_index.contains_key(k) && bdy <= k ==> out.contains_key(k)
})
{
}

pub open spec(checked) fn singleton_index(start: LSN, end: LSN, value: Address) -> LsnAddrIndex
{
    Map::new(|x: LSN| start <= x < end, |x:LSN| value)
}

pub open spec(checked) fn lsn_addr_index_append_record(lsn_addr_index: LsnAddrIndex, msgs: MsgHistory, addr: Address) -> LsnAddrIndex
recommends
    msgs.wf(),
    msgs.seq_start < msgs.seq_end,  // non-empty
{
    let update = singleton_index(msgs.seq_start, msgs.seq_end, addr);
    lsn_addr_index.union_prefer_right(update)
}

pub proof fn lsn_addr_index_append_record_ensures(lsn_addr_index: LsnAddrIndex, msgs: MsgHistory, addr: Address)
requires
    msgs.wf(),
    msgs.seq_start < msgs.seq_end,  // non-empty
ensures
    lsn_disjoint(lsn_addr_index.dom(), msgs) ==>
        lsn_addr_index_append_record(lsn_addr_index, msgs, addr).values()
        == lsn_addr_index.values() + set![addr],
{
    let out = lsn_addr_index_append_record(lsn_addr_index, msgs, addr);
    // TODO(chris): Dafny needed only one line of proof for this mess; does our stdlib need some
    // better triggers? I wonder if it's down to contains-vs-contains_key
    if lsn_disjoint(lsn_addr_index.dom(), msgs) {
        let sum = lsn_addr_index.values() + set![addr];
        // TODO(chris): #[auto] doesn't work in the assert-forall context?
        assert forall |a| #[trigger] sum.contains(a) implies out.values().contains(a) by {
            // Go find witnesses.
            if lsn_addr_index.values().contains(a) {
                let lsn = choose |lsn| #![auto] lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn] == a;
                assert( out.contains_key(lsn) );
            } else {
                assert( out.contains_key(msgs.seq_start) );
            }
        };
        assert( out.values() =~= lsn_addr_index.values() + set![addr] );
    }
}

//////////////////////////////////////////////////////////////////////////////

impl DiskView {
    pub open spec(checked) fn buildable(self, root: Pointer) -> bool
    {
        &&& self.decodable(root)
        &&& self.acyclic()
        &&& root is Some ==> self.boundary_lsn < self.entries[root.unwrap()].message_seq.seq_end
    }

    pub open spec(checked) fn build_lsn_addr_index(self, root: Pointer) -> LsnAddrIndex
    recommends
        self.buildable(root),
    decreases self.the_rank_of(root) when self.decodable(root) && self.acyclic()
    {
        if root is None {
            map!{}
        } else {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            //let start_lsn = if self.boundary_lsn > curr_msgs.seq_start { self.boundary_lsn } else { curr_msgs.seq_start };
            let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());

            // Put the update on the "preferred" side to make recursive proof reasoning easier:
            // there should be no conflicts between update and inner call, but this way we don't
            // even have to make that argument because update values dominate.
            self.build_lsn_addr_index(self.next(root)).union_prefer_right(update)
        }
    }
} // end of impl DiskView

// invariant proof stuff that moved here from the Refinement file
impl DiskView {
    pub open spec(checked) fn addr_supports_lsn(self, addr: Address, lsn: LSN) -> bool
    {
        &&& self.entries.contains_key(addr)
        &&& self.entries[addr].contains_lsn(self.boundary_lsn, lsn)
    }

    #[verifier::spinoff_prover]
    pub proof fn cropped_ptr_build_sub_index(self, root: Pointer, cropped: Pointer, depth: nat)
        requires
            self.buildable(root),
            self.buildable(cropped),
            self.can_crop(root, depth),
            cropped == self.pointer_after_crop(root, depth),
        ensures
            self.build_lsn_addr_index(cropped) <= self.build_lsn_addr_index(root),
        decreases self.the_rank_of(root),
    {
        reveal(TruncatedJournal::index_domain_valid);

        let cropped_index = self.build_lsn_addr_index(cropped);
        let index = self.build_lsn_addr_index(root);

        if depth > 0 {
            self.build_lsn_addr_index_domain_valid(root);
            self.cropped_ptr_build_sub_index(self.next(root), cropped, (depth-1) as nat);
//            assert(self.build_lsn_addr_index(cropped) <= self.build_lsn_addr_index(self.next(root)));

            if self.next(root) is Some {
                self.build_lsn_addr_index_domain_valid(self.next(root));
            }

            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
    
            assert(update.dom().disjoint(self.build_lsn_addr_index(self.next(root)).dom()));
//            assert(self.build_lsn_addr_index(self.next(root)) <= self.build_lsn_addr_index(root));
        }
    }

    spec(checked) fn cropped_msg_seq_contains_lsn(
        boundary: LSN,
        message_seq: MsgHistory,
        lsn: LSN,
    ) -> bool {
        max(boundary as int, message_seq.seq_start as int) <= lsn < message_seq.seq_end
    }

    pub open spec(checked) fn tj_at(self, root: Pointer) -> TruncatedJournal
    {
        TruncatedJournal{freshest_rec: root, disk_view: self}
    }

    pub proof fn build_lsn_addr_index_domain_valid(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
        root is Some, // otherwise BuildLsnAddrIndex is trivially empty
        self.boundary_lsn < self.entries[root.unwrap()].message_seq.seq_end,
    ensures
        self.tj_at(root).index_domain_valid(self.build_lsn_addr_index(root)),
        self.index_keys_map_to_valid_entries(self.build_lsn_addr_index(root)),
    decreases self.the_rank_of(root)
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        if self.next(root) is None {
            // TODO(chris) These lets are trigger something... not sure why, since we have the same
            // defn (build_lsn_addr_index) available in scope. ?
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
            let output = self.build_lsn_addr_index(self.next(root)).union_prefer_right(update);
        } else {
            self.build_lsn_addr_index_domain_valid(self.next(root));
        }
    }

    pub proof fn build_lsn_addr_index_range_valid(self, root: Pointer)
    requires
        self.buildable(root),
        self.tj_at(root).index_domain_valid(self.build_lsn_addr_index(root)),
        self.index_keys_map_to_valid_entries(self.build_lsn_addr_index(root)),
    ensures
        self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)),
    decreases
        self.the_rank_of(root)
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);

        if root is None {
//            assert( self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)) );
        } else if self.next(root) is None {
            // let curr_msgs = self.entries[root.unwrap()].message_seq;
            // let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            // let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
            // let output = self.build_lsn_addr_index(self.next(root)).union_prefer_right(update);
//            assert( self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)) );
        } else {
            self.build_lsn_addr_index_domain_valid(self.next(root));
            self.build_lsn_addr_index_range_valid(self.next(root));

            let tj = self.tj_at(root);
            let sub_index = self.build_lsn_addr_index(self.next(root));
            let index = self.build_lsn_addr_index(root);

            assert forall |addr| index.values().contains(addr)
            implies tj.every_lsn_at_addr_indexed_to_addr(index, addr)
            by {
                if addr != root.unwrap() {
                    assert(sub_index.values().contains(addr));
                }
            }
//            assert( self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)) );
        }
    }

    // oh nice, this really shows the representation is just a duplicate of build_tight
    // replacing all reference of representation to build_tight 
    pub proof fn build_tight_domain_is_build_lsn_addr_index_range(self, root: Pointer) 
    requires
        self.buildable(root),
    ensures
        // This conclusion is used inside the recursion
        root is Some ==>
            forall |lsn| self.build_lsn_addr_index(root).contains_key(lsn) ==>
                self.boundary_lsn <= lsn < self.entries[root.unwrap()].message_seq.seq_end,
        // This conclusion is the one we're trying to actually export
        self.build_lsn_addr_index(root).values() =~= self.build_tight(root).entries.dom(),
        // TODO(chris): I find it kind of disturbing that the ~ between the == in the line above
        // is a functional part of the proof strategy. --jonh
    decreases self.the_rank_of(root)
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);

        if root is Some {
            self.build_tight_domain_is_build_lsn_addr_index_range(self.next(root));
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let begin = max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = singleton_index(begin, curr_msgs.seq_end, root.unwrap());
            assert(update.contains_key(begin));
//            assert forall |k| #![auto] self.build_lsn_addr_index(root).values().contains(k) 
//            implies self.build_tight(root).entries.dom().contains(k) by {
//            }
            self.build_tight_ensures(root);
            assert forall |addr| #![auto]
                self.build_tight(root).entries.dom().contains(addr) implies
                self.build_lsn_addr_index(root).values().contains(addr) by {

                let left_index = self.build_lsn_addr_index(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn));
                if update.values().contains(addr) {
                    assert( self.build_lsn_addr_index(root).contains_key(begin) );   // witness
//                     assert( self.build_lsn_addr_index(root).values().contains(addr) );
                } else {
                    let lsn = choose |lsn| #![auto] left_index.contains_key(lsn) && left_index[lsn]==addr;
                    assert( self.build_lsn_addr_index(root).contains_key(lsn) );    // witness
//                     assert( self.build_lsn_addr_index(root).values().contains(addr) );
                }
            }
        }
    }

    pub proof fn sub_disk_with_newer_lsn_repr_index(self, big: DiskView, ptr: Pointer)
    requires 
        self.decodable(ptr),
        self.acyclic(),
        big.decodable(ptr),
        big.acyclic(),
        ptr is Some ==> self.boundary_lsn < self.entries[ptr.unwrap()].message_seq.seq_end,
        ptr is Some ==> big.boundary_lsn < big.entries[ptr.unwrap()].message_seq.seq_end,
        self.is_sub_disk_with_newer_lsn(big)
    ensures 
        self.build_lsn_addr_index(ptr) <= big.build_lsn_addr_index(ptr)
    decreases 
        self.the_rank_of(ptr)
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);

        if ptr is Some {
            self.sub_disk_with_newer_lsn_repr_index(big, self.next(ptr));
            if self.next(ptr) is Some {
                self.build_lsn_addr_index_domain_valid(self.next(ptr));
            }
            if big.next(ptr) is Some {
                big.build_lsn_addr_index_domain_valid(big.next(ptr));
            }
        }
    }

    pub proof fn sub_disk_repr_index(self, big: Self, ptr: Pointer)
    requires
        self.wf(),
        big.wf(),
        big.acyclic(),
        self.is_sub_disk(big),
        self.is_nondangling_pointer(ptr),
        ptr is Some ==> self.boundary_lsn < self.entries[ptr.unwrap()].message_seq.seq_end,
    ensures
        self.build_lsn_addr_index(ptr) == big.build_lsn_addr_index(ptr),
    decreases if ptr is Some { big.the_ranking()[ptr.unwrap()]+1 } else { 0 }
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);

        assert( forall |addr| #[trigger] self.entries.contains_key(addr) ==> big.entries.dom().contains(addr) );    // new clunikness related to contains-vs-contains_key
        assert( self.valid_ranking(big.the_ranking()) );
        if ptr is Some {
            //let jr = big.entries[ptr.unwrap()];
            //self.sub_disk_repr_index(big, jr.cropped_prior(big.boundary_lsn));
            if big.next(ptr) is Some {
//                assert( big.entries.contains_key(ptr.unwrap()) );
//                assert( big.the_ranking()[big.next(ptr).unwrap()] < big.the_ranking()[ptr.unwrap()] );
            }
            self.sub_disk_repr_index(big, big.next(ptr));
        }
    }

    pub proof fn build_lsn_addr_all_decodable(self, root: Pointer)
    requires
        self.buildable(root),
    ensures
        forall |lsn| #![auto] self.build_lsn_addr_index(root).contains_key(lsn) ==> self.decodable(Some(self.build_lsn_addr_index(root)[lsn])),
    decreases self.the_rank_of(root)
    {
        let lsn_addr_index = self.build_lsn_addr_index(root);   // I want that super-let!
        if root is None {
        } else {
            self.build_lsn_addr_all_decodable(self.next(root));
            assert forall |lsn| #![auto] lsn_addr_index.contains_key(lsn)
            implies self.decodable(Some(lsn_addr_index[lsn])) by {
                if self.build_lsn_addr_index(self.next(root)).contains_key(lsn) {
//                    assert( self.decodable(Some(lsn_addr_index[lsn])) );
                } else {
//                    assert( lsn_addr_index[lsn] == root.unwrap() );
//                    assert( self.decodable(Some(lsn_addr_index[lsn])) );
                }
            }
        }
    }

    pub proof fn build_lsn_addr_honors_rank(self, root: Pointer, lsn_addr_index: Map<LSN, Address>)
    requires
        self.buildable(root),
        lsn_addr_index == self.build_lsn_addr_index(root),  // wish this were a super-let!
    ensures
        forall |lsn1, lsn2| #![auto] ({
            &&& lsn_addr_index.contains_key(lsn1)
            &&& lsn_addr_index.contains_key(lsn2)
            &&& lsn1 <= lsn2
        }) ==> self.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.the_rank_of(Some(lsn_addr_index[lsn2]))
    decreases self.the_rank_of(root)
    {
        self.build_lsn_addr_all_decodable(root);
        if root is None {
        } else if self.next(root) is None {
//             assert( self.build_lsn_addr_index(self.next(root)) == Map::<LSN, Address>::empty() );
        } else {
            self.build_lsn_addr_index_domain_valid(root);
            self.build_lsn_addr_index_domain_valid(self.next(root));
            let prior_index = self.build_lsn_addr_index(self.next(root));
            self.build_lsn_addr_honors_rank(self.next(root), prior_index);
            assert forall |lsn1, lsn2| #![auto] ({
                &&& lsn_addr_index.contains_key(lsn1)
                &&& lsn_addr_index.contains_key(lsn2)
                &&& lsn1 <= lsn2
            }) implies ({
                &&& self.decodable(Some(lsn_addr_index[lsn1]))
                &&& self.decodable(Some(lsn_addr_index[lsn2]))
                &&& self.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.the_rank_of(Some(lsn_addr_index[lsn2]))
            }) by {
                let corner = self.entries[self.next(root).unwrap()].message_seq.seq_end;
                let before = (corner - 1) as nat;
                if lsn1 < corner {
                    assert( prior_index.contains_key(before) ) by {
                        reveal(TruncatedJournal::index_domain_valid);
                    }
//                     assert( lsn1 <= corner );
//                     assert( self.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.the_rank_of(Some(lsn_addr_index[before])) );
//                     assert( self.the_rank_of(Some(lsn_addr_index[corner])) <= self.the_rank_of(Some(lsn_addr_index[corner])) );
                } else {
                    assert( !prior_index.contains_key(lsn1) && !prior_index.contains_key(lsn2) ) by {
                        reveal(TruncatedJournal::index_domain_valid);
                    }
                }
            }
        }
    }

    pub open spec fn index_reflects_disk_view(self, lsn_addr_index: LsnAddrIndex) -> bool
    {
        forall |lsn| #[trigger] lsn_addr_index.contains_key(lsn) ==> {
            &&& self.entries.contains_key(lsn_addr_index[lsn])
            &&& self.entries[lsn_addr_index[lsn]].message_seq.contains(lsn)
        }
    }

    // another thing to tuck into build_lsn_addr_index ensures
    pub proof fn build_lsn_addr_index_reflects_disk_view(self, root: Pointer)
    requires
        self.buildable(root),
    ensures
        self.index_reflects_disk_view(self.build_lsn_addr_index(root)),
    decreases self.the_rank_of(root)
    {
        if root is Some {
            self.build_lsn_addr_index_reflects_disk_view(self.next(root))
        }
    }

    #[verifier(opaque)]
    pub closed spec(checked) fn index_keys_map_to_valid_entries(self, lsn_addr_index: LsnAddrIndex) -> bool
    recommends
        self.wf(),
    {
        forall |lsn| #![auto] lsn_addr_index.contains_key(lsn)
            ==> self.addr_supports_lsn(lsn_addr_index[lsn], lsn)
    }

    // one-off explicit instantiation lemma for use in predicates where reveal is verboten.
    pub proof fn instantiate_index_keys_map_to_valid_entries(self, lsn_addr_index: LsnAddrIndex, lsn: LSN)
    requires
        self.wf(),
        lsn_addr_index.contains_key(lsn),
        self.index_keys_map_to_valid_entries(lsn_addr_index),
    ensures
        self.entries.contains_key(lsn_addr_index[lsn]),
        self.entries[lsn_addr_index[lsn]].contains_lsn(self.boundary_lsn, lsn),
    {
        reveal(DiskView::index_keys_map_to_valid_entries);
    }

} // DiskView proof bits

pub open spec(checked) fn map_to_likes(lsn_addr_map: LsnAddrIndex) -> Likes
decreases lsn_addr_map.dom().len() when lsn_addr_map.dom().finite()
{
    if lsn_addr_map.dom().len() == 0 {
        no_likes()
    } else {
        let k = lsn_addr_map.dom().choose();
        let sub_likes = map_to_likes(lsn_addr_map.remove(k));

        set![lsn_addr_map[k]].to_multiset().add(sub_likes)
    }
}

impl TruncatedJournal {
    pub open spec(checked) fn build_lsn_addr_index(self) ->  LsnAddrIndex
    recommends self.decodable()
    {
        self.disk_view.build_lsn_addr_index(self.freshest_rec)
    }

    pub proof fn build_lsn_addr_index_ensures(self)
    requires self.decodable()
    ensures 
        self.index_domain_valid(self.build_lsn_addr_index()),
        self.disk_view.index_keys_map_to_valid_entries(self.build_lsn_addr_index()),
        self.index_range_valid(self.build_lsn_addr_index())
    {        
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        if self.freshest_rec is Some {
            self.disk_view.build_lsn_addr_index_domain_valid(self.freshest_rec);
            self.disk_view.build_lsn_addr_index_range_valid(self.freshest_rec);
        }
    }

    pub open spec(checked) fn discard_old_cond(self, start_lsn: LSN, keep_addrs: Set<Address>, new: Self) -> bool
    recommends self.wf()
    {
        // new disk_view must be a subdisk contain all kept addrs 
        &&& new.wf()
        &&& new.disk_view.boundary_lsn == start_lsn
        &&& new.disk_view.entries <= self.disk_view.entries
        &&& forall |addr| #[trigger] keep_addrs.contains(addr) ==> new.disk_view.entries.dom().contains(addr)
        &&& new.freshest_rec == if self.seq_end() == start_lsn { None } else { self.freshest_rec }
    }

    pub proof fn discard_old_preserves_acyclicity(self, start_lsn: LSN, keep_addrs: Set<Address>, new: Self)
    requires
        self.wf(),
        self.disk_view.acyclic(),
        self.can_discard_to(start_lsn),
        self.discard_old_cond(start_lsn, keep_addrs, new)
    ensures 
        new.disk_view.acyclic()
    {
        let dv = self.disk_view;
        let post_dv = new.disk_view;
        let ranking = dv.the_ranking();
   
        assert forall |addr| #[trigger] post_dv.entries.contains_key(addr) && post_dv.entries[addr].cropped_prior(post_dv.boundary_lsn) is Some
        implies ranking[post_dv.entries[addr].cropped_prior(post_dv.boundary_lsn).unwrap()] < ranking[addr]
        by {
            assert(dv.entries.contains_key(addr)); // trigger
        }
        assert(post_dv.valid_ranking(ranking)); // witness
    }
}

impl MsgHistory {
    pub open spec(checked) fn tight_discard_old(self, new: Self, new_bdy: LSN) -> bool
    recommends
        self.wf(),
        new.wf(),
        self.can_discard_to(new_bdy),
    {
        let msgs = if self.seq_start <= new_bdy { self.discard_old(new_bdy) } else { self };
        &&& new.ext_equal(msgs)
    }
}

// TODO(jonh): move to pervasive
spec(checked) fn max(a: int, b: int) -> int
{
    if a < b { b } else { a }
}

// Definitions that used to live in the Refinement file, but jonh pulled in here so the invariant
// could be handled using the state_machines invariant machinery.
impl TruncatedJournal {
    // TODO(jonh): HOW THE HECK IS THIS OKAY?
    // Why doesn't truncating the first record violate this for lsns between message_seq.start and
    // boundary!?
    // ...oh, the relevant inv proof isn't completed. Hah. It's not okay.
    // pub open spec(checked) fn valid_entries_appear_in_index(self, lsn_addr_index: LsnAddrIndex) -> bool
    // recommends
    //     self.wf(),
    // {
    //     forall |addr, lsn| self.disk_view.addr_supports_lsn(addr, lsn)
    //          ==> lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn]==addr
    // }

    #[verifier(opaque)]
    pub open spec(checked) fn index_domain_valid(self, lsn_addr_index: LsnAddrIndex) -> bool
    recommends
        self.wf(),
    {
        // lsnAddrIndex's domain is exactly the set of LSN between journal.SeqStart() and journal.SeqEnd()
        &&& forall |lsn| lsn_addr_index.contains_key(lsn) <==> (self.seq_start() <= lsn < self.seq_end())
    }

    pub closed spec /*XXX (checked)*/ fn every_lsn_at_addr_indexed_to_addr(self, lsn_addr_index: LsnAddrIndex, addr: Address) -> bool
    {
        let msgs = self.disk_view.entries[addr].message_seq;
        let boundary_lsn = self.disk_view.boundary_lsn;
        forall |lsn| #[trigger] DiskView::cropped_msg_seq_contains_lsn(boundary_lsn, msgs, lsn) ==> {
            &&& lsn_addr_index.contains_key(lsn)
            &&& lsn_addr_index[lsn] == addr
        }
    }

    pub closed spec /*XXX (checked)*/ fn index_range_valid(self, lsn_addr_index: LsnAddrIndex) -> bool
    recommends
        self.wf(),
        self.index_domain_valid(lsn_addr_index),
        self.disk_view.index_keys_map_to_valid_entries(lsn_addr_index),
    {
        forall |addr| lsn_addr_index.values().contains(addr) ==> {
            self.every_lsn_at_addr_indexed_to_addr(lsn_addr_index, addr)
        }
    }

    pub proof fn build_lsn_addr_honors_rank(self, lsn_addr_index: Map<LSN, Address>)
    requires
        self.decodable(),
        lsn_addr_index == self.build_lsn_addr_index(),
    ensures
        forall |lsn1, lsn2| #![auto] ({
            &&& lsn_addr_index.contains_key(lsn1)
            &&& lsn_addr_index.contains_key(lsn2)
            &&& lsn1 <= lsn2
        }) ==> self.disk_view.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.disk_view.the_rank_of(Some(lsn_addr_index[lsn2]))
    {
        self.disk_view.build_lsn_addr_honors_rank(self.freshest_rec, lsn_addr_index)
    }    
}

state_machine!{ LikesJournal {
    fields {
        pub journal: LinkedJournal_v::LinkedJournal::State,
        pub lsn_addr_index: LsnAddrIndex,
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

    // TODO want to add an impl on Label, but ... state machine macro
    // There's nothing to interpret here; it's the same label as the layer
    // above. There's a lot of useless boilerplate in this layer; perhaps
    // there's a prettier way to decorate an existing state machine with
    // extra ghost state.
    pub open spec fn lbl_i(lbl: Label) -> LinkedJournal_v::LinkedJournal::Label {
        match lbl {
            Label::ReadForRecovery{messages}
                => LinkedJournal_v::LinkedJournal::Label::ReadForRecovery{messages},
            Label::FreezeForCommit{frozen_journal}
                => LinkedJournal_v::LinkedJournal::Label::FreezeForCommit{frozen_journal},
            Label::QueryEndLsn{end_lsn}
                => LinkedJournal_v::LinkedJournal::Label::QueryEndLsn{end_lsn},
            Label::Put{messages}
                => LinkedJournal_v::LinkedJournal::Label::Put{messages},
            Label::DiscardOld{start_lsn, require_end}
                => LinkedJournal_v::LinkedJournal::Label::DiscardOld{start_lsn, require_end},
            Label::Internal{}
                => LinkedJournal_v::LinkedJournal::Label::Internal{},
        }
    }
    
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.journal.wf()
        // TODO this conjunct ought to be part of journal.wf, at least.
        // &&& self.journal.truncated_journal.seq_start() <= self.journal.truncated_journal.seq_end()
    }

    pub open spec fn transitive_likes(self) -> Likes 
    {
        let tj = self.journal.truncated_journal;
        if !tj.decodable() { arbitrary() }
        else { map_to_likes(tj.build_lsn_addr_index()) }
    }

    pub open spec fn imperative_likes(self) -> Likes
    {
        map_to_likes(self.lsn_addr_index)
    }

    transition!{ read_for_recovery(lbl: Label) {
        require lbl is ReadForRecovery;
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }

    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require lbl is FreezeForCommit;

        let fj = lbl->frozen_journal;
        let tj = pre.journal.truncated_journal;
        let new_bdy = fj.seq_start();

        require fj.decodable();
        require tj.disk_view.can_crop(tj.freshest_rec, depth);
        require tj.disk_view.boundary_lsn <= new_bdy;

        let cropped_tj = tj.crop(depth);
        require cropped_tj.can_discard_to(new_bdy);

        // figure out the frozen lsn range
        let post_discard = cropped_tj.discard_old(new_bdy);
        let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < post_discard.seq_end());
        let frozen_index = pre.lsn_addr_index.restrict(frozen_lsns);

        require cropped_tj.discard_old_cond(new_bdy, frozen_index.values(), fj);
    } }

    transition!{ query_end_lsn(lbl: Label) {
        require lbl is QueryEndLsn;
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }
    
    transition!{ put(lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        require lbl is Put;
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, new_journal, Self::lbl_i(lbl));
        update journal = new_journal;
    } }

    transition!{ discard_old(lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        require lbl is DiscardOld;

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;

        require require_end == pre.journal.seq_end();
        require pre.journal.truncated_journal.can_discard_to(start_lsn);

        let lsn_addr_index_post = lsn_addr_index_discard_up_to(pre.lsn_addr_index, start_lsn);
        let keep_addrs = lsn_addr_index_post.values();

        // require new_journal.wf();
        require pre.journal.truncated_journal.discard_old_cond(
            start_lsn, keep_addrs, new_journal.truncated_journal);
        require new_journal.unmarshalled_tail == 
            pre.journal.unmarshalled_tail.bounded_discard(start_lsn);

        update journal = new_journal;
        update lsn_addr_index = lsn_addr_index_post;
    } }

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address, new_journal: LinkedJournal_v::LinkedJournal::State) {
        require lbl is Internal;
        require LinkedJournal_v::LinkedJournal::State::next_by(pre.journal, new_journal, 
            Self::lbl_i(lbl), LinkedJournal_v::LinkedJournal::Step::internal_journal_marshal(cut, addr));

        update journal = new_journal;
        update lsn_addr_index = lsn_addr_index_append_record(
            pre.lsn_addr_index,
            pre.journal.unmarshalled_tail.discard_recent(cut),
            addr);
    } }

    transition!{ internal_no_op(lbl: Label) {
        require lbl is Internal;
    } }

    // TODO(travis): Weird that I can't call my only init operation "init"
    // TODO(travis): one can shadow field names with argument names, leading
    // to confusing error messages. I suggest the state-machine language
    // should simply treat shadowing as an error.
    init!{ initialize(ijournal: TruncatedJournal) {
        require ijournal.decodable();    // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
        // require ijournal.disk_is_tight_wrt_representation(); // Note(Jialin): might not be necessary
        init journal = LinkedJournal_v::LinkedJournal::State{
            truncated_journal: ijournal,
            unmarshalled_tail: MsgHistory::empty_history_at(ijournal.seq_end())}; // Note(Jialin): used to be ijournal.build_tight but I can't think of why
        init lsn_addr_index = ijournal.build_lsn_addr_index();
    } }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        let tj = self.journal.truncated_journal;
        &&& self.wf()
        &&& tj.disk_view.acyclic()
        &&& self.lsn_addr_index == tj.build_lsn_addr_index() // equivalent to imperative_matches_transitive
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, depth: nat) {
    }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        reveal(LinkedJournal_v::LinkedJournal::State::next);
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);
    }

    /* `pub` is only being added to avoid a confusing fake error message, originally we didn't intend for this
       proof function to be `pub` */
    pub proof fn discard_old_step_preserves_acyclicity(pre: Self, post: Self, lbl: Label)
    requires
        pre.inv(),
        Self::discard_old(pre, post, lbl, post.journal),
    ensures
        post.journal.truncated_journal.disk_view.acyclic(),
    {
        let dv = pre.journal.truncated_journal.disk_view;
        let post_dv = post.journal.truncated_journal.disk_view;
        let ranking = dv.the_ranking();

        assert forall |addr| #[trigger] post_dv.entries.contains_key(addr) && post_dv.entries[addr].cropped_prior(post_dv.boundary_lsn) is Some
        implies ranking[post_dv.entries[addr].cropped_prior(post_dv.boundary_lsn).unwrap()] < ranking[addr]
        by {
            assert(dv.entries.contains_key(addr)); // trigger
        }
        assert(post_dv.valid_ranking(ranking)); // witness
    }

    pub proof fn discard_old_maintains_repr_index(pre: Self, post: Self, lbl: Label)
    requires
        pre.inv(),
        Self::discard_old(pre, post, lbl, post.journal),
        post.wf(),
        post.journal.truncated_journal.disk_view.acyclic(),
    ensures
        post.lsn_addr_index == post.journal.truncated_journal.build_lsn_addr_index(),
    {
        let tj_pre = pre.journal.truncated_journal;
        tj_pre.build_lsn_addr_index_ensures();

        let tj_post = post.journal.truncated_journal;
        let bdy_post = tj_post.disk_view.boundary_lsn;
        let repr = tj_post.build_lsn_addr_index();

        reveal(TruncatedJournal::index_domain_valid);
        if bdy_post < tj_pre.seq_end() {
            tj_post.disk_view.build_lsn_addr_index_domain_valid(tj_post.freshest_rec);
            tj_post.disk_view.sub_disk_with_newer_lsn_repr_index(tj_pre.disk_view, tj_post.freshest_rec);
            lsn_addr_index_discard_up_to_ensures(pre.lsn_addr_index, bdy_post);
            // assert(repr <= post.lsn_addr_index);
            // assert(post.lsn_addr_index <= repr);
//            assert(repr.dom() =~= post.lsn_addr_index.dom());
            assert(repr =~= post.lsn_addr_index); // (Jialin): needs to =~= dom then the map, why?
        } else {
            assert(post.lsn_addr_index =~= repr);
        }
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        let tj = pre.journal.truncated_journal;
        let post_tj = post.journal.truncated_journal;
        let start_lsn = lbl->start_lsn;
        tj.discard_old_preserves_acyclicity(start_lsn, post.lsn_addr_index.values(), post_tj);
        Self::discard_old_maintains_repr_index(pre, post, lbl);
    }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address, new_journal: LinkedJournal_v::LinkedJournal::State) {
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);
//        assert( post.wf() );

        let istep:LinkedJournal_v::LinkedJournal::Step = LinkedJournal_v::LinkedJournal::Step::internal_journal_marshal(cut, addr);
//        assert(LinkedJournal_v::LinkedJournal::State::next_by(pre.journal, post.journal, State::lbl_i(lbl), istep));

        // NOTE(Jialin): inv_next duplicates what should be exported by submodule inv
        LinkedJournal_v::LinkedJournal::State::inv_next(pre.journal, post.journal, State::lbl_i(lbl), istep);

        let tj_pre = pre.journal.truncated_journal;
        let tj_post = post.journal.truncated_journal;
//        assert( tj_post.disk_view.acyclic() ); // linked journal inv

        tj_pre.disk_view.sub_disk_repr_index(tj_post.disk_view, tj_pre.freshest_rec);
//        assert( post.lsn_addr_index == tj_post.build_lsn_addr_index() );

//        assert( post.inv() );
    }
   
    #[inductive(internal_no_op)]
    fn internal_no_op_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, ijournal: TruncatedJournal) {
    }
    
} } // state_machine!
        
} // verus!