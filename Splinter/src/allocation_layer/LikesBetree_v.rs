// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{prelude::*, seq_lib::*, set_lib::*, map_lib::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::LinkedSeq_v::*;
use crate::betree::BufferDisk_v;
use crate::betree::BufferDisk_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;
use crate::allocation_layer::Likes_v::*;

verus! {

/// Introduces likes to track the life time of disk data structures.
/// There are two disks (same as LinkedBetree): 
/// (1) dv containing BetreeNodes and (2) BufferDisk containing Buffers

impl<T> LinkedSeq<T> {
    pub open spec(checked) fn likes(self) -> Likes
    {
        self.addrs.to_multiset()
    }
}

impl<T> LinkedBetree<T> {
    // returns betree likes & buffer likes
    pub open spec fn children_likes(self, ranking: Ranking, start: nat) -> (Likes, Likes)
        recommends 
            self.has_root(),
            self.valid_ranking(ranking),
            start <= self.root().children.len()
        decreases 
            self.get_rank(ranking), 0nat, self.root().children.len()-start 
            when ({
                &&& start <= self.root().children.len()
                &&& self.root().valid_child_index(start) ==> 
                    self.child_at_idx(start).get_rank(ranking) < self.get_rank(ranking)
            })
    {
        if start == self.root().children.len() {
            (no_likes(), no_likes())
        } else {
            let (betree_likes, buffer_likes) = self.child_at_idx(start).transitive_likes_internal(ranking);
            let (other_betree_likes, other_buffer_likes) = self.children_likes(ranking, start+1);
            (betree_likes.add(other_betree_likes), buffer_likes.add(other_buffer_likes))
        }
    }

    pub open spec(checked) fn root_betree_likes(self) -> Likes
        
    {
        if self.has_root() {
            set![self.root.unwrap()].to_multiset()
        } else {
            no_likes() 
        }
    }

    pub open spec(checked) fn transitive_likes_internal(self, ranking: Ranking) -> (Likes, Likes)
        recommends self.valid_ranking(ranking)
        decreases self.get_rank(ranking)
    {
        if !self.has_root() { ( no_likes(), no_likes() ) } 
        else {
            let (children_betree_likes, children_buffer_likes) = self.children_likes(ranking, 0);
            let betree_likes = self.root_betree_likes().add(children_buffer_likes);
            let buffer_likes = self.root().buffers.likes().add(children_buffer_likes);
            (betree_likes, buffer_likes)
        }
    }

    pub open spec(checked) fn transitive_likes(self) -> (Likes, Likes)
    {
        if !self.acyclic() { (arbitrary(), arbitrary()) }
        else { self.transitive_likes_internal(self.the_ranking()) }
    }
}

state_machine!{ LikesBetree {
    fields {
        pub betree: LinkedBetreeVars::State,
        // imperatively maintained view of tree node reference
        // prior to clone should be a tree shape (equivalent to refcount)
        pub betree_likes: Likes,
        // imperatively maintained view of buffer pointers (outgoing)
        // used to track life time of each immutable buffer
        pub buffer_likes: Likes,
    }

    pub enum Label
    {
        Label{linked_lbl: LinkedBetreeVars::Label},
    }

    pub open spec fn lbl_i(lbl: Label) -> LinkedBetreeVars::Label {
        lbl->linked_lbl
    }

    // transitions that do not affect likes
    transition!{ likes_noop(lbl: Label, new_betree: LinkedBetreeVars::State) {
        require lbl->linked_lbl is Query || lbl->linked_lbl is Put || lbl->linked_lbl is FreezeAs;
        require LinkedBetreeVars::State::next(pre.betree, new_betree, lbl->linked_lbl);
        update betree = new_betree;
    }}

    transition!{ internal_flush_memtable(lbl: Label, new_betree: LinkedBetreeVars::State, new_addrs: TwoAddrs) {
        let linked_step = LinkedBetreeVars::Step::internal_flush_memtable(new_addrs);
        require LinkedBetreeVars::State::next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);

        let old_root_likes = pre.betree.linked.root_betree_likes();
        let new_root_likes = new_betree.linked.root_betree_likes();

        update betree = new_betree;
        update betree_likes = pre.betree_likes.sub(old_root_likes).add(new_root_likes);
        update buffer_likes = pre.buffer_likes.insert(new_addrs.addr2); // buffer address
    }}

    transition!{ internal_grow(lbl: Label, new_betree: LinkedBetreeVars::State, new_root_addr: Address) {
        let linked_step = LinkedBetreeVars::Step::internal_grow(new_root_addr);
        require LinkedBetreeVars::State::next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step); 

        update betree = new_betree;
        update betree_likes = pre.betree_likes.insert(new_root_addr);
    }}


    transition!{ internal_split(lbl: Label, new_betree: LinkedBetreeVars::State, path: Path<BufferDisk>, 
        request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        let linked_step = LinkedBetreeVars::Step::internal_split(new_betree.linked, path, request, new_addrs, path_addrs);
        require LinkedBetreeVars::State::next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);

        let new_path_likes = path_addrs.to_multiset();
        let new_split_likes = new_addrs.repr().to_multiset();

        let old_path_likes = path.addrs_on_path().to_multiset(); // old path to split parent
        let old_split_likes = path.target().child_at_idx(request.get_child_idx()).root_betree_likes(); // old child 

        let new_betree_likes = pre.betree_likes.sub(old_path_likes).sub(old_split_likes
            ).add(new_path_likes).add(new_split_likes);

        update betree = new_betree;
        update betree_likes = new_betree_likes;
    }}
    
    transition!{ internal_flush(lbl: Label, new_betree: LinkedBetreeVars::State, path: Path<BufferDisk>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        let linked_step = LinkedBetreeVars::Step::internal_flush(new_betree.linked, path, 
            child_idx, buffer_gc, new_addrs, path_addrs);
        require LinkedBetreeVars::State::next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);

        let new_path_likes = path_addrs.to_multiset(); // new path from root to parent of new flush nodes
        let new_flush_likes = new_addrs.repr().to_multiset(); // new flush parent and child node

        let old_path_likes = path.addrs_on_path().to_multiset(); // old path from root to old parent
        let old_flush_likes = path.target().child_at_idx(child_idx).root_betree_likes(); // old flush child

        let new_betree_likes = pre.betree_likes.sub(old_path_likes).sub(old_flush_likes
            ).add(new_path_likes).add(new_flush_likes);

        let flushed_buffers_likes = path.target().flush_buffers(child_idx, buffer_gc).addrs.to_multiset();
        let gced_buffers_likes = path.target().root().buffers.slice(0, buffer_gc as int).addrs.to_multiset();

        let new_buffer_likes = pre.buffer_likes.sub(gced_buffers_likes).add(flushed_buffers_likes);

        update betree = new_betree;
        update betree_likes = new_betree_likes;
        update buffer_likes = new_buffer_likes;
    }}

    transition!{ internal_compact(lbl: Label, new_betree: LinkedBetreeVars::State, path: Path<BufferDisk>, 
        start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        let linked_step = LinkedBetreeVars::Step::internal_compact(new_betree.linked, path, 
            start, end, compacted_buffer, new_addrs, path_addrs);
        require LinkedBetreeVars::State::next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        
        let new_path_likes = path_addrs.to_multiset();
        let old_path_likes = path.addrs_on_path().to_multiset();

        let new_betree_likes = pre.betree_likes.sub(old_path_likes).add(new_path_likes).insert(new_addrs.addr1);

        let compacted_buffer_likes = path.target().root().buffers.slice(start as int, end as int).addrs.to_multiset();
        let new_buffer_likes = pre.buffer_likes.sub(compacted_buffer_likes).insert(new_addrs.addr2);

        update betree = new_betree;
        update betree_likes = new_betree_likes;
        update buffer_likes = new_buffer_likes;
    }}

    transition!{ internal_noop(lbl: Label) {
        require lbl->linked_lbl is Internal;
        require LinkedBetreeVars::State::next(pre.betree, pre.betree, lbl->linked_lbl);
    }}

    init!{ initialize(betree: LinkedBetreeVars::State, stamped_betree: StampedBetree) {
        require LinkedBetreeVars::State::initialize(betree, stamped_betree);
        let (betree_likes, buffer_likes) = betree.linked.transitive_likes();

        init betree = betree;
        init betree_likes = betree_likes;
        init buffer_likes = buffer_likes;
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        let (betree_likes, buffer_likes) = self.betree.linked.transitive_likes();
        &&& self.betree.inv()
        &&& self.betree_likes == betree_likes
        &&& self.buffer_likes == buffer_likes
    }

    #[inductive(likes_noop)]
    fn likes_noop_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State) { 
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
    }
       
    #[inductive(internal_flush_memtable)]
    fn internal_flush_memtable_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State, new_addrs: TwoAddrs) {
        reveal(LinkedBetreeVars::State::next_by);
        LinkedBetreeVars::State::internal_flush_memtable_inductive(pre.betree, new_betree, lbl->linked_lbl, new_addrs);
        assert(new_betree.inv());

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }
       
    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State, new_root_addr: Address) { 
        reveal(LinkedBetreeVars::State::next_by);
        LinkedBetreeVars::State::internal_grow_inductive(pre.betree, new_betree, lbl->linked_lbl, new_root_addr);
        assert(new_betree.inv());

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }
       
    #[inductive(internal_split)]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State, path: Path<BufferDisk>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) { 
        reveal(LinkedBetreeVars::State::next_by);
        LinkedBetreeVars::State::internal_split_inductive(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, request, new_addrs, path_addrs);
        assert(new_betree.inv());

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }
       
    #[inductive(internal_flush)]
    fn internal_flush_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State, path: Path<BufferDisk>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) { 
        reveal(LinkedBetreeVars::State::next_by);
        LinkedBetreeVars::State::internal_flush_inductive(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs);
        assert(new_betree.inv());

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }

    #[inductive(internal_compact)]
    fn internal_compact_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State, path: Path<BufferDisk>, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) { 
        reveal(LinkedBetreeVars::State::next_by);
        LinkedBetreeVars::State::internal_compact_inductive(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, start, end, compacted_buffer, new_addrs, path_addrs);
        assert(new_betree.inv());

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }
       
    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) { 
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
    }
       
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, betree: LinkedBetreeVars::State, stamped_betree: StampedBetree) { 
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
    }
}}

}