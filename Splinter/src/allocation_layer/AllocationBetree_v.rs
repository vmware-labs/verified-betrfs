// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{prelude::*, seq_lib::*, set_lib::*, map_lib::*, multiset::*};
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

verus! {

/// Introduces aulikes to track the life time of disk data structures in terms of Allocation Unit.
/// Labels for the allocation betree communicates the set of new AU and discarded AUs to external composer
/// Incorporates read only reference tracking for determining GC

state_machine!{ AllocationBetree {
    fields {
        pub betree: LinkedBetreeVars::State<Branch>,

        // Multiset<AU Pointer>
        pub betree_aus: AULikes,    // tree node reference

        // Multiset<AU Pointer>
        pub branch_root_aus: AULikes,    // root au of each branch

        // maps root of each branch to its full set of AUs 
        pub branch_full_summary: Map<AU, Set<AU>>,

        // read refs be part of the input state of the compactor
        // mini allocator 

        // compactor needs the concrete address (root)
        pub compactor: Compactor,   // build a new compacted b+ tree
        // pub buffer_read_refs: AULikes;  // root buffer

        // root AU => set of AU
        // pointing at AU versus all AUs

        // track read refs of buffers that are in the middle of read-only reference (compaction)
        // allowing for same tightness
        // buffer modification should have also allowed for 

        // to reuse we need both 1. traitified SM 2. a relaxed requirement that only specifies what must be present
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU> {
        // branch_full_summary values fold
        self.betree_aus.dom() + self.betree_aus.dom() + compactor.accessible_aus()
    }

    pub enum Label
    {
        Label{linked_lbl: LinkedBetreeVars::Label},
    }

    pub open spec fn is_fresh(self, addrs: Set<Address>) -> bool
    {
        &&& self.betree_likes.dom().disjoint(addrs.au)
        &&& self.buffer_likes.dom().disjoint(addrs.au)
    }

    // transitions that do not affect likes
    transition!{ likes_noop(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>) {
        require lbl->linked_lbl is Query || lbl->linked_lbl is Put || lbl->linked_lbl is FreezeAs;
        require LinkedBetreeVars::State::next(pre.betree, new_betree, lbl->linked_lbl);
        update betree = new_betree;
    }}

    transition!{ internal_flush_memtable(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs) {
        require LinkedBetreeVars::State::internal_flush_memtable(pre.betree, new_betree, lbl->linked_lbl, new_betree.memtable, new_addrs);
        require pre.is_fresh(new_addrs.repr());

        let old_root_likes = pre.betree.linked.root_betree_likes();
        let new_root_likes = new_betree.linked.root_betree_likes();

        update betree = new_betree;
        update betree_likes = pre.betree_likes.sub(old_root_likes).add(new_root_likes);
        update buffer_likes = pre.buffer_likes.insert(new_addrs.addr2); // buffer address
    }}

    transition!{ internal_grow(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) {
        require LinkedBetreeVars::State::internal_grow(pre.betree, new_betree, lbl->linked_lbl, new_root_addr);
        require pre.is_fresh(Set::empty().insert(new_root_addr));

        update betree = new_betree;
        update betree_likes = pre.betree_likes.insert(new_root_addr);
    }}

    transition!{ internal_split(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        require LinkedBetreeVars::State::internal_split(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, request, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr().union(path_addrs.to_set()));

        let old_child = path.target().child_at_idx(request.get_child_idx());
        let old_tree_likes = path.addrs_on_path().to_multiset().add(old_child.root_betree_likes());
        let new_tree_likes = path_addrs.to_multiset().add(new_addrs.repr().to_multiset());

        update betree = new_betree;
        update betree_likes = pre.betree_likes.sub(old_tree_likes).add(new_tree_likes);
    }}
    
    transition!{ internal_flush(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {        
        require LinkedBetreeVars::State::internal_flush(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr().union(path_addrs.to_set()));

        let old_parent = path.target();
        let old_child = old_parent.child_at_idx(child_idx);
        let old_tree_likes = path.addrs_on_path().to_multiset().add(old_child.root_betree_likes());
        let new_tree_likes = path_addrs.to_multiset().add(new_addrs.repr().to_multiset());

        let old_buffer_likes = old_parent.root().buffers.slice(0, buffer_gc as int).addrs.to_multiset(); // gced buffers
        let new_buffer_likes = old_parent.flush_buffers(child_idx, buffer_gc).addrs.to_multiset();  // newly flushed to child

        update betree = new_betree;
        update betree_likes = pre.betree_likes.sub(old_tree_likes).add(new_tree_likes);
        update buffer_likes = pre.buffer_likes.sub(old_buffer_likes).add(new_buffer_likes);
    }}

    transition!{ internal_compact(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require LinkedBetreeVars::State::internal_compact(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, start, end, compacted_buffer, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr().union(path_addrs.to_set()));

        let old_tree_likes = path.addrs_on_path().to_multiset();
        let new_tree_likes = path_addrs.to_multiset().insert(new_addrs.addr1);

        let old_buffer_likes = path.target().root().buffers.slice(start as int, end as int).addrs.to_multiset();
        let new_buffer_likes = Multiset::singleton(new_addrs.addr2);

        update betree = new_betree;
        update betree_likes = pre.betree_likes.sub(old_tree_likes).add(new_tree_likes);
        update buffer_likes = pre.buffer_likes.sub(old_buffer_likes).add(new_buffer_likes);
    }}

    transition!{ internal_noop(lbl: Label) {
        require LinkedBetreeVars::State::internal_noop(pre.betree, pre.betree, lbl->linked_lbl);
    }}

    init!{ initialize(betree: LinkedBetreeVars::State<SimpleBuffer>) {
        require LinkedBetreeVars::State::initialize(betree, betree);

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
    fn likes_noop_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>) {
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
    }

    #[inductive(internal_flush_memtable)]
    fn internal_flush_memtable_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs) { 
        reveal(LinkedBetreeVars::State::next_by);
        assert(new_betree.inv()) by {
            pre.inv_is_fresh_ensures(new_addrs.repr());
            let linked_step = LinkedBetreeVars::Step::internal_flush_memtable(new_betree.memtable, new_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }
   
    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) { 
        reveal(LinkedBetreeVars::State::next_by);
        assert(new_betree.inv()) by {
            pre.inv_is_fresh_ensures(set![new_root_addr]);
            let linked_step = LinkedBetreeVars::Step::internal_grow(new_root_addr);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }
   
    #[inductive(internal_split)]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        reveal(LinkedBetreeVars::State::next_by);
        assert(new_betree.inv()) by {
            pre.inv_is_fresh_ensures(new_addrs.repr().union(path_addrs.to_set()));
            let linked_step = LinkedBetreeVars::Step::internal_split(new_betree.linked, path, request, new_addrs, path_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);
    }
   
    #[inductive(internal_flush)]
    fn internal_flush_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        reveal(LinkedBetreeVars::State::next_by);
        assert(new_betree.inv()) by {
            pre.inv_is_fresh_ensures(new_addrs.repr().union(path_addrs.to_set()));
            let linked_step = LinkedBetreeVars::Step::internal_flush(new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);    
    }
   
    #[inductive(internal_compact)]
    fn internal_compact_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) { 
        reveal(LinkedBetreeVars::State::next_by);
        assert(new_betree.inv()) by {
            pre.inv_is_fresh_ensures(new_addrs.repr().union(path_addrs.to_set()));
            let linked_step = LinkedBetreeVars::Step::internal_compact(new_betree.linked, path, start, end, compacted_buffer, new_addrs, path_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }
    
        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        assume(post.betree_likes == betree_likes);
        assume(post.buffer_likes == buffer_likes);    
    }
   
    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {}
   
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, betree: LinkedBetreeVars::State<SimpleBuffer>) {}

    proof fn inv_is_fresh_ensures(self, addrs: Set<Address>)
        requires self.inv(), self.is_fresh(addrs)
        ensures self.betree.linked.is_fresh(addrs)
    {
        assume(false);
    }
}} // end of AllocationBetree state machine

} // end of verus!