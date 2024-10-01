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
use crate::allocation_layer::Likes_v::*;

verus! {

/// Introduces likes to track the life time of disk data structures.
/// There are two disks (same as LinkedBetree): 
/// (1) dv containing BetreeNodes and (2) BufferDisk containing Buffers

impl LinkedSeq {
    pub open spec(checked) fn likes(self) -> Likes
    {
        self.addrs.to_multiset()
    }

    // // workaround to broadcast to_multiset seq property
    // pub broadcast proof fn likes_ensures(self)
    //     ensures
    //         // forall |other| #[trigger] (self.extend(other).likes()) =~= self.likes().add(other.likes()),
    //         self.len() == self.likes().len(),
    //         forall |a| self.contains(a) <==> #[trigger] self.likes().count(a) > 0,
    // {
    //     self.addrs.to_multiset_ensures();
    // }
}

impl<T> LinkedBetree<T> {
    pub open spec(checked) fn root_likes(self) -> Likes
    {
        if self.has_root() {
            Multiset::singleton(self.root.unwrap())
        } else {
            no_likes()
        }
    }

    pub open spec fn children_likes(self, ranking: Ranking, start: nat) -> Likes
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
            no_likes()
        } else {
            let child_betree_likes = self.child_at_idx(start).tree_likes(ranking);
            let other_betree_likes = self.children_likes(ranking, start+1);
            child_betree_likes.add(other_betree_likes)
        }
    }

    pub open spec(checked) fn tree_likes(self, ranking: Ranking) -> Likes
        recommends self.valid_ranking(ranking)
        decreases self.get_rank(ranking)
    {
        if !self.has_root() { no_likes() } 
        else {
            let children_betree_likes  = self.children_likes(ranking, 0);
            self.root_likes().add(children_betree_likes)
        }
    }

    pub open spec(checked) fn transitive_likes(self) -> (Likes, Likes)
    {
        if !self.acyclic() { (arbitrary(), arbitrary()) }
        else {
            let tree_likes = self.tree_likes(self.the_ranking());
            (tree_likes, self.buffer_likes(tree_likes)) 
        }
    }

    pub open spec fn buffer_likes(self, betree_likes: Likes) -> Likes
        decreases betree_likes.len()
    {
        if betree_likes.len() > 0 {
            let addr = betree_likes.choose();
            let sub_buffer_likes = self.buffer_likes(betree_likes.remove(addr));
            self.dv.entries[addr].buffers.likes().add(sub_buffer_likes)
        } else {
            no_likes()
        }
    }

    proof fn children_likes_domain(self, ranking: Ranking, start: nat)
        requires 
            self.has_root(),
            self.valid_ranking(ranking),
            start <= self.root().children.len(),
        ensures ({ 
            let reachable_betree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, start);
            &&& self.children_likes(ranking, start).dom() =~= reachable_betree_addrs
        })
        decreases self.get_rank(ranking), self.root().children.len() - start
    {
        if start == self.root().children.len() {
        } else {
            let reachable_betree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, start);
            assert(self.root().valid_child_index(start)); // trigger
            let child = self.child_at_idx(start);
            assert(child.valid_ranking(ranking));
            self.child_at_idx_reachable_addrs_ensures(start);
            child.tree_likes_domain(ranking);

            let child_betree_likes = child.tree_likes(ranking);
            let other_betree_likes = self.children_likes(ranking, start+1);
            self.children_likes_domain(ranking, start+1);
            self.reachable_betree_addrs_using_ranking_recur_lemma(ranking, start);
        }
    }

    proof fn tree_likes_domain(self, ranking: Ranking)
        requires 
            self.valid_ranking(ranking)
        ensures 
            self.tree_likes(ranking).dom() =~= self.reachable_betree_addrs_using_ranking(ranking),
            self.tree_likes(ranking).dom() <= self.dv.entries.dom(),
        decreases self.get_rank(ranking)
    {
        if self.has_root() {
            self.children_likes_domain(ranking, 0);
            self.reachable_betree_addrs_ignore_ranking(self.the_ranking(), ranking);
            self.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
        }
    }

    broadcast proof fn children_likes_ignore_ranking(self, r1: Ranking, r2: Ranking, start: nat)
        requires 
            self.has_root(),
            self.valid_ranking(r1),
            self.valid_ranking(r2),
            start <= self.root().children.len()
        ensures 
            #![auto] self.children_likes(r1, start) =~= self.children_likes(r2, start),
        decreases 
            self.get_rank(r1), self.root().children.len()-start
    {
        if start < self.root().children.len() {
            broadcast use LinkedBetree::reachable_betree_addrs_ignore_ranking;
            let child = self.child_at_idx(start);
            assert(self.root().valid_child_index(start));
            child.tree_likes_ignore_ranking(r1, r2);
            self.children_likes_ignore_ranking(r1, r2, start+1);
        }
    }

    broadcast proof fn tree_likes_ignore_ranking(self, r1: Ranking, r2: Ranking) 
        requires 
            #[trigger] self.valid_ranking(r1),
            #[trigger] self.valid_ranking(r2),
        ensures 
            self.tree_likes(r1) =~= self.tree_likes(r2)
        decreases 
            self.get_rank(r1)
    {
        if self.has_root() {
            self.children_likes_ignore_ranking(r1, r2, 0);
        }
    }

    proof fn subdisk_implies_same_children_likes(self, other: Self, ranking: Ranking, start: nat)
        requires 
            self.has_root(),
            other.has_root(),
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.dv.is_sub_disk(other.dv),
            self.root().children == other.root().children,
            start <= self.root().children.len(),
        ensures 
            self.children_likes(ranking, start) =~= other.children_likes(ranking, start)
        decreases self.get_rank(ranking), self.root().children.len() - start
    {
        if start < self.root().children.len() {
            let child = self.child_at_idx(start);
            let other_child = other.child_at_idx(start);
            assert(self.root().valid_child_index(start)); // trigger
            child.subdisk_implies_same_tree_likes(other_child, ranking);
            self.subdisk_implies_same_children_likes(other, ranking, start+1);
        }
    }

    proof fn subdisk_implies_same_tree_likes(self, other: Self, ranking: Ranking)
        requires
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.root == other.root,
            self.dv.is_sub_disk(other.dv)
        ensures 
            self.tree_likes(ranking) =~= other.tree_likes(ranking)
        decreases 
            self.get_rank(ranking)
    {
        if self.has_root() {
            self.subdisk_implies_same_children_likes(other, ranking, 0);
        }
    }

    proof fn same_tight_tree_implies_same_transitive_likes(self, other: Self)
        requires             
            self.valid_view(other),
            self.same_tight_tree(other),
        ensures
            self.transitive_likes() == other.transitive_likes()
    {
        let (betree_likes, buffer_likes) = self.transitive_likes();
        let (other_betree_likes, other_buffer_likes) = other.transitive_likes();

        other.subdisk_implies_same_tree_likes(self, self.finite_ranking());
        other.tree_likes_ignore_ranking(self.finite_ranking(), other.the_ranking());
        self.tree_likes_ignore_ranking(self.finite_ranking(), self.the_ranking());

        assert(betree_likes =~= other_betree_likes);
        other.tree_likes_domain(other.the_ranking());
        other.subdisk_implies_same_buffer_likes(self, betree_likes);
    }

    proof fn buffer_likes_additive(self, betree_likes: Likes, delta: Likes)
        requires 
            betree_likes.dom() <= self.dv.entries.dom(),
            delta.dom() <= self.dv.entries.dom(),
        ensures
            self.buffer_likes(betree_likes.add(delta))
            =~= self.buffer_likes(betree_likes).add(self.buffer_likes(delta))
        decreases
            betree_likes.add(delta).len()
    {
        let total = betree_likes.add(delta);

        if betree_likes.len() == 0 {
            assert(total =~= delta);
        } else if delta.len() == 0 {
            assert(total =~= betree_likes);
        } else {
            assert(total.len() > 0); // NOTE: trigger needed for choose
            let random = total.choose();
            assert(total.contains(random));
            
            let random_buffer_likes = self.dv.entries[random].buffers.likes();
            let sub_buffer_likes = self.buffer_likes(total.remove(random));
            assert(self.buffer_likes(total) == random_buffer_likes.add(sub_buffer_likes));
            assert(Multiset::singleton(random).choose() == random);
            assert(Multiset::singleton(random).remove(random) =~= no_likes());
            assert(self.buffer_likes(no_likes()) == no_likes());

            if betree_likes.contains(random) {
                self.buffer_likes_additive(betree_likes.remove(random), delta);
                assert(total.remove(random) == betree_likes.remove(random).add(delta)); // trigger
                self.buffer_likes_additive(betree_likes.remove(random), Multiset::singleton(random));
                assert(betree_likes.remove(random).add(Multiset::singleton(random)) == betree_likes);
                // assert(self.buffer_likes(Multiset::singleton(random)) =~= random_buffer_likes);
                // // assert(
                // //     random_buffer_likes.add(self.buffer_likes(betree_likes.remove(random))) 
                // //     =~= self.buffer_likes(betree_likes)
                // // );
            } else {
                assert(delta.contains(random));
                self.buffer_likes_additive(betree_likes, delta.remove(random));
                assert(total.remove(random) == betree_likes.add(delta.remove(random))); // trigger
                self.buffer_likes_additive(delta.remove(random), Multiset::singleton(random));
                assert(delta.remove(random).add(Multiset::singleton(random)) == delta);
            }
        }
    }

    proof fn addr_for_buffer(self, betree_likes: Likes, buffer: Address) -> (addr: Address)
        requires 
            self.buffer_likes(betree_likes).contains(buffer),
            betree_likes.dom() <= self.dv.entries.dom(),
        ensures 
            betree_likes.contains(addr),
            self.dv.entries[addr].buffers.addrs.contains(buffer),
        decreases
            betree_likes.len()
    {
        let addr = betree_likes.choose();
        if self.dv.entries[addr].buffers.likes().contains(buffer) {
            self.dv.entries[addr].buffers.addrs.to_multiset_ensures();
            addr
        } else {
            let addr = self.addr_for_buffer(betree_likes.remove(addr), buffer);
            addr
        }
    }

    proof fn tree_buffers_are_closed(self, betree_likes: Likes, addr: Address)
    requires 
        betree_likes.contains(addr),
        betree_likes.dom() <= self.dv.entries.dom(),
    ensures 
        self.dv.entries[addr].buffers.likes() <= self.buffer_likes(betree_likes)
    decreases
        betree_likes.len()
    {
        let random = betree_likes.choose();
        if addr == random { }
        else { self.tree_buffers_are_closed(betree_likes.remove(random), addr); }
    }

    proof fn buffer_likes_domain(self, betree_likes: Likes)
        requires 
            self.acyclic(),
            betree_likes.dom() == self.reachable_betree_addrs(),
        ensures 
            self.buffer_likes(betree_likes).dom() =~= self.reachable_buffer_addrs(), 
    {
        let buffer_likes = self.buffer_likes(betree_likes);
        let reachable_buffers = self.reachable_buffer_addrs();

        self.reachable_betree_addrs_using_ranking_closed(self.the_ranking());
        assert forall |buffer| buffer_likes.contains(buffer) <==> reachable_buffers.contains(buffer)
        by {
            if buffer_likes.contains(buffer) {
                let addr = self.addr_for_buffer(betree_likes, buffer);
                assert(self.reachable_buffer(addr, buffer));
            }
            if reachable_buffers.contains(buffer) {
                let addr = choose |addr| self.reachable_buffer(addr, buffer);
                self.dv.entries[addr].buffers.addrs.to_multiset_ensures();
                self.buffer_likes_additive(betree_likes.remove(addr), Multiset::singleton(addr));
                assert(betree_likes == betree_likes.remove(addr).add(Multiset::singleton(addr)));
            }
        }
    }

    proof fn subdisk_implies_same_buffer_likes(self, big: Self, betree_likes: Likes)
        requires 
            self.dv.is_sub_disk(big.dv),
            betree_likes.dom() <= self.dv.entries.dom(),
        ensures 
            self.buffer_likes(betree_likes) =~= big.buffer_likes(betree_likes)
        decreases
            betree_likes.len()
    {
        if betree_likes.len() > 0 {
            let random = betree_likes.choose();
            assert(self.dv.entries.contains_key(random)); // trigger
            assert(big.dv.entries.contains_key(random));  // trigger
            assert(self.dv.entries[random] == big.dv.entries[random]);
            self.subdisk_implies_same_buffer_likes(big, betree_likes.remove(random));
        }
    }
}


state_machine!{ LikesBetree {
    fields {
        pub betree: LinkedBetreeVars::State<SimpleBuffer>,
        // GC across crashes
        // imperatively maintained view of tree node reference
        // prior to clone should be a tree shape (equivalent to refcount)
        pub betree_likes: Likes,
        // imperatively maintained view of buffer pointers (outgoing)
        // used to track life time of each immutable buffer
        pub buffer_likes: Likes,

        // GC across ephemeral state
        // allocation
        // 1. buffer vs b+tree
        // - linked should specify the minimum disk requirement
        //  - specifying what must be available (build tight)
        //  - instead of restricting a precise domain
        //  - buffer disk must also follow this requirement 
        //
        // Allocation<SimpleBuffer>
        // Allocation<Branch> 
        // 2. compaction is a single step before
        // read ref doesn't exist because 
        // - break down compaction: begin (read refs), build (internal), commit (real thing)
        // 
        // 3. au
    }

    pub enum Label
    {
        Label{linked_lbl: LinkedBetreeVars::Label},
    }

    // same definition as Linked because we don't ever reuse allocated pages
    pub open spec fn is_fresh(self, addrs: Set<Address>) -> bool
    {
        self.betree.linked.is_fresh(addrs)
    }

    // transitions that do not affect likes
    transition!{ likes_noop(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>) {
        require lbl->linked_lbl is Query || lbl->linked_lbl is Put || lbl->linked_lbl is FreezeAs;
        require LinkedBetreeVars::State::next(pre.betree, new_betree, lbl->linked_lbl);
        update betree = new_betree;
    }}

    transition!{ internal_flush_memtable(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs) {
        require LinkedBetreeVars::State::internal_flush_memtable(pre.betree, new_betree, lbl->linked_lbl,
            new_betree.memtable, new_betree.linked, new_addrs);
        require pre.is_fresh(new_addrs.repr());

        let discard_betree = pre.betree.linked.root_likes();
        let add_betree = new_betree.linked.root_likes();

        let new_betree_likes = pre.betree_likes.sub(discard_betree).add(add_betree);
        let new_buffer_likes = pre.buffer_likes.insert(new_addrs.addr2);

        // likes level requirement that new betree must contain all live betree addresses
        require new_betree_likes.dom() <= new_betree.linked.dv.entries.dom();
        require new_buffer_likes.dom() <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_likes = new_betree_likes;
        update buffer_likes = new_buffer_likes;
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
        let old_tree_likes = path.addrs_on_path().to_multiset().add(old_child.root_likes());
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
        let old_tree_likes = path.addrs_on_path().to_multiset().add(old_child.root_likes());
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

        let pushed = pre.betree.linked.push_memtable(pre.betree.memtable, new_addrs);
        pre.betree.linked.push_memtable_ensures(pre.betree.memtable, new_addrs);

        let ranking = pre.betree.linked.the_ranking();
        let pushed_ranking = pre.betree.linked.push_memtable_new_ranking(pre.betree.memtable, new_addrs, ranking);

        broadcast use 
            LinkedBetree::reachable_betree_addrs_ignore_ranking, 
            LinkedBetree::children_likes_ignore_ranking, 
            LinkedBetree::tree_likes_ignore_ranking;

        new_betree.linked.dv.subdisk_implies_ranking_validity(pushed.dv, pushed_ranking);
        assert(new_betree.linked.valid_ranking(pushed_ranking)); // trigger

        pushed.agreeable_disks_same_reachable_betree_addrs(new_betree.linked, pushed_ranking);
        new_betree.linked.same_reachable_betree_addrs_implies_same_buffer_addrs(pushed);
        new_betree.linked.reachable_betree_addrs_using_ranking_closed(pushed_ranking);

        pre.betree.linked.tree_likes_domain(pushed_ranking);
        pre.betree.linked.buffer_likes_domain(pre.betree_likes);

        // assert(pre.betree.linked.reachable_buffer_addrs() == pre.buffer_likes.dom()); 
        // assert(post.buffer_likes.dom() =~= pre.buffer_likes.dom() + set![new_addrs.addr2]);
        // assert(post.buffer_likes.dom() =~= pre.betree.linked.reachable_buffer_addrs() + set![new_addrs.addr2]);
        // assert(pushed.reachable_buffer_addrs() == new_betree.linked.reachable_buffer_addrs());
        // assert(pushed.reachable_buffer_addrs() == pre.betree.linked.reachable_buffer_addrs() + set![new_addrs.addr2]);
        // assert(post.buffer_likes.dom() == new_betree.linked.reachable_buffer_addrs());
        // assert(pushed.same_tight_tree(new_betree.linked));

        let linked_step = LinkedBetreeVars::Step::internal_flush_memtable(new_betree.memtable, new_betree.linked, new_addrs);
        LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);

        pushed.same_tight_tree_implies_same_transitive_likes(post.betree.linked);
        assert(post.betree.linked.transitive_likes() == pushed.transitive_likes());

        let (betree_likes, buffer_likes) = post.betree.linked.transitive_likes();
        let root_likes = post.betree.linked.root_likes();        
        if pre.betree.linked.has_root() {
            pre.betree.linked.subdisk_implies_same_children_likes(pushed, pushed_ranking, 0);
            assert(betree_likes =~= post.betree_likes);

            pre.betree.linked.subdisk_implies_same_buffer_likes(pushed, pre.betree_likes);
            // assert(pre.betree.linked.buffer_likes(pre.betree_likes) =~= pushed.buffer_likes(pre.betree_likes));
            // assert(pre.buffer_likes == pre.betree.linked.buffer_likes(pre.betree_likes));
            // assert(buffer_likes == post.betree.linked.buffer_likes(post.betree_likes));
            // assert(pushed.buffer_likes(post.betree_likes) == post.betree.linked.buffer_likes(post.betree_likes));

            assert(betree_likes.contains(new_addrs.addr1));
            pushed.tree_buffers_are_closed(post.betree_likes, new_addrs.addr1);
            
            assert(pushed.root().buffers.addrs =~= pre.betree.linked.root().buffers.addrs + seq![new_addrs.addr2]); // trigger
            assert(pushed.root().buffers.addrs[pushed.root().buffers.len() as int - 1] == new_addrs.addr2); // trigger
            pushed.root().buffers.addrs.to_multiset_ensures();
            pre.betree.linked.root().buffers.addrs.to_multiset_ensures();

            assert(pre.betree.linked.root().buffers.addrs.push(new_addrs.addr2) =~= pushed.root().buffers.addrs);
            assert(pushed.root().buffers.likes().contains(new_addrs.addr2));
            assert(pushed.root().buffers.likes() =~= pre.betree.linked.root().buffers.likes().insert(new_addrs.addr2));
            assert(buffer_likes.contains(new_addrs.addr2));
            assert(post.betree_likes == pre.betree_likes.sub(pre.betree.linked.root_likes()).add(pushed.root_likes()));

            let pre_sub = pre.betree_likes.sub(pre.betree.linked.root_likes());
            let post_sub = post.betree_likes.sub(pushed.root_likes());
            assert(pre_sub =~= post_sub);

            pre.betree.linked.subdisk_implies_same_buffer_likes(pushed, pre_sub);
            pre.betree.linked.buffer_likes_additive(pre_sub, pre.betree.linked.root_likes());
            pushed.buffer_likes_additive(post_sub, pushed.root_likes());

            assert(pre_sub.add(pre.betree.linked.root_likes()) =~= pre.betree_likes);
            assert(pre.buffer_likes =~= pre.betree.linked.buffer_likes(pre_sub).add(pre.betree.linked.buffer_likes(pre.betree.linked.root_likes())));
            assert(post_sub.add(pushed.root_likes()) =~= post.betree_likes);

            pushed.buffer_likes_additive(post_sub, pushed.root_likes());
            // assert(post.betree.linked.buffer_likes(post.betree_likes) =~= 
            //     pushed.buffer_likes(post_sub).add(pushed.buffer_likes(pushed.root_likes())));

            let pre_root = pre.betree.linked.root_likes().choose();
            let _ = pre.betree.linked.buffer_likes(pre.betree.linked.root_likes().remove(pre_root)); // trigger

            // assert(pre.betree.linked.buffer_likes(pre.betree.linked.root_likes()) 
            //     =~= pre.betree.linked.root().buffers.likes()
            // );

            let pushed_root = pushed.root_likes().choose();
            let _ = pushed.buffer_likes(pushed.root_likes().remove(pushed_root));

            // assert(pushed.buffer_likes(pushed.root_likes()) =~= pushed.root().buffers.likes());
            // assert(pre.betree.linked.buffer_likes(pre.betree.linked.root_likes()).insert(new_addrs.addr2)
            //     =~= pushed.buffer_likes(pushed.root_likes())
            // );

            // assert(pre.betree.linked.buffer_likes(pre.betree.linked.root_likes()) =~= pre.betree.linked.root().buffers.likes());
            // assert(pre.buffer_likes.insert(new_addrs.addr2) =~= pushed.buffer_likes(post.betree_likes));
            assert(buffer_likes =~= pre.buffer_likes.insert(new_addrs.addr2));
            assert(buffer_likes =~= post.buffer_likes); // relating the difference
        } else {
            assert(pre.betree_likes =~= no_likes());
            // note: manual unrolling
            assert(pushed.children_likes(pushed_ranking, 1) =~= no_likes());
            assert(pushed.child_at_idx(0).tree_likes(pushed_ranking) =~= no_likes());
            assert(pushed.children_likes(pushed_ranking, 0) =~= no_likes());
            assert(post.betree_likes =~= betree_likes);

            let pushed_root = pushed.root_likes().choose();
            let _ = pushed.buffer_likes(pushed.root_likes().remove(pushed_root));

            assert(pushed.buffer_likes(pushed.root_likes()) =~= pushed.root().buffers.likes());
            assert(post.betree_likes =~= pushed.root_likes());

            let empty = seq![];
            empty.to_multiset_ensures();
            assert(empty.to_multiset() =~= no_likes());

            assert(buffer_likes == pushed.buffer_likes(pushed.root_likes()));
            pushed.root().buffers.addrs.to_multiset_ensures();
            assert(pushed.root().buffers.addrs =~= seq![new_addrs.addr2]);
            assert(pushed.root().buffers.likes() =~= Multiset::singleton(new_addrs.addr2));
            assert(buffer_likes =~= post.buffer_likes); // relating the difference
        }
    }
   
    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) { 
        reveal(LinkedBetreeVars::State::next_by);
        assert(new_betree.inv()) by {
            let linked_step = LinkedBetreeVars::Step::internal_grow(new_root_addr);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }

        let (betree_likes, buffer_likes) = new_betree.linked.transitive_likes();
        let ranking = new_betree.linked.finite_ranking();
        let child = new_betree.linked.child_at_idx(0);

        broadcast use LinkedBetree::tree_likes_ignore_ranking;
        assert(new_betree.linked.valid_ranking(ranking)); // trigger
        pre.betree.linked.dv.subdisk_implies_ranking_validity(new_betree.linked.dv, ranking);
        assert(pre.betree.linked.valid_ranking(ranking)); // trigger

        pre.betree.linked.subdisk_implies_same_tree_likes(child, ranking);
        assert(child.tree_likes(ranking) == pre.betree.linked.tree_likes(ranking));
        assert(child.tree_likes(ranking) == pre.betree_likes);

        assert(new_betree.linked.children_likes(ranking, 1) =~= no_likes());
        assert(new_betree.linked.children_likes(ranking, 0) =~= pre.betree_likes);

        assert(new_betree.linked.tree_likes(ranking) == betree_likes);
        assert(new_betree.linked.tree_likes(ranking) == pre.betree_likes.insert(new_root_addr));
        assert(betree_likes =~= post.betree_likes);

        new_betree.linked.tree_likes_domain(ranking);
        pre.betree.linked.tree_likes_domain(ranking);

        assert(new_betree.linked.buffer_likes(Multiset::singleton(new_root_addr)) =~= no_likes())
        by {
            assert(new_betree.linked.root().buffers == LinkedSeq::empty());
            new_betree.linked.root().buffers.addrs.to_multiset_ensures();
            assert(new_betree.linked.root().buffers.likes() =~= no_likes());
            assert(new_betree.linked.buffer_likes(Multiset::singleton(new_root_addr).remove(new_root_addr)) == no_likes());
        }

        new_betree.linked.buffer_likes_additive(pre.betree_likes, Multiset::singleton(new_root_addr));
        assert(buffer_likes =~= new_betree.linked.buffer_likes(pre.betree_likes));
        pre.betree.linked.subdisk_implies_same_buffer_likes(new_betree.linked, pre.betree_likes);
        assert(post.buffer_likes == buffer_likes);
    }

    #[inductive(internal_split)]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        reveal(LinkedBetreeVars::State::next_by);
        
        let split_parent = path.target().split_parent(request, new_addrs);
        let splitted = path.substitute(split_parent, path_addrs);

        assume(false);
        // must show strong step first
        // assert(pre.betree.post_step(linked_step).same_tight_tree(new_betree.linked));

        assert(new_betree.inv()) by {
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

        assume(false);

        assert(new_betree.inv()) by {
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

        assume(false);

        assert(new_betree.inv()) by {
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
}} // end of LikesBetree state machine


} // end of verus!