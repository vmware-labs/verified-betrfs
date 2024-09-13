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
}

impl<T> LinkedBetree<T> {
    // children likes vs buffer likes
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

    // returns betree likes & buffer likes
    pub open spec fn children_tree_likes(self, ranking: Ranking, start: nat) -> Likes
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
            let child_betree_likes = self.child_at_idx(start).transitive_tree_likes_internal(ranking);
            let other_betree_likes = self.children_tree_likes(ranking, start+1);
            child_betree_likes.add(other_betree_likes)
        }
    }

    pub open spec(checked) fn transitive_tree_likes_internal(self, ranking: Ranking) -> Likes
        recommends self.valid_ranking(ranking)
        decreases self.get_rank(ranking)
    {
        if !self.has_root() { no_likes() } 
        else {
            let children_betree_likes  = self.children_tree_likes(ranking, 0);
            self.root_betree_likes().add(children_betree_likes)
        }
    }

    // returns betree likes and buffer likes
    pub open spec(checked) fn transitive_likes(self) -> (Likes, Likes)
    {
        if !self.acyclic() { (arbitrary(), arbitrary()) }
        else { 
            let tree_likes = self.transitive_tree_likes_internal(self.the_ranking());
            (tree_likes, self.buffer_likes(tree_likes)) 
        }
    }

    // returns betree likes & buffer likes
    // pub open spec fn children_likes(self, ranking: Ranking, start: nat) -> (Likes, Likes)
    //     recommends 
    //         self.has_root(),
    //         self.valid_ranking(ranking),
    //         start <= self.root().children.len()
    //     decreases 
    //         self.get_rank(ranking), 0nat, self.root().children.len()-start 
    //         when ({
    //             &&& start <= self.root().children.len()
    //             &&& self.root().valid_child_index(start) ==> 
    //                 self.child_at_idx(start).get_rank(ranking) < self.get_rank(ranking)
    //         })
    // {
    //     if start == self.root().children.len() {
    //         (no_likes(), no_likes())
    //     } else {
    //         let (child_betree_likes, child_buffer_likes) = self.child_at_idx(start).transitive_likes_internal(ranking);
    //         let (other_betree_likes, other_buffer_likes) = self.children_likes(ranking, start+1);
    //         (child_betree_likes.add(other_betree_likes), child_buffer_likes.add(other_buffer_likes))
    //     }
    // }

    pub open spec(checked) fn root_betree_likes(self) -> Likes
    {
        if self.has_root() {
            Multiset::singleton(self.root.unwrap())
        } else {
            no_likes()
        }
    }

    // pub open spec(checked) fn transitive_likes_internal(self, ranking: Ranking) -> (Likes, Likes)
    //     recommends self.valid_ranking(ranking)
    //     decreases self.get_rank(ranking)
    // {
    //     if !self.has_root() { ( no_likes(), no_likes() ) } 
    //     else {
    //         let (children_betree_likes, children_buffer_likes) = self.children_likes(ranking, 0);
    //         let betree_likes = self.root_betree_likes().add(children_betree_likes);
    //         let buffer_likes = self.root().buffers.likes().add(children_buffer_likes);
    //         (betree_likes, buffer_likes)
    //     }
    // }

    // returns betree likes and buffer likes
    // pub open spec(checked) fn transitive_likes(self) -> (Likes, Likes)
    // {
    //     if !self.acyclic() { (arbitrary(), arbitrary()) }
    //     else { self.transitive_likes_internal(self.the_ranking()) }
    // }

    spec fn reachable_buffer_from(self, ranking: Ranking, 
        addr: Address, buffer_addr: Address, from: nat) -> bool
        recommends self.valid_ranking(ranking), from <= self.root().children.len(), 
    {
        &&& self.reachable_betree_addrs_using_ranking_recur(ranking, from).contains(addr)
        &&& self.dv.get(Some(addr)).buffers.contains(buffer_addr)
    }

    proof fn children_likes_domain(self, ranking: Ranking, start: nat)
        requires 
            self.has_root(),
            self.valid_ranking(ranking),
            start <= self.root().children.len(),
        ensures ({
            let reachable_betree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, start);
            let reachable_buffer_addrs = Set::new(|buffer_addr| exists |addr| 
                #[trigger] self.reachable_buffer_from(ranking, addr, buffer_addr, start));
            &&& self.children_likes(ranking, start).0.dom() =~= reachable_betree_addrs
            &&& self.children_likes(ranking, start).1.dom() =~= reachable_buffer_addrs 
        })
        decreases self.get_rank(ranking), self.root().children.len() - start
    {
        if start == self.root().children.len() {
        } else {
            let reachable_betree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, start);
            let reachable_buffer_addrs = Set::new(|buffer_addr| exists |addr| 
                #[trigger] self.reachable_buffer_from(ranking, addr, buffer_addr, start));
    
            assert(self.root().valid_child_index(start)); // trigger
            let child = self.child_at_idx(start);
            assert(child.valid_ranking(ranking));
            self.child_at_idx_reachable_addrs_ensures(start);
            child.transitive_likes_internal_domain(ranking);

            let (child_betree_likes, child_buffer_likes) = child.transitive_likes_internal(ranking);
            let (other_betree_likes, other_buffer_likes) = self.children_likes(ranking, start+1);
            self.children_likes_domain(ranking, start+1);
            self.reachable_betree_addrs_using_ranking_recur_lemma(ranking, start);

            let sub_reachable_buffer_addrs = Set::new(|buffer_addr| exists |addr| 
                #[trigger] self.reachable_buffer_from(ranking, addr, buffer_addr, start+1));

            assert forall |buffer| reachable_buffer_addrs.contains(buffer) <==> 
                (child_buffer_likes.contains(buffer) || other_buffer_likes.contains(buffer))
            by {
                broadcast use LinkedBetree::reachable_betree_addrs_ignore_ranking;
                if reachable_buffer_addrs.contains(buffer) {
                    let addr = choose |addr| #[trigger] self.reachable_buffer_from(ranking, addr, buffer, start);
                    if child_betree_likes.contains(addr) {
                        assert(child.reachable_buffer(addr, buffer)); // trigger
                        assert(child.reachable_buffer_addrs().contains(buffer)); // trigger
                    } else {
                        assert(self.reachable_buffer_from(ranking, addr, buffer, start+1)); // trigger
                        assert(sub_reachable_buffer_addrs.contains(buffer)); // trigger
                        assert(other_buffer_likes.contains(buffer));
                    }
                }

                if child_buffer_likes.contains(buffer) {
                    let addr = choose |addr| child.reachable_buffer(addr, buffer);
                    assert(child.reachable_buffer_addrs().contains(buffer)); // trigger
                    assert(self.reachable_buffer_from(ranking, addr, buffer, start));
                    assert(reachable_buffer_addrs.contains(buffer));
                } else if other_buffer_likes.contains(buffer) {
                    assert(sub_reachable_buffer_addrs.contains(buffer)); // trigger
                    let addr = choose |addr| #[trigger] self.reachable_buffer_from(ranking, addr, buffer, start+1);
                    assert(self.reachable_buffer_from(ranking, addr, buffer, start));
                    assert(reachable_betree_addrs.contains(addr));
                }
            }
        }
    }

    proof fn transitive_likes_internal_domain(self, ranking: Ranking)
        requires 
            self.valid_ranking(ranking)
        ensures 
            self.transitive_likes_internal(ranking).0.dom() =~= self.reachable_betree_addrs_using_ranking(ranking),
            self.transitive_likes_internal(ranking).1.dom() =~= self.reachable_buffer_addrs(),
        decreases self.get_rank(ranking)
    {
        if self.has_root() {
            let (_, children_buffer_likes) = self.children_likes(ranking, 0);
            self.children_likes_domain(ranking, 0);

            let reachable_buffers = self.reachable_buffer_addrs();
            let buffer_likes = self.transitive_likes_internal(ranking).1;
            self.reachable_betree_addrs_ignore_ranking(self.the_ranking(), ranking);

            assert forall |buffer| reachable_buffers.contains(buffer) <==> buffer_likes.contains(buffer)
            by {
                self.root().buffers.addrs.to_multiset_ensures();
                if reachable_buffers.contains(buffer) {
                    let addr = choose |addr| self.reachable_buffer(addr, buffer);
                    if addr != self.root.unwrap() {
                        assert(self.reachable_buffer_from(ranking, addr, buffer, 0)); // trigger
                        assert(self.children_likes(ranking, 0).1.dom().contains(buffer)); // trigger
                    } else {
                        assert(self.root().buffers.likes().contains(buffer));
                    }
                }
                if buffer_likes.contains(buffer) {
                    if self.root().buffers.likes().contains(buffer) {
                        assert(self.reachable_buffer(self.root.unwrap(), buffer)); // trigger
                    } else {
                        let addr = choose |addr| self.reachable_buffer_from(ranking, addr, buffer, 0);
                        assert(self.children_likes(ranking, 0).1.dom().contains(buffer)); // trigger
                        assert(self.reachable_buffer(addr, buffer));  // trigger
                    }
                }
            }
        }
    }

    broadcast proof fn children_likes_ignore_ranking(self, r1: Ranking, r2: Ranking, start: nat)
        requires 
            self.has_root(),
            self.valid_ranking(r1),
            self.valid_ranking(r2),
            start <= self.root().children.len()
        ensures 
            self.children_likes(r1, start).0 =~= self.children_likes(r2, start).0,
            self.children_likes(r1, start).1 =~= self.children_likes(r2, start).1,
        decreases 
            self.get_rank(r1), self.root().children.len()-start
    {
        if start < self.root().children.len() {
            broadcast use LinkedBetree::reachable_betree_addrs_ignore_ranking;
            let child = self.child_at_idx(start);
            assert(self.root().valid_child_index(start));
            child.transitive_likes_internal_ignore_ranking(r1, r2);
            self.children_likes_ignore_ranking(r1, r2, start+1);
        }
    }

    broadcast proof fn transitive_likes_internal_ignore_ranking(self, r1: Ranking, r2: Ranking) 
        requires 
            self.valid_ranking(r1),
            self.valid_ranking(r2),
        ensures 
            self.transitive_likes_internal(r1).0 =~= self.transitive_likes_internal(r2).0,
            self.transitive_likes_internal(r1).1 =~= self.transitive_likes_internal(r2).1,
        decreases 
            self.get_rank(r1)
    {
        if self.has_root() {
            self.children_likes_ignore_ranking(r1, r2, 0);
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
        // &&& self.betree_likes.dom().disjoint(addrs)
        // &&& self.buffer_likes.dom().disjoint(addrs)
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

        let discard_betree = pre.betree.linked.root_betree_likes();
        let add_betree = new_betree.linked.root_betree_likes();

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

        let ranking = pre.betree.linked.the_ranking();
        let pushed = pre.betree.linked.push_memtable(pre.betree.memtable, new_addrs);
        let pushed_ranking = pre.betree.linked.push_memtable_new_ranking(pre.betree.memtable, new_addrs, ranking);

        broadcast use LinkedBetree::reachable_betree_addrs_ignore_ranking, LinkedBetree::children_likes_ignore_ranking, LinkedBetree::transitive_likes_internal_ignore_ranking;

        assert(pushed.valid_ranking(pushed_ranking)); 
        assume(pushed.valid_buffer_dv());

        new_betree.linked.dv.subdisk_implies_ranking_validity(pushed.dv, pushed_ranking);
        assert(pushed.valid_view(new_betree.linked));
        assert(new_betree.linked.valid_ranking(pushed_ranking));

        pushed.agreeable_disks_same_reachable_betree_addrs(new_betree.linked, pushed_ranking);

        assert(new_betree.linked.reachable_betree_addrs() == pushed.reachable_betree_addrs());
        new_betree.linked.same_reachable_betree_addrs_implies_same_buffer_addrs(pushed);
        assert(new_betree.linked.reachable_buffer_addrs() == pushed.reachable_buffer_addrs());

        new_betree.linked.reachable_betree_addrs_using_ranking_closed(pushed_ranking);
        assert(new_betree.linked.reachable_betree_addrs() <= new_betree.linked.dv.entries.dom());

        assert(post.buffer_likes.dom() <= new_betree.linked.buffer_dv.repr());

        pre.betree.linked.transitive_likes_internal_domain(pushed_ranking);
        pre.betree.linked.transitive_likes_internal_ignore_ranking(ranking, pushed_ranking);

        assert(pre.betree.linked.reachable_buffer_addrs() == pre.buffer_likes.dom()); 

        // but how do we show the increase 
        // one way is to look at buffer_likes of pushed 
        // and reason about what happens to the domain and the buffer likes of pushed
        // it should actually be easy to do because they should have a unit of 1

        // how might this be changed in the future?
        // we know about betree likes when betree likes 

        // right now the only reference we are adding 
        // how do we prove this
        // substitute preserves buffer likes 
        // substitute makes strict edits to transitive likes

        // betree likes => if we do a clone, we added references to a full subtree
        
        // buffer likes = all the outgoing references 
        // is this the right way of tracking it? a dag edge means that more than local changes are appearing at once
        // to represent this tracking 
        // one way to say is that it's fine bc betree is the index and can be stored this way

        assert(post.buffer_likes.dom() =~= pre.buffer_likes.dom() + set![new_addrs.addr2]);
        assert(post.buffer_likes.dom() =~= pre.betree.linked.reachable_buffer_addrs() + set![new_addrs.addr2]);        

        // if we look at just this then we can't 
        // need to reason about reachable buffer addrs
        // we can say this about pushed 
        assume(pushed.reachable_buffer_addrs() == pre.betree.linked.reachable_buffer_addrs() + set![new_addrs.addr2]);

        // post.buffer likes is old plus 1 
        assert(post.buffer_likes.dom() == new_betree.linked.reachable_buffer_addrs());

        // when modifying this what can you say about the transitive likes
        assert(pushed.same_tight_tree(new_betree.linked));
        let linked_step = LinkedBetreeVars::Step::internal_flush_memtable(new_betree.memtable, new_betree.linked, new_addrs);
        LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);

        // TODO: transitive likes on same tightness buddies
        assume(post.betree.linked.transitive_likes() == pushed.transitive_likes());

        let (betree_likes, buffer_likes) = post.betree.linked.transitive_likes();
        assert(post.betree.linked.acyclic()); // ok this much we do know

        // betree likes 
        let root_likes = post.betree.linked.root_betree_likes();
        assert(post.buffer_likes == pre.buffer_likes.insert(new_addrs.addr2)); //true?
        pushed.root().buffers.addrs.to_multiset_ensures(); // TODO(pain)

        if pre.betree.linked.has_root() {
            assume(pushed.children_likes(pushed_ranking, 0) =~= pre.betree.linked.children_likes(pushed_ranking, 0));

            assert(betree_likes =~= post.betree_likes);

            // buffers is somehow the harder thing to prove?
            assert(buffer_likes =~= post.buffer_likes);

        } else {
            // TODO: prove empty node children likes property 
            assume(pushed.children_likes(pushed_ranking, 0).0 =~= no_likes());
            assume(pushed.children_likes(pushed_ranking, 0).1 =~= no_likes());

            assert(betree_likes =~= post.betree_likes);
            assert(pushed.root().buffers.likes() =~= no_likes().insert(pushed.root().buffers[0]));
            assert(buffer_likes =~= post.buffer_likes);
        }


        // let memtable_buffer = LinkedSeq{ addrs: seq![new_addrs.addr2],};
        // let new_root = 
        //     if self.has_root() {
        //         self.root().extend_buffer_seq(memtable_buffer)
        //     } else {
        //         BetreeNode::empty_root(total_domain()).extend_buffer_seq(memtable_buffer)
        //     };

        // let new_dv = self.dv.modify_disk(new_addrs.addr1, new_root);
        // let new_buffer_dv = self.buffer_dv.modify_disk(new_addrs.addr2, memtable.buffer);
        // LinkedBetree{ root: Some(new_addrs.addr1), dv: new_dv, buffer_dv: new_buffer_dv }

        // this part assumes post and pushed have the same transitive like

        // need to prove that new_betree.likes_betree dom()
        // same tight tree isn't the same

        // we know this much
        // but the same tight tree requirement is on the overall tree 


        // ok but what about the other 
        // is this a circular dependency?

        // pushed -> new_betree same reachable 
        // same tight tree => same transitive likes 
        // and then we just need to show that operations
        // starting at the tree results in xyz changes to transitive likes
        // same tight tree implies same transitive likes 
    }
   
    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) { 
        reveal(LinkedBetreeVars::State::next_by);
        assert(new_betree.inv()) by {
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