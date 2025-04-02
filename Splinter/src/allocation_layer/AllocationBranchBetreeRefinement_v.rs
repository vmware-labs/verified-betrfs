// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::{map::*, seq_lib::*, set_lib::*, multiset::*};

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferDisk_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::*;
use crate::allocation_layer::Likes_v::*;
use crate::allocation_layer::LikesBetree_v::*;
use crate::allocation_layer::AllocationBetree_v::*;
use crate::allocation_layer::AllocationBranch_v::*;
use crate::allocation_layer::AllocationBranchBetree_v::*;

verus! {

impl AllocationBranchBetree::Label {
    pub open spec(checked) fn i(self) -> AllocationBetree::Label
    {
        match self {
            Self::Label{linked_lbl} => { AllocationBetree::Label::Label{linked_lbl} }
            Self::Internal{..} =>  { AllocationBetree::Label::Label{linked_lbl: LinkedBetreeVars::Label::Internal{}} }
        }
    }
} // end impl AllocationBranchBetree::Label

impl<T> LinkedBetree<T>{
    proof fn children_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>, ranking: Ranking, start: nat)
    requires 
        self.has_root(),
        self.valid_ranking(ranking),
        self.root == other.root,
        self.dv == other.dv,
        start <= self.root().children.len()
    ensures
        self.children_likes(ranking, start) == other.children_likes(ranking, start)
    decreases self.get_rank(ranking), self.root().children.len() - start
    {
        if start < self.root().children.len() {
            assert(self.root().valid_child_index(start)); // trigger
            self.child_at_idx(start).tree_likes_ignores_buffer_dv(other.child_at_idx(start), ranking);
            self.children_likes_ignores_buffer_dv(other, ranking, start+1);
        }
    }

    proof fn tree_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>, ranking: Ranking)
    requires self.valid_ranking(ranking), self.root == other.root, self.dv == other.dv,
    ensures self.tree_likes(ranking) == other.tree_likes(ranking)
    decreases self.get_rank(ranking)
    {
        if self.has_root() {
            self.children_likes_ignores_buffer_dv(other, ranking, 0);
        }
    }

    proof fn buffer_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>, betree_likes: Likes)
    requires self.dv == other.dv
    ensures self.buffer_likes(betree_likes) == other.buffer_likes(betree_likes)
    decreases betree_likes.len()
    {
        if betree_likes.len() > 0 {
            let addr = betree_likes.choose();
            self.buffer_likes_ignores_buffer_dv(other, betree_likes.remove(addr));
        }
    }

    pub proof fn transitive_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>)
        requires 
            self.acyclic(), 
            self.dv == other.dv,
            self.root == other.root,
        ensures 
            self.transitive_likes() == other.transitive_likes()
    {
        let ranking = self.the_ranking();
        assert(other.valid_ranking(ranking));
        self.tree_likes_ignores_buffer_dv(other, ranking);
        other.tree_likes_ignore_ranking(ranking, other.the_ranking());
        self.buffer_likes_ignores_buffer_dv(other, self.tree_likes(ranking));
    }
}

impl LinkedBetreeVars::State<BranchNode> {
    pub open spec(checked) fn i_buffer_disk(self) -> BufferDisk<SimpleBuffer>
    {
        let (betree_likes, branch_likes) = self.linked.transitive_likes();
        BufferDisk{ 
            entries: Map::new(
                |addr| branch_likes.contains(addr),
                |addr| self.linked.buffer_dv.get_branch(addr).i().i(),
            )
        }
    }

    pub open spec(checked) fn i(self) -> LinkedBetreeVars::State<SimpleBuffer>
    {
        LinkedBetreeVars::State{
            memtable: self.memtable,
            linked: LinkedBetree{
                root: self.linked.root,
                dv: self.linked.dv,
                buffer_dv: self.i_buffer_disk(),
            }
        }
    }

    pub proof fn i_valid(self) 
    requires self.inv()
    ensures 
        self.i().inv(),
        self.linked.transitive_likes() 
        == self.i().linked.transitive_likes(),
    {
        let i_linked = self.i().linked;
        let ranking = self.linked.the_ranking();

        assert(i_linked.valid_ranking(ranking)); // witness
        self.linked.transitive_likes_ignores_buffer_dv(i_linked);

        assert(i_linked.valid_buffer_dv()) by {
            self.linked.tree_likes_domain(ranking);
            self.linked.buffer_likes_domain(self.linked.tree_likes(ranking));
            i_linked.tree_likes_domain(i_linked.the_ranking());
            i_linked.buffer_likes_domain(i_linked.tree_likes(i_linked.the_ranking()));
        }
    }
}

impl AllocationBranchBetree::State { 
    pub open spec(checked) fn i(self) -> AllocationBetree::State
    {
        AllocationBetree::State{
            betree: self.betree.i(),
            betree_aus: self.betree_aus,
            buffer_aus: self.branch_aus,
            compactors: self.compactors,
        }
    }

    proof fn init_refines(self, v: LinkedBetreeVars::State<BranchNode>) 
        requires self.inv(), AllocationBranchBetree::State::initialize(self, v), 
        ensures AllocationBetree::State::initialize(self.i(), v.i()), 
    {
        v.i_valid();
    }

//     proof fn au_likes_noop_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>)
//     requires 
//         pre.inv(),
//         AllocationBetree::State::au_likes_noop(pre, post, lbl, new_betree),
//     ensures
//         post.inv(),
//         LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::likes_noop(new_betree))
//     {
//         reveal(LinkedBetreeVars::State::next);
//         reveal(LinkedBetreeVars::State::next_by);
//         reveal(LikesBetree::State::next_by);
//     }

//     proof fn internal_flush_memtable_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
//         new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs)
//     requires 
//         pre.inv(), 
//         AllocationBetree::State::internal_flush_memtable(pre, post, lbl, new_betree, new_addrs),
//     ensures
//         post.inv(),
//         LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_flush_memtable(new_betree, new_addrs))
//     {
//         reveal(LikesBetree::State::next_by);

//         let pushed = pre.betree.linked.push_memtable(new_betree.memtable.buffer, new_addrs);
//         pre.betree.internal_flush_memtable_aus_ensures(new_betree, new_betree.memtable.buffer, new_addrs);
//         pushed.valid_view_ensures(new_betree.linked);

//         let (pushed_betree_likes, pushed_buffer_likes) = pushed.transitive_likes();
//         LikesBetree::State::push_memtable_likes_ensures(pre.betree, new_betree, new_betree.memtable.buffer, new_addrs);
//         pushed.valid_view_implies_same_transitive_likes(post.betree.linked);

//         pushed.tree_likes_domain(pushed.the_ranking());
//         pushed.buffer_likes_domain(pushed_betree_likes);
//         restrict_domain_au_ensures(pushed_buffer_likes, pushed.buffer_dv.entries);
//         assert(new_betree.linked.valid_buffer_dv());
//     }

//     proof fn internal_grow_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
//         new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address)
//     requires 
//         pre.inv(), 
//         AllocationBetree::State::internal_grow(pre, post, lbl, new_betree, new_root_addr),
//     ensures
//         post.inv(),
//         LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_grow(new_betree, new_root_addr))
//     {
//         reveal(LikesBetree::State::next_by);
//         pre.betree.internal_grow_aus_ensures(new_betree, new_root_addr);
//         LikesBetree::State::grow_likes_ensures(pre.betree, new_betree, new_root_addr);
//     }

//     proof fn internal_split_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
//         new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
//         request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs)
//     requires 
//         pre.inv(), 
//         AllocationBetree::State::internal_split(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs),
//     ensures
//         post.inv(),
//         LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
//             LikesBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs))
//     {
//         reveal(LikesBetree::State::next_by);

//         let (betree_likes, buffer_likes) = pre.betree.linked.transitive_likes();
//         let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);

//         pre.betree.internal_split_aus_ensures(new_betree, path, request, new_addrs, path_addrs);
//         LikesBetree::State::post_split_likes_ensures(pre.betree, new_betree, path, request, new_addrs, path_addrs);

//         let (splitted_betree_likes, splitted_buffer_likes) = splitted.transitive_likes();
//         splitted.valid_view_ensures(new_betree.linked);
//         splitted.valid_view_implies_same_transitive_likes(post.betree.linked);

//         splitted.tree_likes_domain(splitted.the_ranking());
//         splitted.buffer_likes_domain(splitted_betree_likes);
//         restrict_domain_au_ensures(splitted_buffer_likes, splitted.buffer_dv.entries);
//         assert(new_betree.linked.valid_buffer_dv());
//     }

//     proof fn internal_flush_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
//         new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
//         child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
//     requires 
//         pre.inv(), 
//         AllocationBetree::State::internal_flush(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs),
//     ensures
//         post.inv(),
//         LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
//             LikesBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs))
//     {
//         reveal(LikesBetree::State::next_by);
//         let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
//         LikesBetree::State::post_flush_likes_ensures(pre.betree, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);

//         pre.betree.internal_flush_aus_ensures(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
//         let (flushed_betree_likes, flushed_buffer_likes) = flushed.transitive_likes();

//         flushed.valid_view_ensures(new_betree.linked);
//         flushed.valid_view_implies_same_transitive_likes(post.betree.linked);

//         flushed.tree_likes_domain(flushed.the_ranking());
//         flushed.buffer_likes_domain(flushed_betree_likes);
//         restrict_domain_au_ensures(flushed_buffer_likes, flushed.buffer_dv.entries);
//         assert(new_betree.linked.valid_buffer_dv());
//     }

//     proof fn internal_compact_complete_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
//         new_betree: LinkedBetreeVars::State<SimpleBuffer>, input_idx: int, path: Path<SimpleBuffer>, 
//         start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs)
//     requires 
//         pre.inv(), 
//         AllocationBetree::State::internal_compact_complete(pre, post, lbl, input_idx, new_betree, 
//             path, start, end, compacted_buffer, new_addrs, path_addrs),
//     ensures
//         post.inv(),
//         LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
//             LikesBetree::Step::internal_compact(new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs))
//     {
//         reveal(LikesBetree::State::next_by);

//         let (betree_likes, buffer_likes) = pre.betree.linked.transitive_likes();
//         let compacted = LinkedBetreeVars::State::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs);

//         pre.betree.internal_compact_complete_aus_ensures(new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
//         LikesBetree::State::post_compact_likes_ensures(pre.betree, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
        
//         let (compacted_betree_likes, compacted_buffer_likes) = compacted.transitive_likes();
//         compacted.valid_view_ensures(new_betree.linked);
//         compacted.valid_view_implies_same_transitive_likes(post.betree.linked);

//         pre.betree.post_compact_ensures(path, start, end, compacted_buffer, new_addrs, path_addrs);
//         compacted.tree_likes_domain(compacted.the_ranking());
//         compacted.buffer_likes_domain(compacted_betree_likes);
//         restrict_domain_au_ensures(compacted_buffer_likes, compacted.buffer_dv.entries);
//         assert(new_betree.linked.valid_buffer_dv());
//     }

//     proof fn next_refines(pre: Self, post: Self, lbl: AllocationBetree::Label) 
//         requires 
//             pre.inv(),
//             AllocationBetree::State::next(pre, post, lbl),
//         ensures
//             post.inv(),
//             LikesBetree::State::next(pre.i(), post.i(), lbl.i())
//     {
//         reveal(AllocationBetree::State::next);
//         reveal(AllocationBetree::State::next_by);
//         reveal(LikesBetree::State::next);
//         reveal(LikesBetree::State::next_by);

//         match choose |step| AllocationBetree::State::next_by(pre, post, lbl, step) {
//             AllocationBetree::Step::au_likes_noop(new_betree) => { 
//                 Self::au_likes_noop_inv_refines(pre, post, lbl, new_betree);
//             }
//             AllocationBetree::Step::internal_flush_memtable(new_betree, new_addrs) => {
//                 Self::internal_flush_memtable_inv_refines(pre, post, lbl, new_betree, new_addrs);
//             }
//             AllocationBetree::Step::internal_grow(new_betree, new_root_addr) => {
//                 Self::internal_grow_inv_refines(pre, post, lbl, new_betree, new_root_addr);
//             }
//             AllocationBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs) => {
//                 Self::internal_split_inv_refines(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs);
//             }
//             AllocationBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs) => {
//                 Self::internal_flush_inv_refines(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
//             }
//             AllocationBetree::Step::internal_compact_begin(path, start, end, input) => {
//                 assert(LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_noop()));
//             }
//             AllocationBetree::Step::internal_compact_abort(input_idx) => {
//                 assert(LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_noop()));
//             }
//             AllocationBetree::Step::internal_compact_complete(input_idx, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs) => {
//                 Self::internal_compact_complete_inv_refines(pre, post, lbl, new_betree, input_idx, path, start, end, compacted_buffer, new_addrs, path_addrs);
//             }
//             AllocationBetree::Step::internal_buffer_noop(new_betree) => {
//                 pre.betree.linked.valid_view_ensures(new_betree.linked);
//                 pre.betree.linked.valid_view_implies_same_transitive_likes(new_betree.linked);

//                 let (betree_likes, buffer_likes) = pre.betree.linked.transitive_likes();

//                 pre.betree.linked.tree_likes_domain(pre.betree.linked.the_ranking());
//                 pre.betree.linked.buffer_likes_domain(betree_likes);
//                 restrict_domain_au_ensures(buffer_likes, pre.betree.linked.buffer_dv.entries);

//                 assert(post.inv());
//                 assert(LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_buffer_noop(new_betree)));
//             }
//             AllocationBetree::Step::internal_noop() => {
//                 assert(LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_noop()));
//             }
//             _ => { assert(false); }
//         }
//     }
} // end impl AllocationBranchBetree::State

}//verus
