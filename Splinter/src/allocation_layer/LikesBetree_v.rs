// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{prelude::*, seq_lib::*, set::*, set_lib::*, map_lib::*, multiset::*};
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

// singleton is equivalent to seq![]
proof fn singleton_ensures<A>(a: A)
    ensures Multiset::singleton(a) =~= seq![a].to_multiset()
{
    seq![a].to_multiset_ensures();
    assert(seq![a][0] == a);
}

impl SplitAddrs {
    pub open spec(checked) fn likes(self) -> Likes
    {
        Multiset::singleton(self.parent).add(
            Multiset::singleton(self.left).add(
                Multiset::singleton(self.right)
            )
        )
    }
}

impl TwoAddrs {
    pub open spec(checked) fn likes(self) -> Likes
    {
        Multiset::singleton(self.addr1).add(
            Multiset::singleton(self.addr2)
        )
    }
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

    pub open spec(checked) fn transitive_likes(self) -> (Likes, Likes)
    {
        if !self.acyclic() { (arbitrary(), arbitrary()) }
        else {
            let tree_likes = self.tree_likes(self.the_ranking());
            (tree_likes, self.buffer_likes(tree_likes))
        }
    }

    proof fn children_likes_domain(self, ranking: Ranking, start: nat)
        requires 
            self.has_root(),
            self.valid_ranking(ranking),
            start <= self.root().children.len(),
        ensures ({ 
            let children_likes = self.children_likes(ranking, start);
            let reachable_betree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, start);
            &&& children_likes.dom() =~= reachable_betree_addrs
            &&& children_likes.dom() <= self.dv.entries.dom()
            &&& forall |i| start <= i < self.root().children.len()
                ==> #[trigger] self.child_at_idx(i).tree_likes(ranking) <= children_likes
        })
        decreases self.get_rank(ranking), self.root().children.len() - start
    {
        if start == self.root().children.len() {
        } else {
            let reachable_betree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, start);
            assert(self.root().valid_child_index(start)); // trigger
            let child = self.child_at_idx(start);
//            assert(child.valid_ranking(ranking));
            self.child_at_idx_reachable_addrs_ensures(start);
            child.tree_likes_domain(ranking);

            let child_betree_likes = child.tree_likes(ranking);
            let other_betree_likes = self.children_likes(ranking, start+1);
            self.children_likes_domain(ranking, start+1);
            self.reachable_betree_addrs_using_ranking_recur_lemma(ranking, start);
        }
    }

    broadcast proof fn tree_likes_domain(self, ranking: Ranking)
        requires 
            self.valid_ranking(ranking)
        ensures 
            (#[trigger] self.tree_likes(ranking)).dom() =~= self.reachable_betree_addrs_using_ranking(ranking),
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

    proof fn split_node_tree_likes_ensures(self, left: Self, right: Self, ranking: Ranking, start: nat)
        requires 
            self.has_root(),
            left.has_root(),
            right.has_root(),
            self.valid_ranking(ranking),
            left.valid_ranking(ranking),
            right.valid_ranking(ranking),
            self.dv.is_sub_disk(left.dv),
            left.dv == right.dv,
            self.root().children =~= left.root().children + right.root().children,
            start <= self.root().children.len(),
        ensures 
            start < left.root().children.len() ==> 
                self.children_likes(ranking, start) =~= left.children_likes(ranking, start).add(right.children_likes(ranking, 0)),
            start >= left.root().children.len() ==> 
                self.children_likes(ranking, start) =~= right.children_likes(ranking, (start-left.root().children.len()) as nat),
        decreases self.get_rank(ranking), self.root().children.len() - start
    {
        if start == self.root().children.len() {
            return;
        }

        let child = self.child_at_idx(start);
        assert(self.root().valid_child_index(start)); // trigger

        if start < left.root().children.len() {
            let left_child = left.child_at_idx(start);
//            assert(left.root().valid_child_index(start)); // trigger
            child.subdisk_implies_same_tree_likes(left_child, ranking);
            if start == left.root().children.len() - 1 {
                assert(left.children_likes(ranking, start+1) =~= no_likes());
            }
        } else {
            let right_child = right.child_at_idx((start-left.root().children.len()) as nat);
            child.subdisk_implies_same_tree_likes(right_child, ranking);
        }
        self.split_node_tree_likes_ensures(left, right, ranking, start+1);

    }

    proof fn valid_view_implies_same_transitive_likes(self, other: Self)
        requires
            self.acyclic(),
            self.valid_view(other),
        ensures
            self.transitive_likes() == other.transitive_likes()
    {
        let (betree_likes, buffer_likes) = self.transitive_likes();
        let (other_betree_likes, other_buffer_likes) = other.transitive_likes();

        other.subdisk_implies_same_tree_likes(self, self.finite_ranking());
        other.tree_likes_ignore_ranking(self.finite_ranking(), other.the_ranking());
        self.tree_likes_ignore_ranking(self.finite_ranking(), self.the_ranking());

//        assert(betree_likes =~= other_betree_likes);
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
//            assert(total.len() > 0); // NOTE: trigger needed for choose
            let random = total.choose();
            assert(total.contains(random));
            
            let random_buffer_likes = self.dv.entries[random].buffers.likes();
            let sub_buffer_likes = self.buffer_likes(total.remove(random));
//            assert(self.buffer_likes(total) == random_buffer_likes.add(sub_buffer_likes));
//            assert(Multiset::singleton(random).choose() == random);
            assert(Multiset::singleton(random).remove(random) =~= no_likes());
            assert(self.buffer_likes(no_likes()) == no_likes());

            if betree_likes.contains(random) {
                self.buffer_likes_additive(betree_likes.remove(random), delta);
                assert(total.remove(random) == betree_likes.remove(random).add(delta)); // trigger
                self.buffer_likes_additive(betree_likes.remove(random), Multiset::singleton(random));
                assert(betree_likes.remove(random).add(Multiset::singleton(random)) == betree_likes);
            } else {
//                assert(delta.contains(random));
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

    broadcast proof fn subdisk_implies_same_buffer_likes(self, big: Self, betree_likes: Likes)
        requires 
            self.dv.is_sub_disk(big.dv),
            betree_likes.dom() <= self.dv.entries.dom(),
        ensures 
            #[trigger] self.buffer_likes(betree_likes) == #[trigger] big.buffer_likes(betree_likes)
        decreases
            betree_likes.len()
    {
        if betree_likes.len() > 0 {
            let random = betree_likes.choose();
            assert(self.dv.entries.contains_key(random)); // trigger
            assert(big.dv.entries.contains_key(random));  // trigger
//            assert(self.dv.entries[random] == big.dv.entries[random]);
            self.subdisk_implies_same_buffer_likes(big, betree_likes.remove(random));
        }
    }

    proof fn root_buffer_likes_ensures(self)
        requires self.has_root()
        ensures self.buffer_likes(self.root_likes()) == self.root().buffers.likes()
    {
        assert(self.root_likes().remove(self.root.unwrap()) =~= no_likes());
        assert(self.buffer_likes(no_likes()) == no_likes());
        assert(self.buffer_likes(self.root_likes()) =~= self.root().buffers.likes());
    }

    proof fn leaf_likes_is_root_likes(self, ranking: Ranking)
        requires 
            self.has_root(),
            self.root().is_leaf(),
            self.valid_ranking(ranking),
        ensures
            self.tree_likes(ranking) == self.root_likes()
    {
//        assert(self.tree_likes(ranking) == self.root_likes().add(self.children_likes(ranking, 0)));
        assert(self.child_at_idx(0).tree_likes(ranking) =~= no_likes());
        assert(self.children_likes(ranking, 1) =~= no_likes());
        assert(no_likes().add(no_likes()) =~= no_likes());
        assert(self.root_likes().add(no_likes()) =~= self.root_likes());
    }

    proof fn split_parent_children_likes_ensures(self, request: SplitRequest, new_addrs: SplitAddrs, ranking: Ranking, start: nat)
        requires 
            self.valid_ranking(ranking),
            self.can_split_parent(request),
            self.split_parent(request, new_addrs).valid_ranking(ranking),
            start <= self.root().children.len(),
            self.dv.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
        ensures ({
            let result = self.split_parent(request, new_addrs);
            let child_idx = request.get_child_idx();
            let child_root_likes = self.child_at_idx(child_idx).root_likes();
            let new_child_likes = Multiset::singleton(new_addrs.left).add(Multiset::singleton(new_addrs.right));

            &&& start > child_idx 
                ==> result.children_likes(ranking, start+1) == self.children_likes(ranking, start)
            &&& start <= child_idx
                ==> ({
                    &&& child_root_likes <= self.children_likes(ranking, start)
                    &&& result.children_likes(ranking, start) =~= 
                        self.children_likes(ranking, start).sub(child_root_likes).add(new_child_likes)
                })
        })
        decreases self.root().children.len() - start
    {
        if start == self.root().children.len() { return; }
        let result = self.split_parent(request, new_addrs);

        if start == request.get_child_idx() {
            let child = self.child_at_idx(start);
            let left = result.child_at_idx(start);
            let right = result.child_at_idx(start+1);

            assert(result.root().valid_child_index(start)); // trigger
            assert(result.root().valid_child_index(start+1)); // trigger
            assert(result.children_likes(ranking, start+1) == 
                right.tree_likes(ranking).add(result.children_likes(ranking, start+2)));

            if child.root().is_leaf() {
                child.leaf_likes_is_root_likes(ranking);
                left.leaf_likes_is_root_likes(ranking);
                right.leaf_likes_is_root_likes(ranking);
            } else {
                child.split_node_tree_likes_ensures(left, right, ranking, 0);
                assert(self.children_likes(ranking, start) == 
                    child.tree_likes(ranking).add(self.children_likes(ranking, start+1)));
                assert(left.tree_likes(ranking).add(right.tree_likes(ranking)) == 
                    left.root_likes().add(right.root_likes()).add(child.children_likes(ranking, 0))
                );
            }
        } else {
            let idx = if start < request.get_child_idx() { start } else { start + 1 };
            assert(self.root().valid_child_index(start));
//            assert(result.root().valid_child_index(idx));
            self.child_at_idx(start).subdisk_implies_same_tree_likes(result.child_at_idx(idx), ranking);
        }
        self.split_parent_children_likes_ensures(request, new_addrs, ranking, start+1);
    }

    proof fn split_parent_likes_ensures(self, request: SplitRequest, new_addrs: SplitAddrs, ranking: Ranking) 
        requires 
            self.can_split_parent(request),
            self.valid_ranking(ranking),
            self.split_parent(request, new_addrs).valid_ranking(ranking),
            self.dv.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
        ensures ({
            let child = self.child_at_idx(request.get_child_idx());
            let result = self.split_parent(request, new_addrs);

            let added = new_addrs.likes();
            let removed = self.root_likes().add(child.root_likes());
            let add_buffers = child.buffer_likes(child.root_likes());

            &&& removed <= self.tree_likes(ranking)
            &&& result.tree_likes(ranking) 
                == self.tree_likes(ranking).sub(removed).add(added)
            &&& result.buffer_likes(result.tree_likes(ranking))
                == self.buffer_likes(self.tree_likes(ranking)).add(add_buffers)
        })
    {
        let child = self.child_at_idx(request.get_child_idx());
        let result = self.split_parent(request, new_addrs);

        let tree_likes = self.tree_likes(ranking);
        let result_tree_likes = result.tree_likes(ranking);

        let added = new_addrs.likes();
        let removed = self.root_likes().add(child.root_likes());

        self.split_parent_children_likes_ensures(request, new_addrs, ranking, 0);
        assert(result_tree_likes =~= tree_likes.sub(removed).add(added));

        let add_buffers = child.buffer_likes(child.root_likes());
        assert(
            result.buffer_likes(result_tree_likes) 
            =~= self.buffer_likes(tree_likes).add(add_buffers)
        ) by {
            self.tree_likes_domain(ranking);
            result.tree_likes_domain(ranking);

            self.buffer_likes_additive(tree_likes.sub(removed), removed);
            assert(tree_likes.sub(removed).add(removed) =~= tree_likes);
            result.buffer_likes_additive(tree_likes.sub(removed), added);
            self.subdisk_implies_same_buffer_likes(result, tree_likes.sub(removed));
//            assert(self.buffer_likes(tree_likes.sub(removed)) == result.buffer_likes(tree_likes.sub(removed)));

            assert(
                self.buffer_likes(removed).add(add_buffers) == 
                result.buffer_likes(result.root_likes()).add(add_buffers).add(add_buffers)
            ) by {
                self.buffer_likes_additive(self.root_likes(), child.root_likes());
                self.root_buffer_likes_ensures();
                result.root_buffer_likes_ensures();
                child.subdisk_implies_same_buffer_likes(self, child.root_likes());
//                assert(self.buffer_likes(self.root_likes()) == result.buffer_likes(result.root_likes()));
//                assert(self.buffer_likes(removed) == self.buffer_likes(self.root_likes()).add(add_buffers));
            }

            assert(
                result.buffer_likes(added) =~= 
                result.buffer_likes(result.root_likes()).add(add_buffers).add(add_buffers)
            ) by {
                let result_left = result.child_at_idx(request.get_child_idx());
                let result_right = result.child_at_idx(request.get_child_idx()+1);

                child.root_buffer_likes_ensures();
                result_left.root_buffer_likes_ensures();
                result_right.root_buffer_likes_ensures();

                result_left.subdisk_implies_same_buffer_likes(result, result_left.root_likes());
                result_right.subdisk_implies_same_buffer_likes(result, result_right.root_likes());

                result.buffer_likes_additive(result.root_likes(), result_left.root_likes());
                result.buffer_likes_additive(result.root_likes().add(result_left.root_likes()), result_right.root_likes());
                assert(result.root_likes().add(result_left.root_likes()).add(result_right.root_likes()) == added);
            }
        }
    }

    proof fn subtree_buffer_likes_composition(self, other: Self, subtree: Self, other_subtree: Self, ranking: Ranking, sub_delta: Likes, add_delta: Likes)
    requires 
        self.acyclic(),
        other.acyclic(),
        subtree.valid_ranking(ranking),
        other_subtree.valid_ranking(ranking),
        subtree.dv.is_sub_disk(self.dv),
        other_subtree.dv.is_sub_disk(other.dv),
        subtree.tree_likes(ranking) 
            <= self.tree_likes(self.the_ranking()),
        other_subtree.tree_likes(ranking)
            <= other.tree_likes(other.the_ranking()),
        sub_delta <= subtree.buffer_likes(subtree.tree_likes(ranking)),
        other_subtree.buffer_likes(other_subtree.tree_likes(ranking))
            == subtree.buffer_likes(subtree.tree_likes(ranking)).sub(sub_delta).add(add_delta),
        other.buffer_likes(other.tree_likes(other.the_ranking()).sub(other_subtree.tree_likes(ranking)))
            == self.buffer_likes(self.tree_likes(self.the_ranking()).sub(subtree.tree_likes(ranking))) 
    ensures ({
        let tree_likes = self.tree_likes(self.the_ranking());
        let other_tree_likes = other.tree_likes(other.the_ranking());
        &&& other.buffer_likes(other_tree_likes) ==  self.buffer_likes(tree_likes).sub(sub_delta).add(add_delta)
    }) {
        let subtree_likes = subtree.tree_likes(ranking);
        let other_subtree_likes = other_subtree.tree_likes(ranking);

        let tree_likes = self.tree_likes(self.the_ranking());
        let other_tree_likes = other.tree_likes(other.the_ranking());

        broadcast use 
            LinkedBetree::subdisk_implies_same_buffer_likes,
            LinkedBetree::tree_likes_domain
        ;

//        assert(self.buffer_likes(subtree_likes) == subtree.buffer_likes(subtree_likes));
//        assert(other.buffer_likes(other_subtree_likes) == other_subtree.buffer_likes(other_subtree_likes));

        assert(tree_likes.sub(subtree_likes).add(subtree_likes) == tree_likes); // trigger
        assert(other_tree_likes.sub(other_subtree_likes).add(other_subtree_likes) == other_tree_likes); // trigger

        self.buffer_likes_additive(tree_likes.sub(subtree_likes), subtree_likes);
        other.buffer_likes_additive(other_tree_likes.sub(other_subtree_likes), other_subtree_likes);

//        assert(other.buffer_likes(other_tree_likes) == 
//            other.buffer_likes(other_tree_likes.sub(other_subtree_likes)).add(other.buffer_likes(other_subtree_likes))); 

//        assert(other.buffer_likes(other_tree_likes) == 
//            self.buffer_likes(tree_likes.sub(subtree_likes)).add(self.buffer_likes(subtree_likes).sub(sub_delta).add(add_delta))); 
        
        assert(other.buffer_likes(other_tree_likes) == 
            self.buffer_likes(tree_likes.sub(subtree_likes)).add(self.buffer_likes(subtree_likes)).sub(sub_delta).add(add_delta)); 

//        assert(self.buffer_likes(tree_likes) == 
//            self.buffer_likes(tree_likes.sub(subtree_likes)).add(self.buffer_likes(subtree_likes)));
    }
 
    proof fn flush_parent_children_likes_ensures(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, ranking: Ranking, start: nat) 
        requires 
            self.can_flush(child_idx, buffer_gc),
            self.valid_ranking(ranking),
            self.flush(child_idx, buffer_gc, new_addrs).valid_ranking(ranking),
            self.dv.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
            start <= self.root().children.len(),
        ensures ({
            let result = self.flush(child_idx, buffer_gc, new_addrs);
            let child_root_likes = self.child_at_idx(child_idx).root_likes();
            let new_child_root_likes = Multiset::singleton(new_addrs.addr2);

            &&& start > child_idx 
                ==> result.children_likes(ranking, start) == self.children_likes(ranking, start)
            &&& start <= child_idx
                ==> ({
                    &&& child_root_likes <= self.children_likes(ranking, start)
                    &&& result.children_likes(ranking, start) =~= 
                        self.children_likes(ranking, start).sub(child_root_likes).add(new_child_root_likes)
                })
        })
        decreases self.root().children.len() - start
    {
        if start == self.root().children.len() { return; }

        let result = self.flush(child_idx, buffer_gc, new_addrs);
        assert(self.root().valid_child_index(start));
        assert(result.root().valid_child_index(start));

        let child = self.child_at_idx(start);
        let result_child = result.child_at_idx(start);

        if start == child_idx {
            child.subdisk_implies_same_children_likes(result_child, ranking, 0);
//            assert(child.children_likes(ranking, 0) == result_child.children_likes(ranking, 0));
            assert(self.children_likes(ranking, start) == 
                child.tree_likes(ranking).add(self.children_likes(ranking, start+1))); // trigger
            assert(result.children_likes(ranking, start) == 
                result_child.tree_likes(ranking).add(result.children_likes(ranking, start+1)));
        } else {
            child.subdisk_implies_same_tree_likes(result_child, ranking);
        }
        self.flush_parent_children_likes_ensures(child_idx, buffer_gc, new_addrs, ranking, start+1);
    }

    proof fn flush_parent_likes_ensures(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, ranking: Ranking) 
        requires 
            self.can_flush(child_idx, buffer_gc),
            self.valid_ranking(ranking),
            self.flush(child_idx, buffer_gc, new_addrs).valid_ranking(ranking),
            self.dv.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
        ensures ({
            let child = self.child_at_idx(child_idx);
            let result = self.flush(child_idx, buffer_gc, new_addrs);
            let removed = self.root_likes().add(child.root_likes());

            let discard_buffers = self.root().buffers.slice(0, buffer_gc as int).addrs.to_multiset(); // gced buffers in parent
            let add_buffers = self.flush_buffers(child_idx, buffer_gc).addrs.to_multiset();  // newly flushed to child

            &&& removed <= self.tree_likes(ranking)
            &&& result.tree_likes(ranking) 
                == self.tree_likes(ranking).sub(removed).add(new_addrs.likes())
            &&& discard_buffers <= self.buffer_likes(self.tree_likes(ranking))
            &&& result.buffer_likes(result.tree_likes(ranking))
                == self.buffer_likes(self.tree_likes(ranking)).sub(discard_buffers).add(add_buffers)
        })
    {
        let child = self.child_at_idx(child_idx);
        let result = self.flush(child_idx, buffer_gc, new_addrs);
        let removed = self.root_likes().add(child.root_likes());

        self.flush_parent_children_likes_ensures(child_idx, buffer_gc, new_addrs, ranking, 0);
        assert(result.tree_likes(ranking) =~= self.tree_likes(ranking).sub(removed).add(new_addrs.likes()));  

        let gc_slice = self.root().buffers.slice(0, buffer_gc as int);
        let discard_buffers = gc_slice.addrs.to_multiset(); // gced buffers in parent
        let add_buffers = self.flush_buffers(child_idx, buffer_gc).addrs.to_multiset();  // newly flushed to child

        let flush_upto = self.root().buffers.len(); 
        assert(buffer_gc <= flush_upto) by {
            let i = child_idx as int;
            assert(self.root().flushed.update(i, flush_upto).offsets[i] == flush_upto);
        }

        assert(gc_slice.addrs + result.root().buffers.addrs == self.root().buffers.addrs);
        lemma_multiset_commutative(gc_slice.addrs, result.root().buffers.addrs);
//        assert(discard_buffers <= self.root().buffers.addrs.to_multiset());

//        assert(self.tree_likes(ranking) == self.root_likes().add(self.children_likes(ranking, 0)));
        self.root_buffer_likes_ensures();
        self.tree_likes_domain(ranking);
        self.buffer_likes_additive(self.root_likes(), self.children_likes(ranking, 0));
//        assert(discard_buffers <= self.buffer_likes(self.tree_likes(ranking)));

        assert(result.buffer_likes(result.tree_likes(ranking))
            =~= self.buffer_likes(self.tree_likes(ranking)).sub(discard_buffers).add(add_buffers))
        by {
            broadcast use LinkedBetree::subdisk_implies_same_buffer_likes;

            self.tree_likes_domain(ranking);
            result.tree_likes_domain(ranking);

//            assert(result.tree_likes(ranking) == result.root_likes().add(result.children_likes(ranking, 0)));
            result.buffer_likes_additive(result.root_likes(), result.children_likes(ranking, 0));

            result.root_buffer_likes_ensures();
//            assert(result.buffer_likes(result.root_likes()) == self.buffer_likes(self.root_likes()).sub(discard_buffers));

            let new_child_root_likes = Multiset::singleton(new_addrs.addr2);
//            assert(result.children_likes(ranking, 0) 
//                == self.children_likes(ranking, 0).sub(child.root_likes()).add(new_child_root_likes));

            result.buffer_likes_additive(self.children_likes(ranking, 0).sub(child.root_likes()), new_child_root_likes);

//            assert(result.buffer_likes(result.children_likes(ranking, 0))
//                == result.buffer_likes(self.children_likes(ranking, 0).sub(child.root_likes())).add(
//                    result.buffer_likes(new_child_root_likes))
//            );
 
            // assert(result.buffer_likes(result.tree_likes(ranking))
            //     == self.buffer_likes(self.root_likes()).sub(discard_buffers).add(
            //         self.buffer_likes(self.children_likes(ranking, 0).sub(child.root_likes())).add(
            //         result.buffer_likes(new_child_root_likes)))
            // );

            // assert(result.buffer_likes(result.tree_likes(ranking))
            //     == self.buffer_likes(self.root_likes()).add(
            //         self.buffer_likes(self.children_likes(ranking, 0).sub(child.root_likes()))
            //         ).sub(discard_buffers).add(result.buffer_likes(new_child_root_likes))
            // );

            assert(result.buffer_likes(new_child_root_likes) == self.buffer_likes(child.root_likes()).add(add_buffers)) by {
                let result_child = result.child_at_idx(child_idx);
//                assert(child.root().buffers.addrs + self.flush_buffers(child_idx, buffer_gc).addrs == result_child.root().buffers.addrs);
                lemma_multiset_commutative(child.root().buffers.addrs, self.flush_buffers(child_idx, buffer_gc).addrs);
                child.root_buffer_likes_ensures();
                result_child.root_buffer_likes_ensures();
            }

            assert(self.children_likes(ranking, 0) =~= self.children_likes(ranking, 0).sub(child.root_likes()).add(child.root_likes())); // trigger
            self.buffer_likes_additive(self.children_likes(ranking, 0).sub(child.root_likes()), child.root_likes());

//            assert(result.buffer_likes(result.tree_likes(ranking))
//                == self.buffer_likes(self.root_likes()).add(
//                    self.buffer_likes(self.children_likes(ranking, 0).sub(child.root_likes()))
//                    ).add(self.buffer_likes(child.root_likes())).sub(discard_buffers).add(add_buffers)
//            );

//            assert(result.buffer_likes(result.tree_likes(ranking)) == self.buffer_likes(self.root_likes()
//                    ).add(self.buffer_likes(self.children_likes(ranking, 0))).sub(discard_buffers).add(add_buffers)
//            );
        }
    }

    proof fn substitute_children_likes_ensures(self, other: Self, ranking: Ranking, updated_idx: nat, start: nat)
        requires 
            self.has_root(),
            other.has_root(),
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.dv.is_sub_disk(other.dv),
            self.root().children.len() == other.root().children.len(),
            self.root().valid_child_index(updated_idx),
            forall |i| 0 <= i < self.root().children.len() && i != updated_idx
                ==> self.root().children[i] == other.root().children[i],
            start <= self.root().children.len(),
        ensures ({
            let updated = self.child_at_idx(updated_idx);
            let other_updated = other.child_at_idx(updated_idx);
            let children_likes = self.children_likes(ranking, start);
            let other_children_likes = other.children_likes(ranking, start);

            &&& start > updated_idx ==> ({
                &&& other_children_likes == children_likes
            })
            &&& start <= updated_idx ==> ({
                &&& updated.tree_likes(ranking) <= children_likes
                &&& other_updated.tree_likes(ranking) <= other_children_likes
                &&& children_likes.sub(updated.tree_likes(ranking)) 
                    =~= other_children_likes.sub(other_updated.tree_likes(ranking))
                })
            })
        decreases self.root().children.len() - start
    {
        if start == self.root().children.len() {
            return;
        }

        let child = self.child_at_idx(start);
        let other_child = other.child_at_idx(start);
        assert(self.root().valid_child_index(start));

        if start > updated_idx {
            child.subdisk_implies_same_tree_likes(other_child, ranking);
        } else if start < updated_idx {
            child.subdisk_implies_same_tree_likes(other_child, ranking);

            let updated = self.child_at_idx(updated_idx);
            let other_updated = other.child_at_idx(updated_idx);

            self.children_likes_domain(ranking, start+1);
            other.children_likes_domain(ranking, start+1);

//            assert(self.children_likes(ranking, start).sub(updated.tree_likes(ranking))
//                == child.tree_likes(ranking).add(self.children_likes(ranking, start+1).sub(updated.tree_likes(ranking)))
//            );
            assert(other.children_likes(ranking, start).sub(other_updated.tree_likes(ranking))
                == other_child.tree_likes(ranking).add(other.children_likes(ranking, start+1).sub(other_updated.tree_likes(ranking)))
            );
        } 
        self.substitute_children_likes_ensures(other, ranking, updated_idx, start+1);
    }
}

impl <T: Buffer> LinkedBetree<T> {
    proof fn compact_likes_ensures(self, start: nat, end: nat, compacted_buffer: T, new_addrs: TwoAddrs, ranking: Ranking) 
    requires 
        self.can_compact(start, end, compacted_buffer),
        self.valid_ranking(ranking),
        self.compact(start, end, compacted_buffer, new_addrs).valid_ranking(ranking),
        self.dv.is_fresh(new_addrs.repr()),
        new_addrs.no_duplicates(),
    ensures ({
        let result = self.compact(start, end, compacted_buffer, new_addrs);
        let discard_buffers = self.root().buffers.slice(start as int, end as int).addrs.to_multiset(); // gced buffers in parent
        let add_buffers = Multiset::singleton(new_addrs.addr2);

        &&& result.tree_likes(ranking) 
            == self.tree_likes(ranking).sub(self.root_likes()).add(result.root_likes()) // addr1
        &&& discard_buffers <= self.buffer_likes(self.tree_likes(ranking))
        &&& result.buffer_likes(result.tree_likes(ranking))
            == self.buffer_likes(self.tree_likes(ranking)).sub(discard_buffers).add(add_buffers)
    })
    {
        let result = self.compact(start, end, compacted_buffer, new_addrs);
        self.subdisk_implies_same_children_likes(result, ranking, 0);

        assert(result.tree_likes(ranking) 
            == self.tree_likes(ranking).sub(self.root_likes()).add(result.root_likes()));

        let up_to_end = self.root().buffers.slice(0, end as int).addrs;
        let past_end = self.root().buffers.slice(end as int, self.root().buffers.len() as int).addrs;

        assert(up_to_end + past_end == self.root().buffers.addrs);
        lemma_multiset_commutative(up_to_end, past_end);
//        assert(up_to_end.to_multiset() <= self.root().buffers.addrs.to_multiset());
        
        let up_to_start = self.root().buffers.slice(0, start as int).addrs;
        let discard_addrs = self.root().buffers.slice(start as int, end as int).addrs; // gced buffers in parent

        assert(up_to_start + discard_addrs == up_to_end);
        lemma_multiset_commutative(up_to_start, discard_addrs);

        let discard_buffers = discard_addrs.to_multiset(); // gced buffers in parent
//        assert(discard_buffers <= up_to_end.to_multiset());
//        assert(discard_buffers <= self.root().buffers.addrs.to_multiset());
        self.root_buffer_likes_ensures();

//        assert(discard_buffers <= self.buffer_likes(self.root_likes()));

        self.tree_likes_domain(ranking);
//        assert(self.tree_likes(ranking) == self.root_likes().add(self.children_likes(ranking, 0)));
        self.buffer_likes_additive(self.root_likes(), self.children_likes(ranking, 0));

//        assert(discard_buffers <= self.buffer_likes(self.tree_likes(ranking)));
//        assert(self.children_likes(ranking, 0) == result.children_likes(ranking, 0));

        let add_buffers = Multiset::singleton(new_addrs.addr2);
        assert(result.root().buffers.likes() == self.root().buffers.likes().sub(discard_buffers).add(add_buffers))
        by {
            let result_addrs = result.root().buffers.addrs;
            let addrs = self.root().buffers.addrs;

//            assert(addrs.to_multiset().sub(discard_buffers) == past_end.to_multiset().add(up_to_start.to_multiset()));
            assert(result_addrs == up_to_start.push(new_addrs.addr2) + past_end);

            to_multiset_build(up_to_start, new_addrs.addr2); 
//            assert(up_to_start.push(new_addrs.addr2).to_multiset() == up_to_start.to_multiset().add(add_buffers));
            lemma_multiset_commutative(up_to_start.push(new_addrs.addr2), past_end);

//            assert(result_addrs.to_multiset() == up_to_start.to_multiset().add(past_end.to_multiset()).add(add_buffers));
            assert(result_addrs.to_multiset() == addrs.to_multiset().sub(discard_buffers).add(add_buffers));
        }
        result.root_buffer_likes_ensures();

        result.buffer_likes_additive(result.root_likes(), result.children_likes(ranking, 0));
        self.subdisk_implies_same_buffer_likes(result, self.children_likes(ranking, 0));

        assert(result.buffer_likes(result.tree_likes(ranking))
            =~= self.buffer_likes(self.tree_likes(ranking)).sub(discard_buffers).add(add_buffers));
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
        require LinkedBetreeVars::State::internal_flush_memtable(pre.betree, 
            new_betree, lbl->linked_lbl, new_betree.memtable.buffer, new_betree.linked, new_addrs);
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
        let discard_betree = path.addrs_on_path().to_multiset().add(path.target().root_likes()).add(old_child.root_likes());
        let add_betree = path_addrs.to_multiset().add(new_addrs.likes());
        let new_betree_likes = pre.betree_likes.sub(discard_betree).add(add_betree);

        let add_buffers = old_child.buffer_likes(old_child.root_likes());
        let new_buffer_likes = pre.buffer_likes.add(add_buffers);

        // likes level requirement that new betree must contain all live betree addresses
        require new_betree_likes.dom() <= new_betree.linked.dv.entries.dom();
        require pre.buffer_likes.dom() <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_likes = new_betree_likes;
        update buffer_likes = new_buffer_likes;
    }}
    
    transition!{ internal_flush(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {        
        require LinkedBetreeVars::State::internal_flush(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr() + path_addrs.to_set());

        let old_parent = path.target();
        let old_child = old_parent.child_at_idx(child_idx);
        let discard_betree = path.addrs_on_path().to_multiset().add(old_parent.root_likes()).add(old_child.root_likes());
        let add_betree = path_addrs.to_multiset().add(new_addrs.likes());
        let new_betree_likes = pre.betree_likes.sub(discard_betree).add(add_betree);

        let discard_buffers = old_parent.root().buffers.slice(0, buffer_gc as int).addrs.to_multiset(); // gced buffers
        let add_buffers = old_parent.flush_buffers(child_idx, buffer_gc).addrs.to_multiset();  // newly flushed to child
        let new_buffer_likes = pre.buffer_likes.sub(discard_buffers).add(add_buffers);

        // likes level requirement that new betree must contain all live betree addresses
        require new_betree_likes.dom() <= new_betree.linked.dv.entries.dom();
        require new_buffer_likes.dom() <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_likes = new_betree_likes;
        update buffer_likes = new_buffer_likes;
    }}

    transition!{ internal_compact(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require LinkedBetreeVars::State::internal_compact(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, start, end, compacted_buffer, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr().union(path_addrs.to_set()));

        let discard_betree = path.addrs_on_path().to_multiset().add(path.target().root_likes());
        let add_betree = path_addrs.to_multiset().insert(new_addrs.addr1);
        let new_betree_likes = pre.betree_likes.sub(discard_betree).add(add_betree);

        let discard_buffers = path.target().root().buffers.slice(start as int, end as int).addrs.to_multiset();
        let add_buffers = Multiset::singleton(new_addrs.addr2);
        let new_buffer_likes = pre.buffer_likes.sub(discard_buffers).add(add_buffers);

        // likes level requirement that new betree must contain all live betree addresses
        require new_betree_likes.dom() <= new_betree.linked.dv.entries.dom();
        require new_buffer_likes.dom() <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_likes = new_betree_likes;
        update buffer_likes = new_buffer_likes;
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

    pub proof fn internal_flush_memtable_satisfies_strong_step(pre: Self, post: Self, lbl: Label, 
        new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs) -> (istep: LinkedBetreeVars::Step<SimpleBuffer>)
        requires 
            pre.inv(),
            Self::internal_flush_memtable(pre, post, lbl, new_betree, new_addrs),
        ensures 
            pre.betree.strong_step(istep),
            LinkedBetreeVars::State::next_by(pre.betree, post.betree, lbl->linked_lbl, istep)
    {
        reveal(LinkedBetreeVars::State::next_by);

        let buffer = pre.betree.memtable.buffer;
        let pushed = pre.betree.linked.push_memtable(buffer, new_addrs);
        pre.betree.linked.push_memtable_ensures(buffer, new_addrs);

        let ranking = pre.betree.linked.the_ranking();
        let pushed_ranking = pre.betree.linked.push_memtable_new_ranking(buffer, new_addrs, ranking);

        broadcast use 
            LinkedBetree::reachable_betree_addrs_ignore_ranking, 
            LinkedBetree::tree_likes_ignore_ranking;

        new_betree.linked.dv.subdisk_implies_ranking_validity(pushed.dv, pushed_ranking);
        assert(new_betree.linked.valid_ranking(pushed_ranking)); // trigger

        pushed.agreeable_disks_same_reachable_betree_addrs(new_betree.linked, pushed_ranking);
        new_betree.linked.same_reachable_betree_addrs_implies_same_buffer_addrs(pushed);
        new_betree.linked.reachable_betree_addrs_using_ranking_closed(pushed_ranking);

        pre.betree.linked.tree_likes_domain(pushed_ranking);
        pre.betree.linked.buffer_likes_domain(pre.betree_likes);

        return LinkedBetreeVars::Step::internal_flush_memtable(new_betree.memtable.buffer, new_betree.linked, new_addrs);
    }

    #[inductive(internal_flush_memtable)]
    #[verifier::spinoff_prover]
    fn internal_flush_memtable_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs) { 
        let buffer = pre.betree.memtable.buffer;
        let pushed = pre.betree.linked.push_memtable(buffer, new_addrs);

        assert(new_betree.inv()) by {
            let linked_step = Self::internal_flush_memtable_satisfies_strong_step(pre, post, lbl, new_betree, new_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }

        let ranking = pre.betree.linked.the_ranking();
        let pushed_ranking = pre.betree.linked.push_memtable_new_ranking(buffer, new_addrs, ranking);

        broadcast use 
            LinkedBetree::reachable_betree_addrs_ignore_ranking, 
            LinkedBetree::children_likes_ignore_ranking, 
            LinkedBetree::tree_likes_ignore_ranking;

        pushed.valid_view_implies_same_transitive_likes(post.betree.linked);
//        assert(post.betree.linked.transitive_likes() == pushed.transitive_likes());
        
        pre.betree.linked.tree_likes_domain(pushed_ranking);
        pre.betree.linked.buffer_likes_domain(pre.betree_likes);

        let (betree_likes, buffer_likes) = post.betree.linked.transitive_likes();
        if pre.betree.linked.has_root() {
            pre.betree.linked.subdisk_implies_same_children_likes(pushed, pushed_ranking, 0);
            assert(betree_likes =~= post.betree_likes);

            pre.betree.linked.subdisk_implies_same_buffer_likes(pushed, pre.betree_likes);
//            assert(betree_likes.contains(new_addrs.addr1));
            pushed.tree_buffers_are_closed(post.betree_likes, new_addrs.addr1);
            
//            assert(pushed.root().buffers.addrs =~= pre.betree.linked.root().buffers.addrs + seq![new_addrs.addr2]); // trigger
//            assert(pushed.root().buffers.addrs[pushed.root().buffers.len() as int - 1] == new_addrs.addr2); // trigger
            pushed.root().buffers.addrs.to_multiset_ensures();
            pre.betree.linked.root().buffers.addrs.to_multiset_ensures();

            assert(pre.betree.linked.root().buffers.addrs.push(new_addrs.addr2) =~= pushed.root().buffers.addrs);
//            assert(pushed.root().buffers.likes().contains(new_addrs.addr2));
//            assert(pushed.root().buffers.likes() =~= pre.betree.linked.root().buffers.likes().insert(new_addrs.addr2));
//            assert(buffer_likes.contains(new_addrs.addr2));
//            assert(post.betree_likes == pre.betree_likes.sub(pre.betree.linked.root_likes()).add(pushed.root_likes()));

            let pre_sub = pre.betree_likes.sub(pre.betree.linked.root_likes());
            let post_sub = post.betree_likes.sub(pushed.root_likes());
            assert(pre_sub =~= post_sub);

            pre.betree.linked.subdisk_implies_same_buffer_likes(pushed, pre_sub);
            pre.betree.linked.buffer_likes_additive(pre_sub, pre.betree.linked.root_likes());
            pushed.buffer_likes_additive(post_sub, pushed.root_likes());

            assert(pre_sub.add(pre.betree.linked.root_likes()) =~= pre.betree_likes);
//            assert(pre.buffer_likes =~= pre.betree.linked.buffer_likes(pre_sub).add(pre.betree.linked.buffer_likes(pre.betree.linked.root_likes())));
//            assert(post_sub.add(pushed.root_likes()) =~= post.betree_likes);

            pushed.buffer_likes_additive(post_sub, pushed.root_likes());
            let pre_root = pre.betree.linked.root_likes().choose();
            let _ = pre.betree.linked.buffer_likes(pre.betree.linked.root_likes().remove(pre_root)); // trigger

            let pushed_root = pushed.root_likes().choose();
            let _ = pushed.buffer_likes(pushed.root_likes().remove(pushed_root));

//            assert(buffer_likes =~= pre.buffer_likes.insert(new_addrs.addr2));
            assert(buffer_likes =~= post.buffer_likes); // relating the difference
        } else {
//            assert(pre.betree_likes =~= no_likes());
            // note: manual unrolling
            assert(pushed.children_likes(pushed_ranking, 1) =~= no_likes());
            assert(pushed.child_at_idx(0).tree_likes(pushed_ranking) =~= no_likes());
//            assert(pushed.children_likes(pushed_ranking, 0) =~= no_likes());
            assert(post.betree_likes =~= betree_likes);

            let pushed_root = pushed.root_likes().choose();
            let _ = pushed.buffer_likes(pushed.root_likes().remove(pushed_root));

//            assert(pushed.buffer_likes(pushed.root_likes()) =~= pushed.root().buffers.likes());
            assert(post.betree_likes =~= pushed.root_likes());

            let empty = seq![];
            empty.to_multiset_ensures();
            assert(empty.to_multiset() =~= no_likes());

//            assert(buffer_likes == pushed.buffer_likes(pushed.root_likes()));
            pushed.root().buffers.addrs.to_multiset_ensures();
//            assert(pushed.root().buffers.addrs =~= seq![new_addrs.addr2]);
//            assert(pushed.root().buffers.likes() =~= Multiset::singleton(new_addrs.addr2));
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
//        assert(child.tree_likes(ranking) == pre.betree.linked.tree_likes(ranking));
//        assert(child.tree_likes(ranking) == pre.betree_likes);

        assert(new_betree.linked.children_likes(ranking, 1) =~= no_likes());
//        assert(new_betree.linked.children_likes(ranking, 0) =~= pre.betree_likes);

//        assert(new_betree.linked.tree_likes(ranking) == betree_likes);
//        assert(new_betree.linked.tree_likes(ranking) == pre.betree_likes.insert(new_root_addr));
        assert(betree_likes =~= post.betree_likes);

        new_betree.linked.tree_likes_domain(ranking);
        pre.betree.linked.tree_likes_domain(ranking);

        assert(new_betree.linked.buffer_likes(Multiset::singleton(new_root_addr)) =~= no_likes())
        by {
//            assert(new_betree.linked.root().buffers == LinkedSeq::empty());
            new_betree.linked.root().buffers.addrs.to_multiset_ensures();
//            assert(new_betree.linked.root().buffers.likes() =~= no_likes());
            assert(new_betree.linked.buffer_likes(Multiset::singleton(new_root_addr).remove(new_root_addr)) == no_likes());
        }

        new_betree.linked.buffer_likes_additive(pre.betree_likes, Multiset::singleton(new_root_addr));
//        assert(buffer_likes =~= new_betree.linked.buffer_likes(pre.betree_likes));
        pre.betree.linked.subdisk_implies_same_buffer_likes(new_betree.linked, pre.betree_likes);
        assert(post.buffer_likes == buffer_likes);
    }

    pub proof fn internal_split_satisfies_strong_step(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) -> (istep: LinkedBetreeVars::Step<SimpleBuffer>)
        requires 
            pre.inv(),
            Self::internal_split(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs),
        ensures 
            pre.betree.strong_step(istep),
            LinkedBetreeVars::State::next_by(pre.betree, post.betree, lbl->linked_lbl, istep)
    {
        reveal(LinkedBetreeVars::State::next_by);

        let ranking = pre.betree.linked.the_ranking();
        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        pre.betree.post_split_ensures(path, request, new_addrs, path_addrs);

        assert(splitted.reachable_buffers_preserved(new_betree.linked)) by {
            pre.betree.linked.tree_likes_domain(ranking);
            pre.betree.linked.buffer_likes_domain(pre.betree_likes);
//            assert(pre.betree.linked.reachable_buffer_addrs() == pre.buffer_likes.dom());
//            assert(splitted.reachable_buffer_addrs() <= pre.betree.linked.reachable_buffer_addrs());
//            assert(splitted.reachable_buffer_addrs() <= new_betree.linked.buffer_dv.repr());
        }

        return LinkedBetreeVars::Step::internal_split(new_betree.linked, path, request, new_addrs, path_addrs);
    }

    #[inductive(internal_split)]
    #[verifier::spinoff_prover]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {

        assert(new_betree.inv()) by {
            let linked_step = Self::internal_split_satisfies_strong_step(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }

        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        pre.betree.post_split_ensures(path, request, new_addrs, path_addrs);

        assert(splitted.transitive_likes() == (post.betree_likes, post.buffer_likes)) by {
            let subtree = path.target();            
            let new_subtree = subtree.split_parent(request, new_addrs);
            let ranking = pre.betree.linked.the_ranking();

            path.target_ensures();
            path.valid_ranking_throughout(ranking);
//            assert(new_subtree.acyclic());

            let child = subtree.child_at_idx(request.get_child_idx());
            let removed = subtree.root_likes().add(child.root_likes());
            let add_buffers = child.buffer_likes(child.root_likes());

            let finite_ranking = pre.betree.linked.finite_ranking();
            let split_ranking = subtree.split_new_ranking(request, new_addrs, finite_ranking);
            subtree.split_parent_likes_ensures(request, new_addrs, split_ranking);

            let subtree_likes = subtree.tree_likes(split_ranking);
            let new_subtree_likes = new_subtree.tree_likes(split_ranking);

            // substitute 

            let splitted_likes = splitted.tree_likes(splitted.the_ranking());
            let old_path_likes = path.addrs_on_path().to_multiset();
            let new_path_likes = path_addrs.to_multiset();

            path.substitute_likes_ensures(new_subtree, path_addrs, split_ranking);
            pre.betree.linked.tree_likes_ignore_ranking(split_ranking, ranking);

            assert(splitted_likes =~= post.betree_likes) by {
                path_addrs.to_multiset_ensures();
//                assert(removed.is_disjoint_from(new_path_likes));
                assert(splitted_likes == splitted_likes.sub(new_subtree_likes).add(new_subtree_likes));
//                assert(new_subtree_likes == subtree_likes.sub(removed).add(new_addrs.likes()));
//                assert(splitted_likes == pre.betree_likes.sub(old_path_likes).add(new_path_likes).sub(subtree_likes).add(new_subtree_likes));
//                assert(splitted_likes == pre.betree_likes.sub(old_path_likes).sub(removed).add(new_path_likes).add(new_addrs.likes()));
            }

            assert(splitted.buffer_likes(splitted_likes) == pre.buffer_likes.add(add_buffers)) by {
                path.substitute_ensures(new_subtree, path_addrs);
//                assert(subtree_likes <= pre.betree_likes);
//                assert(new_subtree_likes <= splitted_likes);
//                assert(no_likes() <= subtree.buffer_likes(subtree_likes));
                assert(subtree.buffer_likes(subtree_likes).sub(no_likes()).add(add_buffers) 
                    == subtree.buffer_likes(subtree_likes).add(add_buffers));
//                assert(new_subtree.buffer_likes(new_subtree_likes) == subtree.buffer_likes(subtree_likes).add(add_buffers));
                pre.betree.linked.subtree_buffer_likes_composition(splitted, subtree, 
                    new_subtree, split_ranking, no_likes(), add_buffers);
                assert(pre.buffer_likes.sub(no_likes()).add(add_buffers) == pre.buffer_likes.add(add_buffers));
            }
        }
        splitted.valid_view_implies_same_transitive_likes(new_betree.linked);
    }

    pub proof fn internal_flush_satisfies_strong_step(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) -> (istep: LinkedBetreeVars::Step<SimpleBuffer>)
        requires 
            pre.inv(),
            Self::internal_flush(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs),
            new_betree.linked.transitive_likes() == (post.betree_likes, post.buffer_likes),
        ensures 
            pre.betree.strong_step(istep),
            LinkedBetreeVars::State::next_by(pre.betree, post.betree, lbl->linked_lbl, istep)
    {
        reveal(LinkedBetreeVars::State::next_by);
        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        pre.betree.post_flush_ensures(path, child_idx, buffer_gc, new_addrs, path_addrs);

        flushed.valid_view_implies_same_transitive_likes(new_betree.linked);
        flushed.tree_likes_domain(flushed.the_ranking());
        flushed.buffer_likes_domain(post.betree_likes);

        return LinkedBetreeVars::Step::internal_flush(new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs);
    }
   
    #[inductive(internal_flush)]
    fn internal_flush_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {

        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        pre.betree.post_flush_ensures(path, child_idx, buffer_gc, new_addrs, path_addrs);

        assert(flushed.transitive_likes() == (post.betree_likes, post.buffer_likes)) by {
            let subtree = path.target();
            let new_subtree = path.target().flush(child_idx, buffer_gc, new_addrs);
            let ranking = pre.betree.linked.the_ranking();

            path.target_ensures();
            path.valid_ranking_throughout(ranking);
//            assert(new_subtree.acyclic());

            let child = subtree.child_at_idx(child_idx);
            let removed = subtree.root_likes().add(child.root_likes());

            let finite_ranking = pre.betree.linked.finite_ranking();
            let flush_ranking = subtree.flush_new_ranking(child_idx, buffer_gc, new_addrs, finite_ranking);

            subtree.flush_parent_likes_ensures(child_idx, buffer_gc, new_addrs, flush_ranking);

            let subtree_likes = subtree.tree_likes(flush_ranking);
            let new_subtree_likes = new_subtree.tree_likes(flush_ranking);

            let discard_buffers = subtree.root().buffers.slice(0, buffer_gc as int).addrs.to_multiset(); // gced buffers
            let add_buffers = subtree.flush_buffers(child_idx, buffer_gc).addrs.to_multiset();  // newly flushed to child
        
//            assert(new_subtree_likes == subtree_likes.sub(removed).add(new_addrs.likes()));
//            assert(new_subtree.buffer_likes(new_subtree_likes) 
//                == subtree.buffer_likes(subtree_likes).sub(discard_buffers).add(add_buffers));

            // substitute 

            let flushed_likes = flushed.tree_likes(flushed.the_ranking());
            let old_path_likes = path.addrs_on_path().to_multiset();
            let new_path_likes = path_addrs.to_multiset();

            path.substitute_likes_ensures(new_subtree, path_addrs, flush_ranking);
            pre.betree.linked.tree_likes_ignore_ranking(flush_ranking, ranking);

            assert(flushed_likes =~= post.betree_likes) by {
                assert(flushed_likes == flushed_likes.sub(new_subtree_likes).add(new_subtree_likes));
//                assert(flushed_likes == pre.betree_likes.sub(old_path_likes).add(new_path_likes).sub(subtree_likes).add(new_subtree_likes));
//                assert(flushed_likes == pre.betree_likes.sub(old_path_likes).sub(removed).add(new_path_likes).add(new_addrs.likes()));
            }

            assert(flushed.buffer_likes(flushed_likes) == post.buffer_likes) by {
                path.substitute_ensures(new_subtree, path_addrs);
//                assert(subtree_likes <= pre.betree_likes);
//                assert(new_subtree_likes <= flushed_likes);
                pre.betree.linked.subtree_buffer_likes_composition(flushed, subtree, new_subtree, flush_ranking, discard_buffers, add_buffers);
            }
        }

        flushed.valid_view_implies_same_transitive_likes(new_betree.linked);
        assert(new_betree.inv()) by {
            let linked_step = Self::internal_flush_satisfies_strong_step(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        }
    }

    pub proof fn internal_compact_satisfies_strong_step(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) -> (istep: LinkedBetreeVars::Step<SimpleBuffer>)
        requires 
            pre.inv(),
            Self::internal_compact(pre, post, lbl, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs),
            new_betree.linked.transitive_likes() == (post.betree_likes, post.buffer_likes),
        ensures 
            pre.betree.strong_step(istep),
            LinkedBetreeVars::State::next_by(pre.betree, post.betree, lbl->linked_lbl, istep)
    {
        reveal(LinkedBetreeVars::State::next_by);
        let compacted = LinkedBetreeVars::State::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs);
        pre.betree.post_compact_ensures(path, start, end, compacted_buffer, new_addrs, path_addrs);

        compacted.valid_view_implies_same_transitive_likes(new_betree.linked);
        compacted.tree_likes_domain(compacted.the_ranking());
        compacted.buffer_likes_domain(post.betree_likes);

        return LinkedBetreeVars::Step::internal_compact(new_betree.linked, path, start, end, compacted_buffer, new_addrs, path_addrs);
    }

    #[inductive(internal_compact)]
    fn internal_compact_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) { 

        let ranking = pre.betree.linked.the_ranking();
        let compacted = LinkedBetreeVars::State::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs);
        pre.betree.post_compact_ensures(path, start, end, compacted_buffer, new_addrs, path_addrs);

        assert(compacted.transitive_likes() == (post.betree_likes, post.buffer_likes)) by {
            let subtree = path.target();
            let new_subtree = path.target().compact(start, end, compacted_buffer, new_addrs);

            path.target_ensures();
            path.valid_ranking_throughout(ranking);

            let finite_ranking = pre.betree.linked.finite_ranking();
            let compact_ranking = subtree.compact_new_ranking(start, end, compacted_buffer, new_addrs, finite_ranking);

            subtree.compact_likes_ensures(start, end, compacted_buffer, new_addrs, compact_ranking);

            let subtree_likes = subtree.tree_likes(compact_ranking);
            let new_subtree_likes = new_subtree.tree_likes(compact_ranking);
            let compacted_likes = compacted.tree_likes(compacted.the_ranking());

            path.substitute_likes_ensures(new_subtree, path_addrs, compact_ranking);
            pre.betree.linked.tree_likes_ignore_ranking(compact_ranking, ranking);

            assert(compacted_likes == compacted_likes.sub(new_subtree_likes).add(new_subtree_likes));
            assert(compacted_likes =~= post.betree_likes);

            assert(compacted.buffer_likes(compacted_likes) == post.buffer_likes) by {
                path.substitute_ensures(new_subtree, path_addrs);
//                assert(subtree_likes <= pre.betree_likes);
//                assert(new_subtree_likes <= compacted_likes);

                let discard_buffers = path.target().root().buffers.slice(start as int, end as int).addrs.to_multiset();
                let add_buffers = Multiset::singleton(new_addrs.addr2);
                pre.betree.linked.subtree_buffer_likes_composition(compacted, subtree, new_subtree, compact_ranking, discard_buffers, add_buffers);
            }
        }

        compacted.valid_view_implies_same_transitive_likes(new_betree.linked);
        assert(new_betree.inv()) by {
            let linked_step = Self::internal_compact_satisfies_strong_step(pre, post, lbl, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
            LinkedBetreeVars::State::inv_next_by(pre.betree, new_betree, lbl->linked_lbl, linked_step);
        } 
    }
   
    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, betree: LinkedBetreeVars::State<SimpleBuffer>) {}
}} // end of LikesBetree state machine

impl<T: Buffer> Path<T>{
    #[verifier::spinoff_prover]
    proof fn substitute_likes_ensures(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs, ranking: Ranking)
        requires
            self.linked.valid_ranking(ranking),
            self.can_substitute(replacement, path_addrs), 
            self.ranking_for_substitution(replacement, path_addrs, ranking),
            path_addrs.no_duplicates(),
            replacement.is_fresh(path_addrs.to_set()),
            self.linked.dv.is_fresh(set![replacement.root.unwrap()])
        ensures ({
            let result = self.substitute(replacement, path_addrs);
            let result_likes = result.tree_likes(result.the_ranking());
            let replacement_likes = replacement.tree_likes(ranking);
            let target_likes = self.target().tree_likes(ranking);
            let old_path_likes = self.addrs_on_path().to_multiset();
            let new_path_likes = path_addrs.to_multiset();

            &&& result.acyclic()
            &&& replacement_likes <= result_likes
            &&& new_path_likes <= result_likes
            &&& old_path_likes <= self.linked.tree_likes(ranking)
            &&& target_likes <= self.linked.tree_likes(ranking).sub(old_path_likes)
            &&& result_likes.sub(replacement_likes) == 
                self.linked.tree_likes(ranking).sub(old_path_likes).sub(target_likes).add(new_path_likes)
            &&& result.buffer_likes(new_path_likes) == self.linked.buffer_likes(old_path_likes)
            &&& result.buffer_likes(result_likes.sub(replacement_likes)) == 
                self.linked.buffer_likes(self.linked.tree_likes(ranking).sub(target_likes))
        })
        decreases self.depth
    {
        let result = self.substitute(replacement, path_addrs);
        let s_ranking = self.ranking_after_substitution(replacement, path_addrs, ranking);

        let result_likes = result.tree_likes(result.the_ranking());
        let replacement_likes = replacement.tree_likes(ranking);
        let target_likes = self.target().tree_likes(ranking);
        let old_path_likes = self.addrs_on_path().to_multiset();
        let new_path_likes = path_addrs.to_multiset();

        broadcast use LinkedBetree::tree_likes_ignore_ranking;
        path_addrs.to_multiset_ensures();
        self.addrs_on_path().to_multiset_ensures();

        if self.depth > 0 {
            let node = self.linked.root();
            let r = node.pivots.route(self.key) as nat;
            node.pivots.route_lemma(self.key);

            let subtree = self.subpath().linked;
            let new_subtree = self.subpath().substitute(replacement, path_addrs.subrange(1, path_addrs.len() as int));
            let new_children = node.children.update(node.pivots.route(self.key), new_subtree.root);

            self.substitute_ensures(replacement, path_addrs);
            self.subpath().substitute_ensures(replacement, path_addrs.subrange(1, path_addrs.len() as int));
//            assert(result.root().children == new_children);

            let subtree_likes = subtree.tree_likes(s_ranking);
            let new_subtree_likes = new_subtree.tree_likes(s_ranking);

            new_subtree.dv.subdisk_implies_ranking_validity(result.dv, s_ranking);
            new_subtree.subdisk_implies_same_tree_likes(result.child_at_idx(r), s_ranking);
//            assert(new_subtree_likes == result.child_at_idx(r).tree_likes(s_ranking));

//            assert(self.linked.dv.is_sub_disk(result.dv));
            self.linked.substitute_children_likes_ensures(result, s_ranking, r, 0);

//            assert(result.children_likes(s_ranking, 0).sub(new_subtree_likes)
//                == self.linked.children_likes(s_ranking, 0).sub(subtree_likes));

            self.valid_ranking_throughout(ranking);
            self.subpath().substitute_likes_ensures(replacement, path_addrs.subrange(1, path_addrs.len() as int), ranking);

//            assert(result_likes == result.tree_likes(s_ranking));

            // GOAL: replacement_likes <= result_likes
            assert(new_subtree.valid_ranking(s_ranking));
//            assert(replacement_likes <= new_subtree.tree_likes(new_subtree.the_ranking()));
//            assert(replacement_likes <= new_subtree.tree_likes(s_ranking));
//            assert(result.child_at_idx(r).tree_likes(s_ranking) <= result_likes);
//            assert(replacement_likes <= result_likes);

            // GOAL: old_path_likes <= self.linked.tree_likes(ranking)
            //       target_likes <= self.linked.tree_likes(ranking).sub(old_path_likes)
            let old_sub_path_likes = self.subpath().addrs_on_path().to_multiset();
            let new_sub_path_likes = path_addrs.subrange(1, path_addrs.len() as int).to_multiset();

            self.subpath().addrs_on_path().to_multiset_ensures();
            assert(old_path_likes =~= self.linked.root_likes().add(old_sub_path_likes)) by {
                singleton_ensures(self.linked.root.unwrap());
//                assert(seq![self.linked.root.unwrap()] + self.subpath().addrs_on_path() =~= self.addrs_on_path());
                lemma_multiset_commutative(seq![self.linked.root.unwrap()], self.subpath().addrs_on_path());
            }

//            assert(old_sub_path_likes <= subtree.tree_likes(ranking));
            self.linked.children_likes_domain(ranking, 0);
//            assert(subtree.tree_likes(ranking) <= self.linked.tree_likes(ranking));
//            assert(old_path_likes <= self.linked.tree_likes(ranking));
//            assert(target_likes <= self.linked.tree_likes(ranking).sub(old_path_likes));

            // GOAL: result_likes.sub(replacement_likes) =~= 
            //       self.linked.tree_likes(ranking).sub(old_path_likes).add(new_path_likes).sub(target_likes)})
            assert(subtree.valid_ranking(s_ranking)); // trigger
//            assert(new_subtree_likes.sub(replacement_likes)
//                =~= subtree_likes.sub(old_sub_path_likes).add(new_sub_path_likes).sub(target_likes)
//            );

            assert(new_path_likes =~= result.root_likes().add(new_sub_path_likes)) by {
                singleton_ensures(result.root.unwrap());
                assert(seq![result.root.unwrap()] + path_addrs.subrange(1, path_addrs.len() as int) =~= path_addrs);
                lemma_multiset_commutative(seq![result.root.unwrap()], path_addrs.subrange(1, path_addrs.len() as int));
            }

            assert(result_likes.sub(replacement_likes) == self.linked.tree_likes(ranking).sub(old_path_likes).sub(target_likes).add(new_path_likes))
            by {
//                assert(result_likes == result.root_likes().add(result.children_likes(s_ranking, 0)));
//                assert(self.linked.tree_likes(ranking) == self.linked.root_likes().add(self.linked.children_likes(ranking, 0)));

                assert(result_likes.sub(replacement_likes) == 
                    self.linked.children_likes(s_ranking, 0).sub(subtree_likes).add(
                        subtree_likes.sub(old_sub_path_likes).sub(target_likes).add(new_sub_path_likes).add(result.root_likes()))
                );

//                assert(result_likes.sub(replacement_likes) == 
//                    self.linked.root_likes().add(self.linked.children_likes(s_ranking, 0)).sub(old_path_likes).sub(target_likes).add(new_path_likes)
//                );
                assert(self.linked.valid_ranking(s_ranking)); // trigger
                assert(result_likes.sub(replacement_likes) =~= 
                    self.linked.tree_likes(ranking).sub(old_path_likes).sub(target_likes).add(new_path_likes));
            }

            // buffer GOALs
            assert(result.buffer_likes(new_path_likes) =~= self.linked.buffer_likes(old_path_likes)) by {
//                assert(new_subtree.buffer_likes(new_sub_path_likes) == subtree.buffer_likes(old_sub_path_likes));
//                assert(new_subtree.valid_ranking(s_ranking)); // trigger
//                assert(new_sub_path_likes <= new_subtree_likes);
                new_subtree.tree_likes_domain(s_ranking);
    
//                assert(subtree.valid_ranking(ranking));
//                assert(old_sub_path_likes <= subtree.tree_likes(ranking));

                subtree.tree_likes_domain(ranking);
                subtree.subdisk_implies_same_buffer_likes(self.linked, old_sub_path_likes);
                new_subtree.subdisk_implies_same_buffer_likes(result, new_sub_path_likes);

//                assert(result.buffer_likes(new_sub_path_likes) == self.linked.buffer_likes(old_sub_path_likes));
                result.root_buffer_likes_ensures();
                self.linked.root_buffer_likes_ensures();
//                assert(result.buffer_likes(result.root_likes()) =~= self.linked.buffer_likes(self.linked.root_likes()));
    
                result.buffer_likes_additive(result.root_likes(), new_sub_path_likes);
                self.linked.buffer_likes_additive(self.linked.root_likes(), old_sub_path_likes);    
            }

            assert(result.buffer_likes(result_likes.sub(replacement_likes)) =~= 
                self.linked.buffer_likes(self.linked.tree_likes(ranking).sub(target_likes))) 
            by {
//                assert(
//                    self.linked.tree_likes(ranking).sub(old_path_likes).sub(target_likes).add(new_path_likes) == 
//                    self.linked.tree_likes(ranking).sub(target_likes).sub(old_path_likes).add(new_path_likes)
//                );

                assert(result_likes.sub(replacement_likes) 
                    == self.linked.tree_likes(ranking).sub(target_likes).sub(old_path_likes).add(new_path_likes));

                self.linked.tree_likes_domain(ranking);
//                assert(self.linked.dv.is_sub_disk(result.dv));
                assert(self.linked.tree_likes(ranking).dom() <= result.dv.entries.dom());
                result.buffer_likes_additive(self.linked.tree_likes(ranking).sub(target_likes).sub(old_path_likes), new_path_likes);

//                assert(result.buffer_likes(result_likes.sub(replacement_likes)) =~= 
//                    result.buffer_likes(self.linked.tree_likes(ranking).sub(target_likes).sub(old_path_likes)
//                    ).add(result.buffer_likes(new_path_likes)));

                self.linked.subdisk_implies_same_buffer_likes(result, old_path_likes);
                
//                assert(result.buffer_likes(result_likes.sub(replacement_likes)) =~= 
//                    result.buffer_likes(self.linked.tree_likes(ranking).sub(target_likes).sub(old_path_likes)
//                    ).add(result.buffer_likes(old_path_likes)));

                result.buffer_likes_additive(self.linked.tree_likes(ranking).sub(target_likes).sub(old_path_likes), old_path_likes);

                assert(self.linked.tree_likes(ranking).sub(target_likes) =~= 
                    self.linked.tree_likes(ranking).sub(target_likes).sub(old_path_likes).add(old_path_likes));

                self.linked.subdisk_implies_same_buffer_likes(result, self.linked.tree_likes(ranking).sub(target_likes));
            }
        }  else {
            assert(result_likes.sub(replacement_likes) =~= 
            self.linked.tree_likes(ranking).sub(old_path_likes).sub(target_likes).add(new_path_likes));
        }
    }
}

} // end of verus!
