// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::map::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::Memtable_v::*;
// use crate::betree::BufferSeq_v;
use crate::betree::LinkedBufferSeq_v;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::FilteredBetree_v;
use crate::betree::FilteredBetree_v::FilteredBetree;
use crate::betree::LinkedBetree_v::*;
use crate::betree::SplitRequest_v::*;

verus! {

pub type LinkedBufferSeq = LinkedBufferSeq_v::BufferSeq;

impl DiskView{
    pub open spec(checked) fn fresh_ranking_extension(self, r1: Ranking, r2: Ranking) -> bool
    {
        &&& r1 <= r2
        &&& forall |addr| #![auto] !r1.contains_key(addr) && r2.contains_key(addr) ==> !self.entries.contains_key(addr)
    }

    pub proof fn subdisk_implies_ranking_validity(self, big: DiskView, ranking: Ranking)
        requires self.wf(), self.is_subdisk(big), big.valid_ranking(ranking)
        ensures self.valid_ranking(ranking)
    {
        assert forall |addr| self.entries.contains_key(addr) && #[trigger] ranking.contains_key(addr)
        implies self.node_children_respects_rank(ranking, addr)
        by {
            assert(big.entries.dom().contains(addr)); // trigger
            assert(self.entries.dom().contains(addr));
        }
    }

    pub open spec(checked) fn ranking_is_tight(self, ranking: Ranking) -> bool
    {
        ranking.dom().subset_of(self.entries.dom())
    }

    pub proof fn tight_ranking_is_finite(self, ranking: Ranking)
        requires self.wf(), self.ranking_is_tight(ranking)
        ensures ranking.dom().finite()
    {
        lemma_len_subset(ranking.dom(), self.entries.dom());
    }
}

pub proof fn get_max_rank(ranking: Ranking) -> (max: nat)
    requires ranking.dom().finite()
    ensures forall |addr| #[trigger] ranking.contains_key(addr) ==> ranking[addr] <= max
    decreases ranking.dom().len()
{
    if ranking.dom().is_empty() {
        assert forall |addr| #[trigger] ranking.contains_key(addr) 
        implies ranking[addr] <= 0 by { assert(false); }
        0
    } else {
        let curr_addr = ranking.dom().choose();
        let other_max = get_max_rank(ranking.remove(curr_addr));

        if ranking[curr_addr] > other_max {
            ranking[curr_addr]
        } else {
            assert(ranking[curr_addr] <= other_max);
            assert forall |addr| #[trigger] ranking.contains_key(addr)
            implies ranking[addr] <= other_max 
            by {
                if addr != curr_addr {
                    assert(ranking.remove(curr_addr).contains_key(addr)); // trigger
                }
            }
            other_max
        }
    }
}

impl LinkedBetree{
    pub open spec(checked) fn disk_tight_wrt_reachable_betree_addrs(self) -> bool
        recommends self.acyclic()
    {
        self.dv.entries.dom() =~= self.reachable_betree_addrs()
    }

    pub open spec(checked) fn disk_tight_wrt_reachable_buffer_addrs(self) -> bool
        recommends self.acyclic()
    {
        self.buffer_dv.entries.dom() =~= self.reachable_buffer_addrs()
    }

    pub open spec /*XXX(checked)*/ fn i_children_seq(self, ranking: Ranking, start: nat) -> Seq<FilteredBetree_v::BetreeNode>
        recommends self.has_root(),
            self.valid_ranking(ranking),
            start <= self.root().children.len()
        decreases self.get_rank(ranking), 0nat, self.root().children.len() - start 
            when start <= self.root().children.len()
                && (self.root().valid_child_index(start) ==> 
                    self.child_at_idx(start).get_rank(ranking) < self.get_rank(ranking))
    {
        if start == self.root().children.len() {
            seq![]
        } else {
            let child = self.child_at_idx(start).i_node(ranking);
            seq![child] + self.i_children_seq(ranking, start+1)
        }
    }

    pub open spec/*XXX(checked)*/ fn i_children(self, ranking: Ranking) -> Seq<FilteredBetree_v::BetreeNode>
        recommends self.has_root(), self.valid_ranking(ranking)
        decreases self.get_rank(ranking), 1nat
    {
        self.i_children_seq(ranking, 0)
    }

    pub open spec/*XXX(checked)*/ fn i_node(self, ranking: Ranking) -> FilteredBetree_v::BetreeNode
        recommends self.valid_ranking(ranking)
        decreases self.get_rank(ranking), 2nat
    {
        if !self.has_root() {
            FilteredBetree_v::BetreeNode::Nil{}
        } else {
            let root = self.root();
            FilteredBetree_v::BetreeNode::Node{
                buffers: root.buffers.i(self.buffer_dv),
                pivots: root.pivots,
                children: self.i_children(ranking),
                flushed: root.flushed,
            }
        }
    }

    pub open spec(checked) fn i(self) -> FilteredBetree_v::BetreeNode
        recommends self.acyclic()
    {
        self.i_node(self.the_ranking())
    }

    pub proof fn i_children_seq_lemma(self, ranking: Ranking, start: nat)
        requires self.has_root(), 
            self.valid_ranking(ranking),
            start <= self.root().children.len()
        ensures 
            self.i_children_seq(ranking, start).len() == self.root().children.len()-start,
            forall |i| 0 <= i < self.i_children_seq(ranking, start).len() 
            ==> {
                &&& (#[trigger] self.i_children_seq(ranking, start)[i]).wf()
                &&& self.i_children_seq(ranking, start)[i] == self.child_at_idx((i+start) as nat).i_node(ranking)
            }
        decreases self.get_rank(ranking), 0nat, self.root().children.len()-start 
    {
        if start < self.root().children.len() {
            assert(self.root().valid_child_index(start)); // trigger
            self.child_at_idx(start).i_node_wf(ranking);
            self.i_children_seq_lemma(ranking, start+1);
        } 
    }

    pub proof fn i_children_lemma(self, ranking: Ranking)
        requires self.has_root(), self.valid_ranking(ranking)
        ensures 
            self.i_node(ranking).wf_children(),
            self.i_children(ranking).len() == self.root().children.len(),
            forall |i| (#[trigger]self.root().valid_child_index(i))
                ==> self.i_children(ranking)[i as int] == self.child_at_idx(i).i_node(ranking)
        decreases self.get_rank(ranking), 1nat
    {
        self.i_children_seq_lemma(ranking, 0);
    }  

    pub proof fn i_node_wf(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures self.i_node(ranking).wf()
        decreases self.get_rank(ranking), 2nat
    {
        if self.has_root() {
            self.i_children_lemma(ranking);
            let out = self.i_node(ranking);

            assert forall |i| (
                #[trigger] out.valid_child_index(i)
                && out.get_Node_children()[i as int].is_Node()
                && out.get_Node_children()[i as int].local_structure()    
            ) implies (
                out.get_Node_children()[i as int].my_domain() == out.child_domain(i)
            ) by {
                assert(self.root().valid_child_index(i));
            }
        }
    }

    pub proof fn i_wf(self)
        requires self.acyclic()
        ensures self.i().wf()
    {
        self.i_node_wf(self.the_ranking());
    }

    pub proof fn child_at_idx_acyclic(self, idx: nat)
        requires self.acyclic(), self.has_root(), self.root().valid_child_index(idx)
        ensures self.child_at_idx(idx).acyclic()
    {
        assert(self.child_at_idx(idx).valid_ranking(self.the_ranking()));
    }
    
    pub proof fn child_at_idx_valid_ranking(self, idx: nat)
        requires self.acyclic(), self.has_root(), self.root().valid_child_index(idx)
        ensures forall |ranking: Ranking| self.valid_ranking(ranking) ==> #[trigger] self.child_at_idx(idx).valid_ranking(ranking)
    {   
    }

    pub proof fn child_for_key_valid_index(self, k: Key)
        requires self.wf(), self.has_root(), self.root().key_in_domain(k)
        ensures 0 <= self.root().pivots.route(k),
            self.root().valid_child_index(self.root().pivots.route(k) as nat)
    {
        self.root().pivots.route_lemma(k);
    }

    pub proof fn child_for_key_acyclic(self, k: Key)
        requires self.acyclic(), self.has_root(), self.root().key_in_domain(k)
        ensures self.child_for_key(k).acyclic()
    {
        self.child_for_key_valid_index(k);
        assert(self.child_for_key(k).valid_ranking(self.the_ranking()));
    }

    pub proof fn i_children_ignores_ranking(self, r1: Ranking, r2: Ranking)
        requires self.wf(), self.has_root(),
            self.valid_ranking(r1), 
            self.valid_ranking(r2),
        ensures self.i_children(r1) == self.i_children(r2)
        decreases self.get_rank(r1), 0nat
    {
        let a = self.i_children(r1);
        let b = self.i_children(r2);

        self.i_children_lemma(r1);
        self.i_children_lemma(r2);

        assert forall |i| 0 <= i < a.len()
        implies a[i] == b[i]
        by {
            assert(self.root().valid_child_index(i as nat));
            assert(a[i] == self.child_at_idx(i as nat).i_node(r1));
            self.child_at_idx(i as nat).i_node_ignores_ranking(r1, r2);
        }
        assert(a =~= b);
    }

    pub proof fn i_node_ignores_ranking(self, r1: Ranking, r2: Ranking)
        requires self.wf(), self.valid_ranking(r1), self.valid_ranking(r2)
        ensures self.i_node(r1) == self.i_node(r2)
        decreases self.get_rank(r1), 1nat
    {
        if self.has_root() {
            self.i_children_ignores_ranking(r1, r2);
        }
    }

    pub proof fn child_at_idx_commutes_with_i(self, idx: nat) 
        requires 
            self.acyclic(),
            self.has_root(),
            self.root().valid_child_index(idx), 
        ensures 
            self.i().valid_child_index(idx),
            self.child_at_idx(idx).i() == self.i().get_Node_children()[idx as int]
    {
        let child = self.child_at_idx(idx);
        self.child_at_idx_acyclic(idx);
        self.i_children_lemma(self.the_ranking());
        child.i_node_ignores_ranking(self.the_ranking(), child.the_ranking());
    }

    pub proof fn child_for_key_commutes_with_i(self, k: Key)
        requires self.acyclic(), self.has_root(), self.root().key_in_domain(k)
        ensures 
            self.child_for_key(k).acyclic(),
            self.child_for_key(k).i() == self.i().child(k)
    {
        PivotTable::route_lemma_auto();
        self.child_for_key_acyclic(k);
        self.child_for_key_valid_index(k);
        self.i_children_lemma(self.the_ranking());
        self.child_at_idx_commutes_with_i(self.root().pivots.route(k) as nat);
    }

    pub proof fn indexiness_commutes_with_i(self)
        requires self.acyclic(), self.has_root()
        ensures 
            self.root().is_index() ==> self.i().is_index(),
            self.root().is_leaf() ==> self.i().is_leaf()
    {
        self.i_wf();
        self.i_children_lemma(self.the_ranking());

        if self.root().is_index() {
            assert forall |i:nat| 0 <= i < self.i().get_Node_children().len()
            implies #[trigger] self.i().get_Node_children()[i as int].is_Node()
            by {
                assert(self.root().valid_child_index(i));
            }
        }
    }

    pub proof fn betree_subdisk_preserves_i_with_ranking(self, big: LinkedBetree, ranking: Ranking)
        requires 
            self.wf(), big.wf(),
            self.root == big.root,
            self.dv.is_subdisk(big.dv),
            self.buffer_dv.is_subdisk(big.buffer_dv),
            big.valid_ranking(ranking),
        ensures
            self.valid_ranking(ranking),
            self.i_node(ranking) == big.i_node(ranking)
        decreases self.get_rank(ranking), big.get_rank(ranking)
    {
        self.dv.subdisk_implies_ranking_validity(big.dv, ranking);
        assert(self.valid_ranking(ranking));

        if self.has_root() {
            self.root().buffers.subdisk_implies_same_i(self.buffer_dv, big.buffer_dv);

            self.i_children_lemma(ranking);
            big.i_children_lemma(ranking);

            let a = self.i_node(ranking).get_Node_children();
            let b = big.i_node(ranking).get_Node_children();
            assert(a.len() == b.len());

            assert forall |i| 0 <= i < a.len()
            implies a[i] == b[i]
            by {
                assert(self.root().valid_child_index(i as nat));
                assert(big.root().valid_child_index(i as nat));

                self.child_at_idx_acyclic(i as nat);
                big.child_at_idx_acyclic(i as nat);

                self.child_at_idx(i as nat).betree_subdisk_preserves_i_with_ranking(big.child_at_idx(i as nat), ranking);
   
            }
            assert(a =~= b);
        }
    }

    pub proof fn reachable_addrs_using_ranking_recur_body_lemma(self, ranking: Ranking, child_idx: nat)
        requires self.can_recurse_for_reachable(ranking, child_idx)
        ensures 
            forall |i| child_idx <= i < self.child_count() ==>
                (#[trigger]self.child_at_idx(i).reachable_addrs_using_ranking(ranking)
                ).subset_of(self.reachable_addrs_using_ranking_recur(ranking, child_idx))
        decreases self.child_count() - child_idx
    {
        if child_idx < self.child_count() {
            assert(self.root().valid_child_index(child_idx)); // trigger
            self.reachable_addrs_using_ranking_recur_body_lemma(ranking, child_idx+1);
        }
    }

    pub open spec(checked) fn child_subtree_contains_addr(self, ranking: Ranking, addr: Address, start: nat, i: nat) -> bool
        recommends self.wf(), self.valid_ranking(ranking)
    {
        &&& start <= i < self.child_count()
        &&& self.child_at_idx(i).valid_ranking(ranking)
        &&& self.child_at_idx(i).reachable_addrs_using_ranking(ranking).contains(addr)
    }

    pub proof fn reachable_addrs_using_ranking_recur_closed(self, ranking: Ranking, child_idx: nat)
        requires self.can_recurse_for_reachable(ranking, child_idx)
        ensures
            forall |addr| #[trigger] self.reachable_addrs_using_ranking_recur(ranking, child_idx).contains(addr)
                ==> (exists |i| self.child_subtree_contains_addr(ranking, addr, child_idx, i))
        decreases self.get_rank(ranking), self.child_count() - child_idx
    {
        if child_idx < self.child_count() {
            assert(self.root().valid_child_index(child_idx)); // trigger
            self.child_at_idx_acyclic(child_idx);

            let child = self.child_at_idx(child_idx);
            assert(child.valid_ranking(ranking));

            let child_addrs = self.child_at_idx(child_idx).reachable_addrs_using_ranking(ranking);
            let right_subtree_addrs = self.reachable_addrs_using_ranking_recur(ranking, child_idx + 1);

            self.child_at_idx(child_idx).reachable_addrs_using_ranking_closed(ranking);
            self.reachable_addrs_using_ranking_recur_closed(ranking, child_idx+1);

            assert forall |addr| #[trigger] self.reachable_addrs_using_ranking_recur(ranking, child_idx).contains(addr)
            implies (exists |i|  #[trigger]self.child_subtree_contains_addr(ranking, addr, child_idx, i))
            by {
                if right_subtree_addrs.contains(addr) {
                    let i = choose |i| #[trigger] self.child_subtree_contains_addr(ranking, addr, child_idx+1, i);
                    assert(self.child_subtree_contains_addr(ranking, addr, child_idx, i));
                } else {
                    assert(child_addrs.contains(addr));
                    assert(child.has_root() ==> child_addrs.contains(child.root.unwrap()));
                    assert(self.child_subtree_contains_addr(ranking, addr, child_idx, child_idx));
                }
            }
        }
    } 

    pub proof fn reachable_addrs_using_ranking_closed(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures 
            self.has_root() ==> self.reachable_addrs_using_ranking(ranking).contains(self.root.unwrap()),
            forall |addr| #[trigger] self.reachable_addrs_using_ranking(ranking).contains(addr) && Some(addr) != self.root
                ==> (exists |i| self.child_subtree_contains_addr(ranking, addr, 0, i))
        decreases self.get_rank(ranking)
    {
        if self.has_root() {
            let sub_tree_addrs = self.reachable_addrs_using_ranking_recur(ranking, 0);
            self.reachable_addrs_using_ranking_recur_closed(ranking, 0);
            assert(sub_tree_addrs.insert(self.root.unwrap()) =~= self.reachable_addrs_using_ranking(ranking));
        }
    }

    pub proof fn reachable_addrs_are_closed(self, ranking: Ranking, addr: Address)
        requires 
            self.wf(), self.has_root(), 
            self.valid_ranking(ranking),
            self.reachable_addrs_using_ranking(ranking).contains(addr),
            self.dv.entries.dom().contains(addr),
        ensures ({
            let node = self.dv.entries[addr];
            &&& forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int].is_Some() 
                ==> self.reachable_addrs_using_ranking(ranking).contains(node.children[i as int].unwrap())
        })
        decreases self.get_rank(ranking)
    {
        let node = self.dv.entries[addr];
        let reachable_addrs = self.reachable_addrs_using_ranking(ranking);
        self.reachable_addrs_using_ranking_closed(ranking);

        assert forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int].is_Some() 
        implies reachable_addrs.contains(node.children[i as int].unwrap())
        by {
            if addr == self.root.unwrap() {
                self.child_at_idx(i).reachable_addrs_using_ranking_closed(ranking);
                assert(self.child_at_idx(i).has_root());
                self.reachable_addrs_using_ranking_recur_body_lemma(ranking, 0);
                assert(reachable_addrs.contains(node.children[i as int].unwrap()));
            } else {
                assert(self.reachable_addrs_using_ranking(ranking).contains(addr));
                let i = choose |i| self.child_subtree_contains_addr(ranking, addr, 0, i);
                assert(self.root().valid_child_index(i)); // trigger
                self.child_at_idx(i).reachable_addrs_are_closed(ranking, addr);
                self.reachable_addrs_using_ranking_recur_body_lemma(ranking, 0);
            }
        }
    }

    pub proof fn build_tight_preserves_wf(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures self.build_tight_tree().wf()
        decreases self.get_rank(ranking)
    {
        let result = self.build_tight_tree();

        assert forall |addr| #[trigger] result.dv.entries.contains_key(addr)
        implies {
            &&& result.dv.node_has_nondangling_child_ptrs(result.dv.entries[addr])
            &&& result.dv.node_has_linked_children(result.dv.entries[addr])
        } by {
            self.reachable_addrs_are_closed(self.the_ranking(), addr);
        }

        assert forall |addr| result.dv.entries.contains_key(addr)
        implies #[trigger] result.dv.entries[addr].buffers.valid(result.buffer_dv)
        by {
            let node = result.dv.entries[addr];
            assert(node.buffers.valid(self.buffer_dv)); // trigger
            assert forall |i| 0 <= i < node.buffers.len()
            implies #[trigger] result.buffer_dv.repr().contains(node.buffers[i])
            by {
                assert(node.buffers.repr().contains(node.buffers[i]));
                assert(self.reachable_buffer(addr, node.buffers[i]));
            }
            assert(node.buffers.valid(result.buffer_dv));
        }

        lemma_len_subset(result.dv.entries.dom(), self.dv.entries.dom());
        lemma_len_subset(result.buffer_dv.entries.dom(), self.buffer_dv.entries.dom());
    }

    pub proof fn build_tight_preserves_i(self)
        requires self.acyclic()
        ensures 
            self.build_tight_tree().wf(),
            self.build_tight_tree().valid_ranking(self.the_ranking()),
            self.i() == self.build_tight_tree().i()
    {
        let ranking = self.the_ranking();
        let result = self.build_tight_tree();
        self.build_tight_preserves_wf(ranking);
        assert(result.valid_ranking(ranking));
        result.betree_subdisk_preserves_i_with_ranking(self, ranking);
        result.i_node_ignores_ranking(ranking, result.the_ranking());
    }

    pub open spec(checked) fn build_tight_ranking(self, ranking: Ranking) -> Ranking
    {
        ranking.restrict(self.dv.entries.dom())
    }

    pub proof fn identical_children_commutes_with_i(self, idx: nat, other: LinkedBetree, other_idx: nat, ranking: Ranking)
        requires 
            self.wf(), self.has_root(), 
            self.root().valid_child_index(idx),
            other.wf(), other.has_root(), 
            other.root().valid_child_index(other_idx),
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.dv.is_subdisk(other.dv),
            self.buffer_dv.is_subdisk(other.buffer_dv),
            self.root().children[idx as int] == other.root().children[other_idx as int]
        ensures 
            self.i().get_Node_children()[idx as int] == other.i().get_Node_children()[other_idx as int]
    {
        let child = self.child_at_idx(idx);
        let other_child = other.child_at_idx(other_idx);

        self.i_children_lemma(self.the_ranking());
        other.i_children_lemma(other.the_ranking());

        self.child_at_idx_commutes_with_i(idx);
        other.child_at_idx_commutes_with_i(other_idx);

        child.betree_subdisk_preserves_i_with_ranking(other_child, ranking);
        child.i_node_ignores_ranking(self.the_ranking(), ranking);
        other_child.i_node_ignores_ranking(other.the_ranking(), ranking);
    }


    // operations

    pub proof fn push_memtable_wf(self, memtable: Memtable, new_addrs: TwoAddrs)
        requires 
            self.wf(), 
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures
            self.push_memtable(memtable, new_addrs).wf()
    {
        let result = self.push_memtable(memtable, new_addrs);

        if self.has_root() {
            assert forall |i| result.root().valid_child_index(i) ==> self.root().valid_child_index(i) by {} // trigger
            assert(result.dv.node_has_nondangling_child_ptrs(result.root()));
            assert(result.dv.node_has_linked_children(result.root()));
        }
        assert(result.dv.healthy_child_ptrs());
        assert(result.dv.wf());

        assert forall |addr| result.dv.entries.contains_key(addr)
        implies #[trigger] result.dv.entries[addr].buffers.valid(result.buffer_dv)
        by {
            if addr == result.root.unwrap() && self.has_root() {
                let node = result.root();
                assert(node.buffers.len() == self.root().buffers.len() + 1);
                assert(self.root().buffers.valid(self.buffer_dv));

                assert forall |i| 0 <= i < node.buffers.len()
                implies #[trigger] result.buffer_dv.repr().contains(node.buffers[i])
                by {
                    if i < node.buffers.len() - 1 {
                        assert(self.root().buffers[i] == node.buffers[i]);
                        assert(self.buffer_dv.repr().contains(node.buffers[i]));
                        assert(result.buffer_dv.repr().contains(node.buffers[i]));
                    } else {
                        assert(node.buffers[i] == new_addrs.addr2);
                    }
                }
            } else if addr != result.root.unwrap() {
                assert(result.dv.entries[addr].buffers.valid(self.buffer_dv)); //  trigger
            }
        }
        assert(result.dv.no_dangling_buffer_ptr(result.buffer_dv));
        assert(result.wf());
    }

    #[verifier::spinoff_prover]
    pub proof fn push_memtable_new_ranking(self, memtable: Memtable, new_addrs: TwoAddrs, old_ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), 
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
            self.valid_ranking(old_ranking),
            self.dv.ranking_is_tight(old_ranking)
        ensures 
            self.push_memtable(memtable, new_addrs).valid_ranking(new_ranking),
            self.push_memtable(memtable, new_addrs).build_tight_tree().wf(),
            self.push_memtable(memtable, new_addrs).build_tight_tree().valid_ranking(new_ranking),
            new_ranking.dom() == old_ranking.dom().insert(new_addrs.addr1)
    {
        let result = self.push_memtable(memtable, new_addrs);
        self.push_memtable_wf(memtable, new_addrs);

        let new_rank = if self.has_root() { old_ranking[self.root.unwrap()]+1 } else { 0 };
        let new_ranking = old_ranking.insert(new_addrs.addr1, new_rank);

        if self.has_root() {
            // Add this to suppress "recommends" warning for `result.root()` call.
            assert(result.has_root());
            assert forall |i| result.root().valid_child_index(i) ==> self.root().valid_child_index(i) by {} // trigger
        }

        // tenzinhl: Adding this assertion caused the proof to go through. Unsure what it's triggering.
        assert(result.dv.valid_ranking(new_ranking));

        assert(result.valid_ranking(new_ranking));
        result.build_tight_preserves_wf(new_ranking);
        new_ranking
    }

    pub proof fn push_memtable_commutes_with_i(self, memtable: Memtable, new_addrs: TwoAddrs)
        requires 
            self.acyclic(),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures
            self.push_memtable(memtable, new_addrs).build_tight_tree().acyclic(),
            self.push_memtable(memtable, new_addrs).build_tight_tree().i() == self.i().push_memtable(memtable)
    {
        let result = self.push_memtable(memtable, new_addrs);
        let old_ranking = self.build_tight_ranking(self.the_ranking());
        let new_ranking = self.push_memtable_new_ranking(memtable, new_addrs, old_ranking);

        result.build_tight_preserves_i();
        assert(result.build_tight_tree().i() == result.i());

        result.i_node_ignores_ranking(result.the_ranking(), new_ranking);
        result.i_children_lemma(result.the_ranking());

        if self.has_root() {
            assert(self.valid_ranking(new_ranking));

            self.i_children_lemma(new_ranking);
            result.i_children_lemma(new_ranking);

            self.i_children_ignores_ranking(self.the_ranking(), new_ranking);
            result.i_node_ignores_ranking(result.the_ranking(), new_ranking);

            self.root().buffers.subdisk_implies_same_i(self.buffer_dv, result.buffer_dv);

            let a = self.i_children(new_ranking);
            let b = result.i_children(new_ranking);
            assert(a.len() == b.len());

            assert forall |i| 0 <= i < a.len()
            implies a[i] =~= b[i]
            by {
                self.identical_children_commutes_with_i(i as nat, result, i as nat, new_ranking);
            }
        }
        
        assert(result.i().get_Node_children() =~= self.i().push_memtable(memtable).get_Node_children());
        assert(result.i().get_Node_buffers() =~= self.i().push_memtable(memtable).get_Node_buffers());
    }

    pub proof fn grow_new_ranking(self, new_root_addr: Address, old_ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(),
            self.has_root() ==> self.root().my_domain() == total_domain(),
            self.valid_ranking(old_ranking),
            self.is_fresh(Set::empty().insert(new_root_addr)),
            self.dv.ranking_is_tight(old_ranking),
        ensures 
            self.grow(new_root_addr).wf(),
            self.grow(new_root_addr).valid_ranking(new_ranking),
            new_ranking.dom() == old_ranking.dom().insert(new_root_addr),
    {
        self.dv.tight_ranking_is_finite(old_ranking);

        let result = self.grow(new_root_addr);
        let new_rank = 
            if self.has_root() { old_ranking[self.root.unwrap()]+1 } 
            else if old_ranking =~= map![] { 1 }
            else { get_max_rank(old_ranking) + 1 };
        
        old_ranking.insert(new_root_addr, new_rank)
    }

    pub proof fn fresh_entry_preserves_i(self, other: LinkedBetree, ranking: Ranking, new_addr: Address)
        requires 
            self.wf(), other.wf(),
            self.root == other.root,
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.dv.is_subdisk(other.dv),
            self.dv.entries.dom().insert(new_addr) =~= other.dv.entries.dom(),
            self.buffer_dv == other.buffer_dv,
            self.is_fresh(Set::empty().insert(new_addr)),
        ensures 
            self.i_node(ranking) == other.i_node(ranking)
        decreases self.get_rank(ranking)
    {
        if self.has_root() {
            self.i_children_lemma(ranking);
            other.i_children_lemma(ranking);

            assert(self.i_children(ranking).len() == other.i_children(ranking).len());
            assert forall |i| 0 <= i < self.i_children(ranking).len()
            implies self.i_children(ranking)[i] == other.i_children(ranking)[i]
            by {
                assert(self.root().valid_child_index(i as nat)); // trigger
                assert(other.root().valid_child_index(i as nat)); // trigger

                self.child_at_idx_acyclic(i as nat);
                other.child_at_idx_acyclic(i as nat);
                self.child_at_idx(i as nat).fresh_entry_preserves_i(other.child_at_idx(i as nat), ranking, new_addr);
            }

            assert(self.i_node(ranking).get_Node_children() =~= other.i_node(ranking).get_Node_children());
            assert(self.i_node(ranking).get_Node_buffers() =~= other.i_node(ranking).get_Node_buffers());
        }
    }

    pub proof fn grow_commutes_with_i(self, new_root_addr: Address)
        requires 
            self.acyclic(),
            self.has_root() ==> self.root().my_domain() == total_domain(),
            self.is_fresh(Set::empty().insert(new_root_addr))
        ensures
            self.grow(new_root_addr).acyclic(),
            self.grow(new_root_addr).i() == self.i().grow()
    {
        let result = self.grow(new_root_addr);
        let old_ranking = self.build_tight_ranking(self.the_ranking());
        let new_ranking = self.grow_new_ranking(new_root_addr, old_ranking);
        result.i_children_lemma(result.the_ranking());

        result.child_at_idx_acyclic(0);
        let child = result.child_at_idx(0);
        result.child_at_idx_valid_ranking(0);
        child.i_node_ignores_ranking(new_ranking, result.the_ranking());
        
        self.i_node_ignores_ranking(self.the_ranking(), new_ranking);
        self.fresh_entry_preserves_i(child, new_ranking, new_root_addr);

        assert(result.i().get_Node_children() =~= self.i().grow().get_Node_children());
        assert(result.i().get_Node_buffers() =~= self.i().grow().get_Node_buffers());
    }

    pub open spec(checked) fn split_element(self, request: SplitRequest) -> Element
        recommends self.can_split_parent(request)
    {
        // let child = self.child_at_idx(request.get_child_idx()).root(); // TODO(verus): false recommendation note met
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => to_element(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => self.child_at_idx(request.get_child_idx()).root().pivots.pivots[child_pivot_idx as int]
        }
    }

    pub proof fn split_new_ranking(self, request: SplitRequest, new_addrs: SplitAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), self.has_root(),
            self.valid_ranking(ranking),
            self.can_split_parent(request),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.valid_ranking(new_ranking),
            self.split_parent(request, new_addrs).valid_ranking(new_ranking),
            new_ranking.dom() == ranking.dom() + new_addrs.repr()
    {
        let child_idx = request.get_child_idx();
        let old_child_addr = self.root().children[child_idx as int].unwrap();

        let old_parent_rank = ranking[self.root.unwrap()];
        let old_child_rank = ranking[old_child_addr];

        let new_ranking = ranking.insert(new_addrs.left, old_child_rank).insert(new_addrs.right, old_child_rank).insert(new_addrs.parent, old_parent_rank);
        assert(self.dv.valid_ranking(new_ranking));

        let result = self.split_parent(request, new_addrs);
        self.root().pivots.insert_wf(child_idx as int + 1, self.split_element(request));
        assert(result.root().wf());

        let old_child = self.dv.entries[self.root().children[child_idx as int].unwrap()];
        let new_left_child = result.dv.entries[new_addrs.left];
        let new_right_child = result.dv.entries[new_addrs.right];

        assert forall |i| new_left_child.valid_child_index(i) ==> old_child.valid_child_index(i) by {} // trigger
        // assert(result.dv.node_children_respects_rank(new_ranking, new_addrs.left));

        assert forall |i| request.is_SplitLeaf() && new_right_child.valid_child_index(i) ==> old_child.valid_child_index(i) by {} // trigger
        assert forall |i| request.is_SplitIndex() && new_right_child.valid_child_index(i) ==> 
            old_child.valid_child_index(i + request->child_pivot_idx) by {} // trigger
        // assert(result.dv.node_children_respects_rank(new_ranking, new_addrs.right));

        assert forall |i| #[trigger] result.root().valid_child_index(i) ==> 
        ({
            &&& i < child_idx ==> self.root().valid_child_index(i) 
            &&& i > child_idx + 1 ==> self.root().valid_child_index((i-1) as nat)
        }) by {}
        // assert(result.dv.node_children_respects_rank(new_ranking, new_addrs.parent));

        assert(result.dv.valid_ranking(new_ranking));
        assert(new_ranking.dom() =~= ranking.dom() + new_addrs.repr());

        new_ranking
    }

    #[verifier::spinoff_prover]
    pub proof fn split_parent_commutes_with_i(self, request: SplitRequest, new_addrs: SplitAddrs)
        requires 
            self.acyclic(), 
            self.can_split_parent(request),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.split_parent(request, new_addrs).acyclic(),
            self.i().can_split_parent(request),
            self.split_parent(request, new_addrs).i() == self.i().split_parent(request)
    {
        // TODO(JL): fix
        let result = self.split_parent(request, new_addrs);
        let new_ranking = self.split_new_ranking(request, new_addrs, self.the_ranking());

        let child_idx = request.get_child_idx();
        let old_child = self.child_at_idx(child_idx);

        self.i_wf();
        self.child_at_idx_acyclic(child_idx);
        self.child_at_idx_commutes_with_i(child_idx);

        old_child.i_node_ignores_ranking(self.the_ranking(), old_child.the_ranking());
        old_child.indexiness_commutes_with_i();
        assert(self.i().can_split_parent(request));

        let a = result.i_children(result.the_ranking());
        let b = self.i().split_parent(request).get_Node_children();

        assert(a.len() == b.len()) by {
            self.i_children_lemma(self.the_ranking());
            result.i_children_lemma(result.the_ranking());
        }

        assert forall |i| 0 <= i < a.len()
        implies a[i] =~= b[i]
        by {
            result.child_at_idx_acyclic(i as nat);
            result.child_at_idx_commutes_with_i(i as nat);

            if i < child_idx {
                self.identical_children_commutes_with_i(i as nat, result, i as nat, new_ranking);
            } else if i == child_idx {
                let new_left_child = result.child_at_idx(i as nat);
                new_left_child.i_children_lemma(new_ranking);

                assert forall |j| 0 <= j < new_left_child.root().children.len()
                implies #[trigger] new_left_child.i_children(new_ranking)[j] == b[i].get_Node_children()[j]
                by {
                    assert(new_left_child.root().valid_child_index(j as nat));
                    assert(old_child.root().valid_child_index(j as nat));

                    let old_grand_child = old_child.child_at_idx(j as nat);
                    let new_grand_child = new_left_child.child_at_idx(j as nat);

                    old_child.i_children_lemma(self.the_ranking());
                    old_grand_child.betree_subdisk_preserves_i_with_ranking(new_grand_child, new_ranking);
                    old_grand_child.i_node_ignores_ranking(self.the_ranking(), new_ranking);
                }

                assert(new_left_child.i_children(new_ranking) =~= b[i].get_Node_children());
                new_left_child.i_node_ignores_ranking(new_ranking, new_left_child.the_ranking());
            } else if i == child_idx + 1 {
                let new_right_child = result.child_at_idx(i as nat);
                new_right_child.i_children_lemma(new_ranking);

                assert forall |j| 0 <= j < new_right_child.root().children.len()
                implies #[trigger] new_right_child.i_children(new_ranking)[j] == b[i].get_Node_children()[j]
                by {
                    assert(new_right_child.root().valid_child_index(j as nat));

                    if request.is_SplitIndex() {
                        let pivot_idx = request->child_pivot_idx;
                        assert(old_child.root().valid_child_index((j + pivot_idx)  as nat));

                        let old_grand_child = old_child.child_at_idx((j + pivot_idx)  as nat);
                        let new_grand_child = new_right_child.child_at_idx(j as nat);
    
                        old_child.i_children_lemma(self.the_ranking());
                        old_grand_child.betree_subdisk_preserves_i_with_ranking(new_grand_child, new_ranking);
                        old_grand_child.i_node_ignores_ranking(self.the_ranking(), new_ranking);
                    } else {
                        assert(old_child.root().valid_child_index(j as nat));
                    }
                }

                assert(new_right_child.i_children(new_ranking) =~= b[i].get_Node_children());
                new_right_child.i_node_ignores_ranking(new_ranking, new_right_child.the_ranking());
            } else {
                self.identical_children_commutes_with_i((i-1) as nat, result, i as nat, new_ranking);
            }
        }
        assert(a =~= b);
    }

    pub proof fn flush_new_ranking(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), self.has_root(),
            self.valid_ranking(ranking),
            self.can_flush(child_idx, buffer_gc),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.valid_ranking(new_ranking),
            self.flush(child_idx, buffer_gc, new_addrs).valid_ranking(new_ranking),
            new_ranking.dom() == ranking.dom() + new_addrs.repr(),
            buffer_gc <= self.root().buffers.len()
    {
        let result = self.flush(child_idx, buffer_gc, new_addrs);
        let old_child_addr = self.child_at_idx(child_idx).root.unwrap();

        assert(result.dv.entries.contains_key(new_addrs.addr1));
        assert(result.dv.entries.contains_key(new_addrs.addr2));

        let old_child = self.dv.entries[old_child_addr];
        let new_parent = result.dv.entries[new_addrs.addr1];
        let new_child = result.dv.entries[new_addrs.addr2];

        let old_parent_rank = ranking[self.root.unwrap()];
        let old_child_rank = ranking[old_child_addr];
        let new_ranking = ranking.insert(new_addrs.addr1, old_parent_rank).insert(new_addrs.addr2, old_child_rank);

        assert forall |i| #[trigger] new_child.valid_child_index(i) ==> old_child.valid_child_index(i) by {} // trigger
        assert forall |i| #[trigger] new_parent.valid_child_index(i) ==> self.root().valid_child_index(i) by {} // trigger

        assert(result.dv.valid_ranking(new_ranking));

        assert(buffer_gc <= self.root().buffers.len()) by {
            let updated_ofs = self.root().flushed.update(child_idx as int, self.root().buffers.len());
            assert(updated_ofs.offsets[child_idx as int] >= buffer_gc);
        }

        assert(self.root().buffers.valid(self.buffer_dv)); // trigger
        assert(old_child.buffers.valid(self.buffer_dv));   // trigger

        assert(result.wf());
        assert(new_ranking.dom() =~= ranking.dom() + new_addrs.repr());

        new_ranking
    }

    #[verifier::spinoff_prover]
    pub proof fn flush_commutes_with_i(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs)
        requires 
            self.acyclic(), 
            self.can_flush(child_idx, buffer_gc), 
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.flush(child_idx, buffer_gc, new_addrs).acyclic(),
            self.i().can_flush(child_idx, buffer_gc),
            self.flush(child_idx, buffer_gc, new_addrs).i() == self.i().flush(child_idx, buffer_gc)
    {
        let result = self.flush(child_idx, buffer_gc, new_addrs);
        let new_ranking = self.flush_new_ranking(child_idx, buffer_gc, new_addrs, self.the_ranking());
        
        self.i_wf();
        assert(result.i().get_Node_buffers() =~= self.i().flush(child_idx, buffer_gc).get_Node_buffers());

        let a = result.i_children(result.the_ranking());
        let b = self.i().flush(child_idx, buffer_gc).get_Node_children();

        self.i_children_lemma(self.the_ranking());
        result.i_children_lemma(result.the_ranking());

        assert forall |i| 0 <= i < a.len()
        implies a[i] =~= b[i]
        by {
            assert(self.root().valid_child_index(i as nat));
            assert(result.root().valid_child_index(i as nat));

            let old_child = self.child_at_idx(i as nat);
            self.child_at_idx_acyclic(i as nat);
            self.child_at_idx_commutes_with_i(i as nat);
            self.child_at_idx_valid_ranking(i as nat);

            let new_child = result.child_at_idx(i as nat);
            result.child_at_idx_acyclic(i as nat);
            result.child_at_idx_commutes_with_i(i as nat);
            result.child_at_idx_valid_ranking(i as nat);

            if i == child_idx {
                assert(a[i].get_Node_children() == new_child.i_children(result.the_ranking()));
                assert(b[i].get_Node_children() == old_child.i_children(self.the_ranking()));

                assert forall |j| 0 <= j < a[i].get_Node_children().len()
                implies a[i].get_Node_children()[j] == b[i].get_Node_children()[j]
                by {
                    assert(old_child.root().valid_child_index(j as nat));
                    assert(new_child.root().valid_child_index(j as nat));

                    let old_grand_child = old_child.child_at_idx(j as nat);
                    let new_grand_child = new_child.child_at_idx(j as nat);

                    old_child.child_at_idx_acyclic(j as nat);
                    new_child.child_at_idx_acyclic(j as nat);

                    old_child.child_at_idx_valid_ranking(j as nat);
                    new_child.child_at_idx_valid_ranking(j as nat);

                    assert(a[i].get_Node_children()[j] == new_grand_child.i_node(new_ranking)) by {
                        new_child.i_children_lemma(result.the_ranking());
                        new_grand_child.i_node_ignores_ranking(result.the_ranking(), new_ranking);
                    }
                    assert(b[i].get_Node_children()[j] == old_grand_child.i_node(new_ranking)) by {
                        // assert(b[i].get_Node_children()[j] == old_child.i_children(self.the_ranking())[j]);
                        old_child.i_children_lemma(self.the_ranking());
                        // assert(old_child.i_children(self.the_ranking())[j] == old_grand_child.i_node(self.the_ranking()));
                        old_grand_child.i_node_ignores_ranking(self.the_ranking(), new_ranking);
                    }

                    old_grand_child.betree_subdisk_preserves_i_with_ranking(new_grand_child, new_ranking);
                    assert(new_grand_child.i_node(new_ranking) == old_grand_child.i_node(new_ranking));
                }
                assert(a[i].get_Node_children() =~= b[i].get_Node_children());
            } else {
                old_child.i_node_ignores_ranking(old_child.the_ranking(), new_ranking);
                new_child.i_node_ignores_ranking(new_child.the_ranking(), new_ranking);
                old_child.betree_subdisk_preserves_i_with_ranking(new_child, new_ranking);
            }
        }
        assert(a =~= b);
    }

    #[verifier::spinoff_prover]
    pub proof fn compact_new_ranking(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), self.has_root(),
            self.valid_ranking(ranking),
            self.can_compact(start, end, compacted_buffer),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.valid_ranking(new_ranking),
            self.compact(start, end, compacted_buffer, new_addrs).valid_ranking(new_ranking),
            new_ranking.dom() == ranking.dom().insert(new_addrs.addr1),
    {
        let result = self.compact(start, end, compacted_buffer, new_addrs);
        let new_ranking = ranking.insert(new_addrs.addr1, ranking[self.root.unwrap()]);
        assert(new_ranking.dom() =~= ranking.dom().insert(new_addrs.addr1));

        let new_root = result.dv.entries[new_addrs.addr1];
        assert forall |i| #[trigger] new_root.valid_child_index(i) ==> self.root().valid_child_index(i) by {} // trigger
        assert(result.dv.valid_ranking(new_ranking));


        assert forall |addr| result.dv.entries.contains_key(addr)
        implies #[trigger] result.dv.entries[addr].buffers.valid(result.buffer_dv)
        by {
            let node = result.dv.entries[addr];
            if addr == new_addrs.addr1 {
                assert(self.root().buffers.valid(self.buffer_dv)); // trigger
            } else {
                assert(node.buffers.valid(self.buffer_dv));
                node.buffers.subdisk_implies_same_i(self.buffer_dv, result.buffer_dv);
            }
        }
        assert(result.dv.no_dangling_buffer_ptr(result.buffer_dv));
        new_ranking
    }


    pub proof fn can_compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs)
        requires 
            self.acyclic(), 
            self.can_compact(start, end, compacted_buffer),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.i().can_compact(start, end, compacted_buffer)
    {
        self.i_wf();
        assert(self.i().is_Node());
        assert(start < end <= self.i().get_Node_buffers().len());

        let compact_slice = self.root().buffers.slice(start as int, end as int);
        let i_compact_slice = self.i().get_Node_buffers().slice(start as int, end as int);
        assert(compact_slice.i(self.buffer_dv) =~= i_compact_slice);
        assert(self.root().buffers.valid(self.buffer_dv)); // trigger

        let compact_ofs_map = self.root().make_offset_map().decrement(start);
        let i_compact_ofs_map = self.i().make_offset_map().decrement(start);
        assert(compact_ofs_map =~= i_compact_ofs_map);

        assert forall |k| #![auto] self.root().compact_key_range(start, end, k, self.buffer_dv) == self.i().compact_key_range(start, end, k)
        by {
            if self.root().compact_key_range(start, end, k, self.buffer_dv) {
                let buffer_idx = choose |buffer_idx| compact_slice.key_in_buffer_filtered(self.buffer_dv, compact_ofs_map, 0, k, buffer_idx);
                assert(i_compact_slice.key_in_buffer_filtered(i_compact_ofs_map, 0, k, buffer_idx));
            }

            if self.i().compact_key_range(start, end, k) {
                let buffer_idx = choose |buffer_idx| i_compact_slice.key_in_buffer_filtered(i_compact_ofs_map, 0, k, buffer_idx);
                assert(i_compact_ofs_map.offsets[k] == compact_ofs_map.offsets[k]);

                assert(self.root().buffers[buffer_idx + start] == compact_slice[buffer_idx]);
                assert(self.buffer_dv.entries.contains_key(compact_slice[buffer_idx]));

                assert(i_compact_slice.key_in_buffer(0, k, buffer_idx) == compact_slice.key_in_buffer(self.buffer_dv, 0, k, buffer_idx));
                assert(compact_slice.key_in_buffer_filtered(self.buffer_dv, compact_ofs_map, 0, k, buffer_idx));
            }
        }

        assert forall |k| #![auto] compacted_buffer.map.contains_key(k)
        implies {
            let from = if self.i().flushed_ofs(k) <= start { 0 } else { self.i().flushed_ofs(k)-start };
            &&& compacted_buffer.query(k) == self.i().get_Node_buffers().slice(start as int, end as int).query_from(k, from)
        } by {
            let from = if self.i().flushed_ofs(k) <= start { 0 } else { self.i().flushed_ofs(k)-start };
            compact_slice.query_from_commutes_with_i(self.buffer_dv, k, from);
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs)
        requires 
            self.acyclic(), 
            self.can_compact(start, end, compacted_buffer),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.compact(start, end, compacted_buffer, new_addrs).acyclic(),
            self.i().can_compact(start, end, compacted_buffer),
            self.compact(start, end, compacted_buffer, new_addrs).i() == self.i().compact(start, end, compacted_buffer)
    {
        let result = self.compact(start, end, compacted_buffer, new_addrs);
        let new_ranking = self.compact_new_ranking(start, end, compacted_buffer, new_addrs, self.the_ranking());
        self.can_compact_commutes_with_i(start, end, compacted_buffer, new_addrs);

        self.root().buffers.subdisk_implies_same_i(self.buffer_dv, result.buffer_dv);
        assert(result.i().get_Node_buffers() =~= self.i().compact(start, end, compacted_buffer).get_Node_buffers());

        let a = result.i_children(result.the_ranking());
        let b = self.i().compact(start, end, compacted_buffer).get_Node_children();
        result.i_children_lemma(result.the_ranking());
        assert(a.len() == b.len());

        assert forall |i| 0 <= i < a.len()
        implies a[i] == b[i]
        by {
            self.identical_children_commutes_with_i(i as nat, result, i as nat, new_ranking);
        }
        assert(a =~= b);
    }

} // end impl LinkedBetree

pub open spec(checked) fn i_stamped_betree(stamped: StampedBetree) -> FilteredBetree_v::StampedBetree
    recommends stamped.value.acyclic()
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::QueryReceiptLine
        recommends self.linked.acyclic()
    {
        FilteredBetree_v::QueryReceiptLine{ node: self.linked.i(), result: self.result }
    }
}

impl QueryReceipt{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::QueryReceipt
        recommends self.valid()
    {
        let ranking = self.linked.the_ranking();
        // Note(verus): spec(checked) is not checked when calling as a closure
        FilteredBetree_v::QueryReceipt{
            key: self.key,
            root: self.linked.i(),
            lines: Seq::new(self.lines.len(), |i:int| self.lines[i].i())
        }
    }

    pub proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
    {
        PivotTable::route_lemma_auto();

        let i_receipt = self.i();
        let ranking = self.linked.the_ranking();

        assert forall |i:int| #![auto] 0 <= i < i_receipt.lines.len()
        implies i_receipt.lines[i].wf()
        by {
            self.lines[i].linked.i_wf();
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies {
            &&& #[trigger] i_receipt.lines[i].node.key_in_domain(self.key)
            &&& i_receipt.child_linked_at(i) 
        } by {
            assert(self.node(i).key_in_domain(self.key)); // trigger
            self.lines[i].linked.child_for_key_commutes_with_i(self.key);
            assert(self.child_linked_at(i)); // trigger
            assert(self.result_linked_at(i)); // trigger
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.result_linked_at(i) by {
            assert(self.result_linked_at(i)); // trigger
            let node = self.node(i);
            let start = node.flushed_ofs(self.key) as int;
            node.buffers.query_from_commutes_with_i(self.linked.buffer_dv, self.key, start);
        }
        assert(i_receipt.all_lines_wf()); // trigger
    }
}

pub proof fn path_addrs_to_set_additive(path_addrs: PathAddrs)
    requires path_addrs.len() > 0
    ensures path_addrs.to_set() == set![path_addrs[0]] + path_addrs.subrange(1, path_addrs.len() as int).to_set()
{
    let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
    let a = set![path_addrs[0]] + sub_path_addrs.to_set();
    let b = path_addrs.to_set();

    // TODO(verus): lack additive seq to set lemma
    assert forall |addr| a.contains(addr) <==> b.contains(addr)
    by {
        if a.contains(addr) {
            if sub_path_addrs.contains(addr) {
                let idx = choose |idx| 0 <= idx < sub_path_addrs.len() && sub_path_addrs[idx] == addr;
                assert(sub_path_addrs[idx] == path_addrs[idx + 1]);
            }
        }
        if b.contains(addr) {
            let idx = choose |idx| 0 <= idx < path_addrs.len() && path_addrs[idx] == addr;
            if idx > 0 {
                assert(sub_path_addrs[idx-1] == path_addrs[idx]);
            }
        }
    }
    assert(a =~= b);
}

impl Path{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::Path
        recommends self.valid()
    {
        FilteredBetree_v::Path{node: self.linked.i(), key: self.key, depth: self.depth}
    }

    pub proof fn valid_ranking_throughout(self, ranking: Ranking)
        requires self.valid(), self.linked.valid_ranking(ranking)
        ensures 0 < self.depth ==> self.subpath().linked.valid_ranking(ranking),
            self.target().valid_ranking(ranking)
        decreases self.depth
    {
        if 0 < self.depth {
            self.linked.child_for_key_valid_index(self.key);
            self.subpath().valid_ranking_throughout(ranking);
        }
    }

    pub proof fn subpath_commutes_with_i(self)
        requires 0 < self.depth, self.valid()
        ensures
            self.subpath().linked.acyclic(), 
            self.subpath().i() == self.i().subpath()
    {
        self.valid_ranking_throughout(self.linked.the_ranking());
        self.linked.child_for_key_commutes_with_i(self.key);
    }

    pub proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
        decreases self.depth
    {
        self.linked.i_wf();
        if 0 < self.depth {
            self.valid_ranking_throughout(self.linked.the_ranking());
            self.subpath().i_valid();
            self.subpath_commutes_with_i();
            self.linked.indexiness_commutes_with_i();
        }
    }

    pub proof fn target_commutes_with_i(self) 
        requires self.valid(), self.linked.acyclic()
        ensures 
            self.target().acyclic(),
            self.target().dv == self.linked.dv,
            self.target().buffer_dv == self.linked.buffer_dv,
            self.i().valid(), 
            self.i().target() == self.target().i()
        decreases self.depth
    {
        self.valid_ranking_throughout(self.linked.the_ranking());
        self.i_valid();
        if 0 < self.depth {
            self.subpath().target_commutes_with_i();
            self.subpath_commutes_with_i();
        }
    }

    pub proof fn betree_diskview_diff(self, replacement: LinkedBetree, path_addrs: PathAddrs)
        requires 
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
        ensures 
            self.substitute(replacement, path_addrs).dv.entries.dom() =~= replacement.dv.entries.dom() + path_addrs.to_set()
        decreases self.depth
    {
        let result = self.substitute(replacement, path_addrs);

        if 0 < self.depth {
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().betree_diskview_diff(replacement, sub_path_addrs);
            path_addrs_to_set_additive(path_addrs);
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn substitute_preserves_wf(self, replacement: LinkedBetree, path_addrs: PathAddrs)
        requires 
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
            self.linked.is_fresh(path_addrs.to_set()),
            replacement.is_fresh(path_addrs.to_set()),
        ensures ({
            let result = self.substitute(replacement, path_addrs);
            &&& result.wf()
            &&& result.has_root()
            &&& result.root().my_domain() == self.linked.root().my_domain()
            &&& self.linked.dv.is_subdisk(result.dv)
            &&& self.linked.buffer_dv.is_subdisk(result.buffer_dv)
            &&& result.dv.entries.dom() =~= (self.linked.dv.entries.dom() + replacement.dv.entries.dom() + path_addrs.to_set())
        })
        decreases self.depth, 1nat
    {
        if 0 < self.depth {
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().substitute_preserves_wf(replacement, sub_path_addrs);
            path_addrs_to_set_additive(path_addrs);

            let result = self.substitute(replacement, path_addrs);
            let node = result.dv.entries[path_addrs[0]];

            let r = node.pivots.route(self.key);
            PivotTable::route_lemma_auto();
            assert(self.linked.dv.entries.contains_key(self.linked.root.unwrap())); // trigger

            assert forall |i| #[trigger] node.valid_child_index(i)
            implies {
                &&& result.dv.is_nondangling_ptr(node.children[i as int])
                &&& result.dv.child_linked(node, i)
            } by {
                assert(self.linked.root().valid_child_index(i)); // trigger
                if i != r {
                    assert(self.linked.dv.is_nondangling_ptr(node.children[i as int]));
                    assert(self.linked.dv.child_linked(self.linked.root(), i));
                    assert(result.dv.is_nondangling_ptr(node.children[i as int]));
                    assert(result.dv.child_linked(node, i));
                }
            }
            self.betree_diskview_diff(replacement, path_addrs);
            assert(self.linked.root().buffers.valid(self.linked.buffer_dv)); // trigger            
            assert(result.root().buffers.valid(result.buffer_dv));
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn ranking_after_substitution(self, replacement: LinkedBetree, path_addrs: PathAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
            replacement.valid_ranking(ranking),
            ranking.contains_key(self.linked.root.unwrap()),
            path_addrs.to_set().disjoint(ranking.dom()),
            self.linked.is_fresh(path_addrs.to_set()),
            replacement.is_fresh(path_addrs.to_set()),
        ensures 
            self.substitute(replacement, path_addrs).valid_ranking(new_ranking),
            self.linked.dv.fresh_ranking_extension(ranking, new_ranking),
            new_ranking.dom() =~= ranking.dom() + path_addrs.to_set()
        decreases self.depth
    {
        self.substitute_preserves_wf(replacement, path_addrs);
        PivotTable::route_lemma_auto();

        if self.depth == 0 {
            ranking
        } else {
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().substitute_preserves_wf(replacement, sub_path_addrs);

            self.linked.dv.subdisk_implies_ranking_validity(replacement.dv, ranking);
            assert(self.linked.valid_ranking(ranking));
            self.valid_ranking_throughout(ranking);

            let r = self.linked.root().pivots.route(self.key);
            assert(self.linked.root().valid_child_index(r as nat)); // trigger
            assert(self.subpath().linked.has_root());

            let intermediate_ranking = self.subpath().ranking_after_substitution(replacement, sub_path_addrs, ranking);
            let new_root_addr = path_addrs[0];
            let old_root_rank = intermediate_ranking[self.linked.root.unwrap()];
            let subtree_root_rank = intermediate_ranking[subtree.root.unwrap()];
            let new_root_rank = old_root_rank + subtree_root_rank + 1;
          
            let new_ranking = intermediate_ranking.insert(new_root_addr, new_root_rank);
            let result = self.substitute(replacement, path_addrs);

            assert forall |addr| #[trigger] new_ranking.contains_key(addr) && result.dv.entries.contains_key(addr)
            implies result.dv.node_children_respects_rank(new_ranking, addr)
            by {
                self.betree_diskview_diff(replacement, path_addrs);
                if addr == new_root_addr {
                    let node = result.dv.entries[addr];
                    assert forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int].is_Some()
                    implies {
                        &&& new_ranking.contains_key(node.children[i as int].unwrap())
                        &&& new_ranking[node.children[i as int].unwrap()] < new_ranking[addr]
                    } by {
                        assert(self.linked.root().valid_child_index(i)); // trigger
                        if i != r {
                            assert(intermediate_ranking.contains_key(node.children[i as int].unwrap()));
                            assert(intermediate_ranking.contains_key(self.linked.root.unwrap()));
                            assert(self.linked.root().valid_child_index(i));

                            assert(new_ranking.contains_key(node.children[i as int].unwrap()));
                            assert(new_ranking[node.children[i as int].unwrap()] < new_ranking[addr]);
                        }
                    }
                }
            }
            path_addrs_to_set_additive(path_addrs);
            new_ranking
        }
    }

    pub proof fn substitute_commutes_with_i(self, replacement: LinkedBetree, path_addrs: PathAddrs, ranking: Ranking)
        requires 
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
            self.linked.valid_ranking(ranking),
            replacement.valid_ranking(ranking),
            ranking.contains_key(self.linked.root.unwrap()),
            path_addrs.to_set().disjoint(ranking.dom()),
            self.linked.is_fresh(path_addrs.to_set()),
            replacement.is_fresh(path_addrs.to_set()),
        ensures 
            self.substitute(replacement, path_addrs).acyclic(), 
            self.i().can_substitute(replacement.i()),
            self.substitute(replacement, path_addrs).i() === self.i().substitute(replacement.i())
        decreases self.depth
    {        
        self.i_valid();
        replacement.i_wf();

        if 0 < self.depth {
            let new_ranking = self.ranking_after_substitution(replacement, path_addrs, ranking);
            let result = self.substitute(replacement, path_addrs);

            self.substitute_preserves_wf(replacement, path_addrs);
            assert(result.valid_ranking(new_ranking));

            result.i_node_ignores_ranking(result.the_ranking(), new_ranking);
            self.target_commutes_with_i();

            PivotTable::route_lemma_auto();
            result.i_children_lemma(result.the_ranking());
            self.linked.i_children_lemma(self.linked.the_ranking());

            let r = self.linked.root().pivots.route(self.key);
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            let new_children = self.linked.root().children.update(r, subtree.root);

            assert forall |i| 0 <= i < result.i().get_Node_children().len()
            implies #[trigger] result.i().get_Node_children()[i] == self.i().substitute(replacement.i()).get_Node_children()[i]
            by {
                assert(self.linked.root().valid_child_index(i as nat));
                assert(result.root().valid_child_index(i as nat));

                self.linked.child_at_idx_acyclic(i as nat);
                result.child_at_idx_acyclic(i as nat);

                let child = self.linked.child_at_idx(i as nat);
                let new_child = result.child_at_idx(i as nat);
                if i == r {
                    result.child_at_idx_commutes_with_i(i as nat);
                    new_child.i_node_ignores_ranking(result.the_ranking(), new_child.the_ranking());
                    
                    self.subpath().substitute_commutes_with_i(replacement, sub_path_addrs, ranking);
                    self.subpath().betree_diskview_diff(replacement, sub_path_addrs);
                    self.betree_diskview_diff(replacement, path_addrs);
                    self.subpath_commutes_with_i();

                    subtree.dv.subdisk_implies_ranking_validity(new_child.dv, new_child.the_ranking());
                    subtree.betree_subdisk_preserves_i_with_ranking(new_child, new_child.the_ranking());
                    subtree.i_node_ignores_ranking(subtree.the_ranking(), new_child.the_ranking());
                } else {
                    child.dv.subdisk_implies_ranking_validity(new_child.dv, new_ranking);
                    child.betree_subdisk_preserves_i_with_ranking(new_child, new_ranking);
                    child.i_node_ignores_ranking(new_ranking, self.linked.the_ranking());
                    new_child.i_node_ignores_ranking(new_ranking, result.the_ranking());
                }
            }
            assert(result.i().get_Node_children() =~= self.i().substitute(replacement.i()).get_Node_children());
            result.root().buffers.subdisk_implies_same_i(self.linked.buffer_dv, result.buffer_dv);
            assert(result.i().get_Node_buffers() =~= self.i().substitute(replacement.i()).get_Node_buffers());
        }
    }

    pub proof fn fresh_substitution_implies_subdisk(self, replacement: LinkedBetree, path_addrs: PathAddrs)
        requires 
            self.can_substitute(replacement, path_addrs),
            self.linked.dv.is_subdisk(replacement.dv),
            self.linked.buffer_dv.is_subdisk(replacement.buffer_dv),
            self.linked.is_fresh(path_addrs.to_set())
        ensures 
            self.linked.dv.is_subdisk(self.substitute(replacement, path_addrs).dv),
            self.linked.buffer_dv.is_subdisk(self.substitute(replacement, path_addrs).buffer_dv)
        decreases
            self.depth
    {
        if 0 < self.depth {
            self.subpath().fresh_substitution_implies_subdisk(replacement, path_addrs.subrange(1, path_addrs.len() as int));
        }
    }
}

impl LinkedBetreeVars::Label {
    pub open spec(checked) fn i(self) -> FilteredBetree::Label
    {
        match self {
            LinkedBetreeVars::Label::Query{end_lsn, key, value} => FilteredBetree::Label::Query{end_lsn: end_lsn, key: key, value: value},
            LinkedBetreeVars::Label::Put{puts} => FilteredBetree::Label::Put{puts: puts},
            LinkedBetreeVars::Label::FreezeAs{stamped_betree} =>
                FilteredBetree::Label::FreezeAs{stamped_betree:
                    if stamped_betree.value.acyclic() { 
                        i_stamped_betree(stamped_betree) 
                    } else { arbitrary() } },
                    LinkedBetreeVars::Label::Internal{} => FilteredBetree::Label::Internal{},
        }
    }
} // end impl LinkedBetreeVars::Label

impl LinkedBetreeVars::State {
    pub open spec(checked) fn inv(self) -> bool 
    {
        &&& self.wf()
        &&& self.linked.acyclic()
        &&& self.linked.has_root() ==> self.linked.root().my_domain() == total_domain()
    }

    pub open spec(checked) fn i(self) -> FilteredBetree::State
        recommends self.wf(), self.linked.acyclic()
    {
        FilteredBetree::State{root: self.linked.i(), memtable: self.memtable}
    }

    pub proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires LinkedBetreeVars::State::initialize(self, stamped_betree), stamped_betree.value.acyclic()
        ensures FilteredBetree::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        self.linked.i_wf();
    }

    pub proof fn query_refines(self, post: Self, lbl: LinkedBetreeVars::Label, receipt: QueryReceipt)
        requires self.inv(), LinkedBetreeVars::State::query(self, post, lbl, receipt)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        receipt.i_valid();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::query(receipt.i())));
    }

    pub proof fn put_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), LinkedBetreeVars::State::put(self, post, lbl)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::put()));
    }

    pub proof fn freeze_as_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), LinkedBetreeVars::State::freeze_as(self, post, lbl)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        self.linked.i_wf();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::freeze_as()));
    }

    pub proof fn internal_flush_memtable_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_addrs: TwoAddrs)
        requires self.inv(), LinkedBetreeVars::State::internal_flush_memtable(self, post, lbl, new_addrs)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        self.linked.push_memtable_commutes_with_i(self.memtable, new_addrs);
        self.linked.i_wf();
        post.linked.i_wf();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush_memtable()));
    }

    pub proof fn internal_grow_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_root_addr: Address)
        requires self.inv(), LinkedBetreeVars::State::internal_grow(self, post, lbl, new_root_addr)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        self.linked.grow_commutes_with_i(new_root_addr);
        self.linked.i_wf();
        post.linked.i_wf();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_grow()));
    }

    pub proof fn internal_split_refines(self, post: Self, lbl: LinkedBetreeVars::Label, path: Path, request: SplitRequest, 
        new_addrs: SplitAddrs, path_addrs: PathAddrs)
        requires self.inv(), LinkedBetreeVars::State::internal_split(self, post, lbl, path, request, new_addrs, path_addrs)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        assume(false);
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        path.i_valid();
        path.target_commutes_with_i();
        path.target().split_parent_commutes_with_i(request, new_addrs);
        
        let replacement = path.target().split_parent(request, new_addrs);
        let old_ranking = self.linked.build_tight_ranking(self.linked.the_ranking());
        path.valid_ranking_throughout(old_ranking);

        let new_ranking = path.target().split_new_ranking(request, new_addrs, old_ranking);
        path.fresh_substitution_implies_subdisk(replacement, path_addrs);
        path.substitute_commutes_with_i(replacement, path_addrs, new_ranking);
        path.substitute(replacement, path_addrs).build_tight_preserves_i();

        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_split(path.i(), request)));
    }

    pub proof fn internal_flush_refines(self, post: Self, lbl: LinkedBetreeVars::Label, path: Path, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
        requires self.inv(), LinkedBetreeVars::State::internal_flush(self, post, lbl, path, child_idx, buffer_gc, new_addrs, path_addrs)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        path.i_valid();
        path.target_commutes_with_i();
        path.target().flush_commutes_with_i(child_idx, buffer_gc, new_addrs);

        let replacement = path.target().flush(child_idx, buffer_gc, new_addrs);
        let old_ranking = self.linked.build_tight_ranking(self.linked.the_ranking());
        path.valid_ranking_throughout(old_ranking);

        let new_ranking = path.target().flush_new_ranking(child_idx, buffer_gc, new_addrs, old_ranking);
        path.fresh_substitution_implies_subdisk(replacement, path_addrs);
        path.substitute_commutes_with_i(replacement, path_addrs, new_ranking);
        path.substitute(replacement, path_addrs).build_tight_preserves_i();

        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush(path.i(), child_idx, buffer_gc)));
    }

    pub proof fn internal_compact_refines(self, post: Self, lbl: LinkedBetreeVars::Label, path: Path, start: nat, end: nat, 
        compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs)
        requires self.inv(), LinkedBetreeVars::State::internal_compact(self, post, lbl, path, start, end, compacted_buffer, new_addrs, path_addrs)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        path.i_valid();
        path.target_commutes_with_i();
        path.target().compact_commutes_with_i(start, end, compacted_buffer, new_addrs);

        let replacement = path.target().compact(start, end, compacted_buffer, new_addrs);
        let old_ranking = self.linked.build_tight_ranking(self.linked.the_ranking());
        path.valid_ranking_throughout(old_ranking);

        let new_ranking = path.target().compact_new_ranking(start, end, compacted_buffer, new_addrs, old_ranking);
        path.fresh_substitution_implies_subdisk(replacement, path_addrs);
        path.substitute_commutes_with_i(replacement, path_addrs, new_ranking);
        path.substitute(replacement, path_addrs).build_tight_preserves_i();

        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_compact(path.i(), start, end, compacted_buffer)));
    }

    pub proof fn internal_noop_noop(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), LinkedBetreeVars::State::internal_noop(self, post, lbl)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        self.linked.i_wf();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop()));
    }

    pub proof fn next_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), LinkedBetreeVars::State::next(self, post, lbl),
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);

        match choose |step| LinkedBetreeVars::State::next_by(self, post, lbl, step)
        {
            LinkedBetreeVars::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
            LinkedBetreeVars::Step::put() => { self.put_refines(post, lbl); }
            LinkedBetreeVars::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
            LinkedBetreeVars::Step::internal_flush_memtable(new_addrs) => { self.internal_flush_memtable_refines(post, lbl, new_addrs); }
            LinkedBetreeVars::Step::internal_grow(new_root_addr) => { self.internal_grow_refines(post, lbl, new_root_addr); }
            LinkedBetreeVars::Step::internal_split(path, split_request, new_addrs, path_addrs) => { self.internal_split_refines(post, lbl, path, split_request, new_addrs, path_addrs); }
            LinkedBetreeVars::Step::internal_flush(path, child_idx, buffer_gc, new_addrs, path_addrs) => { self.internal_flush_refines(post, lbl, path, child_idx, buffer_gc, new_addrs, path_addrs); }
            LinkedBetreeVars::Step::internal_compact(path, start, end, compacted_buffer, new_addrs, path_addrs) => { self.internal_compact_refines(post, lbl, path, start, end, compacted_buffer, new_addrs, path_addrs); }
            LinkedBetreeVars::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
            _ => { assert(false); } 
        }
    }
} // end impl LinkedBetreeVars::State

}//verus
