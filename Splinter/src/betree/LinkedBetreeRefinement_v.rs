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
use crate::betree::LinkedSeq_v::*;
use crate::betree::BufferDisk_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::FilteredBetree_v;
use crate::betree::FilteredBetree_v::FilteredBetree;
use crate::betree::LinkedBetree_v::*;
use crate::betree::SplitRequest_v::*;

verus! {

impl LinkedBetree<BufferDisk>{
    pub open spec/*XXX(checked)*/ fn i_children_seq(self, ranking: Ranking, start: nat) -> Seq<FilteredBetree_v::BetreeNode>
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
                buffers: i_buffer_seq(root.buffers, self.buffer_dv),
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

    proof fn i_children_seq_lemma(self, ranking: Ranking, start: nat)
        requires 
            self.has_root(), 
            self.valid_ranking(ranking),
            start <= self.root().children.len()
        ensures ({
            let result = self.i_children_seq(ranking, start);
            &&& result.len() == self.root().children.len() - start
            &&& forall |i| 0 <= i < result.len() ==>
            {
                &&& (#[trigger] result[i]).wf()
                &&& result[i] == self.child_at_idx((i+start) as nat).i_node(ranking)
            }
        })
        decreases 
            self.get_rank(ranking), 0nat, self.root().children.len()-start 
    {
        if start < self.root().children.len() {
            assert(self.root().valid_child_index(start)); // trigger
            self.child_at_idx(start).i_node_wf(ranking);
            self.i_children_seq_lemma(ranking, start+1);
        } 
    }

    proof fn i_children_lemma(self, ranking: Ranking)
        requires 
            self.has_root(), 
            self.valid_ranking(ranking)
        ensures
            self.i_node(ranking).wf_children(),
            self.i_children(ranking).len() == self.root().children.len(),
            forall |i| (#[trigger] self.root().valid_child_index(i))
                ==> self.i_children(ranking)[i as int] == self.child_at_idx(i).i_node(ranking)
        decreases self.get_rank(ranking), 1nat
    {
        self.i_children_seq_lemma(ranking, 0);
    }

    proof fn i_node_wf(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures self.i_node(ranking).wf()
        decreases self.get_rank(ranking), 2nat
    {
        if self.has_root() {
            self.i_children_lemma(ranking);
            let out = self.i_node(ranking);

            assert forall |i| (
                #[trigger] out.valid_child_index(i)
                && out->children[i as int] is Node
                && out->children[i as int].local_structure()    
            ) implies (
                out->children[i as int].my_domain() == out.child_domain(i)
            ) by {
                assert(self.root().valid_child_index(i));
            }
        }
    }

    proof fn i_wf(self)
        requires self.acyclic()
        ensures self.i().wf()
    {
        self.i_node_wf(self.the_ranking());
    }

    // proof fn child_at_idx_valid_ranking(self, idx: nat)
    //     requires self.acyclic(), self.has_root(), self.root().valid_child_index(idx)
    //     ensures forall |ranking: Ranking| self.valid_ranking(ranking) 
    //         ==> #[trigger] self.child_at_idx(idx).valid_ranking(ranking)
    // { 
    // }

//     proof fn child_for_key_valid_index(self, k: Key)
//         requires self.wf(), self.has_root(), self.root().key_in_domain(k)
//         ensures 0 <= self.root().pivots.route(k),
//             self.root().valid_child_index(self.root().pivots.route(k) as nat)
//     {
//         self.root().pivots.route_lemma(k);
//     }

//     proof fn child_for_key_acyclic(self, k: Key)
//         requires self.acyclic(), self.has_root(), self.root().key_in_domain(k)
//         ensures self.child_for_key(k).acyclic()
//     {
//         self.child_for_key_valid_index(k);
//         assert(self.child_for_key(k).valid_ranking(self.the_ranking()));
//     }

    proof fn i_children_ignores_ranking(self, r1: Ranking, r2: Ranking)
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

    proof fn i_node_ignores_ranking(self, r1: Ranking, r2: Ranking)
        requires self.wf(), self.valid_ranking(r1), self.valid_ranking(r2)
        ensures self.i_node(r1) == self.i_node(r2)
        decreases self.get_rank(r1), 1nat
    {
        if self.has_root() {
            self.i_children_ignores_ranking(r1, r2);
        }
    }

    // proof fn child_at_idx_commutes_with_i(self, idx: nat) 
    //     requires 
    //         self.acyclic(),
    //         self.has_root(),
    //         self.root().valid_child_index(idx), 
    //     ensures 
    //         self.i().valid_child_index(idx),
    //         self.child_at_idx(idx).i() == self.i()->children[idx as int]
    // {
    //     let child = self.child_at_idx(idx);
    //     self.child_at_idx_acyclic(idx);
    //     self.i_children_lemma(self.the_ranking());
    //     child.i_node_ignores_ranking(self.the_ranking(), child.the_ranking());
    // }

    proof fn child_for_key_commutes_with_i(self, k: Key)
        requires self.acyclic(), self.has_root(), self.root().key_in_domain(k)
        ensures 
            self.child_for_key(k).acyclic(),
            self.child_for_key(k).i() == self.i().child(k)
    {
        let r = self.root().pivots.route(k) as nat;
        let child = self.child_for_key(k);

        self.root().pivots.route_lemma(k);
        assert(self.root().valid_child_index(r));
        assert(child.valid_ranking(self.the_ranking()));

        self.i_children_lemma(self.the_ranking());
        child.i_node_ignores_ranking(self.the_ranking(), child.the_ranking());
    }

    proof fn indexiness_commutes_with_i(self)
        requires self.acyclic(), self.has_root()
        ensures 
            self.root().is_index() ==> self.i().is_index(),
            self.root().is_leaf() ==> self.i().is_leaf()
    {
        self.i_wf();
        self.i_children_lemma(self.the_ranking());

        if self.root().is_index() {
            assert forall |i:nat| 0 <= i < self.i()->children.len()
            implies #[trigger] self.i()->children[i as int] is Node
            by {
                assert(self.root().valid_child_index(i));
            }
        }
    }

    // proof fn betree_subdisk_preserves_i(self, big: LinkedBetree<BufferDisk>, ranking: Ranking)
    //     requires 
    //         self.wf(), 
    //         big.wf(),
    //         self.root == big.root,
    //         self.dv.is_sub_disk(big.dv),
    //         self.buffer_dv.is_sub_disk(big.buffer_dv),
    //         self.valid_buffer_dv(),
    //         big.valid_ranking(ranking),
    //     ensures
    //         // self.valid_ranking(ranking),
    //         self.i() == big.i()
    //     decreases 
    //         self.get_rank(ranking), big.get_rank(ranking)
    // {
    //     self.dv.subdisk_implies_ranking_validity(big.dv, ranking);
    //     assert(self.valid_ranking(ranking));

    //     if self.has_root() {


    //         subdisk_implies_same_i(self.root().buffers, self.buffer_dv, big.buffer_dv);

    //         self.i_children_lemma(ranking);
    //         big.i_children_lemma(ranking);

    //         let a = self.i_node(ranking)->children;
    //         let b = big.i_node(ranking)->children;
    //         assert(a.len() == b.len());

    //         assert forall |i| 0 <= i < a.len()
    //         implies a[i] == b[i]
    //         by {
    //             assert(self.root().valid_child_index(i as nat));
    //             assert(big.root().valid_child_index(i as nat));

    //             self.child_at_idx_acyclic(i as nat);
    //             big.child_at_idx_acyclic(i as nat);

    //             self.child_at_idx(i as nat).betree_subdisk_preserves_i(big.child_at_idx(i as nat), ranking);
    //             // self.child_at_idx(i as nat).betree_subdisk_preserves_i(big.child_at_idx(i as nat), ranking);

    //         }
    //         assert(a =~= b);
    //     }
    // }


    // proof fn betree_subdisk_preserves_i_with_ranking(self, big: LinkedBetree<BufferDisk>, ranking: Ranking)
    //     requires 
    //         self.wf(), big.wf(),
    //         self.root == big.root,
    //         self.dv.is_sub_disk(big.dv),
    //         self.buffer_dv.is_sub_disk(big.buffer_dv),
    //         big.valid_ranking(ranking),
    //     ensures
    //         self.valid_ranking(ranking),
    //         self.i_node(ranking) == big.i_node(ranking)
    //     decreases self.get_rank(ranking), big.get_rank(ranking)
    // {
    //     self.dv.subdisk_implies_ranking_validity(big.dv, ranking);
    //     assert(self.valid_ranking(ranking));

    //     if self.has_root() {
    //         self.root().buffers.subdisk_implies_same_i(self.buffer_dv, big.buffer_dv);

    //         self.i_children_lemma(ranking);
    //         big.i_children_lemma(ranking);

    //         let a = self.i_node(ranking)->children;
    //         let b = big.i_node(ranking)->children;
    //         assert(a.len() == b.len());

    //         assert forall |i| 0 <= i < a.len()
    //         implies a[i] == b[i]
    //         by {
    //             assert(self.root().valid_child_index(i as nat));
    //             assert(big.root().valid_child_index(i as nat));

    //             self.child_at_idx_acyclic(i as nat);
    //             big.child_at_idx_acyclic(i as nat);

    //             self.child_at_idx(i as nat).betree_subdisk_preserves_i_with_ranking(big.child_at_idx(i as nat), ranking);
   
    //         }
    //         assert(a =~= b);
    //     }
    // }


//     proof fn reachable_addrs_are_closed(self, ranking: Ranking, addr: Address)
//         requires 
//             self.wf(), self.has_root(), 
//             self.valid_ranking(ranking),
//             self.reachable_addrs_using_ranking(ranking).contains(addr),
//             self.dv.entries.dom().contains(addr),
//         ensures ({
//             let node = self.dv.entries[addr];
//             &&& forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int] is Some 
//                 ==> self.reachable_addrs_using_ranking(ranking).contains(node.children[i as int].unwrap())
//         })
//         decreases self.get_rank(ranking)
//     {
//         let node = self.dv.entries[addr];
//         let reachable_addrs = self.reachable_addrs_using_ranking(ranking);
//         self.reachable_addrs_using_ranking_closed(ranking);

//         assert forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int] is Some 
//         implies reachable_addrs.contains(node.children[i as int].unwrap())
//         by {
//             if addr == self.root.unwrap() {
//                 self.child_at_idx(i).reachable_addrs_using_ranking_closed(ranking);
//                 assert(self.child_at_idx(i).has_root());
//                 self.reachable_addrs_using_ranking_recur_body_lemma(ranking, 0);
//                 assert(reachable_addrs.contains(node.children[i as int].unwrap()));
//             } else {
//                 assert(self.reachable_addrs_using_ranking(ranking).contains(addr));
//                 let i = choose |i| self.child_subtree_contains_addr(ranking, addr, 0, i);
//                 assert(self.root().valid_child_index(i)); // trigger
//                 self.child_at_idx(i).reachable_addrs_are_closed(ranking, addr);
//                 self.reachable_addrs_using_ranking_recur_body_lemma(ranking, 0);
//             }
//         }
//     }

//     proof fn build_tight_preserves_wf(self, ranking: Ranking)
//         requires self.wf(), self.valid_ranking(ranking)
//         ensures self.build_tight_tree().wf()
//         decreases self.get_rank(ranking)
//     {
//         let result = self.build_tight_tree();

//         assert forall |addr| #[trigger] result.dv.entries.contains_key(addr)
//         implies {
//             &&& result.dv.node_has_nondangling_child_ptrs(result.dv.entries[addr])
//             &&& result.dv.node_has_linked_children(result.dv.entries[addr])
//         } by {
//             self.reachable_addrs_are_closed(self.the_ranking(), addr);
//         }

//         assert forall |addr| result.dv.entries.contains_key(addr)
//         implies #[trigger] result.dv.entries[addr].buffers.valid(result.buffer_dv)
//         by {
//             let node = result.dv.entries[addr];
//             assert(node.buffers.valid(self.buffer_dv)); // trigger
//             assert forall |i| 0 <= i < node.buffers.len()
//             implies #[trigger] result.buffer_dv.repr().contains(node.buffers[i])
//             by {
//                 assert(node.buffers.repr().contains(node.buffers[i]));
//                 assert(self.reachable_buffer(addr, node.buffers[i]));
//             }
//             assert(node.buffers.valid(result.buffer_dv));
//         }

//         lemma_len_subset(result.dv.entries.dom(), self.dv.entries.dom());
//         lemma_len_subset(result.buffer_dv.entries.dom(), self.buffer_dv.entries.dom());
//     }

//     proof fn build_tight_preserves_i(self)
//         requires self.acyclic()
//         ensures 
//             self.build_tight_tree().wf(),
//             self.build_tight_tree().valid_ranking(self.the_ranking()),
//             self.i() == self.build_tight_tree().i()
//     {
//         let ranking = self.the_ranking();
//         let result = self.build_tight_tree();
//         self.build_tight_preserves_wf(ranking);
//         assert(result.valid_ranking(ranking));
//         result.betree_subdisk_preserves_i_with_ranking(self, ranking);
//         result.i_node_ignores_ranking(ranking, result.the_ranking());
//     }

//     proof fn identical_children_commutes_with_i(self, idx: nat, other: LinkedBetree<BufferDisk>, other_idx: nat, ranking: Ranking)
//         requires 
//             self.wf(), self.has_root(), 
//             self.root().valid_child_index(idx),
//             other.wf(), other.has_root(), 
//             other.root().valid_child_index(other_idx),
//             self.valid_ranking(ranking),
//             other.valid_ranking(ranking),
//             self.dv.is_sub_disk(other.dv),
//             self.buffer_dv.is_sub_disk(other.buffer_dv),
//             self.root().children[idx as int] == other.root().children[other_idx as int]
//         ensures 
//             self.i()->children[idx as int] == other.i()->children[other_idx as int]
//     {
//         let child = self.child_at_idx(idx);
//         let other_child = other.child_at_idx(other_idx);

//         self.i_children_lemma(self.the_ranking());
//         other.i_children_lemma(other.the_ranking());

//         self.child_at_idx_commutes_with_i(idx);
//         other.child_at_idx_commutes_with_i(other_idx);

//         child.betree_subdisk_preserves_i_with_ranking(other_child, ranking);
//         child.i_node_ignores_ranking(self.the_ranking(), ranking);
//         other_child.i_node_ignores_ranking(other.the_ranking(), ranking);
//     }


//     // operations

//     // proof fn push_memtable_wf(self, memtable: Memtable, new_addrs: TwoAddrs)
//     //     requires 
//     //         self.wf(), 
//     //         new_addrs.no_duplicates(),
//     //         self.is_fresh(new_addrs.repr()),
//     //     ensures
//     //         self.push_memtable(memtable, new_addrs).wf()
//     // {
//     //     let result = self.push_memtable(memtable, new_addrs);

//     //     if self.has_root() {
//     //         assert forall |i| result.root().valid_child_index(i) ==> self.root().valid_child_index(i) by {} // trigger
//     //         assert(result.dv.node_has_nondangling_child_ptrs(result.root()));
//     //         assert(result.dv.node_has_linked_children(result.root()));
//     //     }
//     //     assert(result.dv.healthy_child_ptrs());
//     //     assert(result.dv.wf());

//     //     assert forall |addr| result.dv.entries.contains_key(addr)
//     //     implies #[trigger] result.dv.entries[addr].buffers.valid(result.buffer_dv)
//     //     by {
//     //         if addr == result.root.unwrap() && self.has_root() {
//     //             let node = result.root();
//     //             assert(node.buffers.len() == self.root().buffers.len() + 1);
//     //             assert(self.root().buffers.valid(self.buffer_dv));

//     //             assert forall |i| 0 <= i < node.buffers.len()
//     //             implies #[trigger] result.buffer_dv.repr().contains(node.buffers[i])
//     //             by {
//     //                 if i < node.buffers.len() - 1 {
//     //                     assert(self.root().buffers[i] == node.buffers[i]);
//     //                     assert(self.buffer_dv.repr().contains(node.buffers[i]));
//     //                     assert(result.buffer_dv.repr().contains(node.buffers[i]));
//     //                 } else {
//     //                     assert(node.buffers[i] == new_addrs.addr2);
//     //                 }
//     //             }
//     //         } else if addr != result.root.unwrap() {
//     //             assert(result.dv.entries[addr].buffers.valid(self.buffer_dv)); //  trigger
//     //         }
//     //     }
//     //     assert(result.dv.no_dangling_buffer_ptr(result.buffer_dv));
//     //     assert(result.wf());
//     // }

//     // #[verifier::spinoff_prover]
//     // proof fn push_memtable_new_ranking(self, memtable: Memtable, new_addrs: TwoAddrs, old_ranking: Ranking) -> (new_ranking: Ranking)
//     //     requires 
//     //         self.wf(), 
//     //         new_addrs.no_duplicates(),
//     //         self.is_fresh(new_addrs.repr()),
//     //         self.valid_ranking(old_ranking),
//     //         self.dv.ranking_is_tight(old_ranking)
//     //     ensures 
//     //         self.push_memtable(memtable, new_addrs).valid_ranking(new_ranking),
//     //         self.push_memtable(memtable, new_addrs).build_tight_tree().wf(),
//     //         self.push_memtable(memtable, new_addrs).build_tight_tree().valid_ranking(new_ranking),
//     //         new_ranking.dom() == old_ranking.dom().insert(new_addrs.addr1)
//     // {
//     //     let result = self.push_memtable(memtable, new_addrs);
//     //     self.push_memtable_wf(memtable, new_addrs);

//     //     let new_rank = if self.has_root() { old_ranking[self.root.unwrap()]+1 } else { 0 };
//     //     let new_ranking = old_ranking.insert(new_addrs.addr1, new_rank);

//     //     if self.has_root() {
//     //         // Add this to suppress "recommends" warning for `result.root()` call.
//     //         assert(result.has_root());
//     //         assert forall |i| result.root().valid_child_index(i) ==> self.root().valid_child_index(i) by {} // trigger
//     //     }

//     //     // tenzinhl: Adding this assertion caused the proof to go through. Unsure what it's triggering.
//     //     assert(result.dv.valid_ranking(new_ranking));

//     //     assert(result.valid_ranking(new_ranking));
//     //     result.build_tight_preserves_wf(new_ranking);
//     //     new_ranking
//     // }

//     proof fn push_memtable_commutes_with_i(self, memtable: Memtable, new_addrs: TwoAddrs)
//         requires 
//             self.acyclic(),
//             new_addrs.no_duplicates(),
//             self.is_fresh(new_addrs.repr()),
//         ensures
//             self.push_memtable(memtable, new_addrs).build_tight_tree().acyclic(),
//             self.push_memtable(memtable, new_addrs).build_tight_tree().i() == self.i().push_memtable(memtable)
//     {
//         let result = self.push_memtable(memtable, new_addrs);
//         let old_ranking = self.build_tight_ranking(self.the_ranking());
//         let new_ranking = self.push_memtable_new_ranking(memtable, new_addrs, old_ranking);

//         result.build_tight_preserves_i();
//         assert(result.build_tight_tree().i() == result.i());

//         result.i_node_ignores_ranking(result.the_ranking(), new_ranking);
//         result.i_children_lemma(result.the_ranking());

//         if self.has_root() {
//             assert(self.valid_ranking(new_ranking));

//             self.i_children_lemma(new_ranking);
//             result.i_children_lemma(new_ranking);

//             self.i_children_ignores_ranking(self.the_ranking(), new_ranking);
//             result.i_node_ignores_ranking(result.the_ranking(), new_ranking);

//             self.root().buffers.subdisk_implies_same_i(self.buffer_dv, result.buffer_dv);

//             let a = self.i_children(new_ranking);
//             let b = result.i_children(new_ranking);
//             assert(a.len() == b.len());

//             assert forall |i| 0 <= i < a.len()
//             implies a[i] =~= b[i]
//             by {
//                 self.identical_children_commutes_with_i(i as nat, result, i as nat, new_ranking);
//             }
//         }
        
//         assert(result.i()->children =~= self.i().push_memtable(memtable)->children);
//         assert(result.i()->buffers =~= self.i().push_memtable(memtable)->buffers);
//     }


//     proof fn fresh_entry_preserves_i(self, other: LinkedBetree<BufferDisk>, ranking: Ranking, new_addr: Address)
//         requires 
//             self.wf(), other.wf(),
//             self.root == other.root,
//             self.valid_ranking(ranking),
//             other.valid_ranking(ranking),
//             self.dv.is_sub_disk(other.dv),
//             self.dv.entries.dom().insert(new_addr) =~= other.dv.entries.dom(),
//             self.buffer_dv == other.buffer_dv,
//             self.is_fresh(Set::empty().insert(new_addr)),
//         ensures 
//             self.i_node(ranking) == other.i_node(ranking)
//         decreases self.get_rank(ranking)
//     {
//         if self.has_root() {
//             self.i_children_lemma(ranking);
//             other.i_children_lemma(ranking);

//             assert(self.i_children(ranking).len() == other.i_children(ranking).len());
//             assert forall |i| 0 <= i < self.i_children(ranking).len()
//             implies self.i_children(ranking)[i] == other.i_children(ranking)[i]
//             by {
//                 assert(self.root().valid_child_index(i as nat)); // trigger
//                 assert(other.root().valid_child_index(i as nat)); // trigger

//                 self.child_at_idx_acyclic(i as nat);
//                 other.child_at_idx_acyclic(i as nat);
//                 self.child_at_idx(i as nat).fresh_entry_preserves_i(other.child_at_idx(i as nat), ranking, new_addr);
//             }

//             assert(self.i_node(ranking)->children =~= other.i_node(ranking)->children);
//             assert(self.i_node(ranking)->buffers =~= other.i_node(ranking)->buffers);
//         }
//     }

//     proof fn grow_commutes_with_i(self, new_root_addr: Address)
//         requires 
//             self.acyclic(),
//             self.has_root() ==> self.root().my_domain() == total_domain(),
//             self.is_fresh(Set::empty().insert(new_root_addr))
//         ensures
//             self.grow(new_root_addr).acyclic(),
//             self.grow(new_root_addr).i() == self.i().grow()
//     {
//         let result = self.grow(new_root_addr);
//         let old_ranking = self.build_tight_ranking(self.the_ranking());
//         let new_ranking = self.grow_new_ranking(new_root_addr, old_ranking);
//         result.i_children_lemma(result.the_ranking());

//         result.child_at_idx_acyclic(0);
//         let child = result.child_at_idx(0);
//         result.child_at_idx_valid_ranking(0);
//         child.i_node_ignores_ranking(new_ranking, result.the_ranking());
        
//         self.i_node_ignores_ranking(self.the_ranking(), new_ranking);
//         self.fresh_entry_preserves_i(child, new_ranking, new_root_addr);

//         assert(result.i()->children =~= self.i().grow()->children);
//         assert(result.i()->buffers =~= self.i().grow()->buffers);
//     }

//     #[verifier::spinoff_prover]
//     proof fn split_parent_commutes_with_i(self, request: SplitRequest, new_addrs: SplitAddrs)
//         requires 
//             self.acyclic(), 
//             self.can_split_parent(request),
//             new_addrs.no_duplicates(),
//             self.is_fresh(new_addrs.repr()),
//         ensures 
//             self.split_parent(request, new_addrs).acyclic(),
//             self.i().can_split_parent(request),
//             self.split_parent(request, new_addrs).i() == self.i().split_parent(request)
//     {
//         // TODO(JL): fix
//         let result = self.split_parent(request, new_addrs);
//         let new_ranking = self.split_new_ranking(request, new_addrs, self.the_ranking());

//         let child_idx = request.xxxget_child_idx();
//         let old_child = self.child_at_idx(child_idx);

//         self.i_wf();
//         self.child_at_idx_acyclic(child_idx);
//         self.child_at_idx_commutes_with_i(child_idx);

//         old_child.i_node_ignores_ranking(self.the_ranking(), old_child.the_ranking());
//         old_child.indexiness_commutes_with_i();
//         assert(self.i().can_split_parent(request));

//         let a = result.i_children(result.the_ranking());
//         let b = self.i().split_parent(request)->children;

//         assert(a.len() == b.len()) by {
//             self.i_children_lemma(self.the_ranking());
//             result.i_children_lemma(result.the_ranking());
//         }

//         assert forall |i| 0 <= i < a.len()
//         implies a[i] =~= b[i]
//         by {
//             result.child_at_idx_acyclic(i as nat);
//             result.child_at_idx_commutes_with_i(i as nat);

//             if i < child_idx {
//                 self.identical_children_commutes_with_i(i as nat, result, i as nat, new_ranking);
//             } else if i == child_idx {
//                 let new_left_child = result.child_at_idx(i as nat);
//                 new_left_child.i_children_lemma(new_ranking);

//                 assert forall |j| 0 <= j < new_left_child.root().children.len()
//                 implies #[trigger] new_left_child.i_children(new_ranking)[j] == b[i]->children[j]
//                 by {
//                     assert(new_left_child.root().valid_child_index(j as nat));
//                     assert(old_child.root().valid_child_index(j as nat));

//                     let old_grand_child = old_child.child_at_idx(j as nat);
//                     let new_grand_child = new_left_child.child_at_idx(j as nat);

//                     old_child.i_children_lemma(self.the_ranking());
//                     old_grand_child.betree_subdisk_preserves_i_with_ranking(new_grand_child, new_ranking);
//                     old_grand_child.i_node_ignores_ranking(self.the_ranking(), new_ranking);
//                 }

//                 assert(new_left_child.i_children(new_ranking) =~= b[i]->children);
//                 new_left_child.i_node_ignores_ranking(new_ranking, new_left_child.the_ranking());
//             } else if i == child_idx + 1 {
//                 let new_right_child = result.child_at_idx(i as nat);
//                 new_right_child.i_children_lemma(new_ranking);

//                 assert forall |j| 0 <= j < new_right_child.root().children.len()
//                 implies #[trigger] new_right_child.i_children(new_ranking)[j] == b[i]->children[j]
//                 by {
//                     assert(new_right_child.root().valid_child_index(j as nat));

//                     if request is SplitIndex {
//                         let pivot_idx = request->child_pivot_idx;
//                         assert(old_child.root().valid_child_index((j + pivot_idx)  as nat));

//                         let old_grand_child = old_child.child_at_idx((j + pivot_idx)  as nat);
//                         let new_grand_child = new_right_child.child_at_idx(j as nat);
    
//                         old_child.i_children_lemma(self.the_ranking());
//                         old_grand_child.betree_subdisk_preserves_i_with_ranking(new_grand_child, new_ranking);
//                         old_grand_child.i_node_ignores_ranking(self.the_ranking(), new_ranking);
//                     } else {
//                         assert(old_child.root().valid_child_index(j as nat));
//                     }
//                 }

//                 assert(new_right_child.i_children(new_ranking) =~= b[i]->children);
//                 new_right_child.i_node_ignores_ranking(new_ranking, new_right_child.the_ranking());
//             } else {
//                 self.identical_children_commutes_with_i((i-1) as nat, result, i as nat, new_ranking);
//             }
//         }
//         assert(a =~= b);
//     }

//     #[verifier::spinoff_prover]
//     proof fn flush_commutes_with_i(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs)
//         requires 
//             self.acyclic(), 
//             self.can_flush(child_idx, buffer_gc), 
//             new_addrs.no_duplicates(),
//             self.is_fresh(new_addrs.repr()),
//         ensures 
//             self.flush(child_idx, buffer_gc, new_addrs).acyclic(),
//             self.i().can_flush(child_idx, buffer_gc),
//             self.flush(child_idx, buffer_gc, new_addrs).i() == self.i().flush(child_idx, buffer_gc)
//     {
//         let result = self.flush(child_idx, buffer_gc, new_addrs);
//         let new_ranking = self.flush_new_ranking(child_idx, buffer_gc, new_addrs, self.the_ranking());
        
//         self.i_wf();
//         assert(result.i()->buffers =~= self.i().flush(child_idx, buffer_gc)->buffers);

//         let a = result.i_children(result.the_ranking());
//         let b = self.i().flush(child_idx, buffer_gc)->children;

//         self.i_children_lemma(self.the_ranking());
//         result.i_children_lemma(result.the_ranking());

//         assert forall |i| 0 <= i < a.len()
//         implies a[i] =~= b[i]
//         by {
//             assert(self.root().valid_child_index(i as nat));
//             assert(result.root().valid_child_index(i as nat));

//             let old_child = self.child_at_idx(i as nat);
//             self.child_at_idx_acyclic(i as nat);
//             self.child_at_idx_commutes_with_i(i as nat);
//             self.child_at_idx_valid_ranking(i as nat);

//             let new_child = result.child_at_idx(i as nat);
//             result.child_at_idx_acyclic(i as nat);
//             result.child_at_idx_commutes_with_i(i as nat);
//             result.child_at_idx_valid_ranking(i as nat);

//             if i == child_idx {
//                 assert(a[i]->children == new_child.i_children(result.the_ranking()));
//                 assert(b[i]->children == old_child.i_children(self.the_ranking()));

//                 assert forall |j| 0 <= j < a[i]->children.len()
//                 implies a[i]->children[j] == b[i]->children[j]
//                 by {
//                     assert(old_child.root().valid_child_index(j as nat));
//                     assert(new_child.root().valid_child_index(j as nat));

//                     let old_grand_child = old_child.child_at_idx(j as nat);
//                     let new_grand_child = new_child.child_at_idx(j as nat);

//                     old_child.child_at_idx_acyclic(j as nat);
//                     new_child.child_at_idx_acyclic(j as nat);

//                     old_child.child_at_idx_valid_ranking(j as nat);
//                     new_child.child_at_idx_valid_ranking(j as nat);

//                     assert(a[i]->children[j] == new_grand_child.i_node(new_ranking)) by {
//                         new_child.i_children_lemma(result.the_ranking());
//                         new_grand_child.i_node_ignores_ranking(result.the_ranking(), new_ranking);
//                     }
//                     assert(b[i]->children[j] == old_grand_child.i_node(new_ranking)) by {
//                         // assert(b[i]->children[j] == old_child.i_children(self.the_ranking())[j]);
//                         old_child.i_children_lemma(self.the_ranking());
//                         // assert(old_child.i_children(self.the_ranking())[j] == old_grand_child.i_node(self.the_ranking()));
//                         old_grand_child.i_node_ignores_ranking(self.the_ranking(), new_ranking);
//                     }

//                     old_grand_child.betree_subdisk_preserves_i_with_ranking(new_grand_child, new_ranking);
//                     assert(new_grand_child.i_node(new_ranking) == old_grand_child.i_node(new_ranking));
//                 }
//                 assert(a[i]->children =~= b[i]->children);
//             } else {
//                 old_child.i_node_ignores_ranking(old_child.the_ranking(), new_ranking);
//                 new_child.i_node_ignores_ranking(new_child.the_ranking(), new_ranking);
//                 old_child.betree_subdisk_preserves_i_with_ranking(new_child, new_ranking);
//             }
//         }
//         assert(a =~= b);
//     }

//     proof fn can_compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs)
//         requires 
//             self.acyclic(), 
//             self.can_compact(start, end, compacted_buffer),
//             new_addrs.no_duplicates(),
//             self.is_fresh(new_addrs.repr()),
//         ensures 
//             self.i().can_compact(start, end, compacted_buffer)
//     {
//         self.i_wf();
//         assert(self.i() is Node);
//         assert(start < end <= self.i()->buffers.len());

//         let compact_slice = self.root().buffers.slice(start as int, end as int);
//         let i_compact_slice = self.i()->buffers.slice(start as int, end as int);
//         assert(compact_slice.i(self.buffer_dv) =~= i_compact_slice);
//         assert(self.root().buffers.valid(self.buffer_dv)); // trigger

//         let compact_ofs_map = self.root().make_offset_map().decrement(start);
//         let i_compact_ofs_map = self.i().make_offset_map().decrement(start);
//         assert(compact_ofs_map =~= i_compact_ofs_map);

//         assert forall |k| #![auto] self.root().compact_key_range(start, end, k, self.buffer_dv) == self.i().compact_key_range(start, end, k)
//         by {
//             if self.root().compact_key_range(start, end, k, self.buffer_dv) {
//                 let buffer_idx = choose |buffer_idx| compact_slice.key_in_buffer_filtered(self.buffer_dv, compact_ofs_map, 0, k, buffer_idx);
//                 assert(i_compact_slice.key_in_buffer_filtered(i_compact_ofs_map, 0, k, buffer_idx));
//             }

//             if self.i().compact_key_range(start, end, k) {
//                 let buffer_idx = choose |buffer_idx| i_compact_slice.key_in_buffer_filtered(i_compact_ofs_map, 0, k, buffer_idx);
//                 assert(i_compact_ofs_map.offsets[k] == compact_ofs_map.offsets[k]);

//                 assert(self.root().buffers[buffer_idx + start] == compact_slice[buffer_idx]);
//                 assert(self.buffer_dv.entries.contains_key(compact_slice[buffer_idx]));

//                 assert(i_compact_slice.key_in_buffer(0, k, buffer_idx) == compact_slice.key_in_buffer(self.buffer_dv, 0, k, buffer_idx));
//                 assert(compact_slice.key_in_buffer_filtered(self.buffer_dv, compact_ofs_map, 0, k, buffer_idx));
//             }
//         }

//         assert forall |k| #![auto] compacted_buffer.map.contains_key(k)
//         implies {
//             let from = if self.i().flushed_ofs(k) <= start { 0 } else { self.i().flushed_ofs(k)-start };
//             &&& compacted_buffer.query(k) == self.i()->buffers.slice(start as int, end as int).query_from(k, from)
//         } by {
//             let from = if self.i().flushed_ofs(k) <= start { 0 } else { self.i().flushed_ofs(k)-start };
//             compact_slice.query_from_commutes_with_i(self.buffer_dv, k, from);
//         }
//     }

//     #[verifier::spinoff_prover]
//     proof fn compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs)
//         requires 
//             self.acyclic(), 
//             self.can_compact(start, end, compacted_buffer),
//             new_addrs.no_duplicates(),
//             self.is_fresh(new_addrs.repr()),
//         ensures 
//             self.compact(start, end, compacted_buffer, new_addrs).acyclic(),
//             self.i().can_compact(start, end, compacted_buffer),
//             self.compact(start, end, compacted_buffer, new_addrs).i() == self.i().compact(start, end, compacted_buffer)
//     {
//         let result = self.compact(start, end, compacted_buffer, new_addrs);
//         let new_ranking = self.compact_new_ranking(start, end, compacted_buffer, new_addrs, self.the_ranking());
//         self.can_compact_commutes_with_i(start, end, compacted_buffer, new_addrs);

//         self.root().buffers.subdisk_implies_same_i(self.buffer_dv, result.buffer_dv);
//         assert(result.i()->buffers =~= self.i().compact(start, end, compacted_buffer)->buffers);

//         let a = result.i_children(result.the_ranking());
//         let b = self.i().compact(start, end, compacted_buffer)->children;
//         result.i_children_lemma(result.the_ranking());
//         assert(a.len() == b.len());

//         assert forall |i| 0 <= i < a.len()
//         implies a[i] == b[i]
//         by {
//             self.identical_children_commutes_with_i(i as nat, result, i as nat, new_ranking);
//         }
//         assert(a =~= b);
//     }

} // end impl LinkedBetree<BufferDisk>

pub open spec(checked) fn i_stamped_betree(stamped: StampedBetree) -> FilteredBetree_v::StampedBetree
    recommends stamped.value.acyclic()
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine<BufferDisk>{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::QueryReceiptLine
        recommends self.linked.acyclic()
    {
        FilteredBetree_v::QueryReceiptLine{ 
            node: self.linked.i(), 
            result: self.result 
        }
    }
}

impl QueryReceipt<BufferDisk>{
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

    proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
    {
        let i_receipt = self.i();
        let ranking = self.linked.the_ranking();

        assert(self.all_lines_wf());

        assert(i_receipt.all_lines_wf()) by {
            assert forall |i| 0 <= i < i_receipt.lines.len()
            implies #[trigger] i_receipt.lines[i].wf() by {
                PivotTable::route_lemma_auto();
                assert(self.lines[i].wf()); // trigger
                self.lines[i].linked.i_wf();
            }
    
            assert forall |i| 0 <= i < self.lines.len()-1 
            implies #[trigger] i_receipt.lines[i].node.key_in_domain(i_receipt.key)
            by {
                assert(i_receipt.lines[i].wf());
                assert(self.node(i).key_in_domain(self.key)); // trigger
            }
        }

        assert forall |i| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.child_linked_at(i) 
        by {
            assert(self.child_linked_at(i)); // trigger
            self.lines[i].linked.child_for_key_commutes_with_i(self.key);
        }

        assert forall |i| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.result_linked_at(i) by {
            let node = self.node(i);
            let start = node.flushed_ofs(self.key) as int;

            assert(self.lines[i].linked.has_root());
            assert(node.key_in_domain(self.key));
            node.pivots.route_lemma(self.key);
            // assert(start <= node.buffers.len());
            assert(self.result_linked_at(i)); // trigger
            query_from_commutes_with_i(node.buffers, self.linked.buffer_dv, self.key, start);
        }
    }
}

impl Path<BufferDisk>{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::Path
        recommends self.valid()
    {
        FilteredBetree_v::Path{node: self.linked.i(), key: self.key, depth: self.depth}
    }

    proof fn subpath_commutes_with_i(self)
        requires 
            0 < self.depth,
            self.valid(),
        ensures
            self.subpath().linked.acyclic(), 
            self.subpath().i() == self.i().subpath()
    {
        self.valid_ranking_throughout(self.linked.the_ranking());
        self.linked.child_for_key_commutes_with_i(self.key);
    }

    proof fn i_valid(self)
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

    proof fn target_commutes_with_i(self) 
        requires 
            self.valid(), 
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

//     proof fn betree_diskview_diff(self, replacement: LinkedBetree<BufferDisk>, path_addrs: PathAddrs)
//         requires 
//             self.can_substitute(replacement, path_addrs),
//             path_addrs.no_duplicates(),
//         ensures 
//             self.substitute(replacement, path_addrs).dv.entries.dom() =~= replacement.dv.entries.dom() + path_addrs.to_set()
//         decreases self.depth
//     {
//         let result = self.substitute(replacement, path_addrs);

//         if 0 < self.depth {
//             let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
//             let subtree = self.subpath().substitute(replacement, sub_path_addrs);
//             self.subpath().betree_diskview_diff(replacement, sub_path_addrs);
//             path_addrs_to_set_additive(path_addrs);
//         }
//     }

//     #[verifier::spinoff_prover]
//     proof fn substitute_preserves_wf(self, replacement: LinkedBetree<BufferDisk>, path_addrs: PathAddrs)
//         requires 
//             self.can_substitute(replacement, path_addrs),
//             path_addrs.no_duplicates(),
//             self.linked.is_fresh(path_addrs.to_set()),
//             replacement.is_fresh(path_addrs.to_set()),
//         ensures ({
//             let result = self.substitute(replacement, path_addrs);
//             &&& result.wf()
//             &&& result.has_root()
//             &&& result.root().my_domain() == self.linked.root().my_domain()
//             &&& self.linked.dv.is_sub_disk(result.dv)
//             &&& self.linked.buffer_dv.is_sub_disk(result.buffer_dv)
//             &&& result.dv.entries.dom() =~= (self.linked.dv.entries.dom() + replacement.dv.entries.dom() + path_addrs.to_set())
//         })
//         decreases self.depth, 1nat
//     {
//         if 0 < self.depth {
//             let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
//             let subtree = self.subpath().substitute(replacement, sub_path_addrs);
//             self.subpath().substitute_preserves_wf(replacement, sub_path_addrs);
//             path_addrs_to_set_additive(path_addrs);

//             let result = self.substitute(replacement, path_addrs);
//             let node = result.dv.entries[path_addrs[0]];

//             let r = node.pivots.route(self.key);
//             PivotTable::route_lemma_auto();
//             assert(self.linked.dv.entries.contains_key(self.linked.root.unwrap())); // trigger

//             assert forall |i| #[trigger] node.valid_child_index(i)
//             implies {
//                 &&& result.dv.is_nondangling_ptr(node.children[i as int])
//                 &&& result.dv.child_linked(node, i)
//             } by {
//                 assert(self.linked.root().valid_child_index(i)); // trigger
//                 if i != r {
//                     assert(self.linked.dv.is_nondangling_ptr(node.children[i as int]));
//                     assert(self.linked.dv.child_linked(self.linked.root(), i));
//                     assert(result.dv.is_nondangling_ptr(node.children[i as int]));
//                     assert(result.dv.child_linked(node, i));
//                 }
//             }
//             self.betree_diskview_diff(replacement, path_addrs);
//             assert(self.linked.root().buffers.valid(self.linked.buffer_dv)); // trigger            
//             assert(result.root().buffers.valid(result.buffer_dv));
//         }
//     }

//     proof fn substitute_commutes_with_i(self, replacement: LinkedBetree<BufferDisk>, path_addrs: PathAddrs, ranking: Ranking)
//         requires 
//             self.can_substitute(replacement, path_addrs),
//             path_addrs.no_duplicates(),
//             self.linked.valid_ranking(ranking),
//             replacement.valid_ranking(ranking),
//             ranking.contains_key(self.linked.root.unwrap()),
//             path_addrs.to_set().disjoint(ranking.dom()),
//             self.linked.is_fresh(path_addrs.to_set()),
//             replacement.is_fresh(path_addrs.to_set()),
//         ensures 
//             self.substitute(replacement, path_addrs).acyclic(), 
//             self.i().can_substitute(replacement.i()),
//             self.substitute(replacement, path_addrs).i() === self.i().substitute(replacement.i())
//         decreases self.depth
//     {        
//         self.i_valid();
//         replacement.i_wf();

//         if 0 < self.depth {
//             let new_ranking = self.ranking_after_substitution(replacement, path_addrs, ranking);
//             let result = self.substitute(replacement, path_addrs);

//             self.substitute_preserves_wf(replacement, path_addrs);
//             assert(result.valid_ranking(new_ranking));

//             result.i_node_ignores_ranking(result.the_ranking(), new_ranking);
//             self.target_commutes_with_i();

//             PivotTable::route_lemma_auto();
//             result.i_children_lemma(result.the_ranking());
//             self.linked.i_children_lemma(self.linked.the_ranking());

//             let r = self.linked.root().pivots.route(self.key);
//             let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
//             let subtree = self.subpath().substitute(replacement, sub_path_addrs);
//             let new_children = self.linked.root().children.update(r, subtree.root);

//             assert forall |i| 0 <= i < result.i()->children.len()
//             implies #[trigger] result.i()->children[i] == self.i().substitute(replacement.i())->children[i]
//             by {
//                 assert(self.linked.root().valid_child_index(i as nat));
//                 assert(result.root().valid_child_index(i as nat));

//                 self.linked.child_at_idx_acyclic(i as nat);
//                 result.child_at_idx_acyclic(i as nat);

//                 let child = self.linked.child_at_idx(i as nat);
//                 let new_child = result.child_at_idx(i as nat);
//                 if i == r {
//                     result.child_at_idx_commutes_with_i(i as nat);
//                     new_child.i_node_ignores_ranking(result.the_ranking(), new_child.the_ranking());
                    
//                     self.subpath().substitute_commutes_with_i(replacement, sub_path_addrs, ranking);
//                     self.subpath().betree_diskview_diff(replacement, sub_path_addrs);
//                     self.betree_diskview_diff(replacement, path_addrs);
//                     self.subpath_commutes_with_i();

//                     subtree.dv.subdisk_implies_ranking_validity(new_child.dv, new_child.the_ranking());
//                     subtree.betree_subdisk_preserves_i_with_ranking(new_child, new_child.the_ranking());
//                     subtree.i_node_ignores_ranking(subtree.the_ranking(), new_child.the_ranking());
//                 } else {
//                     child.dv.subdisk_implies_ranking_validity(new_child.dv, new_ranking);
//                     child.betree_subdisk_preserves_i_with_ranking(new_child, new_ranking);
//                     child.i_node_ignores_ranking(new_ranking, self.linked.the_ranking());
//                     new_child.i_node_ignores_ranking(new_ranking, result.the_ranking());
//                 }
//             }
//             assert(result.i()->children =~= self.i().substitute(replacement.i())->children);
//             result.root().buffers.subdisk_implies_same_i(self.linked.buffer_dv, result.buffer_dv);
//             assert(result.i()->buffers =~= self.i().substitute(replacement.i())->buffers);
//         }
//     }

//     proof fn fresh_substitution_implies_subdisk(self, replacement: LinkedBetree<BufferDisk>, path_addrs: PathAddrs)
//         requires 
//             self.can_substitute(replacement, path_addrs),
//             self.linked.dv.is_sub_disk(replacement.dv),
//             self.linked.buffer_dv.is_sub_disk(replacement.buffer_dv),
//             self.linked.is_fresh(path_addrs.to_set())
//         ensures 
//             self.linked.dv.is_sub_disk(self.substitute(replacement, path_addrs).dv),
//             self.linked.buffer_dv.is_sub_disk(self.substitute(replacement, path_addrs).buffer_dv)
//         decreases
//             self.depth
//     {
//         if 0 < self.depth {
//             self.subpath().fresh_substitution_implies_subdisk(replacement, path_addrs.subrange(1, path_addrs.len() as int));
//         }
//     }
}

impl LinkedBetreeVars::Label {
    pub open spec(checked) fn i(self) -> FilteredBetree::Label
    {
        match self {
            LinkedBetreeVars::Label::Query{end_lsn, key, value} => 
                FilteredBetree::Label::Query{end_lsn: end_lsn, key: key, value: value},
            LinkedBetreeVars::Label::Put{puts} => 
                FilteredBetree::Label::Put{puts: puts},
            LinkedBetreeVars::Label::FreezeAs{stamped_betree} => 
                FilteredBetree::Label::FreezeAs{stamped_betree:
                    if stamped_betree.value.acyclic() { 
                        i_stamped_betree(stamped_betree) 
                    } else { arbitrary() } },    
            LinkedBetreeVars::Label::Internal{} => 
                FilteredBetree::Label::Internal{},
        }
    }
} // end impl LinkedBetreeVars::Label

impl LinkedBetreeVars::State {
    pub open spec(checked) fn i(self) -> FilteredBetree::State
        recommends 
            self.inv(),
    {
        FilteredBetree::State{root: self.linked.i(), memtable: self.memtable}
    }

    proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires 
            LinkedBetreeVars::State::initialize(self, stamped_betree)
        ensures 
            FilteredBetree::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        self.linked.i_wf();
    }

    proof fn query_refines(self, post: Self, lbl: LinkedBetreeVars::Label, receipt: QueryReceipt<BufferDisk>)
        requires 
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::query(self, post, lbl, receipt)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::query(receipt.i()))
    {
        reveal(FilteredBetree::State::next_by);
        receipt.i_valid();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::query(receipt.i())));
    }

    proof fn put_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::put(self, post, lbl)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::put())
    {
        reveal(FilteredBetree::State::next);

        assume(false);
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::put()));
    }

    proof fn freeze_as_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires 
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::freeze_as(self, post, lbl)
        ensures
            FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next_by);
        assume(false);

        // self.linked.i_wf();
        // assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::freeze_as()));
    }

    proof fn internal_flush_memtable_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_addrs: TwoAddrs)
        requires 
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::internal_flush_memtable(self, post, lbl, new_addrs)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush_memtable())
    {
        reveal(FilteredBetree::State::next_by);
        assume(false);
        // self.linked.push_memtable_commutes_with_i(self.memtable, new_addrs);
        // self.linked.i_wf();
        // post.linked.i_wf();
        // assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush_memtable()));
    }

    proof fn internal_grow_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_root_addr: Address)
        requires 
            self.inv(), 
            post.inv(),
            LinkedBetreeVars::State::internal_grow(self, post, lbl, new_root_addr)
        ensures  
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_grow())
    {
        reveal(FilteredBetree::State::next_by);
        assume(false);

        // self.linked.grow_commutes_with_i(new_root_addr);
        // self.linked.i_wf();
        // post.linked.i_wf();
        // assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_grow()));
    }

    proof fn internal_split_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_linked: LinkedBetree<BufferDisk>,
            path: Path<BufferDisk>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs)
        requires 
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::internal_split(self, post, lbl, new_linked, path, request, new_addrs, path_addrs)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_split(path.i(), request))
    {
        reveal(FilteredBetree::State::next_by);
        assume(false);

//         path.i_valid();
//         path.target_commutes_with_i();
//         path.target().split_parent_commutes_with_i(request, new_addrs);
        
//         let replacement = path.target().split_parent(request, new_addrs);
//         let old_ranking = self.linked.build_tight_ranking(self.linked.the_ranking());
//         path.valid_ranking_throughout(old_ranking);

//         let new_ranking = path.target().split_new_ranking(request, new_addrs, old_ranking);
//         path.fresh_substitution_implies_subdisk(replacement, path_addrs);
//         path.substitute_commutes_with_i(replacement, path_addrs, new_ranking);
//         path.substitute(replacement, path_addrs).build_tight_preserves_i();

//         assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_split(path.i(), request)));
    }

    proof fn internal_flush_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_linked: LinkedBetree<BufferDisk>, 
        path: Path<BufferDisk>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
        requires 
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::internal_flush(self, post, lbl, new_linked, path, child_idx, buffer_gc, new_addrs, path_addrs)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush(path.i(), child_idx, buffer_gc))
    {
        reveal(FilteredBetree::State::next_by);
        assume(false);

//         path.i_valid();
//         path.target_commutes_with_i();
//         path.target().flush_commutes_with_i(child_idx, buffer_gc, new_addrs);

//         let replacement = path.target().flush(child_idx, buffer_gc, new_addrs);
//         let old_ranking = self.linked.build_tight_ranking(self.linked.the_ranking());
//         path.valid_ranking_throughout(old_ranking);

//         let new_ranking = path.target().flush_new_ranking(child_idx, buffer_gc, new_addrs, old_ranking);
//         path.fresh_substitution_implies_subdisk(replacement, path_addrs);
//         path.substitute_commutes_with_i(replacement, path_addrs, new_ranking);
//         path.substitute(replacement, path_addrs).build_tight_preserves_i();

//         assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush(path.i(), child_idx, buffer_gc)));
    }

    proof fn internal_compact_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_linked: LinkedBetree<BufferDisk>,
            path: Path<BufferDisk>, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs)
        requires 
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::internal_compact(self, post, lbl, new_linked, 
                path, start, end, compacted_buffer, new_addrs, path_addrs)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_compact(path.i(), start, end, compacted_buffer))
    {
        reveal(FilteredBetree::State::next_by);
        assume(false);
//         path.i_valid();
//         path.target_commutes_with_i();
//         path.target().compact_commutes_with_i(start, end, compacted_buffer, new_addrs);

//         let replacement = path.target().compact(start, end, compacted_buffer, new_addrs);
//         let old_ranking = self.linked.build_tight_ranking(self.linked.the_ranking());
//         path.valid_ranking_throughout(old_ranking);

//         let new_ranking = path.target().compact_new_ranking(start, end, compacted_buffer, new_addrs, old_ranking);
//         path.fresh_substitution_implies_subdisk(replacement, path_addrs);
//         path.substitute_commutes_with_i(replacement, path_addrs, new_ranking);
//         path.substitute(replacement, path_addrs).build_tight_preserves_i();

        // assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_compact(path.i(), start, end, compacted_buffer)));
    }

    proof fn internal_noop_noop(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), post.inv(), LinkedBetreeVars::State::internal_noop(self, post, lbl)
        ensures FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop())
    {
        reveal(FilteredBetree::State::next_by);

        self.linked.i_wf();
        assume(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop()));
    }

    proof fn next_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), post.inv(), LinkedBetreeVars::State::next(self, post, lbl),
        ensures FilteredBetree::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
        reveal(FilteredBetree::State::next);

        match choose |step| LinkedBetreeVars::State::next_by(self, post, lbl, step)
        {
            LinkedBetreeVars::Step::query(receipt) => 
                { self.query_refines(post, lbl, receipt); } 
            LinkedBetreeVars::Step::put() => 
                { self.put_refines(post, lbl); }
            LinkedBetreeVars::Step::freeze_as() => 
                { self.freeze_as_refines(post, lbl); }
            LinkedBetreeVars::Step::internal_flush_memtable(new_addrs) => 
                { self.internal_flush_memtable_refines(post, lbl, new_addrs); }
            LinkedBetreeVars::Step::internal_grow(new_root_addr) => 
                { self.internal_grow_refines(post, lbl, new_root_addr); }
            LinkedBetreeVars::Step::internal_split(new_linked, path, split_request, new_addrs, path_addrs) => 
                { self.internal_split_refines(post, lbl, new_linked, path, split_request, new_addrs, path_addrs); }
            LinkedBetreeVars::Step::internal_flush(new_linked, path, child_idx, buffer_gc, new_addrs, path_addrs) => 
                { self.internal_flush_refines(post, lbl, new_linked, path, child_idx, buffer_gc, new_addrs, path_addrs); }
            LinkedBetreeVars::Step::internal_compact(new_linked, path, start, end, compacted_buffer, new_addrs, path_addrs) => 
                { self.internal_compact_refines(post, lbl, new_linked, path, start, end, compacted_buffer, new_addrs, path_addrs); }
            LinkedBetreeVars::Step::internal_noop() => 
                { self.internal_noop_noop(post, lbl); }
            _ => 
                { assert(false); } 
        }
    }
} // end impl LinkedBetreeVars::State

}//verus
