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

    proof fn i_children_with_ranking(self, ranking: Ranking)
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
            self.i_children_with_ranking(ranking);
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

    proof fn i_children_lemma(self)
        requires 
            self.has_root(),
            self.acyclic(),
        ensures
            self.i().wf_children(),
            self.i()->children.len() == self.root().children.len(),
            forall |i| (#[trigger] self.root().valid_child_index(i))
            ==> ({
                &&& self.child_at_idx(i).acyclic()
                &&& self.i()->children[i as int] == self.child_at_idx(i).i()
            })
    {
        self.i_children_with_ranking(self.the_ranking());
        assert forall |i| #[trigger] self.root().valid_child_index(i)
        implies ({
            &&& self.child_at_idx(i).acyclic()
            &&& self.i()->children[i as int] == self.child_at_idx(i).i()
        }) by {
            let child = self.child_at_idx(i);
            self.child_at_idx_acyclic(i);
            child.i_node_ignores_ranking(child.the_ranking(), self.the_ranking());
        }
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
        requires 
            self.wf(), 
            self.has_root(),
            self.valid_ranking(r1), 
            self.valid_ranking(r2),
        ensures 
            self.i_children(r1) == self.i_children(r2)
        decreases 
            self.get_rank(r1), 0nat
    {
        let a = self.i_children(r1);
        let b = self.i_children(r2);

        self.i_children_with_ranking(r1);
        self.i_children_with_ranking(r2);

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
        requires 
            self.wf(), 
            self.valid_ranking(r1), 
            self.valid_ranking(r2)
        ensures 
            self.i_node(r1) == self.i_node(r2)
        decreases 
            self.get_rank(r1), 1nat
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
    //     self.i_children_with_ranking(self.the_ranking());
    //     child.i_node_ignores_ranking(self.the_ranking(), child.the_ranking());
    // }

    proof fn child_for_key_commutes_with_i(self, k: Key)
        requires 
            self.acyclic(), 
            self.has_root(), 
            self.root().key_in_domain(k)
        ensures 
            self.child_for_key(k).acyclic(),
            self.child_for_key(k).i() == self.i().child(k)
    {
        let r = self.root().pivots.route(k) as nat;
        self.root().pivots.route_lemma(k);
        assert(self.root().valid_child_index(r));
        self.i_children_lemma();
    }

    proof fn indexiness_commutes_with_i(self)
        requires
            self.acyclic(), 
            self.has_root()
        ensures 
            self.root().is_index() ==> self.i().is_index(),
            self.root().is_leaf() ==> self.i().is_leaf()
    {
        self.i_wf();
        self.i_children_with_ranking(self.the_ranking());

        if self.root().is_index() {
            assert forall |i:nat| 0 <= i < self.i()->children.len()
            implies #[trigger] self.i()->children[i as int] is Node
            by {
                assert(self.root().valid_child_index(i));
            }
        }
    }

    proof fn valid_buffer_dv_throughout(self)
        requires
            self.acyclic(),
            self.has_root(),
            self.valid_buffer_dv(),
        ensures 
            self.root().buffers.valid(self.buffer_dv),
            forall |i: nat| i < self.root().children.len()
            ==> #[trigger] self.child_at_idx(i).valid_buffer_dv(),
    {
        self.reachable_betree_addrs_using_ranking_closed(self.the_ranking());
    
        let buffers = self.root().buffers;   
        assert forall |i| 0 <= i < buffers.len() 
        implies self.buffer_dv.repr().contains(#[trigger] buffers[i])
        by {
            assert(self.reachable_buffer(self.root.unwrap(), buffers[i]));
        }

        assert forall |i: nat| i < self.root().children.len()
        implies #[trigger] self.child_at_idx(i).valid_buffer_dv()
        by {
            self.child_at_idx_reachable_addrs_ensures(i);
        }
    }

    proof fn subdisk_preserves_i_with_ranking(self, big: Self, ranking: Ranking, big_ranking: Ranking)
        requires 
            self.valid_ranking(ranking),
            big.valid_ranking(big_ranking),
            self.root == big.root,
            self.dv.is_sub_disk(big.dv),
            self.buffer_dv.is_sub_disk(big.buffer_dv),
            self.valid_buffer_dv(),
        ensures
            self.i() == big.i()
        decreases 
            self.get_rank(ranking),
            big.get_rank(big_ranking),
    {
        if self.has_root() {
            self.valid_buffer_dv_throughout();
            assert(self.i()->buffers =~= big.i()->buffers);

            self.i_children_lemma();
            big.i_children_lemma();

            assert forall |i| 0 <= i < self.i()->children.len()
            implies self.i()->children[i] == big.i()->children[i]
            by {
                let child = self.child_at_idx(i as nat);
                let big_child = big.child_at_idx(i as nat);

                assert(self.root().valid_child_index(i as nat));
                assert(big.root().valid_child_index(i as nat));
                child.subdisk_preserves_i_with_ranking(big_child, ranking, big_ranking);
            }
            assert(self.i()->children =~= big.i()->children);
        }
    }

    proof fn subdisk_preserves_i(self, big: Self)
        requires 
            self.acyclic(),
            big.acyclic(),
            self.root == big.root,
            self.dv.is_sub_disk(big.dv),
            self.buffer_dv.is_sub_disk(big.buffer_dv),
            self.valid_buffer_dv(),
        ensures
            self.i() == big.i()
    {
        if self.has_root() {
            self.subdisk_preserves_i_with_ranking(big, self.the_ranking(), big.the_ranking());
        }
    }

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

    //         self.i_children_with_ranking(ranking);
    //         big.i_children_with_ranking(ranking);

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

    // proof fn same_child_commutes_with_i(self, idx: nat, other: LinkedBetree<BufferDisk>, other_idx: nat, ranking: Ranking)
    //     requires 
    //         self.wf(), 
    //         self.has_root(), 
    //         self.root().valid_child_index(idx),
    //         other.wf(), 
    //         other.has_root(), 
    //         other.root().valid_child_index(other_idx),
    //         self.valid_ranking(ranking),
    //         other.valid_ranking(ranking),
    //         self.dv.is_sub_disk(other.dv),
    //         self.buffer_dv.is_sub_disk(other.buffer_dv),
    //         self.root().children[idx as int] == other.root().children[other_idx as int]
    //     ensures 
    //         self.i()->children[idx as int] == other.i()->children[other_idx as int]
    // {
    //     let child = self.child_at_idx(idx);
    //     let other_child = other.child_at_idx(other_idx);

    //     self.i_children_with_ranking(self.the_ranking());
    //     other.i_children_with_ranking(other.the_ranking());

    //     self.child_at_idx_commutes_with_i(idx);
    //     other.child_at_idx_commutes_with_i(other_idx);

    //     child.betree_subdisk_preserves_i_with_ranking(other_child, ranking);
    //     child.i_node_ignores_ranking(self.the_ranking(), ranking);
    //     other_child.i_node_ignores_ranking(other.the_ranking(), ranking);
    // }

    proof fn valid_root_buffers(self)
        requires 
            self.acyclic(),
            self.has_root(),
            self.valid_buffer_dv(),
        ensures 
            self.root().buffers.valid(self.buffer_dv)
    {
        self.reachable_betree_addrs_using_ranking_closed(self.the_ranking());
    
        let buffers = self.root().buffers;   
        assert forall |i| 0 <= i < buffers.len() 
        implies self.buffer_dv.repr().contains(#[trigger] buffers[i])
        by {
            assert(self.reachable_buffer(self.root.unwrap(), buffers[i]));
        }
    }

    proof fn push_memtable_commutes_with_i(self, memtable: Memtable, new_addrs: TwoAddrs)
        requires 
            self.acyclic(),
            self.valid_buffer_dv(),
            self.push_memtable(memtable, new_addrs).acyclic(),
            self.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
        ensures
            self.push_memtable(memtable, new_addrs).i() == self.i().push_memtable(memtable)
    {
        self.i_wf();
        let result = self.push_memtable(memtable, new_addrs);
    
        if self.has_root() {
            self.i_children_lemma();
            result.i_children_lemma();
            self.valid_buffer_dv_throughout();

            assert forall |i: nat| i < self.i()->children.len()
            implies self.i()->children[i as int] =~= result.i()->children[i as int]
            by {
                assert(self.root().valid_child_index(i)); // trigger
                assert(result.root().valid_child_index(i)); // trigger
                self.child_at_idx(i).subdisk_preserves_i(result.child_at_idx(i));
            }
        } else {
            result.i_children_with_ranking(result.the_ranking());
        }

        assert(result.i()->buffers =~= self.i().push_memtable(memtable)->buffers);
        assert(result.i()->children =~= self.i().push_memtable(memtable)->children);
    }

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
//             self.i_children_with_ranking(ranking);
//             other.i_children_with_ranking(ranking);

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

    proof fn grow_commutes_with_i(self, new_root_addr: Address)
        requires 
            self.acyclic(),
            self.valid_buffer_dv(),
            self.grow(new_root_addr).acyclic(),
            self.has_root() ==> self.root().my_domain() == total_domain(),
            self.is_fresh(Set::empty().insert(new_root_addr))
        ensures
            self.grow(new_root_addr).i() == self.i().grow()
    {
        let result = self.grow(new_root_addr);
        let child = result.child_at_idx(0);

        result.i_children_lemma();
        assert(result.root().valid_child_index(0)); // trigger
        self.subdisk_preserves_i(child);

        assert(result.i()->buffers =~= self.i().grow()->buffers);
        assert(result.i()->children =~= self.i().grow()->children);
    }

    #[verifier::spinoff_prover]
    proof fn split_parent_commutes_with_i(self, request: SplitRequest, new_addrs: SplitAddrs)
        requires 
            self.acyclic(),
            self.split_parent(request, new_addrs).acyclic(),
            self.valid_buffer_dv(),
            self.can_split_parent(request),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.i().can_split_parent(request),
            self.split_parent(request, new_addrs).i() == self.i().split_parent(request)
    {
        let result = self.split_parent(request, new_addrs);
        let child_idx = request.get_child_idx();
        let child = self.child_at_idx(child_idx);

        self.i_wf();
        self.i_children_lemma();
        result.i_children_lemma();

        child.indexiness_commutes_with_i();
        assert(self.i().valid_child_index(child_idx)); // trigger
        assert(self.i().can_split_parent(request));
        assert(result.i()->children.len() == self.i().split_parent(request)->children.len());

        assert forall |i| 0 <= i < result.i()->children.len()
        implies 
            #[trigger] result.i()->children[i] == 
            self.i().split_parent(request)->children[i]
        by {
            let result_child = result.child_at_idx(i as nat);
            let i_child = self.i().split_parent(request)->children[i];

            assert(result.root().valid_child_index(i as nat)); // trigger
            self.valid_buffer_dv_throughout();

            if i < child_idx {
                assert(self.root().valid_child_index(i as nat));
                self.child_at_idx(i as nat).subdisk_preserves_i(result_child);
            } else if i <= child_idx + 1 {
                let delta = if i == child_idx + 1 && request is SplitIndex 
                    { request->child_pivot_idx } else { 0 } ;

                child.i_children_lemma();
                result_child.i_children_lemma();

                assert forall |j| 0 <= j < i_child->children.len()
                implies #[trigger] i_child->children[j] == result_child.i()->children[j]
                by {
                    assert(result_child.root().valid_child_index(j as nat));
                    assert(child.root().valid_child_index((delta + j) as nat));

                    child.child_at_idx_acyclic((delta + j) as nat);
                    child.valid_buffer_dv_throughout();
                    child.child_at_idx((delta + j) as nat).subdisk_preserves_i(result_child.child_at_idx(j as nat));
                }
                assert(i_child->children =~= result_child.i()->children);
            } else {
                assert(self.root().valid_child_index((i-1)as nat));
                self.child_at_idx((i-1)as nat).subdisk_preserves_i(result_child);
            }
        }
        assert(result.i()->children =~= self.i().split_parent(request)->children);
    }

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

//         self.i_children_with_ranking(self.the_ranking());
//         result.i_children_with_ranking(result.the_ranking());

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
//                         new_child.i_children_with_ranking(result.the_ranking());
//                         new_grand_child.i_node_ignores_ranking(result.the_ranking(), new_ranking);
//                     }
//                     assert(b[i]->children[j] == old_grand_child.i_node(new_ranking)) by {
//                         // assert(b[i]->children[j] == old_child.i_children(self.the_ranking())[j]);
//                         old_child.i_children_with_ranking(self.the_ranking());
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
//         result.i_children_with_ranking(result.the_ranking());
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

    proof fn target_valid_buffer_dv(self)
        requires 
            self.valid(), 
            self.linked.valid_buffer_dv(),
        ensures 
            self.target().valid_buffer_dv(),
        decreases self.depth
    {
        if 0 < self.depth {
            let node = self.linked.root();
            let r = node.pivots.route(self.key) as nat;

            node.pivots.route_lemma(self.key);
            assert(self.subpath().linked == self.linked.child_at_idx(r));
            self.linked.valid_buffer_dv_throughout();
            self.subpath().target_valid_buffer_dv();
        }
    }

    proof fn substitute_commutes_with_i(self, replacement: LinkedBetree<BufferDisk>, path_addrs: PathAddrs)
        requires 
            self.linked.acyclic(),
            replacement.acyclic(),
            self.can_substitute(replacement, path_addrs), 
            self.substitute(replacement, path_addrs).acyclic(),
            self.linked.valid_buffer_dv(),
            self.substitute(replacement, path_addrs).valid_buffer_dv(),
            path_addrs.no_duplicates(),
            replacement.is_fresh(path_addrs.to_set()),
        ensures 
            self.i().can_substitute(replacement.i()),
            self.substitute(replacement, path_addrs).i() === self.i().substitute(replacement.i())
        decreases self.depth
    {        
        self.i_valid();
        replacement.i_wf();

        if 0 < self.depth {
            let result = self.substitute(replacement, path_addrs);
            let ranking = result.the_ranking();
            self.substitute_ensures(replacement, path_addrs);

            let i_result = self.i().substitute(replacement.i());
            self.target_commutes_with_i();
            assert(self.i().can_substitute(replacement.i()));
    
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().substitute_ensures(replacement, sub_path_addrs);

            let r = self.linked.root().pivots.route(self.key);
            self.linked.root().pivots.route_lemma(self.key);

            assert( subtree.valid_ranking(ranking) ) by {
                assert(result.root().valid_child_index(r as nat)); // trigger
                subtree.dv.subdisk_implies_ranking_validity(result.dv, ranking);
            }

            assert( subtree.valid_buffer_dv() ) by {
                let result_child = result.child_at_idx(r as nat);
                assert(result_child.valid_ranking(ranking));
                subtree.agreeable_disks_same_reachable_betree_addrs(result_child, ranking);
                subtree.reachable_betree_addrs_ignore_ranking(subtree.the_ranking(), ranking);
                result_child.reachable_betree_addrs_ignore_ranking(result_child.the_ranking(), ranking);
                subtree.same_reachable_betree_addrs_implies_same_buffer_addrs(result_child);
                assert(subtree.reachable_buffer_addrs() == result.child_at_idx(r as nat).reachable_buffer_addrs());        
                result.child_at_idx_reachable_addrs_ensures(r as nat);
            }

            self.linked.valid_buffer_dv_throughout();
            assert(result.i()->buffers =~= i_result->buffers) by {
                assert(result.root().buffers == self.linked.root().buffers);
                subdisk_implies_same_i(result.root().buffers, self.linked.buffer_dv, result.buffer_dv);
            }

            result.i_children_lemma();
            self.linked.i_children_lemma();
            assert(result.i()->children.len() == i_result->children.len());

            assert forall |i| 0 <= i < result.i()->children.len()
            implies #[trigger] result.i()->children[i] == i_result->children[i]
            by {
                assert(self.linked.root().valid_child_index(i as nat)); // trigger
                assert(result.root().valid_child_index(i as nat)); // trigger

                if i != r {
                    self.linked.child_at_idx(i as nat).subdisk_preserves_i(result.child_at_idx(i as nat));
                } else {
                    self.linked.child_at_idx_reachable_addrs_ensures(r as nat);
                    self.subpath().substitute_commutes_with_i(replacement, sub_path_addrs);
                    subtree.subdisk_preserves_i(result.child_at_idx(i as nat));
                    assert(result.i()->children[i] == i_result->children[i]);
                }
            }
            assert(result.i()->children =~= i_result->children);
        }
    }
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
    }

    proof fn put_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::put(self, post, lbl)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::put())
    {
        reveal(FilteredBetree::State::next_by);
    }

    proof fn freeze_as_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires 
            self.inv(), 
            post.inv(), 
            LinkedBetreeVars::State::freeze_as(self, post, lbl)
        ensures
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::freeze_as())
    {
        reveal(FilteredBetree::State::next_by);
        self.linked.i_wf();
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
        self.linked.i_wf();
        post.linked.i_wf();
        self.linked.push_memtable_commutes_with_i(self.memtable, new_addrs);
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
        self.linked.grow_commutes_with_i(new_root_addr);
        self.linked.i_wf();
        post.linked.i_wf();
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

        path.i_valid();
        path.target_commutes_with_i();
        path.target_valid_buffer_dv();

        let new_subtree = path.target().split_parent(request, new_addrs);
        let splitted = path.substitute(new_subtree, path_addrs);

        Self::split_parent_substitute_preserves_inv(self, post, lbl, path, request, new_addrs, path_addrs);
        path.target().split_parent_commutes_with_i(request, new_addrs);
        path.substitute_commutes_with_i(new_subtree, path_addrs);
        post.linked.subdisk_preserves_i(splitted);
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
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop()));
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
