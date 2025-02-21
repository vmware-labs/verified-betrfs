// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
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

broadcast use PivotTable::route_lemma, Buffer::contains_refines, Buffer::query_refines;

impl<T: Buffer> LinkedBetree<T>{
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
                buffers: self.buffer_dv.i_buffer_seq(root.buffers),
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
//            assert(a[i] == self.child_at_idx(i as nat).i_node(r1));
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
            self.buffer_dv.valid_buffers(self.root().buffers),
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

    // valid_view    
    proof fn valid_view_preserves_i_with_ranking(self, other: Self, ranking: Ranking)
        requires 
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.valid_view(other),
            self.valid_buffer_dv(),
            other.valid_buffer_dv(),
        ensures
            self.i() == other.i()
        decreases 
            self.get_rank(ranking),
            other.get_rank(ranking),
    {
        broadcast use BufferDisk::agrees_implies_same_i;
        if self.has_root() {
            self.valid_buffer_dv_throughout();
            other.valid_buffer_dv_throughout();
//            assert(self.i()->buffers =~= other.i()->buffers);

            self.i_children_lemma();
            other.i_children_lemma();

            assert forall |i| 0 <= i < self.i()->children.len()
            implies self.i()->children[i] == other.i()->children[i]
            by {
                let child = self.child_at_idx(i as nat);
                let other_child = other.child_at_idx(i as nat);

//                assert(self.root().valid_child_index(i as nat));
                assert(other.root().valid_child_index(i as nat));

                self.child_at_idx_reachable_addrs_ensures(i as nat);
                self.reachable_betree_addrs_using_ranking_closed(self.the_ranking());
                child.valid_view_preserves_i_with_ranking(other_child, ranking);
            }
            assert(self.i()->children =~= other.i()->children);
        }
    }

    proof fn valid_view_preserves_i(self, other: Self)
    requires 
        self.acyclic(),
        other.acyclic(),
        self.valid_view(other),
        self.valid_buffer_dv(),
        other.valid_buffer_dv(),
    ensures
        self.i() == other.i()
    {
        if self.has_root() {
            let ranking = self.the_ranking();
            other.dv.subdisk_implies_ranking_validity(self.dv, ranking);
            self.valid_view_preserves_i_with_ranking(other, ranking);
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
        broadcast use BufferDisk::agrees_implies_same_i;
        if self.has_root() {
            self.valid_buffer_dv_throughout();

//            assert(self.i()->buffers =~= big.i()->buffers);

            self.i_children_lemma();
            big.i_children_lemma();

            assert forall |i| 0 <= i < self.i()->children.len()
            implies self.i()->children[i] == big.i()->children[i]
            by {
                let child = self.child_at_idx(i as nat);
                let big_child = big.child_at_idx(i as nat);

//                assert(self.root().valid_child_index(i as nat));
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

    proof fn i_bdv_preserves_i(self, ranking: Ranking)
        requires
            self.valid_ranking(ranking),
            self.valid_buffer_dv(),
        ensures 
            self.i() == self.i_bdv().i()
        decreases
            self.get_rank(ranking)
    {
        if self.has_root() {
            let result = self.i_bdv();
            assert(result.valid_ranking(ranking));

            assert forall |i| 0 <= i < result.i()->buffers.len()
            implies #[trigger] result.i()->buffers[i] =~= self.i()->buffers[i]
            by {
                assert(self.reachable_buffer(self.root.unwrap(), self.root().buffers[i])); // trigger
            }
            assert(self.i()->buffers =~= result.i()->buffers);

            self.valid_buffer_dv_throughout();
            self.i_children_lemma();
            result.i_children_lemma();

            assert forall |i| 0 <= i < result.i()->children.len()
            implies #[trigger] result.i()->children[i] =~= self.i()->children[i]
            by {
                assert(self.root().valid_child_index(i as nat)); // trigger
                self.child_at_idx(i as nat).i_bdv_preserves_i(ranking);
            }
            assert(self.i()->children =~= result.i()->children);
        }
    }

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
//        assert(result.i()->children =~= self.i().grow()->children);
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
//        assert(self.i().can_split_parent(request));
//        assert(result.i()->children.len() == self.i().split_parent(request)->children.len());

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

    proof fn flush_commutes_with_i(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs)
        requires 
            self.acyclic(), 
            self.can_flush(child_idx, buffer_gc), 
            self.flush(child_idx, buffer_gc, new_addrs).acyclic(),
            self.valid_buffer_dv(),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.i().can_flush(child_idx, buffer_gc),
            self.flush(child_idx, buffer_gc, new_addrs).i() == self.i().flush(child_idx, buffer_gc)
    {
        self.i_wf();

        let result = self.flush(child_idx, buffer_gc, new_addrs);
//        assert(self.i().can_flush(child_idx, buffer_gc));
        let i_result = self.i().flush(child_idx, buffer_gc);

        let _ = self.flush_new_ranking(child_idx, buffer_gc, new_addrs, self.finite_ranking());
//        assert(buffer_gc <= self.root().buffers.len());
        assert(result.i()->buffers =~= self.i().flush(child_idx, buffer_gc)->buffers);

        self.i_children_lemma();
        result.i_children_lemma();
//        assert(result.i()->children.len() =~= i_result->children.len());

        self.valid_buffer_dv_throughout();

        assert forall |i| 0 <= i < result.i()->children.len()
        implies #[trigger] result.i()->children[i] =~= i_result->children[i]
        by {
            assert(self.root().valid_child_index(i as nat));
            assert(result.root().valid_child_index(i as nat));

            let child = self.child_at_idx(i as nat);
            let result_child = result.child_at_idx(i as nat);

            if i == child_idx {
                child.i_children_lemma();
                result_child.i_children_lemma();

                let i_child = i_result->children[i];
                assert forall |j| 0 <= j < i_child->children.len()
                implies #[trigger] i_child->children[j] == result_child.i()->children[j]
                by {
                    assert(result_child.root().valid_child_index(j as nat));
                    assert(child.root().valid_child_index(j as nat));

                    child.child_at_idx_acyclic(j as nat);
                    child.valid_buffer_dv_throughout();
                    child.child_at_idx(j as nat).subdisk_preserves_i(result_child.child_at_idx(j as nat));
                }
                assert(i_result->children[i]->children =~= result_child.i()->children);
            } else {
                child.subdisk_preserves_i(result_child);
            }
        }
        assert(result.i()->children =~= i_result->children);
    }

    proof fn can_compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: T, new_addrs: TwoAddrs)
        requires 
            self.acyclic(),
            self.can_compact(start, end, compacted_buffer),
            self.valid_buffer_dv(),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.i().can_compact(start, end, compacted_buffer.i())
    {
        self.i_wf();
        reveal(FilteredBetree_v::BetreeNode::valid_compact_key_domain);

        let compact_slice = self.root().buffers.slice(start as int, end as int);
        let i_compact_slice = self.i()->buffers.slice(start as int, end as int);
        assert(self.buffer_dv.i_buffer_seq(compact_slice) =~= i_compact_slice);

        self.valid_buffer_dv_throughout();
//        assert(self.buffer_dv.valid_buffers(self.root().buffers)); 

        let compact_ofs_map = self.root().make_offset_map().decrement(start);
        let i_compact_ofs_map = self.i().make_offset_map().decrement(start);
//        assert(compact_ofs_map =~= i_compact_ofs_map);

        assert forall |k| #[trigger] compacted_buffer.i().map.contains_key(k) 
        implies ({
            let from = if self.i().flushed_ofs(k) <= start { 0 } else { self.i().flushed_ofs(k)-start };
            &&& compacted_buffer.query(k) == self.i()->buffers.slice(start as int, end as int).query_from(k, from)
            &&& self.i().valid_compact_key_domain(start, end, k)
        }) by {
            assert(self.buffer_dv.valid_compact_key_domain(self.root(), start, end, k));
            let buffer_idx = choose |buffer_idx| self.buffer_dv.key_in_buffer_filtered(
                compact_slice, compact_ofs_map, 0, k, buffer_idx);
            assert(i_compact_slice.key_in_buffer_filtered(i_compact_ofs_map, 0, k, buffer_idx));
        
            let from = if self.i().flushed_ofs(k) <= start { 0 } else { self.i().flushed_ofs(k)-start };
            self.buffer_dv.query_from_commutes_with_i(compact_slice, k, from);
        }

        assert forall |k| #[trigger] self.i().valid_compact_key_domain(start, end, k)
        implies compacted_buffer.i().map.contains_key(k) 
        by {
            let buffer_idx = choose |buffer_idx| i_compact_slice.key_in_buffer_filtered(i_compact_ofs_map, 0, k, buffer_idx);
//            assert(i_compact_ofs_map.offsets[k] == compact_ofs_map.offsets[k]);
//            assert(self.root().buffers[buffer_idx + start] == compact_slice[buffer_idx]);
//            assert(self.buffer_dv.entries.contains_key(compact_slice[buffer_idx]));

//            assert(i_compact_slice.key_in_buffer(0, k, buffer_idx) == self.buffer_dv.key_in_buffer(compact_slice, 0, k, buffer_idx));
            assert(self.buffer_dv.key_in_buffer_filtered(compact_slice, compact_ofs_map, 0, k, buffer_idx));
            assert(self.buffer_dv.valid_compact_key_domain(self.root(), start, end, k));
        }
    }

    proof fn compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: T, new_addrs: TwoAddrs)
        requires 
            self.acyclic(), 
            self.can_compact(start, end, compacted_buffer),
            self.compact(start, end, compacted_buffer, new_addrs).acyclic(),
            self.valid_buffer_dv(),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.i().can_compact(start, end, compacted_buffer.i()),
            self.compact(start, end, compacted_buffer, new_addrs).i() == self.i().compact(start, end, compacted_buffer.i())
    {
        let result = self.compact(start, end, compacted_buffer, new_addrs);
        self.can_compact_commutes_with_i(start, end, compacted_buffer, new_addrs);
        let i_result = self.i().compact(start, end, compacted_buffer.i());

        self.valid_buffer_dv_throughout();
        self.buffer_dv.agrees_implies_same_i(result.buffer_dv, self.root().buffers);
        assert(result.i()->buffers =~= i_result->buffers);

        self.i_children_lemma();
        result.i_children_lemma();
//        assert(result.i()->children.len() == i_result->children.len());

        assert forall |i| 0 <= i < result.i()->children.len()
        implies #[trigger] result.i()->children[i] == i_result->children[i]
        by {
            assert(self.root().valid_child_index(i as nat));
            assert(result.root().valid_child_index(i as nat));
            self.child_at_idx(i as nat).subdisk_preserves_i(result.child_at_idx(i as nat));
        }
        assert(result.i()->children =~= i_result->children);
    }

} // end impl LinkedBetree<T>

pub open spec(checked) fn i_stamped_betree<T: Buffer>(v: LinkedBetreeVars::State<T>) -> FilteredBetree_v::StampedBetree
    recommends v.linked.acyclic()
{
    Stamped{value: v.linked.i(), seq_end: v.memtable.seq_end}
}

impl<T: Buffer> QueryReceiptLine<T>{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::QueryReceiptLine
        recommends self.linked.acyclic()
    {
        FilteredBetree_v::QueryReceiptLine{ 
            node: self.linked.i(), 
            result: self.result 
        }
    }
}

impl<T: Buffer> QueryReceipt<T>{
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

//        assert(self.all_lines_wf());

        assert(i_receipt.all_lines_wf()) by {
            assert forall |i| 0 <= i < i_receipt.lines.len()
            implies #[trigger] i_receipt.lines[i].wf() by {
                broadcast use PivotTable::route_lemma;
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

//            assert(self.lines[i].linked.has_root());
            assert(node.key_in_domain(self.key));
            assert(self.result_linked_at(i)); // trigger
//            assert(self.linked.buffer_dv.valid_buffers(node.buffers));
            self.linked.buffer_dv.query_from_commutes_with_i(node.buffers, self.key, start);
        }
    }
}

impl<T: Buffer> Path<T>{
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

            assert(self.subpath().linked == self.linked.child_at_idx(r));
            self.linked.valid_buffer_dv_throughout();
            self.subpath().target_valid_buffer_dv();
        }
    }

    proof fn substitute_commutes_with_i(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs)
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
//            assert(self.i().can_substitute(replacement.i()));
    
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().substitute_ensures(replacement, sub_path_addrs);

            let r = self.linked.root().pivots.route(self.key);
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
//                assert(subtree.reachable_buffer_addrs() == result.child_at_idx(r as nat).reachable_buffer_addrs());        
                result.child_at_idx_reachable_addrs_ensures(r as nat);
            }

            self.linked.valid_buffer_dv_throughout();
            assert(result.i()->buffers =~= i_result->buffers) by {
//                assert(result.root().buffers == self.linked.root().buffers);
                self.linked.buffer_dv.agrees_implies_same_i(result.buffer_dv, result.root().buffers);
            }

            result.i_children_lemma();
            self.linked.i_children_lemma();
//            assert(result.i()->children.len() == i_result->children.len());

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
//                    assert(result.i()->children[i] == i_result->children[i]);
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
                        Stamped{
                            value: stamped_betree.value.i(),
                            seq_end: stamped_betree.seq_end,
                        }
                    } else { arbitrary() } },    
            LinkedBetreeVars::Label::Internal{} => 
                FilteredBetree::Label::Internal{},
        }
    }
} // end impl LinkedBetreeVars::Label

impl<T: Buffer> LinkedBetreeVars::State<T> {
    pub open spec(checked) fn i(self) -> FilteredBetree::State
        recommends 
            self.inv(),
    {
        FilteredBetree::State{root: self.linked.i(), memtable: self.memtable}
    }

    proof fn init_refines(self, v: Self) 
        requires
            LinkedBetreeVars::State::initialize(self, v)
        ensures
            FilteredBetree::State::initialize(self.i(), i_stamped_betree(v))
    {
        v.memtable.buffer.empty_refines();
        self.linked.i_wf();
    }

    proof fn query_refines(self, post: Self, lbl: LinkedBetreeVars::Label, receipt: QueryReceipt<T>)
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

    // stamped betree proof


    proof fn freeze_as_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires 
            self.inv(),
            post.inv(), 
            LinkedBetreeVars::State::freeze_as(self, post, lbl)
        ensures
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::freeze_as())
    {
        reveal(FilteredBetree::State::next_by);
        self.memtable.buffer.empty_refines();
//        assert(self.i().memtable.is_empty());
        self.linked.i_wf();
//        assert(self.i().wf());

        let ranking = self.linked.the_ranking();
        let stamped_value = lbl->stamped_betree.value;

        assert(stamped_value.valid_ranking(ranking));
//        assert(stamped_value.acyclic());

        if self.linked.has_root() {
            self.linked.i_bdv_preserves_i(ranking);
        }
    }

    proof fn internal_flush_memtable_refines(self, post: Self, lbl: LinkedBetreeVars::Label, 
        sealed_memtable: T, new_linked: LinkedBetree<T>, new_addrs: TwoAddrs)
        requires 
            self.inv(),
            post.inv(), 
            self.linked.is_fresh(new_addrs.repr()),
            self.linked.push_memtable(sealed_memtable, new_addrs).reachable_buffers_preserved(new_linked),
            LinkedBetreeVars::State::internal_flush_memtable(self, post, lbl, sealed_memtable, new_linked, new_addrs)
        ensures
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush_memtable())
    {
        reveal(FilteredBetree::State::next_by);
        self.linked.i_wf();
        post.linked.i_wf();

        let result = self.linked.push_memtable(sealed_memtable, new_addrs);
        self.linked.push_memtable_ensures(sealed_memtable, new_addrs);
        result.i_children_lemma();

        if self.linked.has_root() {
            self.linked.i_children_lemma();
            self.linked.valid_buffer_dv_throughout();

            assert forall |i: nat| i < self.linked.i()->children.len()
            implies #[trigger] self.linked.i()->children[i as int] =~= result.i()->children[i as int]
            by {
                assert(self.linked.root().valid_child_index(i)); // trigger
                assert(result.root().valid_child_index(i)); // trigger
                self.linked.child_at_idx(i).subdisk_preserves_i(result.child_at_idx(i));
            }
            self.linked.buffer_dv.agrees_implies_same_i(result.buffer_dv, self.linked.root().buffers);
            assert(result.i()->children =~= self.linked.i().push_memtable(self.memtable)->children);
        } else {
            assert(result.root().valid_child_index(0)); // trigger
//            assert(result.i()->children =~= seq![FilteredBetree_v::BetreeNode::Nil]);
        }
        assert(result.i()->buffers =~= self.linked.i().push_memtable(self.memtable)->buffers);
        result.valid_view_preserves_i(post.linked);
    }

    proof fn internal_grow_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_root_addr: Address)
        requires 
            self.inv(), 
            post.inv(),
            self.linked.is_fresh(set![new_root_addr]),
            LinkedBetreeVars::State::internal_grow(self, post, lbl, new_root_addr)
        ensures  
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_grow())
    {
        reveal(FilteredBetree::State::next_by);
        self.linked.grow_commutes_with_i(new_root_addr);
        self.linked.i_wf();
        post.linked.i_wf();
    }

    proof fn internal_split_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_linked: LinkedBetree<T>,
            path: Path<T>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs)
        requires 
            self.inv(), 
            post.inv(),
            self.linked.is_fresh(new_addrs.repr()),
            self.linked.is_fresh(path_addrs.to_set()),
            Self::post_split(path, request, new_addrs, path_addrs).reachable_buffers_preserved(new_linked),
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

        self.post_split_ensures(path, request, new_addrs, path_addrs);
        path.target().split_parent_commutes_with_i(request, new_addrs);
        path.substitute_commutes_with_i(new_subtree, path_addrs);
        splitted.valid_view_preserves_i(post.linked);
    }

    proof fn internal_flush_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_linked: LinkedBetree<T>, 
        path: Path<T>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
        requires 
            self.inv(), 
            post.inv(), 
            self.linked.is_fresh(new_addrs.repr()),
            self.linked.is_fresh(path_addrs.to_set()),
            Self::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs).reachable_buffers_preserved(new_linked),
            LinkedBetreeVars::State::internal_flush(self, post, lbl, new_linked, path, child_idx, buffer_gc, new_addrs, path_addrs)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush(path.i(), child_idx, buffer_gc))
    {
        reveal(FilteredBetree::State::next_by);

        path.i_valid();
        path.target_commutes_with_i();
        path.target_valid_buffer_dv();

        let new_subtree = path.target().flush(child_idx, buffer_gc, new_addrs);
        let flushed = path.substitute(new_subtree, path_addrs);

        self.post_flush_ensures(path, child_idx, buffer_gc, new_addrs, path_addrs);
        path.target().flush_commutes_with_i(child_idx, buffer_gc, new_addrs);
        path.substitute_commutes_with_i(new_subtree, path_addrs);
        flushed.valid_view_preserves_i(post.linked);
    }

    proof fn internal_compact_refines(self, post: Self, lbl: LinkedBetreeVars::Label, new_linked: LinkedBetree<T>,
            path: Path<T>, start: nat, end: nat, compacted_buffer: T, new_addrs: TwoAddrs, path_addrs: PathAddrs)
        requires 
            self.inv(), 
            post.inv(), 
            self.linked.is_fresh(new_addrs.repr()),
            self.linked.is_fresh(path_addrs.to_set()),
            Self::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs).reachable_buffers_preserved(new_linked),
            LinkedBetreeVars::State::internal_compact(self, post, lbl, new_linked, 
                path, start, end, compacted_buffer, new_addrs, path_addrs)
        ensures 
            FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), 
                FilteredBetree::Step::internal_compact(path.i(), start, end, compacted_buffer.i()))
    {
        reveal(FilteredBetree::State::next_by);

        path.i_valid();
        path.target_commutes_with_i();
        path.target_valid_buffer_dv();
    
        let new_subtree = path.target().compact(start, end, compacted_buffer, new_addrs);
        let compacted = path.substitute(new_subtree, path_addrs);

        self.post_compact_ensures(path, start, end, compacted_buffer, new_addrs, path_addrs);
        path.target().compact_commutes_with_i(start, end, compacted_buffer, new_addrs);
        path.substitute_commutes_with_i(new_subtree, path_addrs);
        compacted.valid_view_preserves_i(post.linked);
    }

    proof fn internal_noop_noop(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), post.inv(), LinkedBetreeVars::State::internal_noop(self, post, lbl)
        ensures FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop())
    {
        reveal(FilteredBetree::State::next_by);
        self.linked.i_wf();
//        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop()));
    }

    proof fn next_by_refines(self, post: Self, lbl: LinkedBetreeVars::Label, step: LinkedBetreeVars::Step<T>)
        requires 
            self.inv(), 
            post.inv(), 
            self.strong_step(step),
            LinkedBetreeVars::State::next_by(self, post, lbl, step),
        ensures 
            FilteredBetree::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(LinkedBetreeVars::State::next_by);
        reveal(FilteredBetree::State::next);

        match step
        {
            LinkedBetreeVars::Step::query(receipt) => 
                { self.query_refines(post, lbl, receipt); } 
            LinkedBetreeVars::Step::put() => 
                { self.put_refines(post, lbl); }
            LinkedBetreeVars::Step::freeze_as() => 
                { self.freeze_as_refines(post, lbl); }
            LinkedBetreeVars::Step::internal_flush_memtable(new_memtable, new_linked, new_addrs) => 
                { self.internal_flush_memtable_refines(post, lbl, new_memtable, new_linked, new_addrs); }
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
