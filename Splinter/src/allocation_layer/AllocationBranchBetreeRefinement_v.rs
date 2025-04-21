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
use crate::betree::LinkedSeq_v::LinkedSeq;
use crate::betree::PivotTable_v::PivotTable;
use crate::betree::LinkedBetree_v::*;
use crate::betree::LinkedBranch_v;
use crate::betree::LinkedBranch_v::Refinement_v;
use crate::betree::PivotBranchRefinement_v;
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

impl<T> LinkedBetree<T> {
    proof fn same_dv_same_buffer_likes<A>(self, other: LinkedBetree<A>, betree_likes: Likes)
        requires self.dv == other.dv
        ensures self.buffer_likes(betree_likes) == other.buffer_likes(betree_likes)
        decreases betree_likes.len()
    {
        if betree_likes.len() > 0 {
            let addr = betree_likes.choose();
            self.same_dv_same_buffer_likes(other, betree_likes.remove(addr));
        }
    }
}

impl Path<BranchNode> {
    pub open spec fn i(self) -> Path<SimpleBuffer>
    {
        Path{
            linked: self.linked.i(),
            key: self.key,
            depth: self.depth,
        }
    }

    proof fn i_ensures(self)
        requires self.valid(),
        ensures
            self.i().valid(), 
            self.addrs_on_path() == self.i().addrs_on_path(),
            self.target().i() == self.i().target(),
        decreases self.depth
    {
        assert(self.i().linked.valid_ranking(self.linked.the_ranking())); // witness
        if self.depth > 0 {
            self.subpath().i_ensures();
        }
    }

    proof fn i_substitute_ensures(self, replacement: LinkedBetree<BranchNode>, path_addrs: PathAddrs)
        requires self.can_substitute(replacement, path_addrs)
        ensures self.substitute(replacement, path_addrs).dv == self.i().substitute(replacement.i(), path_addrs).dv
        decreases self.depth
    {
        if self.depth > 0 {
            self.subpath().i_substitute_ensures(replacement, path_addrs.subrange(1, path_addrs.len() as int));
        }
    }
}

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

impl LinkedBetree<BranchNode> {
    pub open spec(checked) fn i(self) -> LinkedBetree<SimpleBuffer>
    {
        LinkedBetree{
            root: self.root,
            dv: self.dv,
            buffer_dv: self.buffer_dv.i(),
        }
    }

    pub proof fn i_valid(self) 
    requires 
        self.inv()
    ensures 
        self.i().inv(),
        self.transitive_likes() == self.i().transitive_likes(),

        // self.reachable_addrs == self.reachable_buffer_addrs(),

        self.transitive_likes().1.dom() == self.reachable_buffer_addrs(),
        self.i().transitive_likes().1.dom() == self.i().reachable_buffer_addrs(),


        // self.reachable_buffer_addrs() == self.i().reachable_buffer_addrs(),
    {
        let i_linked = self.i();
        let ranking = self.the_ranking();

        assert(i_linked.valid_ranking(ranking)); // witness
        self.transitive_likes_ignores_buffer_dv(i_linked);

        self.tree_likes_domain(ranking);
        self.buffer_likes_domain(self.tree_likes(ranking));
        i_linked.tree_likes_domain(i_linked.the_ranking());
        i_linked.buffer_likes_domain(i_linked.tree_likes(i_linked.the_ranking()));
    }
}

impl LinkedBetreeVars::State<BranchNode> {
    pub open spec(checked) fn i(self) -> LinkedBetreeVars::State<SimpleBuffer>
    {
        LinkedBetreeVars::State{
            memtable: self.memtable,
            linked: self.linked.i(),
        }  
    }
}

impl BufferDisk<BranchNode> {
    // to refine query refines, we need to know that addr get banch is inv
    pub proof fn query_refines(self, buffer: Address, k: Key)
        requires self.get_branch(buffer).inv()
        ensures self.query(buffer, k) == self.i().query(buffer, k)
    {
        let branch = self.get_branch(buffer);
        Refinement_v::query_refines(branch, k, self.query(buffer, k));

        let pivot_branch = branch.i();
        Refinement_v::i_internal_wf(branch, branch.the_ranking());

        let lbl = PivotBranchRefinement_v::QueryLabel{key: k, msg: self.query(buffer, k)};
        PivotBranchRefinement_v::query_refines(pivot_branch, lbl);
    }

    pub proof fn query_from_refines(self, buffers: LinkedSeq, k: Key, start: int)
        requires 
            0 <= start <= buffers.len(),
            forall |i| start <= i < buffers.len() ==> #[trigger] self.get_branch(buffers[i]).inv()
        ensures 
            self.query_from(buffers, k, start) == self.i().query_from(buffers, k, start)
        decreases buffers.len() - start 
    {
        if start < buffers.len() {
            self.query_refines(buffers[start], k);
            self.query_from_refines(buffers, k, start+1);
        }
    }

    pub proof fn i_preserves_sub_disk(self, other: Self)
        requires 
            self.to_branch_disk().wf(),
            other.to_branch_disk().wf(),
            self.is_sub_disk(other),
        ensures 
            self.i().is_sub_disk(other.i())
    {
        assert forall |addr| self.entries.contains_key(addr) 
        implies self.i().entries[addr] == #[trigger] other.i().entries[addr]
        by {
            let branch = self.get_branch(addr);
            let other_branch = other.get_branch(addr);
            assert(self.entries[addr] == other.entries[addr]);
            assert(self.i().entries[addr] == branch.i().i());
            assert(other.i().entries[addr] == other_branch.i().i());

            if branch.has_root() {
                assert(branch.wf());
                if branch.acyclic() {
                    let finite_ranking = branch.the_ranking().restrict(branch.disk_view.entries.dom());
                    assert(other_branch.valid_ranking(finite_ranking));
                    branch.subdisk_same_i_internal(branch.the_ranking(), other_branch, other_branch.the_ranking());
                } else {
                    if other_branch.acyclic() {
                        assert(branch.valid_ranking(other_branch.the_ranking()));
                        assert(false);
                    }
                    assert(!other_branch.acyclic());
                }
            } else {
                assert(branch.root() is Auxiliary);
                assert(branch.i() == other_branch.i());
            }
        }
    }
}

impl<T: Buffer> QueryReceipt<T> {
    proof fn receipt_line_root_is_reachable(self, i: int)
    requires self.valid(), 0 <= i < self.lines.len(),
    ensures forall |j| i <= j < self.lines.len()-1 ==>
        #[trigger] self.lines[i].linked.reachable_betree_addrs().contains(self.lines[j].linked.root.unwrap())
    decreases self.lines.len() - i
    {
        let linked = self.lines[i].linked;
        let ranking = linked.the_ranking();
        assert(linked.acyclic()); // trigger

        if i < self.lines.len() - 1 {
            assert(self.node(i).key_in_domain(self.key)); // trigger
            let r = linked.root().pivots.route(self.key) as nat;
            linked.root().pivots.route_lemma(self.key);
            linked.reachable_betree_addrs_using_ranking_closed(ranking);

            assert forall |j| i < j < self.lines.len()-1
            implies #[trigger] linked.reachable_betree_addrs().contains(self.lines[j].linked.root.unwrap())
            by {
                assert(linked.can_recurse_for_reachable(ranking, r));
                linked.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
                assert(linked.child_at_idx(r).reachable_betree_addrs_using_ranking(ranking) <= linked.reachable_betree_addrs());

                self.receipt_line_root_is_reachable(i+1);
                assert(self.lines[i+1].linked.acyclic()); // trigger
                assert(self.lines[i+1].linked.reachable_betree_addrs().contains(self.lines[j].linked.root.unwrap()));

                assert(self.lines[i+1].linked.reachable_betree_addrs() <= linked.reachable_betree_addrs()) by {
                    assert(self.child_linked_at(i)); // trigger
                    assert(linked.root().valid_child_index(r));
                    assert(linked.child_at_idx(r).valid_ranking(linked.the_ranking()));
                    self.lines[i+1].linked.reachable_betree_addrs_ignore_ranking(ranking, self.lines[i+1].linked.the_ranking());
                }
                assert(linked.reachable_betree_addrs().contains(self.lines[j].linked.root.unwrap()));
            }
        }
    }
}

impl QueryReceipt<BranchNode> {
    pub open spec fn i(self) -> QueryReceipt<SimpleBuffer>
    {
        QueryReceipt{
            key: self.key,
            linked: self.linked.i(),
            lines: Seq::new(self.lines.len(), 
                |i| QueryReceiptLine{
                    linked: LinkedBetree{
                        root: self.lines[i].linked.root,
                        dv: self.lines[i].linked.dv,
                        buffer_dv: self.linked.i().buffer_dv,
                    },
                    result: self.lines[i].result
                }
            )
        }
    }

    proof fn i_preserves_valid(self)
        requires 
            self.valid(), 
            self.linked.inv(),
            self.linked.buffer_dv.sealed_branch_roots(
                self.linked.reachable_buffer_addrs()), // callsite issue
        ensures self.i().valid()
    {
        assert forall |i:nat| i < self.i().lines.len()
        implies (#[trigger] self.i().lines[i as int]).linked.has_root() <==> i < self.i().lines.len()-1
        by {
            if self.i().lines[i as int].linked.has_root() || i < self.i().lines.len()-1 {
                assert(self.lines[i as int].linked.has_root()); // trigger
            }
        }
        assert(self.i().structure());

        assert forall |i| 0 <= i < self.i().lines.len()
        implies ({
            &&& (#[trigger] self.i().lines[i]).wf()
            &&& self.i().lines[i].linked.acyclic()
        }) by {
            let linked = self.lines[i].linked;
            let i_linked = self.i().lines[i].linked;
            let ranking = linked.the_ranking();
    
            assert(self.lines[i].wf()); // trigger
            assert(linked.acyclic()); // trigger
            assert(i_linked.valid_ranking(ranking)); // witness
        }

        self.receipt_line_root_is_reachable(0);

        assert forall |i| 0 <= i < self.i().lines.len()-1
        implies ({
            &&& self.i().linked.buffer_dv.valid_buffers(self.i().node(i).buffers)
            &&& (#[trigger] self.i().node(i)).key_in_domain(self.key)
            &&& self.i().child_linked_at(i)
            &&& self.i().result_linked_at(i)
        }) by {
            self.linked.i_valid();
            assert(self.node(i) == self.i().node(i));
            assert(self.linked.buffer_dv.valid_buffers(self.node(i).buffers)); // trigger

            assert(self.child_linked_at(i)); // trigger
            assert(self.result_linked_at(i)); // trigger

            let linked = self.lines[i].linked;
            assert(self.linked.reachable_betree_addrs().contains(linked.root.unwrap()));
             
            assert forall |idx| 0 <= idx < self.node(i).buffers.len()
            implies self.linked.buffer_dv.get_branch(#[trigger] self.node(i).buffers[idx]).inv()
            by {
                assert(self.linked.reachable_buffer(linked.root.unwrap(), self.node(i).buffers[idx])); // witness
            }

            let start = self.node(i).flushed_ofs(self.key);
            let msg = self.linked.buffer_dv.query_from(self.node(i).buffers, self.key, start as int);

            assert(self.node(i).key_in_domain(self.key)); // trigger
            self.node(i).pivots.route_lemma(self.key);
            self.linked.buffer_dv.query_from_refines(self.node(i).buffers, self.key, start as int);
        }
        assert(self.i().all_lines_wf());
    }
}

impl AllocationBranchBetree::State { 
    pub open spec(checked) fn i(self) -> AllocationBetree::State
    {
        AllocationBetree::State{
            betree: self.betree.i(),
            betree_aus: self.betree_aus,
            buffer_aus: self.branch_aus,
        }
    }

    proof fn init_refines(self, v: LinkedBetreeVars::State<BranchNode>) 
        requires self.inv(), AllocationBranchBetree::State::initialize(self, v), 
        ensures AllocationBetree::State::initialize(self.i(), v.i()), 
    {
        v.linked.i_valid();
    }

    proof fn au_likes_noop_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, new_betree: LinkedBetreeVars::State<BranchNode>)
    requires 
        pre.inv(),
        post.inv(),
        AllocationBranchBetree::State::au_likes_noop(pre, post, lbl, new_betree),
    ensures
        AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::au_likes_noop(new_betree.i())),
    {
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
        reveal(AllocationBetree::State::next_by);

        match lbl->linked_lbl {
            LinkedBetreeVars::Label::Query{end_lsn, key, value} => {
                let receipt = choose |receipt| LinkedBetreeVars::State::query(
                            pre.betree, post.betree, lbl->linked_lbl, receipt);
                let (tree_likes, _) = pre.betree.linked.transitive_likes();
                pre.betree.linked.tree_likes_domain(pre.betree.linked.the_ranking());
                pre.betree.linked.buffer_likes_domain(tree_likes);
                receipt.i_preserves_valid();
                assert(receipt.i().valid_for(pre.betree.linked.i(), key));
                assert(LinkedBetreeVars::State::next_by(pre.betree.i(), post.betree.i(), 
                    lbl->linked_lbl, LinkedBetreeVars::Step::query(receipt.i())));
            }
            LinkedBetreeVars::Label::Put{puts} => {
                assert(puts.wf());
                assert(LinkedBetreeVars::State::next_by(pre.betree.i(), new_betree.i(), 
                    lbl->linked_lbl, LinkedBetreeVars::Step::put()));
            }
            LinkedBetreeVars::Label::FreezeAs{stamped_betree} => {
                assert(pre.betree.linked.i() == stamped_betree.value);
                assert(pre.betree.linked.i().i_bdv().buffer_dv == pre.betree.linked.i().buffer_dv);
                assert(pre.betree.linked.i().i_bdv() =~= pre.betree.linked.i());
                assert(LinkedBetreeVars::State::next_by(pre.betree.i(), new_betree.i(), 
                    lbl->linked_lbl, LinkedBetreeVars::Step::freeze_as()));
            }
            _ => { assert(false); }
        }
    }

    proof fn internal_flush_memtable_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, 
        new_betree: LinkedBetreeVars::State<BranchNode>, branch_idx: int, new_root_addr: Address)
    requires 
        pre.inv(), 
        post.inv(),
        AllocationBranchBetree::State::internal_flush_memtable(pre, post, lbl, new_betree, branch_idx, new_root_addr),
    ensures ({
        let new_branch = pre.wip_branches[branch_idx].branch.unwrap();
        let new_addrs = TwoAddrs{addr1: new_root_addr, addr2: new_branch.root};
        &&& AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            AllocationBetree::Step::internal_flush_memtable(new_betree.i(), new_addrs))}) 
    {
        let new_branch = pre.wip_branches[branch_idx].branch.unwrap();
        let new_addrs = TwoAddrs{addr1: new_root_addr, addr2: new_branch.root};
        let step = AllocationBetree::Step::internal_flush_memtable(new_betree.i(), new_addrs);

        let i_buffer = new_branch.root().i(new_betree.linked.buffer_dv, new_addrs.addr2);
        let i_pushed = pre.i().betree.linked.push_memtable(i_buffer, new_addrs);    
        let pushed = pre.betree.linked.push_memtable(new_branch.root(), new_addrs);

        assert(pushed.valid_view(new_betree.linked));
        assert(pre.betree.linked.is_fresh(new_addrs.repr())) by {
            AllocationBranch::alloc_aus_ensures(pre.wip_branches, branch_idx);
        }
        pre.inv_implies_wf_branch_dv();
        post.inv_implies_wf_branch_dv();
        pre.betree.linked.buffer_dv.i_preserves_sub_disk(new_betree.linked.buffer_dv);
        assert(i_pushed.valid_view(new_betree.i().linked));

        assert(LinkedBetreeVars::State::internal_flush_memtable(pre.i().betree, new_betree.i(), 
            lbl.i()->linked_lbl, i_buffer, new_betree.i().linked, new_addrs));
        assert(AllocationBetree::State::internal_flush_memtable(pre.i(), post.i(), lbl.i(), new_betree.i(), new_addrs));
        reveal(AllocationBetree::State::next_by);
    }

    proof fn internal_split_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, new_betree: LinkedBetreeVars::State<BranchNode>, 
        path: Path<BranchNode>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        post.inv(),
        AllocationBranchBetree::State::internal_split(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs),
    ensures
        AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            AllocationBetree::Step::internal_split(new_betree.i(), path.i(), request, new_addrs, path_addrs))
    {
        assert(pre.betree.linked.is_fresh(new_addrs.repr().union(path_addrs.to_set()))) by {
            to_aus_domain(path_addrs.to_set());
            to_aus_domain(new_addrs.repr());
        }

        path.i_ensures();
        pre.betree.post_split_ensures(path, request, new_addrs, path_addrs);

        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        let i_splitted = LinkedBetreeVars::State::post_split(path.i(), request, new_addrs, path_addrs);

        assert(splitted.i().buffer_dv == i_splitted.buffer_dv);
        path.target_ensures();
        path.i_substitute_ensures(path.target().split_parent(request, new_addrs), path_addrs);

        assert(splitted.i().dv == i_splitted.dv);
        assert(splitted.i() == i_splitted);

        assert(splitted.buffer_dv == new_betree.linked.buffer_dv);
        assert(LinkedBetreeVars::State::internal_split(pre.i().betree, new_betree.i(), 
            lbl.i()->linked_lbl, new_betree.i().linked, path.i(), request, new_addrs, path_addrs));
        assert(split_discard_betree(path, request) == split_discard_betree(path.i(), request));
    
        let old_child = path.target().child_at_idx(request.get_child_idx());
        let i_child = path.i().target().child_at_idx(request.get_child_idx());

        assert(old_child.i() == i_child);
        assert(old_child.root_likes() == old_child.i().root_likes());

        old_child.same_dv_same_buffer_likes(old_child.i(), old_child.root_likes());
        assert(old_child.buffer_likes(old_child.root_likes()) == old_child.i().buffer_likes(old_child.root_likes()));
        assert(split_add_buffers(path, request) == split_add_buffers(path.i(), request));

        assert(AllocationBetree::State::internal_split(pre.i(), post.i(), lbl.i(), new_betree.i(), path.i(), request, new_addrs, path_addrs));
        reveal(AllocationBetree::State::next_by);
    }

    proof fn internal_flush_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, 
        new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        post.inv(),
        AllocationBranchBetree::State::internal_flush(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs),
    ensures
        AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            AllocationBetree::Step::internal_flush(new_betree.i(), path.i(), child_idx, buffer_gc, new_addrs, path_addrs))
    {
        assert(pre.betree.linked.is_fresh(new_addrs.repr() + path_addrs.to_set())) by {
            to_aus_domain(path_addrs.to_set());
            to_aus_domain(new_addrs.repr());    
        }

        path.i_ensures();
        path.target_ensures();
        pre.betree.post_flush_ensures(path, child_idx, buffer_gc, new_addrs, path_addrs);
        path.i_substitute_ensures(path.target().flush(child_idx, buffer_gc, new_addrs), path_addrs);

        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        pre.inv_implies_wf_branch_dv();
        post.inv_implies_wf_branch_dv();
        new_betree.linked.buffer_dv.i_preserves_sub_disk(pre.betree.linked.buffer_dv);

        assert(flushed.i().valid_view(new_betree.i().linked));
        assert(LinkedBetreeVars::State::internal_flush(pre.i().betree, new_betree.i(), lbl.i()->linked_lbl, 
            new_betree.i().linked, path.i(), child_idx, buffer_gc, new_addrs, path_addrs));

        let (new_betree_aus, new_buffer_aus) = AllocationBetree::State::internal_flush_au_likes(path.i(), child_idx, 
            buffer_gc, new_addrs, path_addrs, pre.i().betree_aus, pre.i().buffer_aus);

        post.inv_branch_summary_ensures();
        assert(post.branch_aus.dom() <= summary_aus(post.branch_summary));
        assert(AllocationBetree::State::internal_flush(pre.i(), post.i(), lbl.i(), 
            new_betree.i(), path.i(), child_idx, buffer_gc, new_addrs, path_addrs));
        reveal(AllocationBetree::State::next_by);
    }

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

    proof fn next_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label) 
        requires 
            pre.inv(),
            post.inv(),
            AllocationBranchBetree::State::next(pre, post, lbl),
        ensures
            AllocationBetree::State::next(pre.i(), post.i(), lbl.i())
    {
        reveal(AllocationBetree::State::next);
        reveal(AllocationBetree::State::next_by);
        reveal(AllocationBranchBetree::State::next);
        reveal(AllocationBranchBetree::State::next_by);
        
        match choose |step| Self::next_by(pre, post, lbl, step) {
            AllocationBranchBetree::Step::au_likes_noop(new_betree) => { 
                Self::au_likes_noop_refines(pre, post, lbl, new_betree);
            }
            AllocationBranchBetree::Step::branch_begin() => { 
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop()));
            }
            AllocationBranchBetree::Step::branch_build(idx, post_branch, event) => { 
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop()));
            }
            AllocationBranchBetree::Step::branch_abort(idx) => { 
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop()));
            }
            AllocationBranchBetree::Step::internal_flush_memtable(new_betree, branch_idx, new_root_addr) => {
                Self::internal_flush_memtable_refines(pre, post, lbl, new_betree, branch_idx, new_root_addr);
            }
            AllocationBranchBetree::Step::internal_grow(new_betree, new_root_addr) => {
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
                    AllocationBetree::Step::internal_grow(new_betree.i(), new_root_addr)));
            }
            AllocationBranchBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs) => {
                Self::internal_split_refines(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs);
            }
            AllocationBranchBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs) => {
                Self::internal_flush_refines(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
            }
            AllocationBranchBetree::Step::internal_compact_begin(path, start, end, input) => {
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop()));
            }
            AllocationBranchBetree::Step::internal_compact_abort(input_idx, new_betree) => {
                assert(pre.i().betree.linked.valid_view(new_betree.i().linked)) by {
                    pre.inv_implies_wf_branch_dv();
                    post.inv_implies_wf_branch_dv();
                    new_betree.linked.buffer_dv.i_preserves_sub_disk(pre.betree.linked.buffer_dv);
                }

                assert(pre.i().betree.linked.reachable_buffers_preserved(new_betree.i().linked)) by {
                    pre.betree.linked.i_valid();
                    post.betree.linked.i_valid();
                    pre.betree.linked.transitive_likes_ignores_buffer_dv(post.betree.linked);
                }

                assert(LinkedBetreeVars::State::internal_buffer_noop(pre.i().betree, post.i().betree, lbl.i()->linked_lbl, new_betree.i().linked));
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_buffer_noop(new_betree.i())));
            }
            AllocationBranchBetree::Step::internal_compact_complete(input_idx, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs) => {
                assume(false);
                // Self::internal_compact_complete_inv_refines(pre, post, lbl, new_betree, input_idx, path, start, end, compacted_buffer, new_addrs, path_addrs);
            }
            _ => { assert(false); }
        }
    }
} // end impl AllocationBranchBetree::State

}//verus
