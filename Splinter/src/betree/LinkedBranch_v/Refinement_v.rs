// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::betree::LinkedBranch_v::*;
use crate::betree::PivotBranch_v;
use crate::betree::PivotBranchRefinement_v;
// use crate::spec::KeyType_t::*;
// use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::Ranking;

verus! {

impl LinkedBranch {
    /// Returns the PivotBranch_v::Node interpretation of the LinkedBranch
    pub open spec/*XXX (checked)*/ fn i(self) -> PivotBranch_v::Node
        recommends
            self.acyclic(),
    {
        // Need the_ranking ensures to restore checked
        let ranking = self.the_ranking();
        self.i_internal(ranking)
    }

    pub open spec(checked) fn i_internal(self, ranking: Ranking) -> PivotBranch_v::Node
        recommends
            self.wf(),
            self.valid_ranking(ranking),
        decreases self.get_rank(ranking)
        when self.wf() && self.valid_ranking(ranking)
    {
        match self.root() {
            Node::Leaf{keys, msgs} => {
                PivotBranch_v::Node::Leaf{ keys: keys, msgs: msgs }
            },
            Node::Index{pivots, children} => {
                PivotBranch_v::Node::Index{
                    pivots: pivots,
                    children: Seq::new(
                        children.len(),
                        // Need this weird hack to prove decreases because valid_ranking triggers
                        // on valid_child_index
                        |i|
                            // 0 <= i < children.len() ==> self.root().valid_child_index(i as nat)
                            if self.root().valid_child_index(i as nat) {
                                self.child_at_idx(i as nat).i_internal(ranking)
                            } else {
                                PivotBranch_v::invalid_node()
                            }
                    ),
                }
            },
        }
    }
}

pub open spec(checked) fn inv(branch: LinkedBranch) -> bool
{
    &&& branch.acyclic()
    &&& inv_internal(branch, branch.the_ranking())
}

pub open spec(checked) fn inv_internal(branch: LinkedBranch, ranking: Ranking) -> bool
{
    &&& branch.wf()
    &&& branch.valid_ranking(ranking)
    &&& branch.all_keys_in_range_internal(ranking)
}

// TODO(x9du): dedup with pivotbranch route?
// create get_keys_or_pivots for each Node type, pass into route
pub open spec(checked) fn get_keys_or_pivots(node: Node) -> Seq<Key>
    recommends node.wf()
{
    if node is Leaf { node->keys } else { node->pivots }
}

/// Ensures clause for `Node::route()` method.
pub proof fn lemma_route_ensures(node: Node, key: Key)
    requires node.wf()
    ensures ({
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| 0 <= i <= node.route(key) ==> #[trigger] Key::lte(s[i], key)
        &&& forall |i| node.route(key) < i < s.len() ==> #[trigger] Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    })
{
    let s = if node is Leaf { node->keys } else { node->pivots };
    Key::strictly_sorted_implies_sorted(s);
    Key::largest_lte_ensures(s, key, Key::largest_lte(s, key));
}

pub proof fn lemma_route_auto()
    ensures forall |node: Node, key: Key| node.wf() ==> {
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #![trigger Key::lte(s[i], key)] 0 <= i <= node.route(key) ==> Key::lte(s[i], key)
        &&& forall |i| #![trigger Key::lt(key, s[i])] node.route(key) < i < s.len() ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    }
{
    assert forall |node: Node, key: Key| node.wf() implies {
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #![trigger Key::lte(s[i], key)] 0 <= i <= node.route(key) ==> Key::lte(s[i], key)
        &&& forall |i| #![trigger Key::lt(key, s[i])] node.route(key) < i < s.len() ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    } by {
        lemma_route_ensures(node, key);
    }
}

pub proof fn query_refines(pre: LinkedBranch, key: Key, msg: Message)
    requires
        inv(pre),
        pre.query(key) == msg,
    ensures
        pre.i().query(key) == msg,
{
    query_internal_refines(pre, pre.the_ranking(), key, msg);
}

pub proof fn query_internal_refines(pre: LinkedBranch, ranking: Ranking, key: Key, msg: Message)
    requires
        inv_internal(pre, ranking),
        pre.query_internal(key, ranking) == msg,
    ensures
        pre.i_internal(ranking).query(key) == msg,
    decreases pre.get_rank(ranking)
{
    i_internal_wf(pre, ranking);
    assert(pre.i_internal(ranking).wf());

    lemma_route_auto();

    let r = pre.root().route(key);
    if pre.root() is Index {
        let pivots = pre.root()->pivots;
        let children = pre.root()->children;
        assert(pre.root().valid_child_index((r+1) as nat));
        let child = pre.child_at_idx((r+1) as nat);
        assert(child.wf());
        assert(child.root().wf());
        assert(child.valid_ranking(ranking));
        assert(child.query_internal(key, ranking) == msg);
        query_internal_refines(child, ranking, key, msg);
        assert(0 <= r+1 < pre.i_internal(ranking)->children.len());
        assert(pre.i_internal(ranking)->children[r+1] == child.i_internal(ranking));
    }
}

pub proof fn i_wf(branch: LinkedBranch)
    requires
        inv(branch),
    ensures branch.i().wf(),
{
    i_internal_wf(branch, branch.the_ranking());
}

pub proof fn i_internal_wf(branch: LinkedBranch, ranking: Ranking)
    requires
        inv_internal(branch, ranking),
    ensures
        branch.i_internal(ranking).wf(),
    decreases branch.get_rank(ranking),
{
    let branch_i = branch.i_internal(ranking);
    if branch.root() is Index {
        assert(branch_i is Index);
        let pivots_i = branch_i->pivots;
        let children_i = branch_i->children;
        assert(pivots_i.len() == children_i.len() - 1);

        assert forall |i| 0 <= i < children_i.len() implies (#[trigger] children_i[i]).wf() by {
            assert(branch.root().valid_child_index(i as nat));
            let child = branch.child_at_idx(i as nat);
            assert(child.wf());
            assert(child.valid_ranking(ranking));
            assert(child.all_keys_in_range_internal(ranking)) by {
                assert(branch.all_keys_in_range_internal(ranking));
                assert(branch.child_all_keys_in_range_internal(ranking, i as nat));
            }
            i_internal_wf(child, ranking);
        }

        assert forall |i| #![trigger children_i[i].all_keys()] #![trigger children_i[i].all_keys()] 0 <= i < children_i.len()
        implies children_i[i].all_keys().finite() && !children_i[i].all_keys().is_empty() by {
            assert(branch.root().valid_child_index(i as nat));
            let child = branch.child_at_idx(i as nat);
            assert(child.wf());
            assert(child.valid_ranking(ranking));
            lemma_i_preserves_all_keys(child, ranking);
            lemma_all_keys_finite_and_nonempty(child, ranking);
        }

        assert forall |i| 0 <= i < children_i.len() - 1
        implies branch_i.all_keys_below_bound(i) by {
            assert(branch.root()->pivots.len() == children_i.len() - 1);
            assert(branch.all_keys_in_range_internal(ranking));
            assert(branch.all_keys_below_bound(i, ranking));
            assert(branch.root().valid_child_index(i as nat));
            let child = branch.child_at_idx(i as nat);
            assert(child.wf());
            assert(child.valid_ranking(ranking));
            lemma_i_preserves_all_keys(child, ranking);
        }

        assert forall |i| 0 < i < children_i.len()
        implies branch_i.all_keys_above_bound(i) by {
            assert(branch.all_keys_in_range_internal(ranking));
            assert(branch.all_keys_above_bound(i, ranking));
            assert(branch.root().valid_child_index(i as nat));
            let child = branch.child_at_idx(i as nat);
            assert(child.wf());
            assert(child.valid_ranking(ranking));
            lemma_i_preserves_all_keys(child, ranking);
        }
    }
}

pub proof fn lemma_i_preserves_all_keys(branch: LinkedBranch, ranking: Ranking)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
    ensures
        branch.all_keys(ranking) == branch.i_internal(ranking).all_keys()
    decreases branch.get_rank(ranking)
{
    if branch.root() is Index {
        let branch_i = branch.i_internal(ranking);
        // TODO: make this a helper function
        let branch_i_children_keys = Set::new(|key| 
            exists |i| 0 <= i < branch_i->children.len() 
            && (#[trigger] branch_i->children[i]).all_keys().contains(key));
        assert(branch.all_keys(ranking) == branch.root()->pivots.to_set() + branch.children_keys(ranking));
        assert(branch_i.all_keys() == branch_i->pivots.to_set() + branch_i_children_keys);
        
        assert forall |i| 0 <= i < branch.root()->children.len()
        implies branch.map_all_keys(ranking)[i] == PivotBranchRefinement_v::map_all_keys(branch_i->children)[i] by {
            assert(branch.root().valid_child_index(i as nat));
            lemma_i_preserves_all_keys(branch.child_at_idx(i as nat), ranking);
        }
        assert(branch.map_all_keys(ranking) == PivotBranchRefinement_v::map_all_keys(branch_i->children));
        PivotBranchRefinement_v::lemma_children_all_keys_equivalence(branch_i->children);
        assert(branch.children_keys(ranking) == branch_i_children_keys);
    }
}

pub proof fn lemma_all_keys_finite_and_nonempty(branch: LinkedBranch, ranking: Ranking)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
    ensures
        branch.all_keys(ranking).finite(),
        !branch.all_keys(ranking).is_empty(),
    decreases
        branch.get_rank(ranking),
        1int,
{
    if branch.root() is Leaf {
        assert(branch.all_keys(ranking).contains(branch.root()->keys[0]));
    } else {
        lemma_children_keys_finite_and_nonempty(branch, ranking);
        assert(0 < branch.root()->children.len());
        let key = choose |key| branch.children_keys(ranking).contains(key);
        assert(branch.all_keys(ranking).contains(key));
    }
}

pub proof fn lemma_children_keys_finite_and_nonempty(branch: LinkedBranch, ranking: Ranking)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.root() is Index,
    ensures
        branch.children_keys(ranking).finite(),
        !branch.children_keys(ranking).is_empty(),
    decreases
        branch.get_rank(ranking),
        0int,
{
    let sets = branch.map_all_keys(ranking);
    assert forall |i| 0 <= i < sets.len() implies (#[trigger] sets[i]).finite() && !sets[i].is_empty() by {
        assert(branch.root().valid_child_index(i as nat));
        let child = branch.child_at_idx(i as nat);
        assert(child.wf());
        assert(child.valid_ranking(ranking));
        if child.root() is Index {
            lemma_all_keys_finite_and_nonempty(child, ranking);
        } else {
            assert(child.root()->keys.len() > 0);
            assert(child.all_keys(ranking).contains(child.root()->keys[0]));
        }
    }
    PivotBranchRefinement_v::lemma_union_seq_of_sets_finite(sets);
    assert(sets.len() > 0);
    let key = choose |key| sets[0].contains(key);
    PivotBranchRefinement_v::lemma_set_subset_of_union_seq_of_sets(sets, key);
}

} // verus!
