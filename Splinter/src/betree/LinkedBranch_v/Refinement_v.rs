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
    &&& branch.keys_strictly_sorted_internal(ranking)
    &&& branch.all_keys_in_range_internal(ranking)
}

// TODO(x9du): dedup with pivotbranch route?
// create get_keys_or_pivots for each Node type, pass into route
pub open spec(checked) fn get_keys_or_pivots(node: Node) -> Seq<Key>
{
    if node is Leaf { node->keys } else { node->pivots }
}

/// Ensures clause for `Node::route()` method.
pub proof fn lemma_route_ensures(node: Node, key: Key)
    requires
        node.wf(),
        node.keys_strictly_sorted(),
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
    ensures forall |node: Node, key: Key| node.wf() && node.keys_strictly_sorted() ==> {
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #![trigger Key::lte(s[i], key)] 0 <= i <= node.route(key) ==> Key::lte(s[i], key)
        &&& forall |i| #![trigger Key::lt(key, s[i])] node.route(key) < i < s.len() ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    }
{
    assert forall |node: Node, key: Key| node.wf() && node.keys_strictly_sorted() implies {
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
        assert(child.keys_strictly_sorted_internal(ranking));
        assert(child.query_internal(key, ranking) == msg);
        query_internal_refines(child, ranking, key, msg);
        assert(0 <= r+1 < pre.i_internal(ranking)->children.len());
        assert(pre.i_internal(ranking)->children[r+1] == child.i_internal(ranking));
    }
}

pub proof fn grow_refines(pre: LinkedBranch, addr: Address)
    requires
        inv(pre),
        pre.disk_view.is_fresh(set!{addr}),
    ensures
        inv(pre.grow(addr)),
        pre.grow(addr).i() == pre.i().grow(),
{
    let ranking = pre.the_ranking();
    let post = pre.grow(addr);
    let post_ranking = ranking.insert(addr, ranking[pre.root] + 1);
    assert(post.valid_ranking(post_ranking));
    grow_refines_internal(pre, pre.the_ranking(), post.the_ranking(), addr);
}

pub proof fn grow_refines_internal(pre: LinkedBranch, ranking: Ranking, post_ranking: Ranking, addr: Address)
    requires
        inv_internal(pre, ranking),
        pre.disk_view.is_fresh(set!{addr}),
        pre.grow(addr).valid_ranking(post_ranking),
    ensures
        inv_internal(pre.grow(addr), post_ranking),
        pre.grow(addr).i_internal(post_ranking) == pre.i_internal(ranking).grow(),
    decreases pre.get_rank(ranking)
{
    let post = pre.grow(addr);
    let post_i = post.i_internal(post_ranking);
    let i_then_grow = pre.i_internal(ranking).grow();
    assert(post.wf());
    i_internal_wf(pre, ranking);

    assert(post_i->children.len() == i_then_grow->children.len() == 1);
    assert(post.root().valid_child_index(0));
    assert(post_i->children[0] == post.child_at_idx(0).i_internal(post_ranking));
    assert(post.child_at_idx(0) == LinkedBranch{root: pre.root, disk_view: post.disk_view});
    assert(pre.disk_view.is_subset_of(post.disk_view));
    assert(pre.valid_ranking(post_ranking));
    lemma_subdisk_same_i_internal(pre, post.child_at_idx(0), post_ranking);
    assert(post_i->children[0] == pre.i_internal(post_ranking));

    lemma_i_internal_ignores_ranking(pre, ranking, post_ranking);
    assert(pre.i_internal(post_ranking) == pre.i_internal(ranking));
    assert(i_then_grow->children[0] == pre.i_internal(ranking));
    assert(post_i->children =~~= i_then_grow->children);
    assert(post_i == i_then_grow);

    assert(post_i.wf());
    lemma_i_wf_implies_inv(post, post_ranking);
    assert(post.all_keys_in_range_internal(post_ranking));
}

pub proof fn insert_refines(pre: LinkedBranch, key: Key, msg: Message, path: Path)
    requires
        inv(pre),
        path.valid(),
        path.branch == pre,
        path.key == key,
        path.target().root() is Leaf,
    ensures
        inv(pre.insert(key, msg, path)),
        pre.insert(key, msg, path).i() == pre.i().insert(key, msg,
            PivotBranch_v::Path{node: pre.i(), key: key, depth: path.depth}),
{
    let post = pre.insert(key, msg, path);
    let target_addr = path.target().root;
    lemma_insert_preserves_ranking(pre, pre.the_ranking(), key, msg, path);
    insert_refines_internal(pre, pre.the_ranking(), post.the_ranking(), key, msg, path);
}

pub proof fn lemma_insert_preserves_ranking(pre: LinkedBranch, ranking: Ranking, key: Key, msg: Message, path: Path)
    requires
        pre.keys_strictly_sorted_internal(ranking),
        pre.valid_ranking(ranking),
        path.valid(),
        path.branch == pre,
        path.key == key,
        path.target().root() is Leaf,
    ensures
        pre.insert(key, msg, path).valid_ranking(ranking),
    decreases pre.get_rank(ranking),
{
    let post = pre.insert(key, msg, path);
    if path.depth > 0 {
        let r = pre.root().route(key) + 1;
        lemma_route_auto();
        assert(pre.root().valid_child_index(r as nat));
        lemma_insert_preserves_ranking(pre.child_at_idx(r as nat), ranking, key, msg, path.subpath());
    }
}

pub proof fn insert_refines_internal(pre: LinkedBranch, ranking: Ranking, post_ranking: Ranking, key: Key, msg: Message, path: Path)
    requires
        inv_internal(pre, ranking),
        pre.insert(key, msg, path).valid_ranking(post_ranking),
        path.valid(),
        path.branch == pre,
        path.key == key,
        path.target().root() is Leaf,
    ensures
        inv_internal(pre.insert(key, msg, path), post_ranking),
        pre.insert(key, msg, path).i_internal(post_ranking) == pre.i_internal(ranking).insert(key, msg,
            PivotBranch_v::Path{node: pre.i_internal(ranking), key: key, depth: path.depth}),
{
    assume(false);
    let post = pre.insert(key, msg, path);
    let post_i = post.i_internal(post_ranking);
    let path_i = PivotBranch_v::Path{node: pre.i_internal(ranking), key: key, depth: path.depth};
    lemma_insert_preserves_wf(pre, key, msg, path);
    match pre.root() {
        Node::Leaf{keys, msgs} => {
            assert(post_i == pre.i_internal(ranking).insert(key, msg, path_i));
        }
        Node::Index{pivots, children} => {
            assert(post_i == pre.i_internal(ranking).insert(key, msg, path_i));
        }
    }
    // assert(post.wf());
    assert(post_i.wf());
    lemma_i_wf_implies_inv(post, post_ranking);
}

pub proof fn lemma_insert_preserves_wf(pre: LinkedBranch, key: Key, msg: Message, path: Path)
    requires
        path.valid(),
        path.branch == pre,
        path.key == key,
        path.target().root() is Leaf,
    ensures
        pre.insert(key, msg, path).wf(),
{
    assume(false);
    let post = pre.insert(key, msg, path);
    match pre.root() {
        Node::Leaf{keys, msgs} => {
            let llte = Key::largest_lte(keys, key);
            Key::strictly_sorted_implies_sorted(keys);
            Key::largest_lte_ensures(keys, key, llte);
            // TODO(x9du): refinement should imply this
            // assert(new_node.wf());
        }
        Node::Index{pivots, children} => {
            lemma_target_preserves_disk(path);
            assert(path.target().disk_view == pre.disk_view);
            assert(path.target().root != pre.root);
            assert(post.disk_view.valid_address(pre.root));
            // Goal 1
            assert(post.has_root());

            // Goal 2
            assert(post.disk_view.wf());
        }
    }
}

pub proof fn lemma_target_preserves_disk(path: Path)
    requires
        path.valid(),
    ensures
        path.target().disk_view == path.branch.disk_view,
    decreases path.depth,
{
    if path.depth > 0 {
        lemma_target_preserves_disk(path.subpath());
    }
}

pub proof fn lemma_i_wf_implies_inv(branch: LinkedBranch, ranking: Ranking)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.i_internal(ranking).wf(),
    ensures
        branch.keys_strictly_sorted_internal(ranking),
        branch.all_keys_in_range_internal(ranking),
    decreases branch.get_rank(ranking),
{
    if branch.root() is Index {
        let branch_i = branch.i_internal(ranking);

        assert forall |i| #[trigger] branch.root().valid_child_index(i)
        implies branch.child_at_idx(i).all_keys_in_range_internal(ranking)
            && branch.child_at_idx(i).keys_strictly_sorted_internal(ranking) by {
            let child = branch.child_at_idx(i);
            assert(child.i_internal(ranking) == branch_i->children[i as int]);
            assert(child.i_internal(ranking).wf());
            lemma_i_wf_implies_inv(child, ranking);
        }
        
        assert forall |i| 0 <= i < branch.root()->children.len() - 1
        implies branch.all_keys_below_bound(i, ranking) by {
            assert(branch.root().valid_child_index(i as nat));
            let child = branch.child_at_idx(i as nat);
            assert(branch_i.all_keys_below_bound(i));
            assert forall |key| #[trigger] child.all_keys(ranking).contains(key)
            implies Key::lt(key, branch.root()->pivots[i]) by {
                lemma_i_preserves_all_keys(child, ranking);
                assert(branch_i->children[i].all_keys().contains(key));
                assert(Key::lt(key, branch_i->pivots[i]));
            }
        }

        assert forall |i| 0 < i < branch.root()->children.len()
        implies branch.all_keys_above_bound(i, ranking) by {
            assert(branch.root().valid_child_index(i as nat));
            let child = branch.child_at_idx(i as nat);
            assert(branch_i.all_keys_above_bound(i));
            assert forall |key| child.all_keys(ranking).contains(key)
            implies #[trigger] Key::lte(branch.root()->pivots[i-1], key) by {
                lemma_i_preserves_all_keys(child, ranking);
                assert(branch_i->children[i].all_keys().contains(key));
                assert(Key::lte(branch_i->pivots[i-1], key));
            }
        }
    }
}

pub proof fn lemma_i_internal_ignores_ranking(branch: LinkedBranch, ranking1: Ranking, ranking2: Ranking)
    requires
        branch.wf(),
        branch.valid_ranking(ranking1),
        branch.valid_ranking(ranking2),
    ensures
        branch.i_internal(ranking1) == branch.i_internal(ranking2),
    decreases branch.get_rank(ranking1),
{
    if branch.root() is Index {
        assert forall |i: nat| #[trigger] branch.root().valid_child_index(i)
        implies branch.child_at_idx(i).i_internal(ranking1)
            == branch.child_at_idx(i).i_internal(ranking2) by {
            lemma_i_internal_ignores_ranking(branch.child_at_idx(i), ranking1, ranking2);
        }
        assert(branch.i_internal(ranking1)->children =~~= branch.i_internal(ranking2)->children);
    }
}

pub proof fn lemma_subdisk_same_i_internal(branch1: LinkedBranch, branch2: LinkedBranch, ranking: Ranking)
    requires
        branch1.wf(),
        branch2.wf(),
        branch1.valid_ranking(ranking),
        branch2.valid_ranking(ranking),
        branch1.root() == branch2.root(),
        branch1.disk_view.is_subset_of(branch2.disk_view),
    ensures
        branch1.i_internal(ranking) == branch2.i_internal(ranking),
    decreases branch1.get_rank(ranking),
{
    if branch1.root() is Index {
        assert forall |i: nat| #[trigger] branch1.root().valid_child_index(i)
        implies
            branch2.root().valid_child_index(i)
            && (branch1.child_at_idx(i).i_internal(ranking)
                == branch2.child_at_idx(i).i_internal(ranking)) by {
            lemma_subdisk_same_i_internal(branch1.child_at_idx(i), branch2.child_at_idx(i), ranking);
        }
        assert(branch1.i_internal(ranking)->children =~~= branch2.i_internal(ranking)->children);
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
