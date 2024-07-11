// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin_macros::*;
use vstd::prelude::*;

use crate::betree::LinkedBranch_v::*;
use crate::betree::PivotBranch_v;
use crate::betree::PivotBranchRefinement_v;
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

impl Path {
    pub open spec(checked) fn i(self) -> PivotBranch_v::Path
        recommends
            self.branch.acyclic(),
    {
        PivotBranch_v::Path{ node: self.branch.i(), key: self.key, depth: self.depth }
    }

    pub open spec(checked) fn i_internal(self, ranking: Ranking) -> PivotBranch_v::Path
        recommends
            self.branch.wf(),
            self.branch.valid_ranking(ranking),
    {
        PivotBranch_v::Path{ node: self.branch.i_internal(ranking), key: self.key, depth: self.depth }
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
/// Ensures clause for `Node::route()` method.
pub proof fn lemma_route_ensures(node: Node, key: Key)
    requires
        node.wf(),
        node.keys_strictly_sorted(),
    ensures ({
        let s = node.keys_or_pivots();
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| 0 <= i <= node.route(key) ==> #[trigger] Key::lte(s[i], key)
        &&& forall |i| node.route(key) < i < s.len() ==> #[trigger] Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    })
{
    let s = node.keys_or_pivots();
    Key::strictly_sorted_implies_sorted(s);
    Key::largest_lte_ensures(s, key, Key::largest_lte(s, key));
}

pub proof fn lemma_route_auto()
    ensures forall |node: Node, key: Key| node.wf() && node.keys_strictly_sorted() ==> {
        let s = node.keys_or_pivots();
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #![trigger Key::lte(s[i], key)] 0 <= i <= node.route(key) ==> Key::lte(s[i], key)
        &&& forall |i| #![trigger Key::lt(key, s[i])] node.route(key) < i < s.len() ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    }
{
    assert forall |node: Node, key: Key| node.wf() && node.keys_strictly_sorted() implies {
        let s = node.keys_or_pivots();
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
        pre.insert(key, msg, path).i() == pre.i().insert(key, msg, path.i()),
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
        pre.insert(key, msg, path).i_internal(post_ranking)
            == pre.i_internal(ranking).insert(key, msg, path.i_internal(ranking)),
    decreases pre.get_rank(ranking),
{
    let pre_i = pre.i_internal(ranking);
    i_internal_wf(pre, ranking);
    let post = pre.insert(key, msg, path);
    let post_i = post.i_internal(post_ranking);
    let path_i = path.i_internal(ranking);
    lemma_path_i_valid(path, ranking);
    lemma_path_i_target(path, ranking);

    lemma_insert_preserves_wf(pre, ranking, key, msg, path);

    let except = set!{path.target().root};
    lemma_target_preserves_disk(path);
    assert(pre.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));
    assert(pre.disk_view.same_except(post.disk_view, except));

    if pre.root() is Index {
        let pivots = pre.root()->pivots;
        let children = pre.root()->children;

        assert(path.target().root != pre.root);
        assert(post.root() is Index);

        let i_then_insert = pre_i.insert(key, msg, path_i);
        PivotBranchRefinement_v::lemma_route_auto();
        assert(i_then_insert->children.len() == pre_i->children.len());
        assert(post_i->children.len() == i_then_insert->children.len());

        assert forall |i| 0 <= i < post_i->children.len()
        implies post_i->children[i] == i_then_insert->children[i] by {
            assert(pre.root().valid_child_index(i as nat));

            let r = pre.root().route(key) + 1;
            let r_i = pre_i.route(key) + 1;
            assert(r == r_i);

            if i == r {
                insert_refines_internal(pre.child_at_idx(r as nat), ranking, post_ranking, key, msg, path.subpath());
                assert(post_i->children[i] == post.child_at_idx(r as nat).i_internal(post_ranking));
                assert(i_then_insert->children[i] == pre.child_at_idx(r as nat).i_internal(ranking).insert(key, msg, path.subpath().i_internal(ranking)));
            } else {
                assert(i_then_insert->children[i] == pre_i->children[i]);

                assert(pre.root().valid_child_index(i as nat));
                assert(post.root().valid_child_index(i as nat));
                let pre_child = pre.child_at_idx(i as nat);
                let post_child = post.child_at_idx(i as nat);

                assert(pre_child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
                    if pre_child.reachable_addrs_using_ranking(ranking).contains(path.target().root) {
                        lemma_reachable_implies_all_keys_contains(pre_child, ranking, path.target().root);
                        lemma_all_keys_finite_and_nonempty(path.target(), ranking);
                        let k = choose |k| path.target().all_keys(ranking).contains(k);
                        assert(pre_child.all_keys(ranking).contains(k));
                        lemma_target_all_keys(pre.child_at_idx(r as nat), ranking, path.subpath(), k);
                        assert(pre.child_at_idx(r as nat).all_keys(ranking).contains(k));
                        if i < r {
                            lemma_children_share_key_contradiction(pre, ranking, i as nat, r as nat, k);
                        } else {
                            lemma_children_share_key_contradiction(pre, ranking, r as nat, i as nat, k);
                        }
                    }
                }
                lemma_reachable_unchanged_implies_same_i_internal(
                    pre_child, ranking, post_child, post_ranking, except);
                assert(pre_i->children[i] == post_i->children[i]);
            }
        }
        assert(post_i->children =~~= i_then_insert->children);
        assert(post_i =~~= i_then_insert);
    }

    PivotBranchRefinement_v::lemma_insert_preserves_wf(pre_i, key, msg, path_i);
    assert(post_i.wf());
    lemma_i_wf_implies_inv(post, post_ranking);
}

pub proof fn lemma_children_share_key_contradiction(branch: LinkedBranch, ranking: Ranking, i: nat, j: nat, key: Key)
    requires
        inv_internal(branch, ranking),
        i < j,
        branch.root().valid_child_index(i),
        branch.root().valid_child_index(j),
        branch.child_at_idx(i).all_keys(ranking).contains(key),
        branch.child_at_idx(j).all_keys(ranking).contains(key),
    ensures
        false,
{
    let pivots = branch.root()->pivots;
    if pivots.len() == 0 {
        assert(i == j);
    } else if i < j <= pivots.len() {
        assert(j > 0);
        if i < j - 1 {
            assert(Key::lt(pivots[i as int], pivots[(j-1) as int]));
        }
        assert(Key::lte(pivots[i as int], pivots[(j-1) as int]));

        assert(branch.all_keys_below_bound(i as int, ranking));
        assert(Key::lt(key, pivots[i as int]));
        assert(branch.all_keys_above_bound(j as int, ranking));
        assert(Key::lte(pivots[(j-1) as int], key));
        assert(Key::lt(pivots[(j-1) as int], pivots[i as int]));
    }
}

pub proof fn lemma_insert_preserves_wf(pre: LinkedBranch, ranking: Ranking, key: Key, msg: Message, path: Path)
    requires
        inv_internal(pre, ranking),
        path.valid(),
        path.branch == pre,
        path.key == key,
        path.target().root() is Leaf,
    ensures
        pre.insert(key, msg, path).wf(),
    decreases pre.get_rank(ranking),
{
    let post = pre.insert(key, msg, path);
    match pre.root() {
        Node::Leaf{keys, msgs} => {
            // Goal 1: new target wf
            Key::strictly_sorted_implies_sorted(keys);
            Key::largest_lte_ensures(keys, key, Key::largest_lte(keys, key));
        }
        Node::Index{pivots, children} => {
            lemma_target_preserves_disk(path);
            assert(path.target().disk_view == pre.disk_view);
            assert(path.target().root != pre.root);
            assert(post.disk_view.valid_address(pre.root));
            // Goal 2
            assert(post.has_root());

            let r = (pre.root().route(key) + 1) as nat;
            lemma_route_auto();
            assert(pre.root().valid_child_index(r));
            lemma_insert_preserves_wf(pre.child_at_idx(r), ranking, key, msg, path.subpath());
            // Goal 3
            assert(post.disk_view.wf());
        }
    }
}

pub proof fn lemma_path_i_target(path: Path, ranking: Ranking)
    requires
        inv_internal(path.branch, ranking),
        path.valid(),
    ensures
        path.target().wf(),
        path.target().valid_ranking(ranking),
        path.i_internal(ranking).target() == path.target().i_internal(ranking),
    decreases path.depth,
{
    if path.depth > 0 {
        let r = (path.branch.root().route(path.key) + 1) as nat;
        lemma_route_auto();
        assert(path.branch.root().valid_child_index(r));
        lemma_path_i_target(path.subpath(), ranking);
    }
}

pub proof fn lemma_path_i_valid(path: Path, ranking: Ranking)
    requires
        inv_internal(path.branch, ranking),
        path.valid(),
    ensures
        path.i_internal(ranking).valid(),
    decreases path.depth,
{
    i_internal_wf(path.branch, ranking);
    if 0 < path.depth {
        let r = (path.branch.root().route(path.key) + 1) as nat;
        lemma_route_auto();
        assert(path.branch.root().valid_child_index(r));
        lemma_path_i_valid(path.subpath(), ranking);
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

// TODO(x9du): duplicated from PivotBranchRefinement_v
pub proof fn lemma_target_all_keys(pre: LinkedBranch, ranking: Ranking, path: Path, key: Key)
    requires
        pre.wf(),
        pre.valid_ranking(ranking),
        pre.keys_strictly_sorted_internal(ranking),
        path.valid(),
        path.branch == pre,
    ensures
        path.target().all_keys(ranking).contains(key) ==> pre.all_keys(ranking).contains(key),
    decreases
        path.depth,
{
    if path.target().all_keys(ranking).contains(key) {
        if path.depth > 0 {
            assert(pre.root() is Index);
            let r = (pre.root().route(path.key) + 1) as nat;
            lemma_route_auto();
            assert(pre.root().valid_child_index(r));
            lemma_target_all_keys(pre.child_at_idx(r), ranking, path.subpath(), key);
            assert(pre.map_all_keys(ranking)[r as int].contains(key));
            lemma_set_subset_of_union_seq_of_sets(pre.map_all_keys(ranking), key);
            assert(pre.all_keys(ranking).contains(key));
        }
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

pub proof fn lemma_reachable_implies_all_keys_contains(branch: LinkedBranch, ranking: Ranking, addr: Address)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.disk_view.valid_address(addr),
        branch.reachable_addrs_using_ranking(ranking).contains(addr),
    ensures
        (LinkedBranch{root: addr, disk_view: branch.disk_view}).all_keys(ranking) <= branch.all_keys(ranking),
    decreases branch.get_rank(ranking),
{
    let branch2 = LinkedBranch{root: addr, disk_view: branch.disk_view};
    assert forall |key| branch2.all_keys(ranking).contains(key)
    implies branch.all_keys(ranking).contains(key) by {
        if branch.root() is Index && addr != branch.root {
            let subtree_addrs = branch.children_reachable_addrs_using_ranking(ranking);
            assert(union_seq_of_sets(subtree_addrs).contains(addr));
            lemma_union_seq_of_sets_contains(subtree_addrs, addr);
            let i = choose |i| 0 <= i < subtree_addrs.len() && (#[trigger] subtree_addrs[i]).contains(addr);
            assert(branch.root().valid_child_index(i as nat));
            lemma_reachable_implies_all_keys_contains(branch.child_at_idx(i as nat), ranking, addr);
            assert(branch.map_all_keys(ranking)[i].contains(key));
            lemma_set_subset_of_union_seq_of_sets(branch.map_all_keys(ranking), key);
        }
    }
}

pub proof fn lemma_reachable_addrs_subset(branch: LinkedBranch, ranking: Ranking)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
    ensures
        branch.reachable_addrs_using_ranking(ranking) <= branch.disk_view.entries.dom(),
    decreases branch.get_rank(ranking),
{
    let reachable = branch.reachable_addrs_using_ranking(ranking);
    assert forall |addr| #[trigger] reachable.contains(addr)
    implies branch.disk_view.entries.dom().contains(addr) by {
        if branch.root() is Index {
            if addr != branch.root {
                let subtree_addrs = branch.children_reachable_addrs_using_ranking(ranking);
                lemma_union_seq_of_sets_contains(subtree_addrs, addr);
                let i = choose |i| 0 <= i < subtree_addrs.len()
                    && (#[trigger] subtree_addrs[i]).contains(addr);
                assert(branch.root().valid_child_index(i as nat));
                lemma_reachable_addrs_subset(branch.child_at_idx(i as nat), ranking);
            }
        }
    }
}

pub proof fn lemma_reachable_disjoint_implies_child_reachable_disjoint(branch: LinkedBranch, ranking: Ranking, s: Set<Address>, i: nat)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.reachable_addrs_using_ranking(ranking).disjoint(s),
        branch.root() is Index,
        branch.root().valid_child_index(i),
    ensures
        branch.child_at_idx(i).reachable_addrs_using_ranking(ranking).disjoint(s),
{
    let child_reachable = branch.child_at_idx(i).reachable_addrs_using_ranking(ranking);
    if exists |addr| child_reachable.contains(addr) && s.contains(addr) {
        let addr = choose |addr| child_reachable.contains(addr) && s.contains(addr);
        let subtree_addrs = branch.children_reachable_addrs_using_ranking(ranking);
        assert(subtree_addrs[i as int].contains(addr));
        lemma_set_subset_of_union_seq_of_sets(subtree_addrs, addr);
    }
}

pub proof fn lemma_reachable_unchanged_implies_same_i_internal(branch1: LinkedBranch, ranking1: Ranking, branch2: LinkedBranch, ranking2: Ranking, except: Set<Address>)
    requires
        branch1.wf(),
        branch2.wf(),
        branch1.valid_ranking(ranking1),
        branch2.valid_ranking(ranking2),
        branch1.root == branch2.root,
        branch1.disk_view.same_except(branch2.disk_view, except),
        branch1.reachable_addrs_using_ranking(ranking1).disjoint(except),
    ensures
        branch1.i_internal(ranking1) == branch2.i_internal(ranking2),
    decreases branch1.get_rank(ranking1),
{
    assert(branch1.reachable_addrs_using_ranking(ranking1).contains(branch1.root));
    assert(!except.contains(branch1.root));
    lemma_reachable_addrs_subset(branch1, ranking1);
    assert(branch1.disk_view.entries.remove_keys(except).contains_key(branch1.root));
    assert(branch1.disk_view.entries.remove_keys(except) <= branch1.disk_view.entries);
    assert(branch1.root() == branch2.root());
    if branch1.root() is Index {
        assert forall |i: nat| #[trigger] branch1.root().valid_child_index(i)
        implies branch2.root().valid_child_index(i)
            && (branch1.child_at_idx(i).i_internal(ranking1)
                == branch2.child_at_idx(i).i_internal(ranking2)) by {
            lemma_reachable_disjoint_implies_child_reachable_disjoint(branch1, ranking1, except, i);
            lemma_reachable_unchanged_implies_same_i_internal(
                branch1.child_at_idx(i), ranking1, branch2.child_at_idx(i), ranking2, except);
        }
        assert(branch1.i_internal(ranking1)->children =~~= branch2.i_internal(ranking2)->children);
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
        let branch_i_children_keys = branch_i.children_keys();
        assert(branch.all_keys(ranking) == branch.root()->pivots.to_set() + branch.children_keys(ranking));
        assert(branch_i.all_keys() == branch_i->pivots.to_set() + branch_i.children_keys());

        assert forall |i| 0 <= i < branch.root()->children.len()
        implies branch.map_all_keys(ranking)[i] == PivotBranchRefinement_v::map_all_keys(branch_i->children)[i] by {
            assert(branch.root().valid_child_index(i as nat));
            lemma_i_preserves_all_keys(branch.child_at_idx(i as nat), ranking);
        }
        assert(branch.map_all_keys(ranking) == PivotBranchRefinement_v::map_all_keys(branch_i->children));
        PivotBranchRefinement_v::lemma_children_keys_equivalence(branch_i);
        assert(branch.children_keys(ranking) == branch_i.children_keys());
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
    lemma_union_seq_of_sets_finite(sets);
    assert(sets.len() > 0);
    let key = choose |key| sets[0].contains(key);
    lemma_set_subset_of_union_seq_of_sets(sets, key);
}

} // verus!
