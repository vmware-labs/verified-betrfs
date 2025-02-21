// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin_macros::*;
use vstd::prelude::*;

use crate::betree::LinkedBranch_v::*;
use crate::betree::PivotBranch_v;
use crate::betree::PivotBranchRefinement_v;
use crate::disk::GenericDisk_v::Ranking;

verus! {

broadcast use PivotBranch_v::Node::route_ensures;

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
                            // 0 <= i < children.len() ==> self.root().valid_child_index(i)
                            if self.root().valid_child_index(i) {
                                self.child_at_idx(i).i_internal(ranking)
                            } else {
                                PivotBranch_v::invalid_node()
                            }
                    ),
                }
            },
        }
    }

    pub open spec/*XXX (checked)*/ fn append_via_insert(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path) -> LinkedBranch
        recommends
            path.valid(),
            path.branch == self,
            keys.len() > 0,
            keys.len() == msgs.len(),
            Key::is_strictly_sorted(keys),
            path.target().root() is Leaf,
            Key::lt(path.target().root()->keys.last(), keys[0]),
            path.key == keys[0],
            path.path_equiv(keys.last()),
    {
        // Need path.valid() ==> path.target().wf() to restore checked
        keys.zip_with(msgs).fold_left_alt(self, |branch: LinkedBranch, pair: (Key, Message)|
            branch.insert(pair.0, pair.1, Path{branch: branch, key: pair.0, depth: path.depth}))
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

impl SplitArg {
    pub open spec(checked) fn i(self) -> PivotBranch_v::SplitArg
    {
        match self {
            SplitArg::SplitLeaf{pivot} => {
                PivotBranch_v::SplitArg::SplitLeaf{pivot: pivot}
            }
            SplitArg::SplitIndex{pivot, pivot_index} => {
                PivotBranch_v::SplitArg::SplitIndex{pivot: pivot, pivot_index: pivot_index}
            }
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

pub proof fn lemma_route_to_end(node: Node, key: Key)
    requires
        node.wf(),
        node.keys_strictly_sorted(),
        Key::lte(node.keys_or_pivots().last(), key),
    ensures
        node.route(key) == node.keys_or_pivots().len() - 1,
{
    let r = node.route(key);
    let s = node.keys_or_pivots();
    lemma_route_auto();
    if r < s.len() - 1 {
        assert(Key::lt(key, s.last()));
    }
}

pub proof fn lemma_key_lte_implies_route_lte(node: Node, key1: Key, key2: Key)
    requires
        node.wf(),
        node.keys_strictly_sorted(),
        Key::lte(key1, key2),
    ensures
        node.route(key1) <= node.route(key2)
{
    let s = node.keys_or_pivots();
    Key::strictly_sorted_implies_sorted(s);
    Key::largest_lte_ensures(s, key1, Key::largest_lte(s, key1));
    Key::largest_lte_ensures(s, key2, Key::largest_lte(s, key2));
    // Proof by contradiction
    if (Key::largest_lte(s, key1) > Key::largest_lte(s, key2)) {
        assert(Key::lt(key2, s[Key::largest_lte(s, key1)]));
//        assert(Key::lt(key2, key1));
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
//    assert(pre.i_internal(ranking).wf());

    lemma_route_auto();

    let r = pre.root().route(key);
    if pre.root() is Index {
        let pivots = pre.root()->pivots;
        let children = pre.root()->children;
//        assert(pre.root().valid_child_index(r+1));
        let child = pre.child_at_idx(r+1);
//        assert(child.wf());
//        assert(child.root().wf());
//        assert(child.valid_ranking(ranking));
        assert(child.keys_strictly_sorted_internal(ranking));
//        assert(child.query_internal(key, ranking) == msg);
        query_internal_refines(child, ranking, key, msg);
//        assert(0 <= r+1 < pre.i_internal(ranking)->children.len());
//        assert(pre.i_internal(ranking)->children[r+1] == child.i_internal(ranking));
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
//    assert(post.wf());
    i_internal_wf(pre, ranking);

//    assert(post_i->children.len() == i_then_grow->children.len() == 1);
//    assert(post.root().valid_child_index(0));
    assert(post_i->children[0] == post.child_at_idx(0).i_internal(post_ranking));
//    assert(i_then_grow->children[0] == pre.i_internal(ranking));

    let except = set!{addr};
    assert(pre.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));

    if pre.reachable_addrs_using_ranking(ranking).contains(addr) {
        lemma_reachable_implies_valid_address(pre, ranking, addr);
    }
    lemma_reachable_unchanged_implies_same_i_internal(
        pre, ranking, post.child_at_idx(0), post_ranking, except);
    assert(post_i->children =~~= i_then_grow->children);
//    assert(post_i == i_then_grow);

//    assert(post_i.wf());
    lemma_i_wf_implies_inv(post, post_ranking);
//    assert(post.all_keys_in_range_internal(post_ranking));
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
    lemma_path_target(path, ranking);

    lemma_insert_preserves_wf(pre, ranking, key, msg, path);

    let except = set!{path.target().root};
    assert(pre.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));

    if pre.root() is Index {
        let pivots = pre.root()->pivots;
        let children = pre.root()->children;

//        assert(path.target().root != pre.root);
//        assert(post.root() is Index);

        let i_then_insert = pre_i.insert(key, msg, path_i);
//        assert(i_then_insert->children.len() == pre_i->children.len());
//        assert(post_i->children.len() == i_then_insert->children.len());

        assert forall |i| 0 <= i < post_i->children.len()
        implies post_i->children[i] == i_then_insert->children[i] by {
//            assert(pre.root().valid_child_index(i));

            let r = pre.root().route(key) + 1;
            let r_i = pre_i.route(key) + 1;
//            assert(r == r_i);

            if i == r {
                insert_refines_internal(pre.child_at_idx(r), ranking, post_ranking, key, msg, path.subpath());
//                assert(post_i->children[i] == post.child_at_idx(r).i_internal(post_ranking));
//                assert(i_then_insert->children[i] == pre.child_at_idx(r).i_internal(ranking).insert(key, msg, path.subpath().i_internal(ranking)));
            } else {
//                assert(i_then_insert->children[i] == pre_i->children[i]);

//                assert(pre.root().valid_child_index(i));
                assert(post.root().valid_child_index(i));
                let pre_child = pre.child_at_idx(i);
                let post_child = post.child_at_idx(i);

                assert(pre_child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
                    if pre_child.reachable_addrs_using_ranking(ranking).contains(path.target().root) {
                        lemma_reachable_implies_all_keys_subset(pre_child, ranking, path.target().root);
                        lemma_all_keys_finite_and_nonempty(path.target(), ranking);
                        let k = choose |k| path.target().all_keys(ranking).contains(k);
//                        assert(pre_child.all_keys(ranking).contains(k));
                        lemma_target_all_keys(pre.child_at_idx(r), ranking, path.subpath(), k);
//                        assert(pre.child_at_idx(r).all_keys(ranking).contains(k));
                        if i < r {
                            lemma_children_share_key_contradiction(pre, ranking, i, r, k);
                        } else {
                            lemma_children_share_key_contradiction(pre, ranking, r, i, k);
                        }
                    }
                }
                lemma_reachable_unchanged_implies_same_i_internal(
                    pre_child, ranking, post_child, post_ranking, except);
//                assert(pre_i->children[i] == post_i->children[i]);
            }
        }
        assert(post_i->children =~~= i_then_insert->children);
//        assert(post_i =~~= i_then_insert);
    }

    PivotBranchRefinement_v::lemma_insert_preserves_wf(pre_i, key, msg, path_i);
//    assert(post_i.wf());
    lemma_i_wf_implies_inv(post, post_ranking);
}

pub proof fn append_refines(pre: LinkedBranch, keys: Seq<Key>, msgs: Seq<Message>, path: Path)
    requires
        inv(pre),
        path.valid(),
        path.branch == pre,
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target().root() is Leaf,
        Key::lt(path.target().root()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures
        inv(pre.append(keys, msgs, path)),
        pre.append(keys, msgs, path).i() == pre.i().append(keys, msgs, path.i()),
{
    let post = pre.append(keys, msgs, path);
    lemma_append_via_insert_equiv(pre, keys, msgs, path, pre.the_ranking());
    lemma_append_via_insert_preserves_ranking_and_wf(pre, pre.the_ranking(), keys, msgs, path);
    lemma_append_via_insert_refines(pre, pre.the_ranking(), post.the_ranking(), keys, msgs, path);

    lemma_path_i_internal(path, pre.the_ranking(), keys.last());
    lemma_path_target(path, pre.the_ranking());
    PivotBranchRefinement_v::lemma_append_via_insert_equiv(pre.i(), keys, msgs, path.i());
}

pub proof fn split_refines(pre: LinkedBranch, new_child_addr: Address, path: Path, split_arg: SplitArg)
    requires
        inv(pre),
        path.valid(),
        path.branch == pre,
        path.key == split_arg.get_pivot(),
        path.target().can_split_child_of_index(split_arg, new_child_addr),
        pre.disk_view.is_fresh(set!{new_child_addr}),
    ensures
        inv(pre.split(new_child_addr, path, split_arg)),
        pre.split(new_child_addr, path, split_arg).i() == pre.i().split(path.i(), split_arg.i()),
{
    let post = pre.split(new_child_addr, path, split_arg);
    let pivot = split_arg.get_pivot();
    let split_child_idx = path.target().root().route(pivot) + 1;
    lemma_path_target(path, pre.the_ranking());
    lemma_route_auto();
//    assert(path.target().root().valid_child_index(split_child_idx));
    let split_child = path.target().child_at_idx(split_child_idx);
    let split_child_addr = path.target().root()->children[split_child_idx];
    let post_ranking = pre.the_ranking().insert(new_child_addr, pre.the_ranking()[split_child_addr]);
    let except = set!{path.target().root, split_child_addr, new_child_addr};
    let (left_branch, right_branch) = split_child.split_node(split_arg, new_child_addr);
    let split_except = set!{split_child_addr, new_child_addr};
//    assert(pre.disk_view.entries.remove_keys(split_except) == left_branch.disk_view.entries.remove_keys(split_except));
//    assert(pre.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));

    assert forall |a| #[trigger] post_ranking.contains_key(a) && post.disk_view.entries.contains_key(a)
    implies post.disk_view.node_children_respects_rank(post_ranking, a) by {
        let node = pre.disk_view.entries[a];
        let post_node = post.disk_view.entries[a];
        assert forall |i: int| #[trigger] post_node.valid_child_index(i) implies {
            &&& post_ranking.contains_key(post_node->children[i])
            &&& post_ranking[post_node->children[i]] < post_ranking[a]
        } by {
            if a == path.target().root {
                if i <= split_child_idx {
                    assert(node.valid_child_index(i));
//                    assert(post_node->children[i] == node->children[i]);
                } else if i == split_child_idx + 1 {
//                    assert(post_node->children[i] == new_child_addr);
                } else {
                    assert(node.valid_child_index(i-1));
//                    assert(post_node->children[i] == node->children[i-1]);
                }
            } else if a == split_child_addr {
                assert(node.valid_child_index(i));
//                assert(post_node->children[i] == node->children[i]);
            } else if a == new_child_addr {
                if split_child.root() is Leaf {
                    let split_index = Key::largest_lt(split_child.root()->keys, pivot) + 1;
                    Key::strictly_sorted_implies_sorted(split_child.root()->keys);
                    Key::largest_lt_ensures(split_child.root()->keys, pivot, split_index);
//                    assert(node.valid_child_index(split_index + i));
//                    assert(post_node->children[i] == node->children[split_index + i]);
                } else {
                    let split_index = split_arg->pivot_index + 1;
                    assert(split_child.root().valid_child_index(split_index + i));
//                    assert(post_node->children[i] == split_child.root()->children[split_index + i]);
                }
            } else {
//                assert(node.valid_child_index(i));
//                assert(post_node == node);
            }
        }
    }

    assert(post.valid_ranking(post_ranking));
    split_refines_internal(pre, pre.the_ranking(), post.the_ranking(), new_child_addr, path, split_arg);
}

pub proof fn split_refines_internal(pre: LinkedBranch, ranking: Ranking, post_ranking: Ranking, new_child_addr: Address, path: Path, split_arg: SplitArg)
    requires
        inv_internal(pre, ranking),
        pre.split(new_child_addr, path, split_arg).valid_ranking(post_ranking),
        path.valid(),
        path.branch == pre,
        path.key == split_arg.get_pivot(),
        path.target().can_split_child_of_index(split_arg, new_child_addr),
        pre.disk_view.is_fresh(set!{new_child_addr}),
    ensures
        inv_internal(pre.split(new_child_addr, path, split_arg), post_ranking),
        pre.split(new_child_addr, path, split_arg).i_internal(post_ranking)
            == pre.i_internal(ranking).split(path.i_internal(ranking), split_arg.i()),
    decreases pre.get_rank(ranking),
{
    let post = pre.split(new_child_addr, path, split_arg);
    let pivot = split_arg.get_pivot();
    let split_child_idx = path.target().root().route(pivot) + 1;
    lemma_path_target(path, ranking);
    lemma_route_auto();
//    assert(path.target().root().valid_child_index(split_child_idx));
    let split_child = path.target().child_at_idx(split_child_idx);
    let split_child_addr = path.target().root()->children[split_child_idx];
    let except = set!{path.target().root, split_child_addr, new_child_addr};
    let (left_branch, right_branch) = split_child.split_node(split_arg, new_child_addr);
    let split_except = set!{split_child_addr, new_child_addr};
//    assert(pre.disk_view.entries.remove_keys(split_except) == left_branch.disk_view.entries.remove_keys(split_except));
    assert(pre.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));

    let pre_i = pre.i_internal(ranking);
    let post_i = post.i_internal(post_ranking);
    let path_i = path.i_internal(ranking);
    let i_then_split = pre_i.split(path_i, split_arg.i());
    lemma_split_preserves_wf(pre, ranking, new_child_addr, path, split_arg);
    i_internal_wf(pre, ranking);
    lemma_path_i_valid(path, ranking);
    PivotBranchRefinement_v::lemma_path_target_is_wf(path_i);
//    assert(split_child_idx == path_i.target().route(pivot) + 1);
//    assert(path_i.target()->children[split_child_idx] == split_child.i_internal(ranking));

    if path.depth == 0 {
//        assert(post.root()->children.len() == pre.root()->children.len() + 1);
//        assert(i_then_split->children.len() == pre_i->children.len() + 1);
    } else {
        assert(!except.contains(pre.root)) by {
            lemma_path_target_has_smaller_rank(pre, ranking, path);
        }
//        assert(post.root()->children.len() == pre.root()->children.len());
//        assert(i_then_split->children.len() == pre_i->children.len());
    }
//    assert(post_i->children.len() == i_then_split->children.len());

    assert forall |i| 0 <= i < post_i->children.len()
    implies post_i->children[i] == i_then_split->children[i] by {
        if path.depth == 0 {
            if i == split_child_idx || i == split_child_idx + 1 {
                let (left_node, right_node) = split_child.i_internal(ranking).split_node(split_arg.i());
                lemma_split_node_ranking(pre, ranking, post_ranking, new_child_addr, split_arg, left_branch, right_branch);
                lemma_split_node_interpretation(split_child, ranking, post_ranking, new_child_addr, split_arg, left_branch, right_branch, left_node, right_node);

//                assert(split_child_idx == pre_i.route(pivot) + 1);
//                assert(i_then_split->children[split_child_idx] == left_node);
//                assert(i_then_split->children[split_child_idx + 1] == right_node);
//                assert(post_i->children[i] == post.child_at_idx(i).i_internal(post_ranking));
                assert(post.disk_view.entries.remove_keys(set!{pre.root}) == left_branch.disk_view.entries.remove_keys(set!{pre.root}));
                if left_branch.reachable_addrs_using_ranking(post_ranking).contains(pre.root) {
                    lemma_reachable_child_has_smaller_rank(left_branch, post_ranking, pre.root);
                }
                lemma_reachable_unchanged_implies_same_i_internal(
                    left_branch, post_ranking, post.child_at_idx(split_child_idx), post_ranking, set!{pre.root});
                if right_branch.reachable_addrs_using_ranking(post_ranking).contains(pre.root) {
                    lemma_reachable_child_has_smaller_rank(right_branch, post_ranking, pre.root);
//                    assert(right_branch.root == post.root()->children[split_child_idx + 1]);
                    assert(post.root().valid_child_index(split_child_idx + 1));
//                    assert(post_ranking[right_branch.root] < post_ranking[pre.root]);
                }
                lemma_reachable_unchanged_implies_same_i_internal(
                    right_branch, post_ranking, post.child_at_idx(split_child_idx + 1), post_ranking, set!{pre.root});
            } else {
                let j = if i < split_child_idx { i } else { i - 1 };
//                assert(pre.root().valid_child_index(j));
                let pre_child = pre.child_at_idx(j);
//                assert(i_then_split->children[i] == pre_i->children[j]);
//                assert(pre_i->children[j] == pre_child.i_internal(ranking));
//                assert(post_i->children[i] == post.child_at_idx(i).i_internal(post_ranking));
                assert(pre_child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
                    if pre_child.reachable_addrs_using_ranking(ranking).contains(pre.root) {
                        lemma_reachable_child_has_smaller_rank(pre_child, ranking, pre.root);
                    } else if pre_child.reachable_addrs_using_ranking(ranking).contains(split_child_addr) {
                        lemma_reachable_implies_all_keys_subset(pre_child, ranking, split_child_addr);
                        lemma_all_keys_finite_and_nonempty(split_child, ranking);
                        let k = choose |k| split_child.all_keys(ranking).contains(k);
//                        assert(pre_child.all_keys(ranking).contains(k));
                        if j < split_child_idx {
                            lemma_children_share_key_contradiction(pre, ranking, j, split_child_idx, k);
                        } else {
                            lemma_children_share_key_contradiction(pre, ranking, split_child_idx, j, k);
                        }
                    } else if pre_child.reachable_addrs_using_ranking(ranking).contains(new_child_addr) {
                        lemma_reachable_implies_valid_address(pre_child, ranking, new_child_addr);
                    }
                }
                lemma_reachable_unchanged_implies_same_i_internal(
                    pre_child, ranking, post.child_at_idx(i), post_ranking, except);
            }
        } else {
            let r = pre.root().route(path.key) + 1;
            let r_i = pre_i.route(path.key) + 1;
//            assert(r == r_i);

            if i == r {
                split_refines_internal(pre.child_at_idx(r), ranking, post_ranking, new_child_addr, path.subpath(), split_arg);
                assert(post_i->children[i] == post.child_at_idx(r).i_internal(post_ranking));
                assert(i_then_split->children[i] == pre.child_at_idx(r).i_internal(ranking).split(path.subpath().i_internal(ranking), split_arg.i()));
            } else {
//                assert(i_then_split->children[i] == pre_i->children[i]);
                let pre_child = pre.child_at_idx(i);

                assert(pre_child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
                    if pre_child.reachable_addrs_using_ranking(ranking).contains(path.target().root) {
                        lemma_reachable_implies_all_keys_subset(pre_child, ranking, path.target().root);
                        lemma_all_keys_finite_and_nonempty(path.target(), ranking);
                        let k = choose |k| path.target().all_keys(ranking).contains(k);
//                        assert(pre_child.all_keys(ranking).contains(k));
                        lemma_target_all_keys(pre.child_at_idx(r), ranking, path.subpath(), k);
//                        assert(pre.child_at_idx(r).all_keys(ranking).contains(k));
                        if i < r {
                            lemma_children_share_key_contradiction(pre, ranking, i, r, k);
                        } else {
                            lemma_children_share_key_contradiction(pre, ranking, r, i, k);
                        }
                    } else if pre_child.reachable_addrs_using_ranking(ranking).contains(split_child_addr) {
                        lemma_reachable_implies_all_keys_subset(pre_child, ranking, split_child_addr);
                        lemma_all_keys_finite_and_nonempty(split_child, ranking);
                        let k = choose |k| split_child.all_keys(ranking).contains(k);
//                        assert(pre_child.all_keys(ranking).contains(k));
                        assert(path.target().map_all_keys(ranking)[split_child_idx].contains(k));
                        lemma_set_subset_of_union_seq_of_sets(path.target().map_all_keys(ranking), k);
                        lemma_target_all_keys(pre.child_at_idx(r), ranking, path.subpath(), k);
//                        assert(pre.child_at_idx(r).all_keys(ranking).contains(k));
                        if i < r {
                            lemma_children_share_key_contradiction(pre, ranking, i, r, k);
                        } else {
                            lemma_children_share_key_contradiction(pre, ranking, r, i, k);
                        }
                    } else if pre_child.reachable_addrs_using_ranking(ranking).contains(new_child_addr) {
                        lemma_reachable_implies_valid_address(pre_child, ranking, new_child_addr);
                    }
                }
                lemma_reachable_unchanged_implies_same_i_internal(
                    pre_child, ranking, post.child_at_idx(i), post_ranking, except);
            }
        }
    }

    assert(post_i->children =~~= i_then_split->children);
//    assert(post_i == i_then_split);
    PivotBranchRefinement_v::lemma_split_preserves_wf(pre_i, path_i, split_arg.i());
//    assert(post_i.wf());
    lemma_i_wf_implies_inv(post, post_ranking);
}

pub proof fn lemma_split_node_interpretation(
    branch: LinkedBranch,
    ranking: Ranking,
    post_ranking: Ranking,
    new_child_addr: Address,
    split_arg: SplitArg,
    left_branch: LinkedBranch,
    right_branch: LinkedBranch,
    left_node: PivotBranch_v::Node,
    right_node: PivotBranch_v::Node)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.keys_strictly_sorted_internal(ranking),
        split_arg.wf(branch),
        branch.disk_view.is_fresh(set!{new_child_addr}),
        (left_branch, right_branch) == branch.split_node(split_arg, new_child_addr),
        left_branch.wf(),
        right_branch.wf(),
        left_branch.valid_ranking(post_ranking),
        right_branch.valid_ranking(post_ranking),
        (left_node, right_node) == branch.i_internal(ranking).split_node(split_arg.i()),
    ensures
        left_node == left_branch.i_internal(post_ranking),
        right_node == right_branch.i_internal(post_ranking),
{
    let pivot = split_arg.get_pivot();
    let left_branch_i = left_branch.i_internal(post_ranking);
    let right_branch_i = right_branch.i_internal(post_ranking);
    let branch_i = branch.i_internal(ranking);
    if branch.root() is Leaf {
        Key::strictly_sorted_implies_sorted(branch.root()->keys);
        Key::largest_lt_ensures(branch.root()->keys, pivot, Key::largest_lt(branch.root()->keys, pivot));
    } else {
        let except = set!{branch.root, new_child_addr};
        assert(branch.disk_view.entries.remove_keys(except) == left_branch.disk_view.entries.remove_keys(except));

//        assert(left_node->children.len() == left_branch_i->children.len());
        assert forall |i| 0 <= i < left_node->children.len()
        implies left_node->children[i] == left_branch_i->children[i] by {
            let child = branch.child_at_idx(i);

//            assert(left_node->children[i] == branch_i->children[i]);
            assert(branch_i->children[i] == child.i_internal(ranking));

            assert(left_branch_i->children[i] == left_branch.child_at_idx(i).i_internal(post_ranking));

            assert(child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
                if child.reachable_addrs_using_ranking(ranking).contains(branch.root) {
                    lemma_reachable_child_has_smaller_rank(child, ranking, branch.root);
                } else if child.reachable_addrs_using_ranking(ranking).contains(new_child_addr) {
                    lemma_reachable_implies_valid_address(child, ranking, new_child_addr);
                }
            }
            lemma_reachable_unchanged_implies_same_i_internal(
                child, ranking, left_branch.child_at_idx(i), post_ranking, except);
        }
        assert(left_node->children =~~= left_branch_i->children);

//        assert(right_node->children.len() == right_branch_i->children.len());
        assert forall |i| 0 <= i < right_node->children.len()
        implies right_node->children[i] == right_branch_i->children[i] by {
            let j = i + split_arg->pivot_index + 1;
            let child = branch.child_at_idx(j);

//            assert(right_node->children[i] == branch_i->children[j]);
            assert(branch_i->children[j] == child.i_internal(ranking));

            assert(right_branch_i->children[i] == right_branch.child_at_idx(i).i_internal(post_ranking));

            assert(child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
                if child.reachable_addrs_using_ranking(ranking).contains(branch.root) {
                    lemma_reachable_child_has_smaller_rank(child, ranking, branch.root);
                } else if child.reachable_addrs_using_ranking(ranking).contains(new_child_addr) {
                    lemma_reachable_implies_valid_address(child, ranking, new_child_addr);
                }
            }
            lemma_reachable_unchanged_implies_same_i_internal(
                child, ranking, right_branch.child_at_idx(i), post_ranking, except);
        }
        assert(right_node->children =~~= right_branch_i->children);
    }
}

pub proof fn lemma_split_node_ranking(
    branch: LinkedBranch,
    ranking: Ranking,
    post_ranking: Ranking,
    new_child_addr: Address,
    split_arg: SplitArg,
    left_branch: LinkedBranch,
    right_branch: LinkedBranch)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.keys_strictly_sorted_internal(ranking),
        branch.can_split_child_of_index(split_arg, new_child_addr),
        branch.split_child_of_index(split_arg, new_child_addr).valid_ranking(post_ranking),
        (left_branch, right_branch) == branch.child_at_idx(branch.root().route(split_arg.get_pivot()) + 1).split_node(split_arg, new_child_addr),
    ensures
        left_branch.valid_ranking(post_ranking),
        right_branch.valid_ranking(post_ranking),
{
    let post = branch.split_child_of_index(split_arg, new_child_addr);
    lemma_split_preserves_wf(branch, ranking, new_child_addr, Path{branch: branch, key: split_arg.get_pivot(), depth: 0}, split_arg);
    lemma_route_auto();
    let r = branch.root().route(split_arg.get_pivot()) + 1;
    assert(post.root().valid_child_index(r));
//    assert(left_branch.root == post.root()->children[r]);
//    assert(post_ranking.contains_key(left_branch.root));
    assert(post.root().valid_child_index(r+1));
//    assert(right_branch.root == post.root()->children[r+1]);
//    assert(post_ranking.contains_key(right_branch.root));

    assert forall |a| #[trigger] post_ranking.contains_key(a) && left_branch.disk_view.entries.contains_key(a)
    implies left_branch.disk_view.node_children_respects_rank(post_ranking, a) by {
        let parent_node = post.disk_view.entries[a];
        let node = left_branch.disk_view.entries[a];
        assert forall |i: int| #[trigger] node.valid_child_index(i) implies {
            &&& post_ranking.contains_key(node->children[i])
            &&& post_ranking[node->children[i]] < post_ranking[a]
        } by {
            assert(parent_node.valid_child_index(i));
            if a == branch.root {
                assert(parent_node.valid_child_index(i+1));
                if i <= r {
//                    assert(parent_node->children[i] == node->children[i]);
                } else {
//                    assert(parent_node->children[i+1] == node->children[i]);
                }
            } else {
//                assert(node == parent_node);
            }
        }
    }
}

pub proof fn lemma_reachable_implies_valid_address(branch: LinkedBranch, ranking: Ranking, addr: Address)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.reachable_addrs_using_ranking(ranking).contains(addr),
    ensures
        branch.disk_view.valid_address(addr),
    decreases branch.get_rank(ranking),
{
    if addr != branch.root {
        let subtree_addrs = branch.children_reachable_addrs_using_ranking(ranking);
        lemma_union_seq_of_sets_contains(subtree_addrs, addr);
        let i = choose |i| 0 <= i < subtree_addrs.len() && (#[trigger] subtree_addrs[i]).contains(addr);
        assert(branch.root().valid_child_index(i));
        lemma_reachable_implies_valid_address(branch.child_at_idx(i), ranking, addr);
    }
}

pub proof fn lemma_path_target_has_smaller_rank(branch: LinkedBranch, ranking: Ranking, path: Path)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.keys_strictly_sorted_internal(ranking),
        path.valid(),
        path.branch == branch,
        path.depth > 0,
    ensures
        ranking[path.target().root] < ranking[branch.root],
    decreases branch.get_rank(ranking),
{
    lemma_route_auto();
    let r = branch.root().route(path.key) + 1;
    assert(branch.root().valid_child_index(r));
//    assert(ranking[branch.child_at_idx(r).root] < ranking[branch.root]);
    if path.subpath().depth == 0 {
        assert(path.target() == path.subpath().target());
//        assert(path.target() == branch.child_at_idx(r));
    } else {
        lemma_path_target_has_smaller_rank(branch.child_at_idx(r), ranking, path.subpath());
    }
}

pub proof fn lemma_reachable_child_has_smaller_rank(branch: LinkedBranch, ranking: Ranking, addr: Address)
    requires
        branch.wf(),
        branch.valid_ranking(ranking),
        branch.root() is Index,
        ranking.contains_key(addr),
        union_seq_of_sets(branch.children_reachable_addrs_using_ranking(ranking)).contains(addr),
    ensures
        ranking[addr] < ranking[branch.root],
    decreases branch.get_rank(ranking),
{
    let subtree_addrs = branch.children_reachable_addrs_using_ranking(ranking);
    lemma_union_seq_of_sets_contains(subtree_addrs, addr);
    let i = choose |i| 0 <= i < subtree_addrs.len() && (#[trigger] subtree_addrs[i]).contains(addr);
    assert(branch.root().valid_child_index(i));
    if addr != branch.child_at_idx(i).root {
        lemma_reachable_child_has_smaller_rank(branch.child_at_idx(i), ranking, addr);
    }
}

pub proof fn lemma_split_preserves_wf(pre: LinkedBranch, ranking: Ranking, new_child_addr: Address, path: Path, split_arg: SplitArg)
    requires
        pre.valid_ranking(ranking),
        pre.keys_strictly_sorted_internal(ranking),
        path.valid(),
        path.branch == pre,
        path.key == split_arg.get_pivot(),
        path.target().can_split_child_of_index(split_arg, new_child_addr),
        pre.disk_view.is_fresh(set!{new_child_addr}),
    ensures
        pre.split(new_child_addr, path, split_arg).wf(),
    decreases pre.get_rank(ranking),
{
    let post = pre.split(new_child_addr, path, split_arg);
    let pivot = split_arg.get_pivot();
    let split_child_idx = path.target().root().route(pivot) + 1;
    lemma_path_target(path, ranking);
    lemma_route_auto();
//    assert(path.target().root().valid_child_index(split_child_idx));
    let split_child = path.target().child_at_idx(split_child_idx);
    let split_child_addr = path.target().root()->children[split_child_idx];
    let except = set!{path.target().root, split_child_addr, new_child_addr};
    let (left_branch, right_branch) = split_child.split_node(split_arg, new_child_addr);
    let split_except = set!{split_child_addr, new_child_addr};
//    assert(pre.disk_view.entries.remove_keys(split_except) == left_branch.disk_view.entries.remove_keys(split_except));
//    assert(pre.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));
}

pub proof fn lemma_path_i_internal(path: Path, ranking: Ranking, key: Key)
    requires
        inv_internal(path.branch, ranking),
        path.valid(),
        path.path_equiv(key),
    ensures
        path.i_internal(ranking).valid(),
        path.i_internal(ranking).target() == path.target().i_internal(ranking),
        path.i_internal(ranking).path_equiv(key),
    decreases path.depth,
{
    let path_i = path.i_internal(ranking);
    lemma_route_auto();
    i_internal_wf(path.branch, ranking);
    if path.depth > 0 {
        lemma_path_i_internal(path.subpath(), ranking, key);
    }
}

pub proof fn lemma_append_keys_are_path_equiv(keys: Seq<Key>, path: Path, ranking: Ranking)
    requires
        path.branch.valid_ranking(ranking),
        path.branch.keys_strictly_sorted_internal(ranking),
        path.valid(),
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        path.key == keys[0],
        path.path_equiv(keys.last())
    ensures
        forall |key| keys.contains(key) ==> path.path_equiv(key)
    decreases path.depth
{
    lemma_route_auto();

    if 0 < path.depth {
        let r = path.branch.root().route(path.key) + 1;
        assert(path.branch.root().valid_child_index(r));
        lemma_append_keys_are_path_equiv(keys, path.subpath(), ranking);
    }

    Key::strictly_sorted_implies_sorted(keys);

    let node = path.branch.root();
    assert forall |key| keys.contains(key) implies path.path_equiv(key) by {
        lemma_key_lte_implies_route_lte(node, keys[0], key);
        lemma_key_lte_implies_route_lte(node, key, keys.last());
//        assert(node.route(path.key) == node.route(key));
    }
}

pub proof fn lemma_append_incremental(keys: Seq<Key>, msgs: Seq<Message>, path: Path, path1: Path, ranking: Ranking)
    requires
        path.branch.valid_ranking(ranking),
        path.branch.keys_strictly_sorted_internal(ranking),
        path.valid(),
        keys.len() > 1,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target().root() is Leaf,
        Key::lt(path.target().root()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
        path1 == (Path{branch: path.branch.append(keys.take(1), msgs.take(1), path),
            key: keys[1], depth: path.depth}),
    ensures
        path.branch.append(keys, msgs, path)
            == path1.branch.append(keys.skip(1), msgs.skip(1), path1),
    decreases path.depth,
{
    let post = path.branch.append(keys, msgs, path);
    let post1 = path1.branch.append(keys.skip(1), msgs.skip(1), path1);

    let except = set!{path.target().root};
    lemma_path_target(path, ranking);
//    assert(path.branch.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));

    if path.depth == 0 {
        assert(path.branch.root()->keys + keys == path.branch.root()->keys + keys.take(1) + keys.skip(1));
        assert(path.branch.root()->msgs + msgs == path.branch.root()->msgs + msgs.take(1) + msgs.skip(1));
        assert(post =~~= post1);
    } else {
        let r = path.branch.root().route(path.key);
        let r1 = path1.branch.root().route(keys[1]);
        lemma_route_auto();
        lemma_append_keys_are_path_equiv(keys, path, ranking);
        assert(path.path_equiv(keys[1]));
//        assert(r == path.branch.root().route(keys[1]));
//        assert(r == r1);
//        assert(path.branch.root().valid_child_index(r+1));
//        assert(path1.subpath().branch == path1.branch.child_at_idx(r+1));
//        assert(path1.subpath().branch == path.branch.child_at_idx(r+1).append(keys.take(1), msgs.take(1), path.subpath()));
//        assert(path1.subpath().branch == path.subpath().branch.append(keys.take(1), msgs.take(1), path.subpath()));
        lemma_append_incremental(keys, msgs, path.subpath(), path1.subpath(), ranking);

//        assert(post =~~= post1);
    }
}

pub proof fn lemma_append_via_insert_path(path: Path, ranking: Ranking, keys: Seq<Key>, msgs: Seq<Message>)
    requires
        path.branch.valid_ranking(ranking),
        path.branch.keys_strictly_sorted_internal(ranking),
        path.valid(),
        keys.len() > 1,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target().root() is Leaf,
        Key::lt(path.target().root()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures ({
            let path1 = Path{branch: path.branch.insert(keys[0], msgs[0], path), key: keys[1], depth: path.depth};
            &&& path1.valid()
            &&& path1.target() == path.target().insert_leaf(keys[0], msgs[0])
            &&& path1.path_equiv(keys.last())
        })
    decreases path.depth,
{
    let post = path.branch.insert(keys[0], msgs[0], path);

    let except = set!{path.target().root};
    lemma_path_target(path, ranking);
//    assert(path.branch.disk_view.entries.remove_keys(except) == post.disk_view.entries.remove_keys(except));

    let path1 = Path{branch: post, key: keys[1], depth: path.depth};
    lemma_insert_preserves_wf(path.branch, ranking, keys[0], msgs[0], path);
    lemma_route_auto();
    lemma_append_keys_are_path_equiv(keys, path, ranking);
    assert(path.path_equiv(keys[1]));

    if path.depth == 0 {
        lemma_route_to_end(path.target().root(), keys[0]);
//        assert(path1.branch.root()->keys.last() == keys[0]);

        let r1_key1 = path1.branch.root().route(keys[1]);
        assert(r1_key1 == path1.branch.root()->keys.len() - 1) by {
            assert(Key::lt(keys[0], keys[1]));
            if r1_key1 < path1.branch.root()->keys.len() - 1 {
                assert(Key::lt(keys[1], path1.branch.root()->keys.last()));
            }
        }
        let r1_key2 = path1.branch.root().route(keys.last());
        assert(r1_key2 == path1.branch.root()->keys.len() - 1) by {
            assert(Key::lt(keys[0], keys.last()));
            if r1_key2 < path1.branch.root()->keys.len() - 1 {
                assert(Key::lt(keys.last(), path1.branch.root()->keys.last()));
            }
        }
//        assert(r1_key1 == r1_key2);
    } else {
        let r = path.branch.root().route(path.key);
//        assert(path.branch.root().valid_child_index(r+1));
        lemma_append_via_insert_path(path.subpath(), ranking, keys, msgs);
    }
}

pub proof fn lemma_append_via_insert_equiv(branch: LinkedBranch, keys: Seq<Key>, msgs: Seq<Message>, path: Path, ranking: Ranking)
    requires
        inv_internal(branch, ranking),
        path.valid(),
        path.branch == branch,
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target().root() is Leaf,
        Key::lt(path.target().root()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures
        branch.append(keys, msgs, path) == branch.append_via_insert(keys, msgs, path),
    decreases keys.len(),
{
    lemma_path_target(path, ranking);
    let post = branch.append(keys, msgs, path);
    let via_insert = branch.append_via_insert(keys, msgs, path);
    let keys_msgs = keys.zip_with(msgs);
    let insert0 = branch.insert(keys[0], msgs[0], path);
    let r = path.target().root().route(keys[0]);
    lemma_route_auto();
//    assert(path.target().root().keys_strictly_sorted());
    lemma_route_to_end(path.target().root(), keys[0]);
//    assert(r == path.target().root()->keys.len() - 1);
    assert(path.target().root()->keys.insert(r+1, keys[0]) == path.target().root()->keys + keys.take(1));
    assert(path.target().root()->msgs.insert(r+1, msgs[0]) == path.target().root()->msgs + msgs.take(1));

    if keys.len() == 1 {
        reveal_with_fuel(vstd::prelude::Seq::fold_left_alt, 2);
//        assert(via_insert == insert0);
        assert(keys.take(1) == keys);
        assert(msgs.take(1) == msgs);
//        assert(insert0 == post);
    } else {
        let path1 = Path{branch: insert0, key: keys[1], depth: path.depth};
        lemma_append_via_insert_path(path, ranking, keys, msgs);
//        assert(path1.valid());
//        assert(path1.target().root()->keys.last() == keys[0]);
//        assert(Key::lt(path1.target().root()->keys.last(), keys[1]));

        lemma_insert_preserves_ranking(branch, ranking, keys[0], msgs[0], path);
        insert_refines_internal(branch, ranking, ranking, keys[0], msgs[0], path);
        lemma_append_via_insert_equiv(insert0, keys.skip(1), msgs.skip(1), path1, ranking);

//        assert(insert0 == branch.append(keys.take(1), msgs.take(1), path));
        lemma_append_incremental(keys, msgs, path, path1, ranking);
//        assert(post == insert0.append(keys.skip(1), msgs.skip(1), path1));

        assert(keys_msgs.skip(1) == keys.skip(1).zip_with(msgs.skip(1)));
//        assert(via_insert == insert0.append_via_insert(keys.skip(1), msgs.skip(1), path1));

//        assert(post == via_insert);
    }
}

pub proof fn lemma_append_via_insert_preserves_ranking_and_wf(pre: LinkedBranch, ranking: Ranking, keys: Seq<Key>, msgs: Seq<Message>, path: Path)
    requires
        inv_internal(pre, ranking),
        path.valid(),
        path.branch == pre,
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target().root() is Leaf,
        Key::lt(path.target().root()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures
        pre.append_via_insert(keys, msgs, path).valid_ranking(ranking),
        pre.append_via_insert(keys, msgs, path).wf(),
    decreases keys.len(),
{
    let post = pre.append_via_insert(keys, msgs, path);
    let insert0 = pre.insert(keys[0], msgs[0], path);
    let keys_msgs = keys.zip_with(msgs);
    lemma_insert_preserves_ranking(pre, ranking, keys[0], msgs[0], path);
    if keys_msgs.len() == 1 {
        reveal_with_fuel(vstd::prelude::Seq::fold_left_alt, 2);
//        assert(post == insert0);
        lemma_insert_preserves_wf(pre, ranking, keys[0], msgs[0], path);
    } else {
        let path1 = Path{branch: insert0, key: keys[1], depth: path.depth};
        lemma_append_via_insert_path(path, ranking, keys, msgs);
        lemma_path_target(path, ranking);
        lemma_route_to_end(path.target().root(), keys[0]);
//        assert(path1.target().root()->keys.last() == keys[0]);
//        assert(keys.skip(1)[0] == keys[1]);
//        assert(Key::lt(keys[0], keys[1]));
        insert_refines_internal(pre, ranking, ranking, keys[0], msgs[0], path);
        lemma_append_via_insert_preserves_ranking_and_wf(insert0, ranking, keys.skip(1), msgs.skip(1), path1);
        assert(keys_msgs.skip(1) == keys.skip(1).zip_with(msgs.skip(1)));
//        assert(post == insert0.append_via_insert(keys.skip(1), msgs.skip(1), path1));
    }
}

pub proof fn lemma_append_via_insert_refines(pre: LinkedBranch, ranking: Ranking, post_ranking: Ranking, keys: Seq<Key>, msgs: Seq<Message>, path: Path)
    requires
        inv_internal(pre, ranking),
        pre.append_via_insert(keys, msgs, path).valid_ranking(post_ranking),
        path.valid(),
        path.branch == pre,
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target().root() is Leaf,
        Key::lt(path.target().root()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures
        inv_internal(pre.append_via_insert(keys, msgs, path), post_ranking),
        pre.append_via_insert(keys, msgs, path).i_internal(post_ranking)
            == pre.i_internal(ranking).append_via_insert(keys, msgs, path.i_internal(ranking)),
    decreases keys.len(),
{
    lemma_append_via_insert_preserves_ranking_and_wf(pre, ranking, keys, msgs, path);
    let keys_msgs = keys.zip_with(msgs);
    let post = pre.append_via_insert(keys, msgs, path);
    let post_i = post.i_internal(post_ranking);
    let pre_i = pre.i_internal(ranking);
    let path_i = path.i_internal(ranking);
    let i_then_append = pre_i.append_via_insert(keys, msgs, path_i);
    let insert0 = pre.insert(keys[0], msgs[0], path);
    lemma_route_auto();

    if keys_msgs.len() == 1 {
        reveal_with_fuel(vstd::prelude::Seq::fold_left_alt, 2);
//        assert(post == insert0);
        insert_refines_internal(pre, ranking, post_ranking, keys[0], msgs[0], path);
//        assert(insert0.i_internal(post_ranking) == pre_i.insert(keys[0], msgs[0], path_i));
//        assert(i_then_append =~~= pre_i.insert(keys[0], msgs[0], path_i));
//        assert(post_i == i_then_append);
    } else {
        let path1 = Path{branch: insert0, key: keys[1], depth: path.depth};
        lemma_append_via_insert_path(path, ranking, keys, msgs);
        lemma_path_target(path, ranking);
        lemma_route_to_end(path.target().root(), keys[0]);
//        assert(path1.target().root()->keys.last() == keys[0]);
//        assert(keys.skip(1)[0] == keys[1]);
//        assert(Key::lt(keys[0], keys[1]));

        lemma_insert_preserves_ranking(pre, ranking, keys[0], msgs[0], path);
        insert_refines_internal(pre, ranking, ranking, keys[0], msgs[0], path);

        assert(keys_msgs.skip(1) == keys.skip(1).zip_with(msgs.skip(1)));
//        assert(post == insert0.append_via_insert(keys.skip(1), msgs.skip(1), path1));

        lemma_append_via_insert_refines(insert0, ranking, post_ranking, keys.skip(1), msgs.skip(1), path1);
    }
}

pub proof fn lemma_children_share_key_contradiction(branch: LinkedBranch, ranking: Ranking, i: int, j: int, key: Key)
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
//        assert(i == j);
    } else if i < j <= pivots.len() {
//        assert(j > 0);
        if i < j - 1 {
            assert(Key::lt(pivots[i], pivots[j-1]));
        }
//        assert(Key::lte(pivots[i], pivots[j-1]));

        assert(branch.all_keys_below_bound(i, ranking));
//        assert(Key::lt(key, pivots[i]));
        assert(branch.all_keys_above_bound(j, ranking));
        assert(Key::lte(pivots[j-1], key));
//        assert(Key::lt(pivots[j-1], pivots[i]));
    }
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
    if path.depth > 0 {
        let r = pre.root().route(key) + 1;
        lemma_route_auto();
        assert(pre.root().valid_child_index(r));
        lemma_insert_preserves_ranking(pre.child_at_idx(r), ranking, key, msg, path.subpath());
    }
}

pub proof fn lemma_insert_preserves_wf(pre: LinkedBranch, ranking: Ranking, key: Key, msg: Message, path: Path)
    requires
        pre.valid_ranking(ranking),
        pre.keys_strictly_sorted_internal(ranking),
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
            lemma_path_target(path, ranking);
//            assert(path.target().disk_view == pre.disk_view);
//            assert(path.target().root != pre.root);
//            assert(post.disk_view.valid_address(pre.root));
            // Goal 2
//            assert(post.has_root());

            let r = pre.root().route(key) + 1;
            lemma_route_auto();
//            assert(pre.root().valid_child_index(r));
            lemma_insert_preserves_wf(pre.child_at_idx(r), ranking, key, msg, path.subpath());
            // Goal 3
//            assert(post.disk_view.wf());
        }
    }
}

pub proof fn lemma_path_target(path: Path, ranking: Ranking)
    requires
        path.valid(),
        path.branch.valid_ranking(ranking),
        path.branch.keys_strictly_sorted_internal(ranking),
    ensures
        path.target().wf(),
        path.target().valid_ranking(ranking),
        path.target().keys_strictly_sorted_internal(ranking),
        path.target().disk_view == path.branch.disk_view,
        path.i_internal(ranking).target() == path.target().i_internal(ranking),
    decreases path.depth,
{
    if path.depth > 0 {
        let r = path.branch.root().route(path.key) + 1;
        lemma_route_auto();
//        assert(path.branch.root().valid_child_index(r));
        lemma_path_target(path.subpath(), ranking);
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
        let r = path.branch.root().route(path.key) + 1;
        lemma_route_auto();
        assert(path.branch.root().valid_child_index(r));
        lemma_path_i_valid(path.subpath(), ranking);
    }
}

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
//            assert(pre.root() is Index);
            let r = pre.root().route(path.key) + 1;
            lemma_route_auto();
            assert(pre.root().valid_child_index(r));
            lemma_target_all_keys(pre.child_at_idx(r), ranking, path.subpath(), key);
            assert(pre.map_all_keys(ranking)[r].contains(key));
            lemma_set_subset_of_union_seq_of_sets(pre.map_all_keys(ranking), key);
//            assert(pre.all_keys(ranking).contains(key));
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
            assert(child.i_internal(ranking) == branch_i->children[i]);
//            assert(child.i_internal(ranking).wf());
            lemma_i_wf_implies_inv(child, ranking);
        }
        
        assert forall |i| 0 <= i < branch.root()->children.len() - 1
        implies branch.all_keys_below_bound(i, ranking) by {
            assert(branch.root().valid_child_index(i));
            let child = branch.child_at_idx(i);
            assert(branch_i.all_keys_below_bound(i));
            assert forall |key| #[trigger] child.all_keys(ranking).contains(key)
            implies Key::lt(key, branch.root()->pivots[i]) by {
                lemma_i_preserves_all_keys(child, ranking);
//                assert(branch_i->children[i].all_keys().contains(key));
//                assert(Key::lt(key, branch_i->pivots[i]));
            }
        }

        assert forall |i| 0 < i < branch.root()->children.len()
        implies branch.all_keys_above_bound(i, ranking) by {
            assert(branch.root().valid_child_index(i));
            let child = branch.child_at_idx(i);
            assert(branch_i.all_keys_above_bound(i));
            assert forall |key| child.all_keys(ranking).contains(key)
            implies #[trigger] Key::lte(branch.root()->pivots[i-1], key) by {
                lemma_i_preserves_all_keys(child, ranking);
//                assert(branch_i->children[i].all_keys().contains(key));
//                assert(Key::lte(branch_i->pivots[i-1], key));
            }
        }
    }
}

pub proof fn lemma_reachable_implies_all_keys_subset(branch: LinkedBranch, ranking: Ranking, addr: Address)
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
//            assert(union_seq_of_sets(subtree_addrs).contains(addr));
            lemma_union_seq_of_sets_contains(subtree_addrs, addr);
            let i = choose |i| 0 <= i < subtree_addrs.len() && (#[trigger] subtree_addrs[i]).contains(addr);
//            assert(branch.root().valid_child_index(i));
            lemma_reachable_implies_all_keys_subset(branch.child_at_idx(i), ranking, addr);
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
                assert(branch.root().valid_child_index(i));
                lemma_reachable_addrs_subset(branch.child_at_idx(i), ranking);
            }
        }
    }
}

pub proof fn lemma_reachable_disjoint_implies_child_reachable_disjoint(branch: LinkedBranch, ranking: Ranking, s: Set<Address>, i: int)
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
        assert(subtree_addrs[i].contains(addr));
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
//    assert(branch1.reachable_addrs_using_ranking(ranking1).contains(branch1.root));
//    assert(!except.contains(branch1.root));
    lemma_reachable_addrs_subset(branch1, ranking1);
    assert(branch1.disk_view.entries.remove_keys(except).contains_key(branch1.root));
    assert(branch1.disk_view.entries.remove_keys(except) <= branch1.disk_view.entries);
//    assert(branch1.root() == branch2.root());
    if branch1.root() is Index {
        assert forall |i: int| #[trigger] branch1.root().valid_child_index(i)
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
//        assert(branch_i is Index);
        let pivots_i = branch_i->pivots;
        let children_i = branch_i->children;
//        assert(pivots_i.len() == children_i.len() - 1);

        assert forall |i| 0 <= i < children_i.len() implies (#[trigger] children_i[i]).wf() by {
            assert(branch.root().valid_child_index(i));
            let child = branch.child_at_idx(i);
//            assert(child.wf());
//            assert(child.valid_ranking(ranking));
//            assert(child.all_keys_in_range_internal(ranking)) by {
////                assert(branch.all_keys_in_range_internal(ranking));
//            }
            i_internal_wf(child, ranking);
        }

//        assert forall |i| #![trigger children_i[i].all_keys()] #![trigger children_i[i].all_keys()] 0 <= i < children_i.len()
//        implies children_i[i].all_keys().finite() && !children_i[i].all_keys().is_empty() by {
//            assert(branch.root().valid_child_index(i));
//            let child = branch.child_at_idx(i);
////            assert(child.wf());
////            assert(child.valid_ranking(ranking));
//            lemma_i_preserves_all_keys(child, ranking);
//            lemma_all_keys_finite_and_nonempty(child, ranking);
//        }

        assert forall |i| 0 <= i < children_i.len() - 1
        implies branch_i.all_keys_below_bound(i) by {
//            assert(branch.root()->pivots.len() == children_i.len() - 1);
//            assert(branch.all_keys_in_range_internal(ranking));
            assert(branch.all_keys_below_bound(i, ranking));
            assert(branch.root().valid_child_index(i));
            let child = branch.child_at_idx(i);
//            assert(child.wf());
//            assert(child.valid_ranking(ranking));
            lemma_i_preserves_all_keys(child, ranking);
        }

        assert forall |i| 0 < i < children_i.len()
        implies branch_i.all_keys_above_bound(i) by {
//            assert(branch.all_keys_in_range_internal(ranking));
            assert(branch.all_keys_above_bound(i, ranking));
            assert(branch.root().valid_child_index(i));
            let child = branch.child_at_idx(i);
//            assert(child.wf());
//            assert(child.valid_ranking(ranking));
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
//        assert(branch.all_keys(ranking) == branch.root()->pivots.to_set() + branch.children_keys(ranking));
//        assert(branch_i.all_keys() == branch_i->pivots.to_set() + branch_i.children_keys());

        assert forall |i| 0 <= i < branch.root()->children.len()
        implies branch.map_all_keys(ranking)[i] == PivotBranchRefinement_v::map_all_keys(branch_i->children)[i] by {
            assert(branch.root().valid_child_index(i));
            lemma_i_preserves_all_keys(branch.child_at_idx(i), ranking);
        }
        assert(branch.map_all_keys(ranking) == PivotBranchRefinement_v::map_all_keys(branch_i->children));
        PivotBranchRefinement_v::lemma_children_keys_equivalence(branch_i);
//        assert(branch.children_keys(ranking) == branch_i.children_keys());
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
//        assert(0 < branch.root()->children.len());
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
        assert(branch.root().valid_child_index(i));
        let child = branch.child_at_idx(i);
//        assert(child.wf());
//        assert(child.valid_ranking(ranking));
        if child.root() is Index {
            lemma_all_keys_finite_and_nonempty(child, ranking);
        } else {
//            assert(child.root()->keys.len() > 0);
            assert(child.all_keys(ranking).contains(child.root()->keys[0]));
        }
    }
    lemma_union_seq_of_sets_finite(sets);
//    assert(sets.len() > 0);
    let key = choose |key| sets[0].contains(key);
    lemma_set_subset_of_union_seq_of_sets(sets, key);
}

} // verus!