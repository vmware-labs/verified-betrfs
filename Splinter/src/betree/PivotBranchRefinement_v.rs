// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
// use crate::betree::Domain_v::*;
use crate::betree::PivotBranch_v::*;

verus! {

impl Node {
    // Takes in a btree node and returns the buffer abstraction
    pub open spec(checked) fn i(self) -> Buffer
        recommends self.wf()
        decreases self
        when self is Index ==> forall |key| 0 <= #[trigger] self.route(key) + 1 < self.get_Index_children().len()
    {
        match self {
            Node::Leaf{keys, msgs} => {
                Buffer{map: Map::new(|key| keys.contains(key), |key| msgs[self.route(key)])}
            }
            Node::Index{pivots, children} => {
                Buffer{map: Map::new(
                    // TODO: why do we also want self.all_keys().contains(key) here?
                    // children[self.route(key) + 1].i().map.contains_key(key)
                    // ==> self.i().map.contains_key(lbl.key) by lemma_interpretation_delegation
                    // ==> self.all_keys().contains(key) by lemma_interpretation
                    // TODO: adding triggers in here causes ungraceful dump
                    |key| /*self.all_keys().contains(key) &&*/ children[self.route(key) + 1].i().map.contains_key(key),
                    |key| children[self.route(key) + 1].i().map[key]
                )}
            }
        }
    }
}

pub open spec(checked) fn get_keys_or_pivots(node: Node) -> Seq<Key>
    recommends node.wf()
{
    if node is Leaf { node.get_Leaf_keys() } else { node.get_Index_pivots() }
}

pub open spec(checked) fn le_route(node: Node, key: Key, i: int) -> bool
    recommends node.wf()
{
    0 <= i <= node.route(key)
}

pub open spec(checked) fn gt_route(node: Node, key: Key, i: int) -> bool
    recommends node.wf()
{
    let s = get_keys_or_pivots(node);
    node.route(key) < i < s.len()
}

pub proof fn lemma_route_ensures(node: Node, key: Key)
    requires node.wf()
    ensures ({
        // TODO: this causes WARNING 'if' cannot be used in patterns
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #[trigger] le_route(node, key, i) ==> Key::lte(s[i], key)
        &&& forall |i| #[trigger] gt_route(node, key, i) ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    })
{
    let s = if node is Leaf { node.get_Leaf_keys() } else { node.get_Index_pivots() };
    Key::strictly_sorted_implies_sorted(s);
    Key::largest_lte_ensures(s, key, Key::largest_lte(s, key));
}

pub proof fn lemma_route_auto()
    ensures forall |node: Node, key: Key| node.wf() ==> {
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #[trigger] le_route(node, key, i) ==> Key::lte(s[i], key)
        &&& forall |i| #[trigger] gt_route(node, key, i) ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    }
{
    assert forall |node: Node, key: Key| node.wf() implies {
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #[trigger] le_route(node, key, i) ==> Key::lte(s[i], key)
        &&& forall |i| #[trigger] gt_route(node, key, i) ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    } by {
        lemma_route_ensures(node, key);
    }
}

pub proof fn lemma_grow_preserves_wf(node: Node)
    requires
        node.wf(),
        node.all_keys().len() > 0
    ensures node.grow().wf()
{
    assume(false);
}

pub proof fn lemma_grow_preserves_all_keys(node: Node)
    requires node.wf()
    ensures node.grow().all_keys() == node.all_keys()
{
    assume(false);
}

pub proof fn lemma_interpretation_delegation(node: Node, key: Key)
    requires
        node.wf(),
        node is Index,
        node.get_Index_children()[Key::largest_lte(node.get_Index_pivots(), key) + 1].i().map.contains_key(key)
    ensures node.i().map.contains_pair(key, node.get_Index_children()[Key::largest_lte(node.get_Index_pivots(), key) + 1].i().map[key])
{
    assume(false);
}

// (tenzinhl): We think this is the `grow_refines` lemma.
pub proof fn lemma_grow_preserves_i(node: Node)
    requires
        node.wf(),
        node.all_keys().len() > 0
    ensures
        node.grow().wf(),
        node.grow().i() == node.i()
{
    assume(false);
}

pub proof fn lemma_insert_leaf_is_correct(node: Node, key: Key, msg: Message)
    requires
        node is Leaf,
        node.wf()
    ensures
        node.insert_leaf(key, msg).i() == (Buffer{map: node.i().map.insert(key, msg)}),
        node.insert_leaf(key, msg).all_keys() == node.all_keys().insert(key)
{
    assume(false);
}

pub proof fn lemma_split_leaf_preserves_wf(node: Node, split_arg: SplitArg)
    requires
        node.wf(),
        node is Leaf,
        split_arg.wf(node),
    ensures ({
        let (left_leaf, right_leaf) = node.split_leaf(split_arg);
        &&& left_leaf.wf()
        &&& right_leaf.wf()
    })
{
    assume(false);
}

pub proof fn lemma_sub_index_preserves_wf(node: Node, from: int, to: int)
    requires
        node.wf(),
        node is Index,
        0 <= from < to <= node.get_Index_children().len()
    ensures node.sub_index(from, to).wf()
{
    assume(false);
}

pub proof fn lemma_split_index_preserves_wf(node: Node, split_arg: SplitArg)
    requires
        node.wf(),
        node is Index,
        split_arg.wf(node)
    ensures ({
        let (left_index, right_index) = node.split_index(split_arg);
        &&& left_index.wf()
        &&& right_index.wf()
    })
{
    assume(false);
}

pub proof fn lemma_split_node_preserves_wf(node: Node, split_arg: SplitArg)
    requires
        node.wf(),
        split_arg.wf(node)
    ensures ({
        let (left_node, right_node) = node.split_node(split_arg);
        &&& left_node.wf()
        &&& right_node.wf()
    })
{
    assume(false);
}

pub proof fn lemma_split_leaf_interpretation(old_leaf: Node, split_arg: SplitArg)
    requires
        old_leaf.wf(),
        old_leaf is Leaf,
        split_arg.wf(old_leaf)
    ensures ({
        let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
        &&& left_leaf.wf()
        &&& right_leaf.wf()
        &&& old_leaf.i().map == Key::map_pivoted_union(left_leaf.i().map, split_arg.get_pivot(), right_leaf.i().map)
    })
{
    assume(false);
}

pub proof fn lemma_split_index_interpretation1(old_index: Node, split_arg: SplitArg)
    requires
        old_index.wf(),
        old_index is Index,
        split_arg.wf(old_index)
    ensures ({
        let (left_index, right_index) = old_index.split_index(split_arg);
        &&& left_index.wf()
        &&& right_index.wf()
        &&& old_index.i().map.submap_of(Key::map_pivoted_union(left_index.i().map, split_arg.get_pivot(), right_index.i().map))
    })
{
    assume(false);
}

pub proof fn lemma_split_index_interpretation2(old_index: Node, split_arg: SplitArg)
    requires
        old_index.wf(),
        old_index is Index,
        split_arg.wf(old_index),
        ({
            let (left_index, right_index) = old_index.split_index(split_arg);
            &&& left_index.wf()
            &&& right_index.wf()
        })
    ensures ({
        let (left_index, right_index) = old_index.split_index(split_arg);
        Key::map_pivoted_union(left_index.i().map, split_arg.get_pivot(), right_index.i().map).dom()
            <= old_index.i().map.dom()
    })
{
    assume(false);
}

pub proof fn lemma_split_index_interpretation(old_index: Node, split_arg: SplitArg)
    requires
        old_index.wf(),
        old_index is Index,
        split_arg.wf(old_index),
        ({
            let (left_index, right_index) = old_index.split_index(split_arg);
            &&& left_index.wf()
            &&& right_index.wf()
        })
    ensures ({
        let (left_index, right_index) = old_index.split_index(split_arg);
        old_index.i().map == Key::map_pivoted_union(left_index.i().map, split_arg.get_pivot(), right_index.i().map)
    })
{
    assume(false);
}

pub proof fn lemma_split_node_interpretation(old_node: Node, split_arg: SplitArg)
    requires
        old_node.wf(),
        split_arg.wf(old_node),
        ({
            let (left_node, right_node) = old_node.split_node(split_arg);
            &&& left_node.wf()
            &&& right_node.wf()
        })
    ensures ({
        let (left_node, right_node) = old_node.split_node(split_arg);
        old_node.i().map == Key::map_pivoted_union(left_node.i().map, split_arg.get_pivot(), right_node.i().map)
    })
{
    assume(false);
}

pub proof fn lemma_split_leaf_all_keys(old_leaf: Node, split_arg: SplitArg)
    requires
        old_leaf.wf(),
        old_leaf is Leaf,
        split_arg.wf(old_leaf),
        ({
            let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
            &&& left_leaf.wf()
            &&& right_leaf.wf()
        })
    ensures ({
        let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
        &&& old_leaf.all_keys() == left_leaf.all_keys() + right_leaf.all_keys()
        &&& forall |key| left_leaf.all_keys().contains(key)
            <==> (Key::lt(key, split_arg.get_pivot()) && old_leaf.all_keys().contains(key))
        &&& forall |key| right_leaf.all_keys().contains(key)
            <==> (Key::lte(split_arg.get_pivot(), key) && old_leaf.all_keys().contains(key))
    })
{
    assume(false);
}

/// (x9du): not sure if this is correct or useful
pub proof fn lemma_interpretation(node: Node)
    requires node.wf()
    ensures node.i().map.dom().subset_of(node.all_keys())
    // maybe a hassle to prove
    // forall |key| node.all_keys().contains(key) ==> node.query(lbl.key) == node.i().map[key]
{
    assume(false);
}

#[verifier::ext_equal]
pub struct QueryLabel {
    pub key: Key,
    pub msg: Message,
}

#[verifier::ext_equal]
pub struct InsertLabel {
    pub key: Key,
    pub msg: Message,
    pub path: Path,
}

#[verifier::ext_equal]
pub struct AppendLabel {
    pub keys: Seq<Key>,
    pub msgs: Seq<Message>,
}

#[verifier::ext_equal]
pub struct InternalLabel {}

// ============ ============
// ============ TRANSITION REFINEMENTS ============
// ============ ============

pub proof fn query_refines(pre: Node, lbl: QueryLabel)
    requires
        pre.wf(),
        pre.query(lbl.key) == lbl.msg
    ensures
        pre.i().query(lbl.key) == lbl.msg
    decreases pre
{
    let r = pre.route(lbl.key);
    lemma_route_auto();
    if pre is Index {
        let pivots = pre.get_Index_pivots();
        let children = pre.get_Index_children();

        assert(children[r+1].wf());
        assert(lbl.msg == children[r+1].query(lbl.key)); // subgoal 1

        query_refines(children[r+1], lbl);
        assert(children[r+1].i().query(lbl.key) == lbl.msg); // subgoal 2

        if pre.i().map.contains_key(lbl.key) {
            assert(children[r+1].i().map.contains_key(lbl.key));
            lemma_interpretation_delegation(pre, lbl.key);
            assert(pre.i().map[lbl.key] == children[r+1].i().map[lbl.key]);
        } else {
            if (children[r+1].i().map.contains_key(lbl.key)) {
                lemma_interpretation_delegation(pre, lbl.key);
                assert(pre.i().map.contains_key(lbl.key)); // contradiction
            }
            assert(!children[r+1].i().map.contains_key(lbl.key));
        }
        assert(pre.i().query(lbl.key) == children[r+1].i().query(lbl.key)); // subgoal 3
    }
}

pub proof fn lemma_insert_leaf_preserves_wf(node: Node, key: Key, msg: Message)
    requires
        node.wf(),
        node is Leaf,
    ensures
        node.insert_leaf(key, msg).wf(),
{
    Key::strictly_sorted_implies_sorted(node.get_Leaf_keys());
    Key::largest_lte_ensures(node.get_Leaf_keys(), key, Key::largest_lte(node.get_Leaf_keys(), key));
}

pub proof fn lemma_insert_preserves_wf(node: Node, key: Key, msg: Message, path: Path)
    requires
        node.wf(),
        path.valid(),
        // path.target().wf(), // maybe remove this, should come from valid
        path.node == node,
        path.key == key,
        path.target() is Leaf,
    ensures
        node.insert(key, msg, path).wf(),
    decreases node
{
    match node {
        Node::Leaf{keys, msgs} => {
            lemma_insert_leaf_preserves_wf(node, key, msg);
        },
        Node::Index{pivots, children} => {
            let post = node.insert(key, msg, path);
            assert(post is Index);
            let post_pivots = post.get_Index_pivots();
            let post_children = post.get_Index_children();

            let r = node.route(key);
            lemma_route_auto();
            assert(0 <= r+1 < children.len());
            // dont need this
            // lemma_insert_preserves_wf(children[r+1], key, msg, path.subpath());
            // assert(path.subpath().node == children[r+1]);
            // assert(children[r+1].insert(key, msg, path.subpath()).wf());

            // automatically proven, but keeping to get rid of recommendation not met
            assert(post_pivots.len() == post_children.len() - 1);

            assert(forall |i| 0 <= i < children.len() && i != r+1 ==> children[i] == post_children[i]);
            // change everything to pivots since they are the same
            assert(pivots == post_pivots);
            assert(forall |i| 0 <= i < children.len() - 1 ==> node.all_keys_below_bound(i));
            assert(forall |i| 0 < i < children.len() ==> node.all_keys_above_bound(i));

            assume(post_children[r+1].all_keys() == children[r+1].all_keys().insert(key));

            if (r+1 < children.len() - 1) {
                assert forall |k| post_children[r+1].all_keys().contains(k)
                    implies #[trigger] Key::lt(k, post_pivots[r+1])
                    by {
                        if (k == key) {
                            assert(gt_route(node, key, r+1));
                            assert(Key::lt(key, pivots[r+1]));
                        } else {
                            // assert(children[r+1].all_keys().contains(k));
                            assert(node.all_keys_below_bound(r+1));
                            // assert(Key::lt(k, pivots[r+1]));
                            // assert(Key::lt(k, post_pivots[r+1]));
                        }
                    }
                assert(post.all_keys_below_bound(r+1));
            }
            assume(false);
            if (0 <= r) {
                assert(post.all_keys_above_bound(r+1));
            }
            
            // TODO: Everything below should be super obvious. Shorten?
            

            assert forall |i| 0 <= i < post_children.len() - 1 && i != r+1
                implies post.all_keys_below_bound(i)
                by {
                    assert forall |key| children[i].all_keys().contains(key)
                        implies #[trigger] Key::lt(key, pivots[i])
                        by {
                            assert(node.all_keys_below_bound(i));
                        }
                    assert(forall |key| post_children[i].all_keys().contains(key)
                        ==> #[trigger] Key::lt(key, post_pivots[i]));
                }

            assert forall |i| 0 < i < post_children.len() && i != r+1
                implies post.all_keys_above_bound(i)
                by {
                    assert forall |key| children[i].all_keys().contains(key)
                        implies #[trigger] Key::lte(pivots[i-1], key)
                        by {
                            assert(node.all_keys_above_bound(i));
                        }
                        assert(forall |key| post_children[i].all_keys().contains(key)
                            ==> #[trigger] Key::lte(post_pivots[i-1], key))
                }
        },
    }
}

pub proof fn insert_refines(pre: Node, lbl: InsertLabel)
    requires
        pre.wf(),
        lbl.path.valid(),
        // lbl.path.target().wf(), // maybe remove this, should come from valid
        lbl.path.node == pre,
        lbl.path.key == lbl.key,
        lbl.path.target() is Leaf,
    ensures
        pre.insert(lbl.key, lbl.msg, lbl.path).wf(),
        pre.insert(lbl.key, lbl.msg, lbl.path).i() == pre.i().insert(lbl.key, lbl.msg),
{
    // TODO(tenzinhl): fixy.
    assume(false);
    lemma_insert_leaf_is_correct(lbl.path.target(), lbl.key, lbl.msg);

    // Goal 1
    assert(pre.insert(lbl.key, lbl.msg, lbl.path).wf());
    
    // Goal 2, will prove later (x9du)
    assume(pre.insert(lbl.key, lbl.msg, lbl.path).i() == pre.i().insert(lbl.key, lbl.msg));
}

// use `lemma_grow_preserves_i` instead
// pub proof fn grow_refines(pre: Node, lbl: QueryLabel)
//     requires
//         pre.wf(),
//         pre.query(lbl.key) == lbl.msg
//     ensures
//         pre.i().query(lbl.key) == lbl.msg
//     decreases pre
// {
// }


}