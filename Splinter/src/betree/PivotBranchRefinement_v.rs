// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
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
        // TODO(x9du): this when condition is kind of annoying to prove
        when self is Index ==> forall |key| 0 <= #[trigger] self.route(key) + 1 < self->children.len()
    {
        match self {
            Node::Leaf{keys, msgs} => {
                Buffer{map: Map::new(|key| keys.contains(key), |key| msgs[self.route(key)])}
            }
            Node::Index{pivots, children} => {
                Buffer{map: Map::new(
                    // TODO(x9du): why do we also want self.all_keys().contains(key) here?
                    // children[self.route(key) + 1].i().map.contains_key(key)
                    // ==> self.i().map.contains_key(lbl.key) by lemma_interpretation_delegation
                    // ==> self.all_keys().contains(key) by lemma_interpretation
                    // TODO(x9du): adding triggers in here causes ungraceful dump
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
    if node is Leaf { node->keys } else { node->pivots }
}

/// Simple bool spec fn, returns: 0 <= i < node.route(key)
/// (i.e.: if the index i is less than or equal to index key gets routed to).
pub open spec(checked) fn lte_route(node: Node, key: Key, i: int) -> bool
    recommends node.wf()
{
    0 <= i <= node.route(key)
}

/// Simple bool spec fn, returns: node.route(key) < i < pivots.len()
/// (i.e.: if index i is gt the child index key gets routed to).
pub open spec(checked) fn gt_route(node: Node, key: Key, i: int) -> bool
    recommends node.wf()
{
    let s = get_keys_or_pivots(node);
    node.route(key) < i < s.len()
}

/// Ensures clause for `Node::route()` method.
/// 
/// NOTE: if you're ever trying to derive that other pivots in the pivots
/// array are <= or > the pivot that's routed to by `route()`, be aware that
/// the trigger is somewhat unintuitive. You can't just try and compare the
/// pivots directly, instead the trigger in the ensures of this lemma are the
/// `lte_route` and `gt_route` functions.
/// 
/// (tenzinhl): We tried switching the trigger to just be `Key::lte` in the
/// past however this caused previously verifying lemmas to fail (most likely
/// due to proof instability caused by changing how things are triggered). For
/// now we'll stick with this scheme and just be aware of it.
pub proof fn lemma_route_ensures(node: Node, key: Key)
    requires node.wf()
    ensures ({
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #[trigger] lte_route(node, key, i) ==> Key::lte(s[i], key)
        &&& forall |i| #[trigger] gt_route(node, key, i) ==> Key::lt(key, s[i])
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
        &&& forall |i| #[trigger] lte_route(node, key, i) ==> Key::lte(s[i], key)
        &&& forall |i| #[trigger] gt_route(node, key, i) ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    }
{
    assert forall |node: Node, key: Key| node.wf() implies {
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #[trigger] lte_route(node, key, i) ==> Key::lte(s[i], key)
        &&& forall |i| #[trigger] gt_route(node, key, i) ==> Key::lt(key, s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    } by {
        lemma_route_ensures(node, key);
    }
}

pub proof fn lemma_key_lte_implies_route_lte(node: Node, key1: Key, key2: Key)
    requires
        node.wf(),
        Key::lte(key1, key2),
    ensures
        node.route(key1) <= node.route(key2)
{
    let s = if node is Leaf { node->keys } else { node->pivots };
    Key::strictly_sorted_implies_sorted(s);
    Key::largest_lte_ensures(s, key1, Key::largest_lte(s, key1));
    Key::largest_lte_ensures(s, key2, Key::largest_lte(s, key2));
    // Proof by contradiction
    if (Key::largest_lte(s, key1) > Key::largest_lte(s, key2)) {
        assert(Key::lt(key2, s[Key::largest_lte(s, key1)]));
        assert(Key::lt(key2, key1));
    }
}

pub proof fn lemma_index_all_keys(node: Node, key: Key)
    requires
        node is Index,
        node.all_keys().contains(key)
    ensures
        node->pivots.contains(key)
        || (exists |i| 0 <= i < node->children.len()
            && (#[trigger] node->children[i]).all_keys().contains(key))
{}

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
        node->children[Key::largest_lte(node->pivots, key) + 1].i().map.contains_key(key)
    ensures node.i().map.contains_pair(key, node->children[Key::largest_lte(node->pivots, key) + 1].i().map[key])
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

// Proves that insert() on a leaf node refines (as well as other useful and
// guaranteed properties).
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
        0 <= from < to <= node->children.len()
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

/// Prove that the `all_keys` of the left and right child after splitting an index node 
/// maintain certain wf properties.
pub proof fn lemma_split_index_all_keys(old_index: Node, split_arg: SplitArg)
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
        &&& old_index.all_keys() == left_index.all_keys() + right_index.all_keys() + set![split_arg.get_pivot()]
        &&& forall |key| left_index.all_keys().contains(key)
            <==> (Key::lt(key, split_arg.get_pivot()) && old_index.all_keys().contains(key))
        &&& forall |key| (right_index.all_keys().contains(key) || key == split_arg.get_pivot())
            <==> (Key::lte(split_arg.get_pivot(), key) && old_index.all_keys().contains(key))
    })
{
    let (left_index, right_index) = old_index.split_index(split_arg);
    let pivot = split_arg.get_pivot();
    let pivot_index = split_arg->pivot_index;
    
    assert(left_index.wf());
    assert(right_index.wf());
    
    // Assert that old index's pivots and children are related to left and right indices by concatenation.
    // It's surprising (in a good way) that Verus is able to get these facts just through assertion (probably
    // through triggering seq axioms).
    assert(old_index->pivots == left_index->pivots + seq![pivot] + right_index->pivots);
    assert(old_index->children == left_index->children + right_index->children);

    // Ensures GOAL 1
    assert(old_index.all_keys() =~~= left_index.all_keys() + right_index.all_keys() + set![pivot]);

    // ========= ========= =========
    // CURRENT WORK
    // ========= ========= =========

    assert(left_index->pivots == old_index->pivots.subrange(0, pivot_index));
    assert(left_index->children == old_index->children.subrange(0, pivot_index + 1));
    assert(right_index->pivots == old_index->pivots.subrange(pivot_index + 1, old_index->pivots.len() as int));
    assert(right_index->children == old_index->children.subrange(pivot_index + 1, old_index->children.len() as int));

    // Ensures Goal 2
    assert forall |key| left_index.all_keys().contains(key)
    implies #[trigger] Key::lt(key, pivot) && old_index.all_keys().contains(key) by {
        if (!left_index->pivots.contains(key)) {
            lemma_index_all_keys(left_index, key);
            let i = choose |i| 0 <= i < left_index->children.len()
                && (#[trigger] left_index->children[i]).all_keys().contains(key);
            assert(left_index->children[i] == old_index->children[i]);
            assert(old_index.all_keys_below_bound(i));
            assert(Key::lt(key, old_index->pivots[i]));
            if (i < left_index->children.len() - 1) {
                assert(Key::lt(old_index->pivots[i], pivot));
            } else {
                assert(old_index->pivots[i] == pivot);
            }
            assert(Key::lt(key, pivot));
        }
    }

    assert forall |key| #[trigger] Key::lt(key, pivot) && old_index.all_keys().contains(key)
    implies left_index.all_keys().contains(key) by {
        if (old_index->pivots.contains(key)) {
            let i = choose |i| 0 <= i < old_index->pivots.len() && old_index->pivots[i] == key;
            if (i >= pivot_index) { // proof by contradiction
                assert(Key::lt(pivot, key));
            }
            assert(i < pivot_index == left_index->pivots.len());
            assert(left_index->pivots.contains(key));
        } else {
            let i = choose |i| 0 <= i < old_index->children.len()
                && (#[trigger] old_index->children[i]).all_keys().contains(key);
            if (i >= pivot_index + 1) { // proof by contradiction
                assert(old_index.all_keys_above_bound(i));
                assert(Key::lte(old_index->pivots[i-1], key));
                Key::strictly_sorted_implies_sorted(old_index->pivots);
                assert(Key::lte(pivot, old_index->pivots[i-1]));
            }
            assert(i < pivot_index + 1 == left_index->children.len());
            assert(left_index->children[i].all_keys().contains(key));
        }
    }

    assert forall |key| (right_index.all_keys().contains(key) || key == pivot)
    implies #[trigger] Key::lte(pivot, key) && old_index.all_keys().contains(key) by {
        if (key == pivot) {
        } else if (right_index->pivots.contains(key)) {
            assert(Key::lt(pivot, key));
        } else {
            lemma_index_all_keys(right_index, key);
            let i = choose |i| 0 <= i < right_index->children.len()
                && (#[trigger] right_index->children[i]).all_keys().contains(key);
            assert(right_index->children[i] == old_index->children[i + pivot_index + 1]);
            assert(old_index.all_keys_above_bound(i + pivot_index + 1));
            assert(Key::lte(old_index->pivots[i + pivot_index + 1 - 1], key));
            if (0 < i) {
                assert(Key::lt(pivot, old_index->pivots[i + pivot_index]));
            } else {
                assert(old_index->pivots[i + pivot_index] == pivot);
            }
            Key::lte(pivot, key);
        }
    }

    assert forall |key| #[trigger] Key::lte(pivot, key) && old_index.all_keys().contains(key)
    implies (right_index.all_keys().contains(key) || key == pivot) by {
        if (old_index->pivots.contains(key)) {
            let i = choose |i| 0 <= i < old_index->pivots.len() && old_index->pivots[i] == key;
            if (i == pivot_index) {
                assert(key == pivot);
            } else if (i < pivot_index) { // proof by contradiction
                assert(Key::lt(key, pivot));
            } else {
                assert(pivot_index < i);
                assert(right_index->pivots.contains(key));
            }
        } else {
            let i = choose |i| 0 <= i < old_index->children.len()
                && (#[trigger] old_index->children[i]).all_keys().contains(key);
            if (i < pivot_index + 1) { // proof by contradiction
                assert(old_index.all_keys_below_bound(i));
                assert(Key::lt(key, old_index->pivots[i]));
                Key::strictly_sorted_implies_sorted(old_index->pivots);
                assert(Key::lte(old_index->pivots[i], pivot));
            }
            assert(pivot_index + 1 <= i);
            assert(right_index->children[i - (pivot_index + 1)].all_keys().contains(key));
        }
    }
}

pub proof fn lemma_split_node_all_keys(old_node: Node, split_arg: SplitArg)
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
        &&& if (old_node is Leaf) {
                &&& old_node.all_keys() == left_node.all_keys() + right_node.all_keys()
                &&& forall |key| right_node.all_keys().contains(key)
                    <==> (Key::lte(split_arg.get_pivot(), key) && old_node.all_keys().contains(key))
            } else {
                &&& old_node.all_keys() == left_node.all_keys() + right_node.all_keys() + set![split_arg.get_pivot()]
                &&& forall |key| (right_node.all_keys().contains(key) || key == split_arg.get_pivot())
                    <==> (Key::lte(split_arg.get_pivot(), key) && old_node.all_keys().contains(key))
            }
        &&& forall |key| left_node.all_keys().contains(key)
            <==> (Key::lt(key, split_arg.get_pivot()) && old_node.all_keys().contains(key))
    })
{
    if (old_node is Leaf) {
        lemma_split_leaf_all_keys(old_node, split_arg);
    } else {
        lemma_split_index_all_keys(old_node, split_arg);
    }
}

pub proof fn lemma_interpretation(node: Node)
    requires
        node.wf(),
    ensures
        node.i().map.dom().subset_of(node.all_keys()),
    decreases node,
{
    if (node is Index) {
        let children = node->children;
        lemma_route_auto();

        assert(forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).wf());

        assert forall |key| node.i().map.dom().contains(key)
        implies #[trigger] node.all_keys().contains(key) by {
            let r = node.route(key);
            assert(0 <= r + 1 < children.len());
            assert(children[r + 1].i().map.contains_key(key));
            lemma_interpretation(children[r+1]);
        }
    }
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
    pub path: Path,
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
        let pivots = pre->pivots;
        let children = pre->children;

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
    Key::strictly_sorted_implies_sorted(node->keys);
    Key::largest_lte_ensures(node->keys, key, Key::largest_lte(node->keys, key));
}

pub proof fn lemma_insert_inserts_to_all_keys(node: Node, key: Key, msg: Message, path: Path)
    requires
        node.wf(),
        path.valid(),
        path.node == node,
        path.key == key,
        path.target() is Leaf,
    ensures
        node.insert(key, msg, path).all_keys() == node.all_keys().insert(key)
    decreases node,
{
    match node {
        Node::Leaf{keys, msgs} => {
            lemma_insert_leaf_is_correct(node, key, msg);
        },
        Node::Index{pivots, children} => {
            let post = node.insert(key, msg, path);
            let r = node.route(key);
            lemma_route_auto();
            assert(0 <= r + 1 < children.len());

            // Recursively call the lemma on the changed child: the child we inserted into.
            lemma_insert_inserts_to_all_keys(children[r+1], key, msg, path.subpath());
            // This implies that the changed child's all_keys is the same as before except with the
            // new key inserted.
            assert(post->children[r+1].all_keys() == children[r+1].all_keys().insert(key));

            // Now let's just assert that each of the post state's children all_keys
            // are the same as the pre (besides the changed child).
            assert(post->children.len() == children.len());
            assert(forall |i| 0 <= i < post->children.len() && i != (r+1)
                ==> post->children[i] =~~= #[trigger] children[i]);

            // GOAL
            assert(node.insert(key, msg, path).all_keys() =~~= node.all_keys().insert(key));
        },
    }
}

pub proof fn lemma_insert_preserves_wf(node: Node, key: Key, msg: Message, path: Path)
    requires
        node.wf(),
        path.valid(),
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
            assert(post is Index); // For recommends

            let r = node.route(key);
            lemma_route_auto();
            assert(0 <= r+1 < children.len()); // For recommends

            lemma_insert_preserves_wf(children[r+1], key, msg, path.subpath());

            // For recommends
            assert(pivots.len() == post->pivots.len());
            assert(children.len() == post->children.len());

            // Subgoal 1, needed for asserting that unchanged keys in children[r+1].all_keys() still satisfy bounds
            lemma_insert_inserts_to_all_keys(children[r+1], key, msg, path.subpath());
            assert(post->children[r+1].all_keys() == children[r+1].all_keys().insert(key));

            // Subgoal 2: the only changed child, r+1, satisfies all keys bounds

            if (r+1 < children.len() - 1) {
                assert(node.all_keys_below_bound(r+1));
                assert(gt_route(node, key, r+1));
                assert(Key::lt(key, pivots[r+1]));
                assert(post.all_keys_below_bound(r+1));
            }

            if (0 <= r) {
                assert(node.all_keys_above_bound(r+1));
                assert(lte_route(node, key, r));
                assert(Key::lte(pivots[r], key));
                assert(post.all_keys_above_bound(r+1));
            }

            // Subgoal 3: the unchanged children still satisfy all keys bounds

            assert forall |i| 0 <= i < post->children.len() - 1 && i != r+1
                implies post.all_keys_below_bound(i) by
            {
                assert(node.all_keys_below_bound(i));
            }

            assert forall |i| 0 < i < post->children.len() && i != r+1
                implies post.all_keys_above_bound(i) by
            {
                assert(node.all_keys_above_bound(i));
            }
        },
    }
}

pub proof fn lemma_path_target_is_wf(path: Path)
    requires
        path.valid(),
    ensures
        path.target().wf(),
    decreases
        path.depth
{
    if path.depth > 0 {
        lemma_path_target_is_wf(path.subpath());
    }
}

// Proves that inserting into a node and then refining is the same
// as refining then inserting into the refinement.
pub proof fn insert_refines(pre: Node, lbl: InsertLabel)
    requires
        pre.wf(),
        lbl.path.valid(),
        lbl.path.node == pre,
        lbl.path.key == lbl.key,
        lbl.path.target() is Leaf,
    ensures
        pre.insert(lbl.key, lbl.msg, lbl.path).wf(),
        pre.insert(lbl.key, lbl.msg, lbl.path).i() == pre.i().insert(lbl.key, lbl.msg),
    decreases
        pre
{
    lemma_route_auto();

    lemma_path_target_is_wf(lbl.path);
    assert(lbl.path.target().wf());
    lemma_insert_leaf_is_correct(lbl.path.target(), lbl.key, lbl.msg);

    // Goal 1 - After insertion the node is still well formed.
    lemma_insert_preserves_wf(pre, lbl.key, lbl.msg, lbl.path);
    
    // Goal 2 - Inserting into node then abstracting to Map,
    // is the same as abstracting to map, then inserting to map.

    match pre {
        Node::Leaf{keys, msgs} => {}, // Given by lemma_insert_leaf_is_correct!
        Node::Index{pivots, children} => {
            let post = pre.insert(lbl.key, lbl.msg, lbl.path);
            let r = pre.route(lbl.key);
            
            // Suppress recommendation
            assert(0 <= r + 1 < children.len());
            assert(post.wf());
            assert(post->children.len() == children.len()); 
            assert(forall |i| 0 <= i < post->children.len() ==> (#[trigger] post->children[i]).wf());
            assert(forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).wf());

            // TODO(x9du): This assert forall is known to be flaky (can fail as you modify/add other lemmas).
            // Required to trigger the route ensures for each of the children.
            assert forall |i, key| 0 <= i < children.len() && children[i] is Index
            implies 0 <= #[trigger] children[i].route(key) + 1 < children[i]->children.len() by {
                lemma_route_ensures(children[i], key);
            }

            // Assert that other children don't change
            assert(forall |i| #![auto] 0 <= i < children.len() && i != (r+1) ==> post->children[i].i() == children[i].i());

            // Assert that the changed child has original keys plus the new key-value pair.
            let child_label = InsertLabel{ key: lbl.key, msg: lbl.msg, path: lbl.path.subpath() };
            insert_refines(children[r+1], child_label);
            assert(post->children[r+1].i() == children[r+1].i().insert(lbl.key, lbl.msg));

            assert(post.i() =~~= pre.i().insert(lbl.key, lbl.msg));
        },
    }
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

/// Proves that if the first and last key in a sorted seq of keys are path
/// equiv (i.e.: would map to the same node), then *all* keys in seq must
/// be path equiv.
pub proof fn lemma_append_keys_are_path_equiv(keys: Seq<Key>, path: Path)
    requires
        path.valid(),
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        path.key == keys[0],
        path.path_equiv(keys.last())
    ensures
        forall |key| keys.contains(key) ==> path.path_equiv(key)
    decreases path.depth
{
    if 0 < path.depth {
        lemma_append_keys_are_path_equiv(keys, path.subpath());
    }

    lemma_route_auto();
    Key::strictly_sorted_implies_sorted(keys);

    assert forall |key| keys.contains(key) implies path.path_equiv(key) by {
        let node = path.node;
        lemma_key_lte_implies_route_lte(node, keys[0], key);
        lemma_key_lte_implies_route_lte(node, key, keys.last());
        assert(path.node.route(path.key) == path.node.route(key));
    }
}

pub proof fn lemma_to_set_distributes_over_plus<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_set() == a.to_set().union(b.to_set())
{
    assert forall |x| a.to_set().union(b.to_set()).contains(x)
    implies #[trigger] (a + b).to_set().contains(x) by {
        assert(a.to_set().contains(x) || b.to_set().contains(x));
        if (a.to_set().contains(x)) {
            assert(a.contains(x));
            let i = a.index_of(x);
            assert((a + b)[i] == x);
        } else {
            assert(b.to_set().contains(x));
            assert(b.contains(x));
            let i = b.index_of(x);
            assert((a + b)[a.len() + i] == x);
        }
        assert((a + b).contains(x));
    }
    assert((a + b).to_set() == a.to_set().union(b.to_set()));
}

pub proof fn lemma_append_appends_to_all_keys(pre: Node, new_keys: Seq<Key>, new_msgs: Seq<Message>, path: Path)
    requires
        pre.wf(),
        path.valid(),
        path.node == pre,
        new_keys.len() > 0,
        new_keys.len() == new_msgs.len(),
        Key::is_strictly_sorted(new_keys),
        path.target() is Leaf,
        Key::lt(path.target()->keys.last(), new_keys[0]),
        path.key == new_keys[0],
        path.path_equiv(new_keys.last())
    ensures
        pre.append(new_keys, new_msgs, path).all_keys() == pre.all_keys().union(new_keys.to_set())
    decreases pre,
{
    lemma_path_target_is_wf(path);
    assert(path.target().wf());
    assert(path.target()->keys.len() > 0);
    let post = pre.append(new_keys, new_msgs, path);

    match pre {
        Node::Leaf{keys, msgs} => {
            lemma_to_set_distributes_over_plus(keys, new_keys);
        },
        Node::Index{pivots, children} => {
            let r = pre.route(new_keys[0]);
            lemma_append_keys_are_path_equiv(new_keys, path);
            lemma_route_auto();
            assert(0 <= r + 1 < children.len());
            assert(children.len() == post->children.len());

            // Recursively call the lemma on the changed child: the child we inserted into.
            lemma_append_appends_to_all_keys(children[r+1], new_keys, new_msgs, path.subpath());
            // This implies that the changed child's all_keys is the same as before except with the
            // new key inserted.
            assert(post->children[r+1].all_keys() == children[r+1].all_keys().union(new_keys.to_set()));

            // Now let's just assert that each of the post state's children all_keys
            // are the same as the pre (besides the changed child).
            assert(post->children.len() == children.len());
            assert(forall |i| 0 <= i < post->children.len() && i != (r+1)
                ==> post->children[i] =~~= #[trigger] children[i]);

            // GOAL
            assert(post.all_keys() =~~= pre.all_keys().union(new_keys.to_set()));
        },
    }
}

pub proof fn lemma_append_preserves_wf(pre: Node, keys: Seq<Key>, msgs: Seq<Message>, path: Path)
    requires
        pre.wf(),
        path.valid(),
        path.node == pre,
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target() is Leaf,
        Key::lt(path.target()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last())
    ensures
        pre.append(keys, msgs, path).wf(),
    decreases pre
{
    lemma_path_target_is_wf(path);
    assert(path.target().wf());
    assert(path.target()->keys.len() > 0);
    let post = pre.append(keys, msgs, path);

    if pre is Leaf {
        assert(post is Leaf);
        Key::strictly_sorted_implies_sorted(pre->keys);
        Key::strictly_sorted_implies_sorted(keys);
        assert forall |i: int, j: int| 0 <= i < pre->keys.len() && 0 <= j < keys.len()
        implies Key::lt(pre->keys[i], keys[j]) by {
            assert(Key::lte(pre->keys[i], pre->keys.last()));
            assert(Key::lte(keys[0], keys[j]));
        }
    } else {
        let pivots = pre->pivots;
        let children = pre->children;
        assert(post is Index); // For recommends

        let r = pre.route(path.key);
        lemma_append_keys_are_path_equiv(keys, path);
        lemma_route_auto();
        assert(0 <= r+1 < children.len()); // For recommends

        lemma_append_preserves_wf(children[r+1], keys, msgs, path.subpath());

        // For recommends
        assert(pivots.len() == post->pivots.len());
        assert(children.len() == post->children.len());

        lemma_append_appends_to_all_keys(children[r+1], keys, msgs, path.subpath());

        // Subgoal 1
        assert(!post->children[r+1].all_keys().is_empty()) by {
            assert(post->children[r+1].all_keys().contains(keys[0]));
        }

        // Subgoal 2, needed for asserting that unchanged keys in children[r+1].all_keys() still satisfy bounds
        assert(post->children[r+1].all_keys() =~~= children[r+1].all_keys().union(keys.to_set()));

        // Subgoal 3: the only changed child, r+1, satisfies all keys bounds

        if (r+1 < children.len() - 1) {
            assert(pre.all_keys_below_bound(r+1));

            assert forall |key| keys.contains(key)
            implies Key::lt(key, pivots[r+1]) by {
                assert(gt_route(pre, key, r+1));
            }

            assert(post.all_keys_below_bound(r+1));
        }

        if (0 <= r) {
            assert(pre.all_keys_above_bound(r+1));

            assert forall |key| #[trigger] keys.contains(key)
            implies Key::lte(pivots[r], key) by {
                assert(lte_route(pre, key, r));
            }

            assert(post.all_keys_above_bound(r+1));
        }

        // Subgoal 4: the unchanged children still satisfy all keys bounds

        assert forall |i| 0 <= i < post->children.len() - 1 && i != r+1
        implies post.all_keys_below_bound(i) by
        {
            assert(pre.all_keys_below_bound(i));
        }

        assert forall |i| 0 < i < post->children.len() && i != r+1
        implies post.all_keys_above_bound(i) by
        {
            assert(pre.all_keys_above_bound(i));
        }
    }
}

pub proof fn append_refines(pre: Node, lbl: AppendLabel)
    requires
        pre.wf(),
        lbl.path.valid(),
        lbl.path.node == pre,
        lbl.keys.len() > 0,
        lbl.keys.len() == lbl.msgs.len(),
        Key::is_strictly_sorted(lbl.keys),
        lbl.path.target() is Leaf,
        Key::lt(lbl.path.target()->keys.last(), lbl.keys[0]),
        lbl.path.key == lbl.keys[0],
        lbl.path.path_equiv(lbl.keys.last())
    ensures
        pre.append(lbl.keys, lbl.msgs, lbl.path).wf(),
        pre.append(lbl.keys, lbl.msgs, lbl.path).i() == (
            Buffer{map: pre.i().map.union_prefer_right(Map::new(
                |key| lbl.keys.contains(key),
                |key| lbl.msgs[(Node::Leaf{ keys: lbl.keys, msgs: lbl.msgs }).route(key)]))}),
    decreases
        pre,
{
    lemma_route_auto();
    lemma_append_keys_are_path_equiv(lbl.keys, lbl.path);

    // Goal 1 - WF is preserved
    lemma_append_preserves_wf(pre, lbl.keys, lbl.msgs, lbl.path);

    lemma_path_target_is_wf(lbl.path);
    assert(lbl.path.target().wf());
    assert(lbl.path.target()->keys.len() > 0);

    let post = pre.append(lbl.keys, lbl.msgs, lbl.path);
    assert(post.wf());
    let append_leaf = Node::Leaf{ keys: lbl.keys, msgs: lbl.msgs };
    let append_map = Map::new(
        |key| lbl.keys.contains(key),
        |key| lbl.msgs[append_leaf.route(key)]);
    let pre_i_then_append = Buffer{map: pre.i().map.union_prefer_right(append_map)};

    // Goal 2 - Appending to node then refine is same as refine then append.
    match pre {
        Node::Leaf{keys, msgs} => {
            assert(pre == lbl.path.target());
            assert(lbl.path.depth == 0);
            let post_target = Node::Leaf{ keys: keys + lbl.keys, msgs: msgs + lbl.msgs };
            assert(post == lbl.path.substitute(post_target));
            assert(post == post_target);

            lemma_to_set_distributes_over_plus(keys, lbl.keys);
            // GOAL 1
            assert(post.i().map.dom() =~~= pre_i_then_append.map.dom());

            // GOAL 2
            assert forall |k| post.i().map.contains_key(k)
            implies #[trigger] post.i().map[k] == #[trigger] pre_i_then_append.map[k] by {
                if (keys.contains(k)) {
                    let i = keys.index_of(k);
                    assert(post_target->keys[i] == k);
                    // Proof by contradiction
                    if (lbl.keys.contains(k)) {
                        let j = lbl.keys.index_of(k);
                        assert(post_target->keys[keys.len() + j] == k);
                        assert(i < keys.len() + j);
                        assert(Key::lt(post_target->keys[i], post_target->keys[keys.len() + j]));
                    }
                    assert(!lbl.keys.contains(k));
                    assert(!append_map.contains_key(k));
                    assert(pre.i().map.contains_key(k));

                    assert(post_target->keys[pre.route(k)] == k);
                    assert(post_target->keys[post_target.route(k)] == k);
                    // Proof by contradiction
                    if (pre.route(k) < post_target.route(k)) {
                        assert(Key::lt(post_target->keys[pre.route(k)], post_target->keys[post_target.route(k)]));
                    }
                    if (pre.route(k) > post_target.route(k)) {
                        assert(Key::lt(post_target->keys[post_target.route(k)], post_target->keys[pre.route(k)]));
                    }
                    assert(pre.route(k) == post_target.route(k));
                } else {
                    assert(lbl.keys.contains(k));
                    assert(append_map.contains_key(k));
                    assert(post_target->keys.contains(k));

                    assert(post_target->keys[post_target.route(k)] == k);
                    assert(post_target->keys[keys.len() + append_leaf.route(k)] == k);
                    // Proof by contradiction
                    if (post_target.route(k) < keys.len() + append_leaf.route(k)) {
                        assert(Key::lt(
                            post_target->keys[post_target.route(k)],
                            post_target->keys[keys.len() + append_leaf.route(k)]));
                    }
                    if (post_target.route(k) > keys.len() + append_leaf.route(k)) {
                        assert(Key::lt(
                            post_target->keys[keys.len() + append_leaf.route(k)],
                            post_target->keys[post_target.route(k)]));
                    }
                    assert(post_target.route(k) == keys.len() + append_leaf.route(k));
                }
            }
            
            assert(post.i().map =~~= pre_i_then_append.map);
            assert(post.i() =~~= pre_i_then_append);
        },
        Node::Index{pivots, children} => {
            let r = pre.route(lbl.keys[0]);

            // GOAL 1 START (prove by showing that all children are the same except children along
            // modified path).

            // Start copying insert_refines proof that unmodified children
            // are unmodified.

            // Trigger stuff to get that the post->children are wf() and more.
            assert(0 <= r + 1 < children.len());
            assert(post.wf());
            assert(post->children.len() == children.len()); 
            assert(forall |i| 0 <= i < post->children.len() ==> (#[trigger] post->children[i]).wf());
            assert(forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).wf());

            // TODO(x9du): flaky assert forall by
            // Required to trigger the route ensures for each of the children.
            assert forall |i, key| 0 <= i < children.len() && children[i] is Index
            implies 0 <= #[trigger] children[i].route(key) + 1 < children[i]->children.len() by {
                lemma_route_ensures(children[i], key);
            }
    
            // Assert that the i() of all unchanged children are the same!
            assert(forall |i| #![auto] 0 <= i < children.len() && i != (r+1) ==> post->children[i].i() == children[i].i());

            // Prove that the changed child still satisfies the append_refines.
            let child_label = AppendLabel{ keys: lbl.keys, msgs: lbl.msgs, path: lbl.path.subpath() };
            append_refines(children[r+1], child_label);

            // GOAL 1
            assert(post.i().map.dom() =~~= pre_i_then_append.map.dom());

            // GOAL 2
            assert(forall |k| post.i().map.contains_key(k) ==>
                (#[trigger] post.i().map[k]) =~~= (#[trigger] pre_i_then_append.map[k]));
            assert(post.i().map =~~= pre_i_then_append.map);

            // OVERALL GOAL
            assert(post.i() =~~= pre_i_then_append);
        },
    }
}

pub proof fn lemma_subset_finite<A>(a: Set<A>, b: Set<A>)
    requires
        a.finite(),
        b <= a,
    ensures
        b.finite(),
{
    assert(b == a.intersect(b));
}

pub proof fn lemma_split_child_of_index_preserves_wf(pre: Node, split_arg: SplitArg)
requires
    pre.can_split_child_of_index(split_arg),
ensures
    pre.split_child_of_index(split_arg).wf(),
{
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split_child_of_index(split_arg);

    // Suppress recommends
    assert(pre is Index);
    assert(post is Index);
    lemma_route_auto();
    lemma_route_ensures(pre, pivot);
    assert(0 <= r + 1 < children.len());

    // Suppress recommends
    assert(split_arg.wf(children[r+1]));
    assert(post->pivots.len() == pivots.len() + 1);
    assert(0 <= r + 2 <= post->pivots.len());
    assert(post->pivots[r+1] == pivot);

    lemma_split_node_preserves_wf(children[r+1], split_arg);

    assert(post =~~= pre.split_child_of_index(split_arg));
    assert(post->pivots.len() == post->children.len() - 1);
    assert(post->pivots =~~= pivots.insert(r+1, pivot));

    // Assert pivots to the left of where new pivot was inserted are still sorted.
    assert(Key::is_strictly_sorted(post->pivots.subrange(0, r+1)));

    // Assert pivots to the right of where new pivot was inserted are still sorted.
    assert(Key::is_strictly_sorted(post->pivots.subrange(r+2, post->pivots.len() as int)));

    // post->pivots[r] < pivot < post->pivots[r+2] (when r, r+2 exist)
    // TODO(x9du): might be some duplication of this proof in split_preserves_wf
    if (r >= 0) {
        assert(Key::lt(post->pivots[r], post->pivots[r+1])) by {
            assert(pivots[r] == post->pivots[r]);
            assert(post->pivots[r+1] == pivot);

            if (children[r+1] is Leaf) {
                // If the split child is Leaf, then the targeted key that's
                // being split can NOT be one of the end indices of the child's keys,
                // because otherwise one of the partitions would be empty, and that
                // contradicts the split_arg wf() precondition.

                // The index that child will be split on is index of where split_arg.pivot
                // would be inserted into child's keys.
                let c_keys = children[r+1]->keys;
                let split_index = Key::largest_lt(c_keys, pivot) + 1;

                assert(0 < split_index < c_keys.len());

                // By definition of Key::largest_lt, we know that:
                assert(Key::lt(c_keys[0], pivot));

                assert(pre.all_keys_above_bound(r+1));
                assert(children[r+1].all_keys().contains(c_keys[0]));
                // Needs this weird r+1-1 in order to trigger the postcondition of
                // all_keys_above_bound (because quantified `i` appears as `i-1` in trigger).
                assert(Key::lte(pivots[r+1-1], c_keys[0]));

                // And then combined with transitivity we should get:
                assert(Key::lt(pivots[r], pivot));
            } else {
                assert(split_arg is SplitIndex);
                assert(children[r+1] is Index);
                let pivot_index = split_arg->pivot_index;
                let key = children[r+1]->children[pivot_index].all_keys().choose();
                assert(Key::lt(key, pivot)) by {
                    assert(children[r+1].all_keys_below_bound(pivot_index));
                }
                assert(children[r+1].all_keys().contains(key));
                assert(Key::lte(pivots[r+1-1], key)) by {
                    assert(pre.all_keys_above_bound(r+1));
                }
                assert(Key::lt(pivots[r], pivot));
            }
        }
    }

    if (r+2 < post->pivots.len()) {
        assert(Key::lt(post->pivots[r+1], post->pivots[r+2])) by {
            assert(post->pivots[r+2] == pivots[r+1]);
            assert(post->pivots[r+1] == pivot);

            assert(0 <= r+1 < pivots.len()); // Suppress recommends.

            assert(pre.all_keys_below_bound(r+1));

            if (children[r+1] is Leaf) {
                let c_keys = children[r+1]->keys;
                let split_index = Key::largest_lt(c_keys, pivot) + 1;

                assert(0 < split_index < c_keys.len());

                assert(children[r+1].wf()); // suppress recommends
                Key::strictly_sorted_implies_sorted(c_keys); // suppress recommends
                Key::largest_lt_ensures(c_keys, pivot, Key::largest_lt(c_keys, pivot));
                assert(Key::lte(pivot, c_keys.last()));

                assert(children[r+1].all_keys().contains(c_keys.last()));
                // by all_keys_below_bound
                assert(Key::lt(c_keys.last(), pivots[r+1]));

                assert(Key::lt(pivot, pivots[r+1]));
            } else {
                assert(children[r+1].all_keys().contains(pivot));
                // by all_keys_below_bound
                assert(Key::lt(pivot, pivots[r+1]));
            }
        }
    }

    // Stitch the two ends together.
    assert forall |i, j| 0 <= i < j < post->pivots.len()
        implies Key::lt(post->pivots[i], post->pivots[j]) by
    {
        if (j < r+1) {
            // Untouched section to the left of insert is still sorted.
            assert(Key::lt(post->pivots[i], post->pivots[j]));
        } else if (i > r+1) {
            // Untouched section to the right of insert is still sorted.
            assert(Key::lt(post->pivots[i], post->pivots[j]));
        } else {
            if (i < r) {
                assert(Key::lt(post->pivots[i], post->pivots[r]));
            }
            if (r+2 < j) {
                assert(Key::lt(post->pivots[r+2], post->pivots[j]));
            }
            assert(Key::lt(post->pivots[i], post->pivots[j]));
        }
    }

    // Goal 1
    assert(Key::is_strictly_sorted(post->pivots));

    assert(post->children.len() == children.len() + 1);

    assert(forall |i| 0 <= i < r+1 ==> #[trigger] children[i] == post->children[i]);
    assert(forall |i| 0 <= i < r+1 ==> #[trigger] pivots[i] == post->pivots[i]);
    assert forall |i| 0 <= i < r+1 implies post.all_keys_below_bound(i) by {
        assert(pre.all_keys_below_bound(i));
    }
    assert forall |i| 0 < i < r+1 implies post.all_keys_above_bound(i) by {
        assert(pre.all_keys_above_bound(i));
    }

    assert(forall |i: int| r+2 < i < post->children.len() ==> children[i-1] == post->children[i]);
    assert(forall |i: int| r+2 < i < post->children.len() - 1 ==> pivots[i-1] == post->pivots[i]);
    assert forall |i: int| r+2 < i < post->children.len() - 1
    implies post.all_keys_below_bound(i) by {
        assert(pre.all_keys_below_bound(i - 1));
    }
    assert forall |i: int| r+2 < i < post->children.len()
    implies post.all_keys_above_bound(i) by {
        assert(pre.all_keys_above_bound(i - 1));
        assert(post->pivots[i-1] == pre->pivots[i-1-1]);
    }

    let (left_node, right_node) = children[r+1].split_node(split_arg);
    assert(left_node == post->children[r+1]);
    assert(right_node == post->children[r+2]);
    lemma_split_node_all_keys(children[r+1], split_arg);

    // Goal 2
    lemma_subset_finite(children[r+1].all_keys(), post->children[r+1].all_keys());
    lemma_subset_finite(children[r+1].all_keys(), post->children[r+2].all_keys());

    // Goal 3
    if (children[r+1] is Leaf) {
        assert(post->children[r+1] is Leaf);
        assert(post->children[r+2] is Leaf);
        assert(!post->children[r+1].all_keys().is_empty()) by {
            assert(post->children[r+1]->keys.len() > 0);
            assert(post->children[r+1]->keys.to_set().contains(post->children[r+1]->keys[0]));
        }
        assert(!post->children[r+2].all_keys().is_empty()) by {
            assert(post->children[r+2]->keys.len() > 0);
            assert(post->children[r+2]->keys.to_set().contains(post->children[r+2]->keys[0]));
        }
    } else {
        assert(post->children[r+1] is Index);
        assert(post->children[r+2] is Index);
        assert(split_arg is SplitIndex);
        let pivot_index = split_arg->pivot_index;
        assert(!post->children[r+1].all_keys().is_empty()) by {
            assert(post->children[r+1]->children[0] == children[r+1]->children[0]);
            assert(post->children[r+1].all_keys().contains(children[r+1]->children[0].all_keys().choose()));
        }
        assert(!post->children[r+2].all_keys().is_empty()) by {
            assert(post->children[r+2]->children[0] == children[r+1]->children[pivot_index + 1]);
            assert(post->children[r+2].all_keys().contains(children[r+1]->children[pivot_index + 1].all_keys().choose()));
        }
    }

    assert(post.all_keys_below_bound(r+1));
    assert(post.all_keys_above_bound(r+2));

    if (r+2 < post->children.len() - 1) {
        assert forall |key| post->children[r+2].all_keys().contains(key)
        implies #[trigger] Key::lt(key, post->pivots[r+2]) by {
            assert(pre->children[r+1].all_keys().contains(key));
            assert(pre.all_keys_below_bound(r+1));
            assert(Key::lt(key, pre->pivots[r+1]));
        }
        assert(post.all_keys_below_bound(r+2));
    }

    if (0 < r+1) {
        assert forall |key| post->children[r+1].all_keys().contains(key)
        implies #[trigger] Key::lte(post->pivots[r+1-1], key) by {
            assert(pre->children[r+1].all_keys().contains(key));
            assert(pre.all_keys_above_bound(r+1));
            assert(Key::lte(pre->pivots[r+1-1], key));
        }
        assert(post.all_keys_above_bound(r+1));
    }

    // Goal 4
    assert(forall |i| 0 <= i < post->children.len() - 1 ==> post.all_keys_below_bound(i));
    // Goal 5
    assert(forall |i| 0 < i < post->children.len() ==> post.all_keys_above_bound(i));
}

pub proof fn lemma_split_child_of_index_all_keys(pre: Node, split_arg: SplitArg)
requires
    pre.can_split_child_of_index(split_arg),
ensures
    if split_arg is SplitLeaf {
        pre.split_child_of_index(split_arg).all_keys() == pre.all_keys().insert(split_arg.get_pivot())
    } else {
        pre.split_child_of_index(split_arg).all_keys() == pre.all_keys()
    },
{
    // TODO(x9du): clean this proof up
    assert(pre is Index);
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split_child_of_index(split_arg);
    assert(post is Index);

    // Suppress recommends
    lemma_route_auto();
    lemma_route_ensures(pre, pivot);
    assert(0 <= r + 1 < children.len());
    assert(split_arg.wf(children[r+1]));
    assert(post->pivots.len() == pivots.len() + 1);
    assert(post->children.len() == children.len() + 1);
    assert(0 <= r + 2 <= post->pivots.len());
    assert(post->pivots[r+1] == pivot);

    lemma_split_node_preserves_wf(children[r+1], split_arg);
    lemma_split_node_all_keys(children[r+1], split_arg);

    assert(forall |i| 0 <= i < r+1 ==> #[trigger] children[i] == post->children[i]);
    assert(forall |i: int| r+2 < i < post->children.len() ==> children[i-1] == post->children[i]);

    assert(post->pivots == pivots.insert(r+1, pivot));

    assert forall |key| pre.all_keys().contains(key) implies post.all_keys().contains(key) by {
        if (pivots.contains(key)) {
            let i = pivots.index_of(key);
            if (i < r+1) {
                assert(pivots.insert(r+1, pivot)[i] == key);
            } else {
                assert(pivots.insert(r+1, pivot)[i+1] == key);
            }
            assert(pivots.insert(r+1, pivot).contains(key));
            assert(post->pivots.contains(key));
            assert(post.all_keys().contains(key));
        } else {
            assert(!pivots.to_set().contains(key));
            let i = choose |i| 0 <= i < children.len() 
                && (#[trigger] children[i]).all_keys().contains(key);
            if (i < r+1) {
                assert(post->children[i].all_keys().contains(key));
            } else if (i == r+1) {
                assert({
                    ||| post->children[r+1].all_keys().contains(key)
                    ||| post->children[r+2].all_keys().contains(key)
                    ||| key == pivot
                });
            } else {
                assert(post->children[i+1].all_keys().contains(key));
            }
            assert(post.all_keys().contains(key));
        }
    }

    if (split_arg is SplitLeaf) {
        assert(post.all_keys() == pre.all_keys().insert(split_arg.get_pivot()));
    } else {
        let pivot_index = split_arg->pivot_index;
        assert(0 <= pivot_index < children[r+1]->pivots.len());
        /*assert(old_index->pivots == left_index->pivots + seq![pivot] + right_index->pivots);
        assert(old_index->children == left_index->children + right_index->children); */
        assert forall |key| post.all_keys().contains(key) implies pre.all_keys().contains(key) by {
            if (post->pivots.contains(key)) {
                if (key == pivot) {
                    assert(pivot == children[r+1]->pivots[pivot_index]);
                    assert(children[r+1]->pivots.to_set().contains(key));
                } else {
                    assert(pivots.contains(key));
                }
            } else {
                assert(pre.all_keys().contains(key));
            }
            assert(pre.all_keys().contains(key));
        }

        assert(post.all_keys() == pre.all_keys());
    }
}

pub proof fn lemma_split_all_keys(pre: Node, path: Path, split_arg: SplitArg)
requires
    pre.wf(),
    path.valid(),
    path.node == pre,
    path.key == split_arg.get_pivot(),
    path.target().can_split_child_of_index(split_arg),
ensures
    if split_arg is SplitLeaf {
        pre.split(path, split_arg).all_keys() == pre.all_keys().insert(split_arg.get_pivot())
    } else {
        pre.split(path, split_arg).all_keys() == pre.all_keys()
    },
decreases
    path.depth,
{
    // TODO(x9du): can use this in lemma_split_child_of_index_preserves_wf?
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split(path, split_arg);

    // Suppress recommends
    assert(pre is Index);
    assert(post is Index);
    lemma_route_auto();
    lemma_route_ensures(pre, pivot);
    assert(0 <= r + 1 < children.len());

    if (path.depth == 0) {
        lemma_split_child_of_index_all_keys(pre, split_arg);
    } else {
        lemma_split_all_keys(children[r+1], path.subpath(), split_arg);
        assert(post->pivots == pivots);
        assert(post->pivots.to_set() == pivots.to_set());
        assert(post->children.len() == children.len());
        if split_arg is SplitLeaf {
            assert(forall |i| 0 <= i < post->children.len() && i != r+1 ==> post->children[i].all_keys() == (#[trigger] children[i]).all_keys());
            assert(post->children[r+1].all_keys() == children[r+1].all_keys().insert(split_arg.get_pivot()));
            assert(post.all_keys() == pre.all_keys().insert(split_arg.get_pivot()));
        } else {
            assert(forall |i| 0 <= i < post->children.len() ==> post->children[i].all_keys() == (#[trigger] children[i]).all_keys());
            assert(post.all_keys() == pre.all_keys());
        }
    }
}

pub proof fn lemma_target_all_keys(pre: Node, path: Path, key: Key)
    requires
        pre.wf(),
        path.valid(),
        path.node == pre,
    ensures
        path.target().all_keys().contains(key) ==> pre.all_keys().contains(key),
    decreases
        path.depth,
{
    if (path.depth == 0) {
        assert(path.target() == pre);
    } else {
        assert(pre is Index);
        let r = pre.route(path.key);
        lemma_route_auto();
        lemma_target_all_keys(pre->children[r+1], path.subpath(), key);
    }
}

pub proof fn lemma_split_preserves_wf(pre: Node, path: Path, split_arg: SplitArg)
requires
    pre.wf(),
    path.valid(),
    path.node == pre,
    path.key == split_arg.get_pivot(),
    // Asserts `split_arg.wf()`
    path.target().can_split_child_of_index(split_arg),
ensures
    pre.split(path, split_arg).wf(),
decreases
    path.depth
{
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split(path, split_arg);

    // Suppress recommends
    assert(pre is Index);
    assert(post is Index);
    lemma_route_auto();
    lemma_route_ensures(pre, pivot);
    assert(0 <= r + 1 < children.len());

    if (path.depth == 0) {
        lemma_split_child_of_index_preserves_wf(pre, split_arg);
    } else {
        assert(children.len() == post->children.len());
        assert(pivots == post->pivots);
        assert(forall |i| 0 <= i < children.len() && i != r+1 ==> #[trigger] children[i] == post->children[i]);
        assert(path.subpath().node == children[r+1]);
        assert(path.subpath().valid());
        lemma_split_preserves_wf(children[r+1], path.subpath(), split_arg);
        assert(post->children[r+1] == children[r+1].split(path.subpath(), split_arg));
        assert(post->children[r+1].wf());

        lemma_split_all_keys(children[r+1], path.subpath(), split_arg);

        // In the split child is leaf case, children[r+1] all_keys also contains the pivot.
        // Shared asserts for proving pivot < pivots[r+1] and pivots[r] < pivot.
        assert(children[r+1] is Index);
        assert(post->children[r+1] is Index);
        let r2 = path.target().route(pivot);
        assert(0 <= r2 + 1 < path.target()->children.len());

        if (split_arg is SplitLeaf) {
            assert(path.target()->children[r2+1] is Leaf);
            assert(post->children[r+1].all_keys() == children[r+1].all_keys().insert(pivot));
            let split_keys = path.target()->children[r2+1]->keys;
            assert(split_keys.len() > 0);

            assert(path.target()->children[r2+1].wf());
            assert(Key::is_strictly_sorted(split_keys));
            Key::strictly_sorted_implies_sorted(split_keys);
            Key::largest_lt_ensures(split_keys, pivot, Key::largest_lt(split_keys, pivot));
        }

        if (r+1 < post->children.len() - 1) {
            assert(post.all_keys_below_bound(r+1)) by {
                assert(pre.all_keys_below_bound(r+1));

                // pivot < pivots[r+1] idea:
                // - pivot <= last key in split child
                // - This key is also in children[r+1], so it's < pivots[r+1] by all_keys_below_bound
                if (split_arg is SplitLeaf) {
                    let split_keys = path.target()->children[r2+1]->keys;
                    let last_key = split_keys.last();
                    assert(Key::lte(pivot, last_key));

                    assert(path.target()->children[r2+1].all_keys().contains(last_key));
                    assert(path.target().all_keys().contains(last_key));
                    lemma_target_all_keys(children[r+1], path.subpath(), last_key);
                    assert(children[r+1].all_keys().contains(last_key));
                    assert(Key::lt(last_key, pivots[r+1]));

                    assert(Key::lt(pivot, pivots[r+1]));
                }
            }
        }

        if (0 < r+1 < post->children.len()) {
            // pivots[r] <= pivot idea:
            // - First key in split child < pivot
            // - This key is also in children[r+1], so it's >= pivots[r] by all_keys_above_bound
            // We need this fact for the last assert so took it out of the assert by.
            if (split_arg is SplitLeaf) {
                let split_keys = path.target()->children[r2+1]->keys;
                let key = split_keys.first();
                assert(Key::lt(key, pivot));

                assert(path.target()->children[r2+1].all_keys().contains(key));
                assert(path.target().all_keys().contains(key));
                lemma_target_all_keys(children[r+1], path.subpath(), key);
                assert(children[r+1].all_keys().contains(key));
                assert(Key::lte(pivots[r+1-1], key)) by {
                    assert(pre.all_keys_above_bound(r+1));
                }

                assert(Key::lt(pivots[r+1-1], pivot));
            }

            assert(post.all_keys_above_bound(r+1)) by {
                assert(pre.all_keys_above_bound(r+1));
            }
        }
        assert(0 < r+1 < post->children.len() && split_arg is SplitLeaf ==> Key::lt(pivots[r], pivot));

        assert forall |i| 0 <= i < post->children.len() - 1 && i != r+1
        implies post.all_keys_below_bound(i) by {
            assert(pre.all_keys_below_bound(i));
        }

        assert forall |i| 0 < i < post->children.len() && i != r+1
        implies post.all_keys_above_bound(i) by {
            assert(pre.all_keys_above_bound(i));
        }
    }
}

// Prove that splitting a node is equivalent to a no-op in the interpreted space.
pub proof fn split_refines(pre: Node, path: Path, split_arg: SplitArg)
requires
    pre.wf(),
    path.valid(),
    path.node == pre,
    path.key == split_arg.get_pivot(),
    path.target().can_split_child_of_index(split_arg),
ensures
    pre.split(path, split_arg).wf(),
    pre.i() =~~= pre.split(path, split_arg).i(),
decreases
    path.depth,
{
    lemma_route_auto();
    assert(pre is Index);
    let pivots = pre->pivots;
    let children = pre->children;
    let post = pre.split(path, split_arg);
    let pivot = split_arg.get_pivot();

    lemma_split_preserves_wf(pre, path, split_arg);
    assert(post.wf());
    assert(post is Index);

    let r = pre.route(pivot);
    assert(0 <= r + 1 < children.len());

    if (path.depth == 0) {
        assert(post->children.len() == children.len() + 1);
        assert(post->pivots.len() == pivots.len() + 1);
        assert(post->pivots[r+1] == pivot);

        assert(forall |i| 0 <= i < post->children.len() ==> (#[trigger] post->children[i]).wf());
        assert(forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).wf());

        assert forall |i, key| 0 <= i < children.len() && children[i] is Index
        implies 0 <= #[trigger] children[i].route(key) + 1 < children[i]->children.len() by {
            lemma_route_ensures(children[i], key);
        }
        assert forall |i, key| 0 <= i < post->children.len() && post->children[i] is Index
        implies 0 <= #[trigger] post->children[i].route(key) + 1 < post->children[i]->children.len() by {
            lemma_route_ensures(post->children[i], key);
        }

        lemma_split_node_preserves_wf(children[r+1], split_arg);
        lemma_split_node_interpretation(children[r+1], split_arg);

        assert forall |k| pre.i().map.contains_key(k) implies post.i().map.contains_key(k) by {
            let r2 = pre.route(k);
            let post_r2 = post.route(k);
            assert(0 <= r2 + 1 < children.len());
            assert(-1 <= r2 < pivots.len());
            assert(0 <= post_r2 + 1 < post->children.len());
            assert(-1 <= post_r2 < post->pivots.len());
            assert(-1 <= post_r2 <= pivots.len());

            assert(children[r2+1].i().map.contains_key(k));

            if (r2 < r || (r2 == r && Key::lt(k, pivot))) {
                assert(r2 == post_r2) by {
                    if (r2 >= 0) {
                        assert(lte_route(pre, k, r2));
                        assert(Key::lte(pivots[r2], k));
                        assert(pivots[r2] == post->pivots[r2]);
                    }
                    if (r2 < post->pivots.len() - 1) {
                        assert(Key::lt(k, post->pivots[r2+1])) by {
                            if (r2 < r) {
                                assert(gt_route(pre, k, r2+1));
                                assert(Key::lt(k, pivots[r2+1]));
                                assert(pivots[r2+1] == post->pivots[r2+1]);
                            }
                        }
                    }
                    Key::largest_lte_is_lemma(post->pivots, k, r2);
                }
            } else if (r2 > r || (r2 == r && Key::lte(pivot, k))) {
                assert(r2+1 == post_r2) by {
                    if (r2+1 >= 0) {
                        assert(Key::lte(post->pivots[r2+1], k)) by {
                            if (r2 > r) {
                                assert(lte_route(pre, k, r2));
                                assert(Key::lte(pivots[r2], k));
                                assert(pivots[r2] == post->pivots[r2+1]);
                            }
                        }
                    }
                    if (r2+1 < post->pivots.len() - 1) {
                        assert(gt_route(pre, k, r2+1));
                        assert(Key::lt(k, pivots[r2+1]));
                        assert(pivots[r2+1] == post->pivots[r2+2]);
                    }
                    Key::largest_lte_is_lemma(post->pivots, k, r2+1);
                }
            }

            if (r2 == r) {
                if (Key::lt(k, pivot)) {
                    assert(post->children[r2+1].i().map.contains_key(k));
                    assert(r2 == post_r2);
                } else {
                    assert(post->children[r2+2].i().map.contains_key(k));
                    assert(r2+1 == post_r2);
                }
            } else if r2 < r {
                assert(children[r2+1] == post->children[r2+1]);
                assert(post->children[r2+1].i().map.contains_key(k));
                assert(r2 == post_r2);
            } else {
                assert(children[r2+1] == post->children[r2+2]);
                assert(post->children[r2+2].i().map.contains_key(k));
                assert(r2+1 == post_r2);
            }
        }

        assert forall |k| #[trigger] post.i().map.contains_key(k)
        implies pre.i().map.contains_key(k) && post.i().map[k] == pre.i().map[k] by {
            let r2 = pre.route(k);
            let post_r2 = post.route(k);
            assert(0 <= post_r2 + 1 < post->children.len());

            assert(post->children[post_r2+1].i().map.contains_key(k));
            lemma_interpretation(post->children[post_r2+1]);
            assert(post->children[post_r2+1].all_keys().contains(k));

            if (post_r2 <= r) {
                assert(r2 == post_r2) by {
                    if (post_r2 >= 0) {
                        assert(lte_route(post, k, post_r2));
                        assert(Key::lte(post->pivots[post_r2], k));
                        assert(pivots[post_r2] == post->pivots[post_r2]);
                    }
                    if (post_r2 < pivots.len() - 1) {
                        assert(gt_route(post, k, post_r2+1));
                        assert(Key::lt(k, post->pivots[post_r2+1]));
                        assert(Key::lte(post->pivots[post_r2+1], pivots[post_r2+1])) by {
                            if (post_r2 < r) {
                                assert(post->pivots[post_r2+1] == pivots[post_r2+1]);
                            } else if (post_r2 == r) {
                                assert(Key::lt(post->pivots[post_r2+1], post->pivots[post_r2+2]));
                                assert(post->pivots[post_r2+2] == pivots[post_r2+1]);
                            }
                        }
                    }
                    Key::largest_lte_is_lemma(pivots, k, post_r2);
                }
            } else if (post_r2 >= r+1) {
                assert(r2 == post_r2-1) by {
                    if (post_r2-1 >= 0) {
                        assert(Key::lte(pivots[post_r2-1], k)) by {
                            if (post_r2 > r+1) {
                                assert(lte_route(post, k, post_r2));
                                assert(Key::lte(post->pivots[post_r2], k));
                                assert(post->pivots[post_r2] == pivots[post_r2-1]);
                            } else if (post_r2 == r+1) {
                                assert(lte_route(post, k, post_r2-1));
                                assert(Key::lte(post->pivots[post_r2-1], k));
                                assert(post->pivots[post_r2-1] == pivots[post_r2-1]);
                            }
                        }
                    }
                    if (post_r2-1 < pivots.len() - 1) {
                        assert(gt_route(post, k, post_r2+1));
                        assert(Key::lt(k, post->pivots[post_r2+1]));
                        assert(pivots[post_r2] == post->pivots[post_r2+1]);
                    }
                    Key::largest_lte_is_lemma(pivots, k, post_r2-1);
                }
            }
            
            if (post_r2 == r) {
                assert(Key::lt(k, pivot)) by {
                    assert(post.all_keys_below_bound(post_r2+1));
                    assert(Key::lt(k, post->pivots[post_r2+1]));
                }
                assert(children[r+1].i().map.contains_key(k));
                assert(r2 == post_r2);
            } else if (post_r2 == r+1) {
                assert(Key::lte(pivot, k)) by {
                    assert(post.all_keys_above_bound(post_r2+1));
                    assert(Key::lte(post->pivots[post_r2+1-1], k));
                }
                assert(children[r+1].i().map.contains_key(k));
                assert(r2 == post_r2-1);
            } else if (post_r2 < r) {
                assert(children[post_r2+1] == post->children[post_r2+1]);
                assert(children[post_r2+1].i().map.contains_key(k));
                assert(r2 == post_r2);
            } else {
                assert(children[post_r2] == post->children[post_r2+1]);
                assert(children[post_r2].i().map.contains_key(k));
                assert(r2 == post_r2-1);
            }
            assert(pre.i().map.contains_key(k));
        }

        // GOAL 1
        assert(pre.i().map.dom() =~~= post.i().map.dom());

        // OVERALL GOAL
        assert(pre.i().map =~~= post.i().map);
    } else {
        assert(path.subpath().valid());
        split_refines(children[r+1], path.subpath(), split_arg);
    }
}

}