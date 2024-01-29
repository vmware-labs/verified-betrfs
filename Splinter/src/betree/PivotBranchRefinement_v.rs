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
    if node is Leaf { node.get_Leaf_keys() } else { node.get_Index_pivots() }
}

pub open spec(checked) fn lte_route(node: Node, key: Key, i: int) -> bool
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
        let s = get_keys_or_pivots(node);
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| #[trigger] lte_route(node, key, i) ==> Key::lte(s[i], key)
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
    pub path: Path,
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
            let post_pivots = post.get_Index_pivots();
            let post_children = post.get_Index_children();
            let r = node.route(key);
            lemma_route_auto();
            assert(0 <= r + 1 < children.len());

            // Recursively call the lemma on the changed child: the child we inserted into.
            lemma_insert_inserts_to_all_keys(children[r+1], key, msg, path.subpath());
            // This implies that the changed child's all_keys is the same as before except with the
            // new key inserted.
            assert(post_children[r+1].all_keys() == children[r+1].all_keys().insert(key));

            // Now let's just assert that each of the post state's children all_keys
            // are the same as the pre (besides the changed child).
            assert(post_children.len() == children.len());
            assert(forall |i| 0 <= i < post_children.len() && i != (r+1)
                ==> post_children[i] =~~= children[i]);

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
            let post_pivots = post.get_Index_pivots();
            let post_children = post.get_Index_children();

            let r = node.route(key);
            lemma_route_auto();
            assert(0 <= r+1 < children.len()); // For recommends

            lemma_insert_preserves_wf(children[r+1], key, msg, path.subpath());

            // For recommends
            assert(pivots.len() == post_pivots.len());
            assert(children.len() == post_children.len());

            // Subgoal 1, needed for asserting that unchanged keys in children[r+1].all_keys() still satisfy bounds
            lemma_insert_inserts_to_all_keys(children[r+1], key, msg, path.subpath());
            assert(post_children[r+1].all_keys() == children[r+1].all_keys().insert(key));

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

            assert forall |i| 0 <= i < post_children.len() - 1 && i != r+1
                implies post.all_keys_below_bound(i) by
            {
                assert(node.all_keys_below_bound(i));
            }

            assert forall |i| 0 < i < post_children.len() && i != r+1
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
            let post_children = post.get_Index_children();
            let r = pre.route(lbl.key);
            
            // Suppress recommendation
            assert(0 <= r + 1 < children.len());
            assert(post.wf());
            assert(post_children.len() == children.len()); 
            assert(forall |i| 0 <= i < post_children.len() ==> (#[trigger] post_children[i]).wf());

            // Assert that other children don't change
            assert(forall |i| #![auto] 0 <= i < children.len() && i != (r+1) ==> post_children[i].i() == children[i].i());

            // Assert that the changed child has original keys plus the new key-value pair.
            let child_label = InsertLabel{ key: lbl.key, msg: lbl.msg, path: lbl.path.subpath() };
            insert_refines(children[r+1], child_label);
            assert(post_children[r+1].i() == children[r+1].i().insert(lbl.key, lbl.msg));

            assert forall |k| post.i().map.contains_key(k)
            implies #[trigger] pre.i().insert(lbl.key, lbl.msg).map.contains_key(k) by {
                if (k == lbl.key) {
                    assert(pre.i().insert(lbl.key, lbl.msg).map.contains_key(k));
                } else
                /*if (k != lbl.key)*/ {
                    // (x9du) If commented out, only fails on following assert line 566.
                    // If uncommented, fails on the second forall implies line 571 and the assert on line 575.
                    assume(false);
                    assert(pre.i().map.contains_key(k));
                }
                assert(pre.i().insert(lbl.key, lbl.msg).map.contains_key(k));
            }

            assert forall |k| pre.i().insert(lbl.key, lbl.msg).map.contains_key(k)
            implies #[trigger] post.i().map.contains_key(k) by {
            }
            assert(post.i().map.dom() =~~= pre.i().insert(lbl.key, lbl.msg).map.dom());
            assert(forall |k| post.i().map.contains_key(k) ==> #[trigger] post.i().map[k] == pre.i().insert(lbl.key, lbl.msg).map[k]);
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

// pub proof fn append_refines(pre: Node, lbl: AppendLabel)
//     requires
//         pre.wf(),
//         lbl.path.valid(),
//         lbl.path.node == pre,
//         lbl.path.target() == Node::empty_leaf(),
//         lbl.keys.len() > 0,
//         lbl.keys.len() == lbl.msgs.len(),
//         Key::is_strictly_sorted(lbl.keys),
//         lbl.path.key == lbl.keys[0],
//         lbl.path.path_equiv(lbl.keys.last())
//     ensures
//         //

}