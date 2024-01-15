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
                    |key| /*self.all_keys().contains(key) &&*/ children[self.route(key) + 1].i().map.contains_key(key),
                    |key| children[self.route(key) + 1].i().map[key]
                )}
            }
        }
    }
}

pub proof fn route_ensures(node: Node, key: Key)
    requires node.wf()
    ensures ({
        let s = if node is Leaf { node.get_Leaf_keys() } else { node.get_Index_pivots() };
        &&& -1 <= #[trigger] node.route(key) < s.len()
        &&& forall |i| 0 <= i <= node.route(key) ==> Key::lte(#[trigger] s[i], key)
        &&& forall |i| node.route(key) < i < s.len() ==> Key::lt(key, #[trigger] s[i])
        &&& s.contains(key) ==> 0 <= node.route(key) && s[node.route(key)] == key
    })
{
    let s = if node is Leaf { node.get_Leaf_keys() } else { node.get_Index_pivots() };
    Key::strictly_sorted_implies_sorted(s);
    Key::largest_lte_ensures(s, key, Key::largest_lte(s, key));
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

pub proof fn lemma_interpretation(node: Node)
    requires node.wf()
    ensures node.all_keys() == node.i().map.dom()
    // maybe a hassle to prove
    // forall |key| node.all_keys().contains(key) ==> node.query(lbl.key) == node.i().map[key]
{
    assume(false);
}

#[verifier::ext_equal]
pub struct QueryLabel {
    pub key: Key,
    pub msg: Message
}

#[verifier::ext_equal]
pub struct InsertLabel {
    pub key: Key,
    pub msg: Message
}

#[verifier::ext_equal]
pub struct AppendLabel {
    pub keys: Seq<Key>,
    pub msgs: Seq<Message>
}

#[verifier::ext_equal]
pub struct InternalLabel {}

pub proof fn query_refines(pre: Node, lbl: QueryLabel)
    requires
        pre.wf(),
        // pre is Index ==> 0 <= pre.route(lbl.key)+1 < pre.get_Index_children().len(),
        pre.query(lbl.key) == lbl.msg
    // ensures
        // pre.i().query(lbl.key) == lbl.msg
    decreases pre
{
    let r = pre.route(lbl.key);
    route_ensures(pre, lbl.key);
    if pre is Index {
        let pivots = pre.get_Index_pivots();
        let children = pre.get_Index_children();
        assert(pre.wf_index(pivots, children));
        let i = r+1;
        assert(0 <= i < children.len());
        assert(children[i].wf()); // fail by should be true by pre.wf()
        assume(false);
        route_ensures(children[r+1], lbl.key);
        assert(lbl.msg == children[r+1].query(lbl.key));

        query_refines(children[r+1], lbl);
        assert(children[r+1].i().query(lbl.key) == lbl.msg);
        if pre.i().map.contains_key(lbl.key) {
            assert(children[r+1].i().map.contains_key(lbl.key)); //fail but should be true by i()
            lemma_interpretation_delegation(pre, lbl.key);
            assert(pre.i().map[lbl.key] == children[r+1].i().map[lbl.key]);
        } else {
            if (children[r+1].i().map.contains_key(lbl.key)) {
                lemma_interpretation_delegation(pre, lbl.key);
                assert(pre.i().map.contains_key(lbl.key)); // contradiction
            }
            assert(!children[r+1].i().map.contains_key(lbl.key));
        }
        assert(pre.i().query(lbl.key) == children[r+1].i().query(lbl.key));

        // i() def copied here for convenience
        // Buffer{map: Map::new(
        //     |key| children[self.route(key) + 1].i().map.contains_key(key),
        //     |key| children[self.route(key) + 1].i().map[key]
        // )}
    }
}

}