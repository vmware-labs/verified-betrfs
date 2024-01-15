// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::Domain_v::*;
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
                    |key| self.all_keys().contains(key) && children[self.route(key) + 1].i().map.contains_key(key),
                    |key| children[self.route(key) + 1].i().map[key]
                )}
            }
        }
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

// TODO: time limit this function
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
    // assume(false);
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

// TODO: time limit this function
pub proof fn lemma_split_leaf_interpretation(old_leaf: Node, split_arg: SplitArg)
    requires
        old_leaf.wf(),
        old_leaf is Leaf,
        split_arg.wf(old_leaf),
        // this condition doesn't work for some reason?
        ({
            let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
            &&& left_leaf.wf()
            &&& right_leaf.wf()
        })
    ensures ({
        let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
        old_leaf.i().map == Key::map_pivoted_union(left_leaf.i().map, split_arg.get_pivot(), right_leaf.i().map)
    })
{
    // need to satisfy i() when
    assume(false);
}

pub proof fn lemma_split_index_interpretation1(old_index: Node, split_arg: SplitArg)
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
        old_index.i().map.submap_of(Key::map_pivoted_union(left_index.i().map, split_arg.get_pivot(), right_index.i().map))
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

}