// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::Domain_v::*;

verus! {

#[is_variant]
pub enum Node {
    Index{pivots: Seq<Key>, children: Seq<Node>},
    Leaf{keys: Seq<Key>, msgs: Seq<Message>}
}

impl Node {
    pub open spec(checked) fn all_keys(self) -> Set<Key>
        decreases self
    {
        match self {
            Node::Leaf{keys, msgs} => keys.to_set(),
            Node::Index{pivots, children} => {
                let pivotKeys = pivots.to_set();
                let indexKeys = Set::new(|key| 
                    exists |i| 0 <= i < children.len() 
                    && #[trigger] children[i].all_keys().contains(key));
                pivotKeys + indexKeys
            }
        }
    }

    pub open spec(checked) fn all_keys_below_bound(self, i: int) -> bool
        recommends
            self is Index,
            0 <= i < self.get_Index_children().len() - 1,
            0 <= i < self.get_Index_pivots().len()
    {
        forall |key| self.get_Index_children()[i].all_keys().contains(key)
            ==> #[trigger] Key::lt(key, self.get_Index_pivots()[i])
    }

    pub open spec(checked) fn all_keys_above_bound(self, i: int) -> bool
        recommends
            self is Index,
            0 <= i < self.get_Index_children().len(),
            0 <= i - 1 < self.get_Index_pivots().len()
    {
        forall |key| self.get_Index_children()[i].all_keys().contains(key)
            ==> #[trigger] Key::lte(self.get_Index_pivots()[i-1], key)
    }

    pub open spec(checked) fn wf(self) -> bool
        decreases self
    {
        match self {
            Node::Leaf{keys, msgs} => {
                &&& keys.len() == msgs.len()
                &&& Key::is_strictly_sorted(keys)
            },
            Node::Index{pivots, children} => {
                &&& pivots.len() == children.len() - 1
                &&& Key::is_strictly_sorted(pivots)
                &&& forall |i| 0 <= i < children.len() ==> #[trigger] children[i].wf()
                &&& forall |i| 0 <= i < children.len() - 1 ==> self.all_keys_below_bound(i)
                &&& forall |i| 0 < i < children.len() ==> self.all_keys_above_bound(i)
            }
        }
    }

    pub open spec(checked) fn route(self, key: Key) -> int
        recommends self.wf()
    {
        let s = if self is Leaf { self.get_Leaf_keys() } else { self.get_Index_pivots() };
        Key::largest_lte(s, key)
    }

    pub open spec(checked) fn query(self, key: Key) -> Message
        recommends self.wf()
        decreases self when self is Index && 0 <= self.route(key)+1 < self.get_Index_children().len()
    {
        let r = self.route(key);
        match self {
            Node::Leaf{keys, msgs} => {
                if r >= 0 && keys[r] == key { msgs[r] } else { Message::Update{delta: nop_delta()} }
            },
            Node::Index{pivots, children} => {
                children[r+1].query(key)
            }
        }
    }

    pub open spec(checked) fn grow(self) -> Node
    {
        Node::Index{pivots: seq![], children: seq![self]}
    }

    pub open spec(checked) fn insert_leaf(self, key: Key, msg: Message) -> Node
        recommends
            self is Leaf,
            self.wf()
    {
        let llte = Key::largest_lte(self.get_Leaf_keys(), key);
        if 0 <= llte && self.get_Leaf_keys()[llte] == key {
            Node::Leaf{
                keys: self.get_Leaf_keys(), 
                msgs: self.get_Leaf_msgs().update(llte, msg)
            }
        } else {
            Node::Leaf{
                keys: self.get_Leaf_keys().insert(llte+1, key),
                msgs: self.get_Leaf_msgs().insert(llte+1, msg)
            }
        }
    }

    pub open spec(checked) fn append_to_new_leaf(self, new_keys: Seq<Key>, new_msgs: Seq<Message>) -> Node
        recommends
            new_keys.len() == new_msgs.len(),
            Key::is_strictly_sorted(new_keys)
    {
        Node::Leaf{ keys: new_keys, msgs: new_msgs }
    }

    pub open spec(checked) fn split_leaf(self, pivot: Key, left_leaf: Node, right_leaf: Node) -> bool
    {
        &&& self is Leaf
        &&& left_leaf is Leaf
        &&& right_leaf is Leaf
        &&& 0 < left_leaf.get_Leaf_keys().len() == left_leaf.get_Leaf_msgs().len()
        &&& 0 < right_leaf.get_Leaf_keys().len() == right_leaf.get_Leaf_msgs().len()
        &&& self.get_Leaf_keys() == left_leaf.get_Leaf_keys() + right_leaf.get_Leaf_keys()
        &&& self.get_Leaf_msgs() == left_leaf.get_Leaf_msgs() + right_leaf.get_Leaf_msgs()
        &&& Key::lt(left_leaf.get_Leaf_keys().last(), pivot)
        &&& Key::lte(pivot, right_leaf.get_Leaf_keys()[0])
    }

    pub open spec(checked) fn sub_index(self, from: int, to: int) -> Node
        recommends
            self is Index,
            self.get_Index_children().len() == self.get_Index_pivots().len() + 1,
            0 <= from < to <= self.get_Index_children().len()
    {
        Node::Index{ pivots: self.get_Index_pivots().subrange(from, to-1), children: self.get_Index_children().subrange(from, to) }
    }

    pub open spec(checked) fn split_index(self, pivot: Key, left_index: Node, right_index: Node) -> bool
    {
        &&& self.wf()
        &&& self is Index
        &&& left_index is Index
        &&& right_index is Index
        &&& 0 < left_index.get_Index_children().len() < self.get_Index_children().len()

        &&& left_index == self.sub_index(0, left_index.get_Index_children().len() as int)
        &&& right_index == self.sub_index(left_index.get_Index_children().len() as int, self.get_Index_children().len() as int)
        &&& forall |key| left_index.get_Index_children().last().all_keys().contains(key) ==> #[trigger] Key::lt(key, pivot)
        &&& forall |key| right_index.get_Index_children()[0].all_keys().contains(key) ==> #[trigger] Key::lte(pivot, key)
        &&& pivot == self.get_Index_pivots()[left_index.get_Index_pivots().len() as int]
    }

    pub open spec(checked) fn split_node(self, pivot: Key, left_node: Node, right_node: Node) -> bool
    {
        ||| self.split_leaf(pivot, left_node, right_node)
        ||| self.split_index(pivot, left_node, right_node)
    }

    pub open spec(checked) fn split_child_of_index(self, pivot: Key, new_index: Node) -> bool
    {
        let child_idx = self.route(pivot) + 1;
        &&& self.wf()
        &&& self is Index
        &&& new_index is Index
        &&& new_index.get_Index_children().len() == self.get_Index_children().len() + 1
        &&& new_index.get_Index_pivots() == self.get_Index_pivots().insert(child_idx, pivot)
        &&& new_index.get_Index_children() == self.get_Index_children()
            .update(child_idx, new_index.get_Index_children()[child_idx])
            .insert(child_idx + 1, new_index.get_Index_children()[child_idx + 1])
        &&& self.get_Index_children()[child_idx].split_node(pivot, new_index.get_Index_children()[child_idx], new_index.get_Index_children()[child_idx + 1])
    }

    pub open spec(checked) fn insert(self, key: Key, msg: Message, path: Path, new_target: Node) -> Node
        recommends
            self.wf(),
            path.valid(),
            path.node == self,
            path.key == key,
            path.target() is Leaf,
            path.target().insert_leaf(key, msg) == new_target
    {
        path.substitute(new_target)
    }

    pub open spec(checked) fn append(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path, new_target: Node) -> Node
        recommends
            self.wf(),
            path.valid(),
            path.node == self,
            path.target() == self.empty(),
            keys != Seq::<Key>::empty(),
            keys.len() == msgs.len(),
            Key::is_strictly_sorted(keys),
            new_target == path.target().append_to_new_leaf(keys, msgs),
            path.key == new_target.get_Leaf_keys()[0],
            path.path_equiv(new_target.get_Leaf_keys().last()) // all new keys must route to the same location
    {
        path.substitute(new_target)
    }

    pub open spec(checked) fn split(self, path: Path, new_target: Node) -> Node
        recommends
            self.wf(),
            path.valid(),
            path.node == self,
            path.target().split_child_of_index(path.key, new_target),
    {
        path.substitute(new_target)
    }

    pub open spec(checked) fn empty(self) -> Node
    {
        Node::Leaf{ keys: seq![], msgs: seq![] }
    }
}

#[verifier::ext_equal]
pub struct Path {
    pub node: Node,
    pub key: Key,
    pub depth: nat
}

impl Path {
    pub open spec(checked) fn subpath(self) -> Path
        recommends
            0 < self.depth,
            self.node.wf(),
            self.node is Index
    {
        Path{
            node: self.node.get_Index_children()[self.node.route(self.key) + 1],
            key: self.key,
            depth: (self.depth - 1) as nat
        }
    }

    pub open spec(checked) fn valid(self) -> bool
        decreases self.depth
    {
        &&& self.node.wf()
        &&& 0 < self.depth ==> self.node is Index
        &&& 0 < self.depth ==> self.subpath().valid()
    }

    pub open spec(checked) fn target(self) -> Node
        recommends self.valid()
        decreases self.depth
    {
        if 0 == self.depth {
            self.node
        } else {
            self.subpath().target()
        }
    }

    pub open spec(checked) fn replaced_children(self, replacement: Node) -> Seq<Node>
        recommends
            self.valid(),
            0 < self.depth
        decreases self.subpath().depth
    {
        let new_child = self.subpath().substitute(replacement);
        self.node.get_Index_children().update(self.node.route(self.key) + 1, new_child)
    }

    pub open spec(checked) fn substitute(self, replacement: Node) -> Node
        recommends self.valid()
        decreases self.depth, 1nat
    {
        if 0 == self.depth {
            replacement
        } else {
            Node::Index{ pivots: self.node.get_Index_pivots(), children: self.replaced_children(replacement) }
        }
    }

    pub open spec(checked) fn path_equiv(self, other_key: Key) -> bool
        recommends self.valid()
        decreases self.depth, 1nat
    {
        &&& self.node.route(self.key) == self.node.route(other_key)
        &&& 0 < self.depth ==> self.subpath().path_equiv(other_key)
    }
}

}
