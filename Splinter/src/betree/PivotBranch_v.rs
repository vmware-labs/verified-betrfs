// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::betree::Buffer_v::*;
// use crate::betree::Domain_v::*;

verus! {

#[is_variant]
pub enum SplitArg {
    SplitIndex{pivot: Key, pivot_index: int},
    SplitLeaf{pivot: Key}
}

impl SplitArg {
    pub open spec(checked) fn wf(self, split_node: Node) -> bool
    {
        match self {
            Self::SplitLeaf{pivot} => {
                &&& split_node is Leaf
                &&& split_node.get_Leaf_keys().len() == split_node.get_Leaf_msgs().len()
                &&& 0 < Key::largest_lt(split_node.get_Leaf_keys(), pivot) + 1 < split_node.get_Leaf_keys().len()
            }
            Self::SplitIndex{pivot, pivot_index} => {
                &&& split_node is Index
                &&& split_node.wf()
                &&& 0 <= pivot_index < split_node.get_Index_pivots().len()
                &&& split_node.get_Index_pivots()[pivot_index] == pivot
            }
        }
    }

    pub open spec(checked) fn get_pivot(self) -> Key
    {
        if self is SplitLeaf {
            self.get_SplitLeaf_pivot()
        } else {
            self.get_SplitIndex_pivot()
        }
    }
}

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

    pub open spec/*XXX (checked)*/ fn query(self, key: Key) -> Message
        recommends self.wf()
        decreases self when self is Index && 0 <= self.route(key)+1 < self.get_Index_children().len()
    {
        // Need ensures from route to restore checked
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

    pub open spec/* XXX (checked)*/ fn insert_leaf(self, key: Key, msg: Message) -> Node
        recommends
            self is Leaf,
            self.wf()
    {
        // Need largest_lte ensures to restore checked
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

    pub open spec/* XXX (checked)*/ fn insert(self, key: Key, msg: Message, path: Path) -> Node
        recommends
            self.wf(),
            path.valid(),
            path.node == self,
            path.key == key,
            path.target() is Leaf
    {
        // Need target ensures to restore checked
        path.substitute(path.target().insert_leaf(key, msg))
    }

    pub open spec(checked) fn grow(self) -> Node
        recommends self.wf()
    {
        Node::Index{pivots: seq![], children: seq![self]}
    }

    pub open spec(checked) fn append_to_new_leaf(self, new_keys: Seq<Key>, new_msgs: Seq<Message>) -> Node
        recommends
            new_keys.len() == new_msgs.len(),
            Key::is_strictly_sorted(new_keys)
    {
        Node::Leaf{ keys: new_keys, msgs: new_msgs }
    }

    pub open spec(checked) fn append(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path) -> Node
        recommends
            self.wf(),
            path.valid(),
            path.node == self,
            path.target() == self.empty(),
            keys.len() > 0,
            keys.len() == msgs.len(),
            Key::is_strictly_sorted(keys),
            path.key == keys[0],
            path.path_equiv(keys.last()) // all new keys must route to the same location
    {
        path.substitute(path.target().append_to_new_leaf(keys, msgs))
    }

    pub open spec(checked) fn split_leaf(self, split_arg: SplitArg) -> (Node, Node)
        recommends split_arg.wf(self)
    {
        let pivot = split_arg.get_pivot();
        let split_index = Key::largest_lt(self.get_Leaf_keys(), pivot) + 1;
        let left_leaf = Node::Leaf{
            keys: self.get_Leaf_keys().take(split_index),
            msgs: self.get_Leaf_msgs().take(split_index)
        };
        let right_leaf = Node::Leaf{
            keys: self.get_Leaf_keys().skip(split_index),
            msgs: self.get_Leaf_msgs().skip(split_index)
        };
        (left_leaf, right_leaf)
    }

    pub open spec(checked) fn sub_index(self, from: int, to: int) -> Node
        recommends
            self is Index,
            self.get_Index_children().len() == self.get_Index_pivots().len() + 1,
            0 <= from < to <= self.get_Index_children().len()
    {
        Node::Index{ pivots: self.get_Index_pivots().subrange(from, to-1), children: self.get_Index_children().subrange(from, to) }
    }

    pub open spec/*XXX (checked)*/ fn split_index(self, split_arg: SplitArg) -> (Node, Node)
        recommends split_arg.wf(self)
    {
        // Assert split_arg.wf(self) ==> self.wf() ==>
        // self.get_Index_children().len() == self.get_Index_pivots().len() + 1
        // to restore checked
        let pivot_index = split_arg.get_SplitIndex_pivot_index();
        let left_index = self.sub_index(0, pivot_index + 1);
        let right_index = self.sub_index(pivot_index + 1, self.get_Index_children().len() as int);
        (left_index, right_index)
    }

    pub open spec(checked) fn split_node(self, split_arg: SplitArg) -> (Node, Node)
        recommends split_arg.wf(self)
    {
        if (self is Leaf) {
            self.split_leaf(split_arg)
        } else {
            self.split_index(split_arg)
        }
    }

    pub open spec/* XXX (checked)*/ fn can_split_child_of_index(self, split_arg: SplitArg) -> bool
    {
        &&& self.wf()
        &&& self is Index
        &&& {
            // Need route ensures to restore checked
            let child_idx = self.route(split_arg.get_pivot()) + 1;
            split_arg.wf(self.get_Index_children()[child_idx])
            }
    }

    pub open spec/* XXX (checked)*/ fn split_child_of_index(self, split_arg: SplitArg) -> Node
        recommends self.can_split_child_of_index(split_arg)
    {
        // Need route ensures to restore checked
        let pivot = split_arg.get_pivot();
        let child_idx = self.route(pivot) + 1;
        let (left_node, right_node) = self.get_Index_children()[child_idx].split_node(split_arg);
        Node::Index{
            pivots: self.get_Index_pivots().insert(child_idx, pivot),
            children: self.get_Index_children()
                .update(child_idx, left_node)
                .insert(child_idx + 1, right_node)
        }
    }

    pub open spec(checked) fn split(self, path: Path, split_arg: SplitArg) -> Node
        recommends
            self.wf(),
            path.valid(),
            path.node == self,
            path.key == split_arg.get_pivot(),
            path.target().can_split_child_of_index(split_arg)
    {
        path.substitute(path.target().split_child_of_index(split_arg))
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
    pub open spec/* XXX (checked)*/ fn subpath(self) -> Path
        recommends
            0 < self.depth,
            self.node.wf(),
            self.node is Index
    {
        // Need route ensures to restore checked
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

    pub open spec/* XXX (checked)*/ fn replaced_children(self, replacement: Node) -> Seq<Node>
        recommends
            self.valid(),
            0 < self.depth
        decreases self.subpath().depth
    {
        // Need route ensures to restore checked
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
