// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

/// This file defines the PivotBranch data structure. Under the `betree/` folder, all "Branch" data structures are
/// just B+-trees. They are called "Branches" to distinguish them from the Be-tree data structures, and because
/// Be-tree nodes can point to B+-trees (thus making B+-trees "branches" of a Be-tree).
/// 
/// A PivotBranch is a B+-tree defined in its most natural form, where the pivots are Keys, and Index nodes directly
/// contain sequences of their children (i.e.: in a concrete implementation its one massive nested data structure, instead
/// of using pointers). AKA it's a "functional" tree (immutable, defined).

use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::betree::Buffer_v::*;
// use crate::betree::Domain_v::*;

verus! {

// TODO: comment which functions are actually transitions that need refinement proofs!

/// (x9du): A SplitArg is a value used for determining a pivot value at which to split
/// a B+tree node into two nodes. Its an enum to handle the cases for splitting an index
/// node vs. a Leaf node separately.
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
                &&& split_node->keys.len() == split_node->msgs.len()
                &&& 0 < Key::largest_lt(split_node->keys, pivot) + 1 < split_node->keys.len()
            }
            Self::SplitIndex{pivot, pivot_index} => {
                &&& split_node is Index
                &&& split_node.wf()
                &&& 0 <= pivot_index < split_node->pivots.len()
                &&& split_node->pivots[pivot_index] == pivot
            }
        }
    }

    pub open spec(checked) fn get_pivot(self) -> Key
    {
        if self is SplitLeaf {
            self.arrow_SplitLeaf_pivot()
        } else {
            self.arrow_SplitIndex_pivot()
        }
    }
}

/*
Node in a B+ tree. There are two types of B+ tree nodes: index nodes and leaf nodes.
The B+ tree is a map from keys to messages.

Index nodes have n - 1 pivots and n child nodes.
The pivots are strictly sorted and partition the key space into n key ranges:
(-infinity, pivots[0]), [pivots[0], pivots[1]), ..., [pivots[n-3], pivots[n-2]), [pivots[n-2], infinity).
Each child node owns one key range, in order:
children[i] owns range [pivots[i-1], pivots[i]) where pivots[-1] = -infinity, pivots[n] = infinity.

    Example:
    pivots =      p0  p1  p2
    children =  c0  c1  c2  c3

    c0 range = (-infinity, p0)
    c1 range = [p0, p1)
    c2 range = [p1, p2)
    c3 range = [p2, infinity)

Leaf nodes store a map from keys to messages.
keys[i] maps to msgs[i].
*/
pub enum Node {
    Index{pivots: Seq<Key>, children: Seq<Node>},
    Leaf{keys: Seq<Key>, msgs: Seq<Message>}
}

impl Node {
    /// Returns the set of pivots this node contains (empty set if
    /// self is Leaf).
    /// 
    /// Wrote this function to return a set instead of a seq to follow
    /// the precedent created by all_keys (which returns a set).
    pub open spec(checked) fn get_pivots(self) -> Set<Key>
    {
        match self {
            Node::Leaf{keys, msgs} => {
                Set::empty()
            },
            Node::Index{pivots, children} => {
                pivots.to_set()
            }
        }
    }

    /// Returns the set of all keys contained under this node.
    /// - For leaf nodes this is just all keys the leaf node contains.
    /// - For index nodes, this is the set union of all pivot keys + keys contained
    ///   under all leaf nodes under this index node.
    pub open spec(checked) fn all_keys(self) -> Set<Key>
        decreases self
    {
        match self {
            Node::Leaf{keys, msgs} => keys.to_set(),
            Node::Index{pivots, children} => {
                let pivotKeys = pivots.to_set();
                let indexKeys = Set::new(|key| 
                    exists |i| 0 <= i < children.len() 
                    && (#[trigger] children[i]).all_keys().contains(key));
                pivotKeys + indexKeys
            }
        }
    }

    /// Pre: self must be an Index node
    ///
    /// Returns true iff all keys under node child[i] are less than pivots[i] 
    pub open spec(checked) fn all_keys_below_bound(self, i: int) -> bool
        recommends
            self is Index,
            0 <= i < self->children.len() - 1,
            0 <= i < self->pivots.len()
    {
        forall |key| self->children[i].all_keys().contains(key)
            ==> #[trigger] Key::lt(key, self->pivots[i])
    }

    /// Pre: self must be an Index node
    /// 
    /// Returns true iff all keys under node child[i] are >= pivots[i-1].
    pub open spec(checked) fn all_keys_above_bound(self, i: int) -> bool
        recommends
            self is Index,
            0 <= i < self->children.len(),
            0 <= i - 1 < self->pivots.len()
    {
        forall |key| self->children[i].all_keys().contains(key)
            ==> #[trigger] Key::lte(self->pivots[i-1], key)
    }

    /// Returns true iff self is a well-formed B+ tree node.
    pub open spec(checked) fn wf(self) -> bool
        decreases self
    {
        match self {
            // Leaf nodes store key-value pairs sorted by key.
            Node::Leaf{keys, msgs} => {
                &&& keys.len() > 0
                &&& keys.len() == msgs.len()
                &&& Key::is_strictly_sorted(keys)
            },
            // For a well-formed tree, all pivots are unique and strictly sorted if we do an in-order traversal.
            // This ensures that no child has an empty domain.
            Node::Index{pivots, children} => {
                // The pivots go between the children, thus |pivots| == |children| - 1.
                &&& pivots.len() == children.len() - 1
                &&& Key::is_strictly_sorted(pivots)
                &&& forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).wf()
                &&& forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).all_keys().finite()
                &&& forall |i| 0 <= i < children.len() ==> !(#[trigger] children[i]).all_keys().is_empty()
                // For children[0:-1], all keys they contain should be < their upper pivot.
                // This also gives us that children[i]'s pivots are < pivots[i] (if children are index nodes)
                &&& forall |i| 0 <= i < children.len() - 1 ==> self.all_keys_below_bound(i)
                // For children[1:], all keys they contain should be >= their lower pivot.
                &&& forall |i| 0 < i < children.len() ==> self.all_keys_above_bound(i)
            }
        }
    }

    /// Returns the index before where the key would be inserted into the given node.
    /// Let `r` be the return value.
    /// If self is Index, then `r + 1` is the index of the child node that `key` belongs
    /// to.
    /// If self is Node, then `r + 1` is the index `key` would be inserted into. (Note that
    /// in practice we don't allow duplicate keys, so if `key` is already in the sequence,
    /// we'd just update the value at `r`).
    pub open spec(checked) fn route(self, key: Key) -> int
        recommends self.wf()
    {
        // (tenzinhl): this notion of `route` returning values in the range [-1, |pivots| - 1) is
        // very strange, would be much more natural to have it return [0, |pivots|) (then that means
        // it returns the actual child index you would expect to find key under). Currently we keep having
        // to add 1 everywhere.
        let s = if self is Leaf { self->keys } else { self->pivots };
        Key::largest_lte(s, key)
    }

    /// Returns the Message mapped to the given key.
    pub open spec/*XXX (checked)*/ fn query(self, key: Key) -> Message
        recommends self.wf()
        decreases self
        when self is Index ==> 0 <= self.route(key)+1 < self->children.len()
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

    /// Pre: self is a Leaf node.
    /// Returns a new Leaf node where the key-message pair {key, msg} is inserted into
    /// self.
    pub open spec/* XXX (checked)*/ fn insert_leaf(self, key: Key, msg: Message) -> Node
        recommends
            self is Leaf,
            self.wf()
    {
        // Need largest_lte ensures to restore checked
        let llte = Key::largest_lte(self->keys, key);
        if 0 <= llte && self->keys[llte] == key {
            Node::Leaf{
                keys: self->keys, 
                msgs: self->msgs.update(llte, msg)
            }
        } else {
            Node::Leaf{
                keys: self->keys.insert(llte+1, key),
                msgs: self->msgs.insert(llte+1, msg)
            }
        }
    }

    /// Pre: path.node == self && path.target is Leaf
    /// 
    /// Returns a new tree rooted at self where {key, msg} is inserted at the Leaf node
    /// targeted by `path`.
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

    /// Returns a new tree formed by creating a new Index node who's only child is self.
    pub open spec(checked) fn grow(self) -> Node
        recommends self.wf()
    {
        Node::Index{pivots: seq![], children: seq![self]}
    }

    /// Update the empty Leaf node targeted by the `path` (which starts at self) to have the key-value pairs
    /// specified by `keys` and `msgs`.
    pub open spec(checked) fn append(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path) -> Node
        recommends
            self.wf(),
            path.valid(),
            path.node == self,
            keys.len() > 0,
            keys.len() == msgs.len(),
            Key::is_strictly_sorted(keys),
            path.target() is Leaf,
            path.target().wf(), // comes from path.valid(), but not having this here causes recommendation not met
            Key::lt(path.target()->keys.last(), keys[0]),
            path.key == keys[0],
            path.path_equiv(keys.last()) // all new keys must route to the same location
    {
        path.substitute(Node::Leaf{ keys: path.target()->keys + keys, msgs: path.target()->msgs + msgs })
    }

    /// Pre: self is Leaf
    /// 
    /// Returns two leaf nodes formed by splitting `self` into two Leaf nodes, where
    /// the left node contains all keys < `split_arg`, and right node contains all keys
    /// >= `split_arg`.
    pub open spec(checked) fn split_leaf(self, split_arg: SplitArg) -> (Node, Node)
        recommends
            self is Leaf,
            split_arg.wf(self)
    {
        let pivot = split_arg.get_pivot();
        let split_index = Key::largest_lt(self->keys, pivot) + 1;
        let left_leaf = Node::Leaf{
            keys: self->keys.take(split_index),
            msgs: self->msgs.take(split_index)
        };
        let right_leaf = Node::Leaf{
            keys: self->keys.skip(split_index),
            msgs: self->msgs.skip(split_index)
        };
        (left_leaf, right_leaf)
    }

    /// Pre: self is Index
    /// 
    /// Returns a new Index node formed by taking self.children[from:to] and all pivots that divide
    /// those children.
    pub open spec(checked) fn sub_index(self, from: int, to: int) -> Node
        recommends
            self is Index,
            self->children.len() == self->pivots.len() + 1,
            0 <= from < to <= self->children.len()
    {
        Node::Index{ pivots: self->pivots.subrange(from, to-1), children: self->children.subrange(from, to) }
    }

    /// Pre: self is Index
    /// 
    /// Returns two new index nodes that partition `self.children` such that the left node only contains
    /// children with keys < split_arg.key, and right node only contains children with keys >= split_arg.key.
    /// 
    /// Example:
    /// pivots =     [p0  p1  p2]
    /// children = [c0  c1  c2  c3]
    /// pivot index = 2
    /// 
    /// left pivots =     [p0  p1]
    /// left children = [c0  c1  c2]
    /// 
    /// right pivots =        []
    /// right children =    [c3]
    pub open spec/*XXX (checked)*/ fn split_index(self, split_arg: SplitArg) -> (Node, Node)
        recommends
            self is Index,
            split_arg.wf(self)
    {
        // Assert split_arg.wf(self) ==> self.wf() ==>
        // self->children.len() == self->pivots.len() + 1
        // to restore checked
        let pivot_index = split_arg.arrow_SplitIndex_pivot_index();
        let left_index = self.sub_index(0, pivot_index + 1);
        let right_index = self.sub_index(pivot_index + 1, self->children.len() as int);
        (left_index, right_index)
    }

    /// Return two nodes created by splitting self based on the `split_arg`.
    pub open spec(checked) fn split_node(self, split_arg: SplitArg) -> (Node, Node)
        recommends split_arg.wf(self)
    {
        if (self is Leaf) {
            self.split_leaf(split_arg)
        } else {
            self.split_index(split_arg)
        }
    }

    /// Returns true iff self is an Index node and can be split with the provided split_arg 
    /// (split_arg.wf() with respect to `self.children[r+1]`).
    pub open spec/* XXX (checked)*/ fn can_split_child_of_index(self, split_arg: SplitArg) -> bool
    {
        &&& self.wf()
        &&& self is Index
        &&& {
            // Need route ensures to restore checked
            let child_idx = self.route(split_arg.get_pivot()) + 1;
            split_arg.wf(self->children[child_idx])
            }
    }

    /// Pre: self is Index
    /// 
    /// Returns a new Index node where the child containing `split_arg.pivot` is split on said pivot.
    /// The pivot arg can NOT be an existing pivot in the Index (because duh, otherwise you'd have two
    /// pivots with the same value, the bucket between them would be empty which is dumb).
    /// This adds a new pivot value to self.
    pub open spec/* XXX (checked)*/ fn split_child_of_index(self, split_arg: SplitArg) -> Node
        recommends self.can_split_child_of_index(split_arg)
    {
        // Need route ensures to restore checked
        let pivot = split_arg.get_pivot();
        let child_idx = self.route(pivot) + 1;
        let (left_node, right_node) = self->children[child_idx].split_node(split_arg);
        Node::Index{
            pivots: self->pivots.insert(child_idx, pivot),
            children: self->children
                .update(child_idx, left_node)
                .insert(child_idx + 1, right_node)
        }
    }

    /// Returns a new tree formed by splitting the children of `path.target()` on split_arg.
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
}

/// A `Path` describes a target node from a given starting node (using a key to target as well
/// as a number of steps to take).
#[verifier::ext_equal]
pub struct Path {
    /// The current node.
    pub node: Node,
    /// The target key of the path (does change across subpaths).
    pub key: Key,
    /// How many steps remain. If 0, then `node` is the target node of the path.
    pub depth: nat,
}

impl Path {
    /// Returns the next `Path`.
    pub open spec/* XXX (checked)*/ fn subpath(self) -> Path
        recommends
            0 < self.depth,
            self.node.wf(),
            self.node is Index
    {
        // (x9du) Need route ensures to restore `(checked)` annotation on function.
        Path{
            node: self.node->children[self.node.route(self.key) + 1],
            key: self.key,
            depth: (self.depth - 1) as nat
        }
    }

    /// Returns `true` iff self is a valid Path.
    pub open spec(checked) fn valid(self) -> bool
        decreases self.depth
    {
        &&& self.node.wf()
        &&& 0 < self.depth ==> self.node is Index
        &&& 0 < self.depth ==> self.subpath().valid()
    }

    /// Returns Node targeted by a path (i.e.: the last path element).
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

    /// Returns the Seq of children for self.node when `self.target` is replaced with `replacement`.
    pub open spec/* XXX (checked)*/ fn replaced_children(self, replacement: Node) -> Seq<Node>
        recommends
            self.valid(),
            0 < self.depth
        decreases self.subpath().depth
    {
        // (x9du) Need route ensures to restore (checked) annotation on function.
        let new_child = self.subpath().substitute(replacement);
        self.node->children.update(self.node.route(self.key) + 1, new_child)
    }

    /// Returns the tree rooted at self.node, where self.target() is replaced with `replacement`.
    pub open spec(checked) fn substitute(self, replacement: Node) -> Node
        recommends self.valid()
        decreases self.depth, 1nat
    {
        if 0 == self.depth {
            replacement
        } else {
            Node::Index{ pivots: self.node->pivots, children: self.replaced_children(replacement) }
        }
    }

    /// Returns true iff `other_key` leads to the same target node as `self.key`.
    pub open spec(checked) fn path_equiv(self, other_key: Key) -> bool
        recommends self.valid()
        decreases self.depth, 1nat
    {
        &&& self.node.route(self.key) == self.node.route(other_key)
        &&& 0 < self.depth ==> self.subpath().path_equiv(other_key)
    }
}

}
