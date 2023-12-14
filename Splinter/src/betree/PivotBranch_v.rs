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
}

}
