// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::Memtable_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {
// This is a functional model of a Betree, but it doesn't require that child
// maps be stored as contiguous ranges separated by a finite sets of pivots.
// That's complexity that we push down a layer, to the PivotBetree. Here,
// instead, we have a child for every possible key, as though every key is a
// pivot. That's not *exactly* right, since adjacent children
// (in fact, infinite ranges of adjacent children) will be identical:
// children for keys 40..70 may all carry (identical) buffer including
// keys in [40..70), since of course they're represented by the same node
// in PivotBetree, the next layer down the refinement stack.
//
// This trickiness mostly appears in the Path Substitution code, which has
// to decide which of the infinity children are getting replaced -- the answer
// depends on how the PivotBetree has decided to divvy up the child pointers.


pub type StampedBetree = Stamped<BetreeNode>;

pub open spec(checked) fn empty_image() -> StampedBetree {
    Stamped{ value: BetreeNode::Nil, seq_end: 0 }
}

#[verifier::ext_equal]
pub struct ChildMap{ 
    pub map: Map<Key, BetreeNode> 
}

pub open spec(checked) fn constant_child_map(target: BetreeNode) -> ChildMap {
    ChildMap{ map: Map::new( |k| true, |k| target ) }
}

impl ChildMap {
    pub open spec(checked) fn wf(self) -> bool
    decreases self
    {
        &&& total_keys(self.map.dom())
        &&& forall |k: Key| #![auto] self.map[k].wf()
    }
}


pub open spec(checked) fn empty_child_map() -> ChildMap {
    constant_child_map(BetreeNode::Nil)
}

#[verifier::ext_equal]
pub enum BetreeNode {
    Nil,
    Node{ 
        buffer: Buffer,
        children: ChildMap},
}

impl BetreeNode {
    pub open spec(checked) fn wf(self) -> bool
    decreases self
    {
        self is Node ==> self->children.wf()
    }

    pub open spec(checked) fn child(self, key: Key) -> BetreeNode
    recommends
        self.wf(),
        self is Node,
    {
        self->children.map[key]
    }

    pub open spec(checked) fn empty_root() -> BetreeNode {
        BetreeNode::Node {
            buffer: Buffer::empty(),
            children: empty_child_map()
        }
    }

    pub open spec(checked) fn promote(self) -> BetreeNode {
        if self is Nil {
            Self::empty_root() 
        } else {
            self
        }
    }

    pub open spec(checked) fn merge_buffer(self, new_buffer: Buffer) -> BetreeNode {
        BetreeNode::Node{
            buffer: self->buffer.merge(new_buffer),
            children: self->children,
        }
    }

    pub open spec(checked) fn push_memtable(self, memtable: Memtable) -> StampedBetree {
        Stamped{
            value: self.promote().merge_buffer(memtable.buffer),
            seq_end: memtable.seq_end
        }
    }

    pub open spec(checked) fn filter_buffer_and_children(self, filter: Set<Key>) -> BetreeNode {
        if self is Nil {
            self
        } else {
            let filtered_children = ChildMap {
                map: Map::new( |k| true, |k| if filter.contains(k) { self->children.map[k] } else { BetreeNode:: Nil } )
            };
            BetreeNode::Node {
                buffer: self->buffer.apply_filter(filter),
                children: filtered_children,
            }
        }
    }

    pub open spec(checked) fn split(self, left_keys: Set<Key>, right_keys: Set<Key>) -> BetreeNode {
        // We suppose that a lower layer will use this when leftKeys+rightKeys are all
        // identical, so that the first two branches of the if expression each produce
        // a single BetreeNode (with a shared representation below).
        let map = Map::new( |k| true, |k| 
                if left_keys.contains(k) {self.child(k).filter_buffer_and_children(left_keys)} 
                else if right_keys.contains(k) {self.child(k).filter_buffer_and_children(right_keys)} 
                else {self.child(k)});
        BetreeNode::Node {
            buffer: self->buffer,
            children: ChildMap{ map }
        }
    }

    pub open spec(checked) fn flush(self, down_keys: Set<Key>) -> BetreeNode {
        let kept_buffer = self->buffer.apply_filter(all_keys().difference(down_keys));
        let moved_buffer = self->buffer.apply_filter(down_keys);
        let out_children_map = Map::new( |k| true, |k| 
            if down_keys.contains(k) {self.child(k).promote().merge_buffer(moved_buffer)}
            else {self.child(k)}
        );
        BetreeNode::Node {
            buffer: kept_buffer,
            children: ChildMap{ map: out_children_map}
        }
    }
} // end impl BetreeNode



pub struct QueryReceiptLine {
    pub node: BetreeNode,
    pub result: Message,
}

impl QueryReceiptLine {
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.node.wf()
        &&& self.result.is_Define()
    }
} //end impl QueryReceiptLine

// NB the top line is the line for the root node; hence Result()==ResultAt(0)
// The bottom line is always Nil
// #[verifier::ext_equal]
pub struct QueryReceipt {
    pub key: Key,
    pub root: BetreeNode,
    pub lines: Seq<QueryReceiptLine>,
}

impl QueryReceipt {
    pub open spec(checked) fn structure(self) -> bool {
        &&& 0 < self.lines.len()
        &&& self.lines[0].node == self.root
        &&& (forall |i| #![auto] 0 <= i < self.lines.len() ==> (
            self.lines[i].node is Node <==> i < self.lines.len() - 1
        ))
        &&& self.lines.last().result == Message::empty()
    }

    pub open spec(checked) fn all_lines_wf(self) -> bool {
        forall |i| #![auto] 0 <= i < self.lines.len() ==> self.lines[i].wf()
    }

    pub open spec(checked) fn child_at(self, i: int) -> BetreeNode 
        recommends 
            self.all_lines_wf(),
            self.structure(),
            0 <= i < self.lines.len() - 1,
    {
        self.lines[i].node.child(self.key)
    }

    pub open spec(checked) fn child_linked_at(self, i: int) -> bool 
        recommends 
            self.all_lines_wf(),
            self.structure(),
            0 <= i < self.lines.len() - 1,
    {
        self.lines[i+1].node == self.child_at(i)
    }

    pub open spec(checked) fn result_at(self, i: int) -> Message 
        recommends 0 <= i < self.lines.len()
    {
        self.lines[i].result
    }

    pub open spec(checked) fn result_linked_at(self, i: int) -> bool 
        recommends 
            self.all_lines_wf(),
            self.structure(),
            0 <= i < self.lines.len() - 1,
    {
        let msg = self.lines[i].node->buffer.query(self.key);
        self.result_at(i) == self.result_at(i+1).merge(msg)
    }

    pub open spec(checked) fn valid(self) -> bool {
        &&& self.structure()
        &&& self.all_lines_wf()
        &&& (forall |i| #![auto] 0 <= i < self.lines.len()-1 ==> self.child_linked_at(i))
        &&& (forall |i| #![auto] 0 <= i < self.lines.len()-1 ==> self.result_linked_at(i))
    }

    pub open spec(checked) fn result(self) -> Message 
        recommends self.structure()
    {
        self.result_at(0)
    }

    pub open spec(checked) fn valid_for(self, root: BetreeNode, key: Key) -> bool {
        &&& self.valid()
        &&& self.root == root
        &&& self.key == key
    }
} // end impl QueryReceipt


pub struct Path {
    pub node: BetreeNode,
    pub key: Key,
    pub routing: Seq<Set<Key>>,
}

impl Path {
    pub open spec(checked) fn subpath(self) -> Path 
    recommends 
        0 < self.routing.len(),
        self.node.wf(),
        self.node is Node,
    {
        Path{node: self.node.child(self.key), key: self.key, routing: self.routing.subrange(1, self.routing.len() as int)}
    }

    pub open spec(checked) fn common_children(self) -> bool
    recommends
        self.node.wf(),
        self.node is Node,
        0 < self.routing.len(),
    {
        forall |k: Key| #![auto] self.routing.index(0).contains(k) ==> self.node.child(k) == self.node.child(self.key)
    }

    pub open spec(checked) fn valid(self) -> bool 
    decreases self.routing.len()
    {
        &&& self.node.wf()
        &&& self.node is Node
        &&& 0 < self.routing.len() ==> {
            &&& self.subpath().valid()
            &&& self.common_children()
        }
    }

    pub open spec(checked) fn target(self) -> BetreeNode 
    recommends self.valid()
    decreases self.routing.len()
    {
        if self.routing.len() == 0 {
            self.node
        } else {
            self.subpath().target()
        }
    }

    pub open spec(checked) fn replaced_children(self, replacement: BetreeNode) -> ChildMap
    recommends
        self.valid(),
        replacement.wf(),
        0 < self.routing.len(),
    decreases
        self.subpath().routing.len()
    {
        let replaced_child = self.subpath().substitute(replacement);
        ChildMap{
            map: Map::new( |k| true, |k| if self.routing.index(0).contains(k) {replaced_child} else { self.node.child(k)} )
        }
    }

    pub open spec(checked) fn substitute(self, replacement: BetreeNode) -> BetreeNode 
    recommends 
        self.valid(),
        replacement.wf(),
    decreases
        self.routing.len(), 1nat
    {
        if self.routing.len() == 0 {
            replacement
        } else {
            BetreeNode::Node{
                buffer: self.node->buffer,
                children: self.replaced_children(replacement)
            }
        }
    }
} //end impl Path


state_machine!{ PagedBetree {
    fields {
        pub memtable: Memtable,
        pub root: BetreeNode,
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.root.wf()
    }

    pub enum Label
    {
        Query{end_lsn: LSN, key: Key, value: Value},
        Put{puts: MsgHistory},
        FreezeAs{stamped_betree: StampedBetree},
        Internal{},   // Local No-op label
    }

    transition!{ query(lbl: Label, receipt: QueryReceipt) {
        require let Label::Query{end_lsn, key, value} = lbl;
        require end_lsn == pre.memtable.seq_end;
        require receipt.valid_for(pre.root, key);
        require Message::Define{value} == receipt.result().merge(pre.memtable.query(key));
    }}

    transition!{ put(lbl: Label) {
        require let Label::Put{puts} = lbl;
        require puts.wf();
        require puts.seq_start == pre.memtable.seq_end;
        update memtable = pre.memtable.apply_puts(puts);
    }}

    transition!{ freeze_as(lbl: Label) {
        require let Label::FreezeAs{stamped_betree} = lbl;
        require pre.wf();
        require pre.memtable.is_empty();
        require stamped_betree == Stamped{value: pre.root, seq_end: pre.memtable.seq_end};
    }}

    transition!{ internal_flush_memtable(lbl: Label) {
        require let Label::Internal{} = lbl;
        require pre.wf();
        update memtable = pre.memtable.drain();
        update root = pre.root.push_memtable(pre.memtable).value;
    }}

    transition!{ internal_grow(lbl: Label) {
        require let Label::Internal{} = lbl;
        require pre.wf();
        update root = BetreeNode::Node{
            buffer: Buffer::empty(),
            children: constant_child_map(pre.root)
        };
    }}

    transition!{ internal_split(lbl: Label, path: Path, left_keys: Set<Key>, right_keys: Set<Key>) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path.node == pre.root;
        update root = path.substitute(path.target().split(left_keys, right_keys));
    }}

    transition!{ internal_flush(lbl: Label, path: Path, down_keys: Set<Key>) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path.node == pre.root;
        update root = path.substitute(path.target().flush(down_keys));
    }}

    transition!{ internal_noop(lbl: Label) {
        require let Label::Internal{} = lbl;
        require pre.wf();
    }}

    init!{ initialize(stamped_betree: StampedBetree) {
        require stamped_betree.value.wf();
        init memtable = Memtable::empty_memtable(stamped_betree.seq_end);
        init root = stamped_betree.value;
    }}
}} // end PagedBetree state machine



} // end verus!
