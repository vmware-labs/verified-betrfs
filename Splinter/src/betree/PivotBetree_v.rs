// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {
// This is a functional model of a Betree with nodes with pivot table

pub type StampedBetree = Stamped<BetreeNode>;

pub open spec(checked) fn empty_image() -> StampedBetree {
    Stamped{ value: BetreeNode::Nil, seq_end: 0 }
}

#[verifier::ext_equal]
pub enum BetreeNode {
    Nil,
    Node{
        buffer: SimpleBuffer,
        pivots: PivotTable,
        children: Seq<BetreeNode>
    },
}

impl BetreeNode {
    pub open spec(checked) fn local_structure(self) -> bool
    {
        &&& self is Node ==> {
            &&& self->pivots.wf()
            &&& self->children.len() == self->pivots.num_ranges()
        }
    }

    pub open spec(checked) fn valid_child_index(self, child_idx: nat) -> bool
    {
        &&& self is Node
        &&& child_idx < self->children.len()
    }

    pub open spec(checked) fn my_domain(self) -> Domain
    recommends
        self.local_structure(),
        self is Node,
    {
        let _ = spec_affirm(0 < self->pivots.num_ranges());
        Domain::Domain{
            start: self->pivots.pivots[0],
            end: self->pivots.pivots.last()
        }
    }

    // equivalent to DomainRoutedToChild
    pub open spec(checked) fn child_domain(self, child_idx: nat) -> Domain
    recommends
        self.local_structure(),
        self is Node,
        0 <= child_idx < self->children.len(),
    {
        Domain::Domain{
            start: self->pivots.pivots[child_idx as int],
            end: self->pivots.pivots[child_idx as int + 1]
        }
    }

    pub open spec(checked) fn linked_children(self) -> bool
    recommends
        self.local_structure(), self is Node
    {
       &&& forall |i|
        ( 
            (#[trigger] self.valid_child_index(i))
            && self->children[i as int] is Node
            && self->children[i as int].local_structure() 
        ) ==> {
            self->children[i as int].my_domain() == self.child_domain(i)
        }
    }

    pub open spec(checked) fn wf_children(self) -> bool
        recommends self is Node
        decreases self, 0nat when self is Node
    {
        &&& (forall |i| #[trigger] self.valid_child_index(i)
            ==> self->children[i as int].wf())
    }

    pub open spec(checked) fn wf(self) -> bool
        decreases self, 1nat
    {
        &&& self.local_structure()
        &&& self is Node ==> {
            &&& self.wf_children()
            &&& self.linked_children()
        }
    }

    pub open spec(checked) fn merge_buffer(self, new_buffer: SimpleBuffer) -> BetreeNode
        recommends self is Node
    {
        BetreeNode::Node{
            buffer: self->buffer.merge(new_buffer),
            pivots: self->pivots,
            children: self->children
        }
    }

    pub open spec(checked) fn push_memtable(self, memtable: Memtable<SimpleBuffer>) -> BetreeNode
    recommends self.wf()
    {
        self.promote(total_domain()).merge_buffer(memtable.buffer)
    }

    pub open spec(checked) fn is_leaf(self) -> bool
    {
        &&& self is Node
        &&& self->children.len() == 1
        &&& self->children[0] is Nil
    }

    pub open spec(checked) fn is_index(self) -> bool
    {
        &&& self is Node
        &&& forall |i| #[trigger] self.valid_child_index(i) ==> self->children[i as int] is Node
    }

    pub open spec(checked) fn can_split_leaf(self, split_key: Key) -> bool
    {
        &&& self.wf()
        &&& self.is_leaf()
        &&& self.my_domain().contains(split_key)
        &&& self.my_domain()->start != to_element(split_key)
    }

    pub open spec(checked) fn split_leaf(self, split_key: Key) -> (BetreeNode, BetreeNode)
        recommends self.can_split_leaf(split_key)
    {
        let left_filter = Domain::Domain{ start: self.my_domain()->start, end: to_element(split_key) };
        let right_filter = Domain::Domain{ start: to_element(split_key), end: self.my_domain()->end };

        let new_left = BetreeNode::Node{
            buffer: self->buffer.apply_filter(left_filter.key_set()),
            pivots: self->pivots.update(1, to_element(split_key)),
            children: self->children
        };

        let new_right = BetreeNode::Node{
            buffer: self->buffer.apply_filter(right_filter.key_set()),
            pivots: self->pivots.update(0, to_element(split_key)),
            children: self->children
        };

        (new_left, new_right)
    }

    pub open spec(checked) fn can_split_index(self, pivot_idx: nat) -> bool
    {
        &&& self.wf()
        &&& self.is_index()
        &&& 0 < pivot_idx < self->pivots.num_ranges()
    }

    pub open spec(checked) fn  split_index(self, pivot_idx: nat) -> (BetreeNode, BetreeNode)
        recommends self.can_split_index(pivot_idx)
    {
        let split_element = self->pivots.pivots[pivot_idx as int];
        let left_filter = Domain::Domain{ start: self.my_domain()->start, end: split_element };
        let right_filter = Domain::Domain{ start: split_element, end: self.my_domain()->end };

        let new_left = BetreeNode::Node{
            buffer: self->buffer.apply_filter(left_filter.key_set()),
            pivots: self->pivots.subrange(0, pivot_idx as int +1),
            children: self->children.subrange(0, pivot_idx as int)
        };

        let new_right = BetreeNode::Node{
            buffer: self->buffer.apply_filter(right_filter.key_set()),
            pivots: self->pivots.subrange(pivot_idx as int, self->pivots.len() as int),
            children: self->children.subrange(pivot_idx as int, self->children.len() as int)
        };

        (new_left, new_right)
    }

    pub open spec(checked) fn can_split_parent(self, request: SplitRequest) -> bool
    {
        &&& self.wf()
        &&& self is Node
        &&& match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                &&& self.valid_child_index(child_idx)
                &&& self->children[child_idx as int].can_split_leaf(split_key)
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                &&& self.valid_child_index(child_idx)
                &&& self->children[child_idx as int].can_split_index(child_pivot_idx)
            }
        }
    }

    pub open spec(checked) fn split_parent(self, request: SplitRequest) -> BetreeNode
        recommends self.can_split_parent(request)
    {
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                let idx = child_idx as int;
                let old_child = self->children[idx];
                let (new_left_child, new_right_child) = old_child.split_leaf(split_key);

                BetreeNode::Node{
                    buffer: self->buffer,
                    pivots: self->pivots.insert(idx+1, to_element(split_key)),
                    children: self->children.update(idx, new_left_child).insert(idx+1, new_right_child)
                }
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                let idx = child_idx as int;
                let old_child = self->children[idx];
                let (new_left_child, new_right_child) = old_child.split_index(child_pivot_idx);
                let split_element = old_child->pivots.pivots[child_pivot_idx as int];

                BetreeNode::Node{
                    buffer: self->buffer,
                    pivots: self->pivots.insert(idx+1, split_element),
                    children: self->children.update(idx, new_left_child).insert(idx+1, new_right_child)
                }
            }
        }
    }

    pub open spec(checked) fn empty_root(domain: Domain) -> BetreeNode
        recommends domain.wf(), domain is Domain
    {
        BetreeNode::Node{
            buffer: SimpleBuffer::empty(),
            pivots: domain_to_pivots(domain),
            children: seq![BetreeNode::Nil]
        }
    }

    pub open spec(checked) fn grow(self) -> BetreeNode
    {
        BetreeNode::Node{
            buffer: SimpleBuffer::empty(),
            pivots: domain_to_pivots(total_domain()),
            children: seq![self]
        }
    }

    pub open spec(checked) fn promote(self, domain: Domain) -> BetreeNode
    recommends
        self.wf(),
        domain.wf(),
        domain is Domain,
    {
        if self is Nil {
            BetreeNode::empty_root(domain)
        } else {
            self
        }
    }

    pub open spec(checked) fn can_flush(self, child_idx: nat) -> bool
    {
        &&& self.wf()
        &&& self is Node
        &&& self.valid_child_index(child_idx)
    }

    pub open spec /*XXX(checked)*/ fn flush(self, child_idx: nat) -> BetreeNode
        recommends self.can_flush(child_idx)
    {
        let child_domain = self.child_domain(child_idx);
        let keep_keys = all_keys().difference(child_domain.key_set());
        let kept_buffer = self->buffer.apply_filter(keep_keys);
        let moved_buffer = self->buffer.apply_filter(child_domain.key_set());

        let old_child = self->children[child_idx as int];
        //XXX promote ensures wf
        let new_child = old_child.promote(child_domain).merge_buffer(moved_buffer);

        BetreeNode::Node{
            buffer: kept_buffer,
            pivots: self->pivots,
            children: self->children.update(child_idx as int, new_child)
        }
    }

    pub open spec(checked) fn key_in_domain(self, key: Key) -> bool
    {
        &&& self.wf()
        &&& self is Node
        &&& self->pivots.bounded_key(key)
    }

    pub open spec /*XXX(checked)*/ fn child(self, key: Key) -> BetreeNode
    recommends
        self.wf(),
        self is Node,
        self.key_in_domain(key),
    {
        //XXX self->pivots.route_lemma(key)
        self->children[self->pivots.route(key)]
    }
} // end impl BetreeNode

pub struct QueryReceiptLine{
    pub node: BetreeNode,
    pub result: Message
}

impl QueryReceiptLine{
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.node.wf()
        &&& self.result is Define
    }
} // end impl QueryReceiptLine

pub struct QueryReceipt{
    pub key: Key,
    pub root: BetreeNode,
    pub lines: Seq<QueryReceiptLine>
}

impl QueryReceipt{
    pub open spec(checked) fn structure(self) -> bool
    {
        &&& 0 < self.lines.len()
        &&& self.lines[0].node == self.root
        &&& (forall |i| #![auto] 0 <= i < self.lines.len() ==> {
            self.lines[i].node is Node <==> i < self.lines.len()-1
        })
        &&& self.lines.last().result == Message::Define{value: default_value()}
    }

    pub open spec(checked) fn all_lines_wf(self) -> bool
    {
        &&& (forall |i| #![auto] 0 <= i < self.lines.len() ==> self.lines[i].wf())
        &&& (forall |i| #![auto] 0 <= i < self.lines.len()-1 ==> self.lines[i].node.key_in_domain(self.key))
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
        0 <= i < self.lines.len()-1,
    {
        self.lines[i+1].node == self.child_at(i)
    }

    pub open spec(checked) fn result_at(self, i: int) -> Message
        recommends 0 <= i < self.lines.len()
    {
        self.lines[i].result
    }

    pub open spec(checked) fn result_linked_at(self, i:int) -> bool
    recommends
        self.all_lines_wf(),
        self.structure(),
        0 <= i < self.lines.len()-1,
    {
        let msg = self.lines[i].node->buffer.query(self.key);
        self.lines[i].result == self.result_at(i+1).merge(msg)
    }

    pub open spec(checked) fn valid(self) -> bool
    {
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

    pub open spec(checked) fn valid_for(self, root: BetreeNode, key: Key) -> bool
    {
        &&& self.valid()
        &&& self.root == root
        &&& self.key == key
    }
} // end impl QueryReceipt

pub struct Path{
    pub node: BetreeNode,
    pub key: Key,
    pub depth: nat
}

impl Path{
    pub open spec(checked) fn subpath(self) -> Path
    recommends
        0 < self.depth,
        self.node.key_in_domain(self.key),
    {
        let depth = (self.depth - 1) as nat;
        Path{node: self.node.child(self.key), key: self.key, depth: depth}
    }

    pub open spec(checked) fn valid(self) -> bool
        decreases self.depth
    {
        &&& self.node.wf()
        &&& self.node.key_in_domain(self.key)
        &&& (0 < self.depth ==> self.node.is_index())
        &&& (0 < self.depth ==> self.subpath().valid())
    }

    pub open spec(checked) fn target(self) -> BetreeNode
    recommends
        self.valid(),
    decreases self.depth
    {
        if self.depth == 0 {
            self.node
        } else {
            self.subpath().target()
        }
    }

    //XXX apply target_ensures
    pub open spec/*XXX(checked)*/ fn can_substitute(self, replacement: BetreeNode) -> bool
    {
        &&& self.valid()
        &&& replacement.wf()
        &&& replacement is Node
        &&& replacement.my_domain() == self.target().my_domain()
    }

    pub open spec /*XXX (checked)*/ fn replaced_children(self, replacement: BetreeNode) -> Seq<BetreeNode>
    recommends
        self.can_substitute(replacement), 
        0 < self.depth
    decreases self.subpath().depth
    {
        let new_child = self.subpath().substitute(replacement);
        let r = self.node->pivots.route(self.key);
        //XXX self->pivots.route_lemma(key)
        self.node->children.update(r, new_child)
    }

    pub open spec(checked) fn substitute(self, replacement: BetreeNode) -> BetreeNode
        recommends self.can_substitute(replacement)
        decreases self.depth, 1nat
    {
        if self.depth == 0 {
            replacement
        } else {
            BetreeNode::Node{
                buffer: self.node->buffer,
                pivots: self.node->pivots,
                children: self.replaced_children(replacement)
            }
        }
    }
} // end impl Path


state_machine!{ PivotBetree {
    fields {
        pub memtable: Memtable<SimpleBuffer>,
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
        update root = pre.root.push_memtable(pre.memtable);
    }}

    transition!{ internal_grow(lbl: Label) {
        require let Label::Internal{} = lbl;
        require pre.wf();
        update root = pre.root.grow();
    }}

    transition!{ internal_split(lbl: Label, path: Path, request: SplitRequest) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path.target().can_split_parent(request);
        require path.node == pre.root;
        update root = path.substitute(path.target().split_parent(request));
    }}

    transition!{ internal_flush(lbl: Label, path: Path, child_idx: nat) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path.target().can_flush(child_idx);
        require path.node == pre.root;
        update root = path.substitute(path.target().flush(child_idx));
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
}} // end PivotBetree state machine


} // end verus!
