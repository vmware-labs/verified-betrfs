// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {
// Changes from a single buffer to a stack of buffers, tracks actvie buffers for ranges of keys.
// Includes garbage collection of inactive buffers and compaction of buffers.
// In contrast to the PivotBetree above, upon flushing a buffer down the tree, 
// the FilteredBetree keeps the entire buffer but notes that it should filter out the keys in 
// that buffer for the child to which it was flushed.

pub type StampedBetree = Stamped<BetreeNode>;

pub open spec(checked) fn empty_image() -> StampedBetree {
    Stamped{ value: BetreeNode::Nil, seq_end: 0 }
}

#[verifier::ext_equal]
pub enum BetreeNode {
    Nil,
    Node{
        buffers: BufferSeq,
        pivots: PivotTable,
        children: Seq<BetreeNode>,
        flushed: BufferOffsets // # of buffers flushed to each child
    },
}


impl BetreeNode {
    pub open spec(checked) fn local_structure(self) -> bool
    {
        &&& self is Node ==> {
            &&& self->pivots.wf()
            &&& self->children.len() == self->pivots.num_ranges()
            &&& self->children.len() == self->flushed.len()
            &&& self->flushed.all_lte(self->buffers.len()) // values in flushed are bounded by # of buffers
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
        self.valid_child_index(child_idx),
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
        &&& (forall |i| (#[trigger] self.valid_child_index(i))
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

    pub open spec(checked) fn push_memtable(self, memtable: Memtable) -> BetreeNode
    recommends
        self.wf(),
    {
        let buffers = BufferSeq{buffers: seq![memtable.buffer]};
        self.promote(total_domain()).extend_buffer_seq(buffers)
    }

    pub open spec(checked) fn extend_buffer_seq(self, buffers: BufferSeq) -> BetreeNode
        recommends self is Node
    {
        BetreeNode::Node{
            buffers: self->buffers.extend(buffers),
            pivots: self->pivots,
            children: self->children,
            flushed: self->flushed
        }
    }

    #[verifier(recommends_by)]
    pub proof fn flushed_ofs_inline_lemma(self, key: Key)
    {
        self->pivots.route_lemma(key);
//        assert( 0 <= self->pivots.route(key) < self->flushed.offsets.len() );
    }


    // returns the flushed offset (index into buffers) for a given key
    // buffers flushed to a child are no longer active for that child
    // renamed from ActiveBuffersForKey
    pub open spec /*XXX (checked)*/ fn flushed_ofs(self, key: Key) -> nat
    recommends
        self.key_in_domain(key),
    {
        recommends_by(Self::flushed_ofs_inline_lemma);
        let r = self->pivots.route(key);
        self->flushed.offsets[r]
    }

    pub open spec(checked) fn is_leaf(self) -> bool
    {
        &&& self is Node
        &&& self->children.len() == 1
        &&& self->children[0] is Nil
        &&& self->flushed.len() == 1
        &&& self->flushed.offsets[0] == 0
    }

    pub open spec(checked) fn is_index(self) -> bool
    {
        &&& self is Node
        &&& forall |i| 0 <= i < self->children.len() ==> (#[trigger] self->children[i]) is Node
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
        let new_left = BetreeNode::Node{
            buffers: self->buffers,
            pivots: self->pivots.update(1, to_element(split_key)),
            children: self->children,
            flushed: self->flushed
        };

        let new_right = BetreeNode::Node{
            buffers: self->buffers,
            pivots: self->pivots.update(0, to_element(split_key)),
            children: self->children,
            flushed: self->flushed
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
        let idx = pivot_idx as int;
        let new_left = BetreeNode::Node{
            buffers: self->buffers,
            pivots: self->pivots.subrange(0, idx+1),
            children: self->children.subrange(0, idx),
            flushed: self->flushed.slice(0, idx)
        };

        let new_right = BetreeNode::Node{
            buffers: self->buffers,
            pivots: self->pivots.subrange(idx, self->pivots.len() as int),
            children: self->children.subrange(idx, self->children.len() as int),
            flushed: self->flushed.slice(idx, self->flushed.len() as int)
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
                    buffers: self->buffers,
                    pivots: self->pivots.insert(idx+1, to_element(split_key)),
                    children: self->children.update(idx, new_left_child).insert(idx+1, new_right_child),
                    flushed: self->flushed.dup(idx)
                }
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                let idx = child_idx as int;
                let old_child = self->children[idx];
                let (new_left_child, new_right_child) = old_child.split_index(child_pivot_idx);
                let split_element = old_child->pivots.pivots[child_pivot_idx as int];

                BetreeNode::Node{
                    buffers: self->buffers,
                    pivots: self->pivots.insert(idx+1, split_element),
                    children: self->children.update(idx, new_left_child).insert(idx+1, new_right_child),
                    flushed: self->flushed.dup(idx)
                }
            }
        }
    }

    pub open spec(checked) fn empty_root(domain: Domain) -> BetreeNode
        recommends domain.wf(), domain is Domain
    {
        BetreeNode::Node{
            buffers: BufferSeq::empty(),
            pivots: domain_to_pivots(domain),
            children: seq![BetreeNode::Nil],
            flushed: BufferOffsets{offsets: seq![0]}
        }
    }

    pub open spec(checked) fn grow(self) -> BetreeNode
    {
        BetreeNode::Node{
            buffers: BufferSeq::empty(),
            pivots: domain_to_pivots(total_domain()),
            children: seq![self],
            flushed: BufferOffsets{offsets: seq![0]}
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

    pub open spec(checked) fn can_flush(self, child_idx: nat, buffer_gc: nat) -> bool
    {
        &&& self.wf()
        &&& self is Node
        &&& self.valid_child_index(child_idx)
        &&& self->flushed.update(child_idx as int, 
                self->buffers.len()).all_gte(buffer_gc)
    }

    pub open spec /*XXX (checked)*/ fn flush(self, child_idx: nat, buffer_gc: nat) -> BetreeNode
        recommends self.can_flush(child_idx, buffer_gc)
    {
        let idx = child_idx as int;
        let flush_upto = self->buffers.len(); 
        let flushed_ofs = self->flushed.offsets[idx];
        
        // when we perform a flush to a child, all active buffers for that child (up to the most recent buffer) are flushed
        let buffers_to_child = self->buffers.slice(flushed_ofs as int, flush_upto as int);
        let new_child = self->children[idx].promote(self.child_domain(child_idx)).extend_buffer_seq(buffers_to_child);

        // updates to parent node (self)
        // we take advantage of flush time to optionally garbage collect buffers that are no longer active by all children
        // buffer_gc tells us how many buffers (starting from oldest) we can garbage collect
        let bfrs = self->buffers;
        let start = buffer_gc as int;
        let end = flush_upto as int;
        // TODO(andrea): Interesting that 
        // let _ = spec_affirm(0 <= start <= end <= bfrs.len());
        // didn't satisfy the recommends, but breaking it into 3 separate
        // statements does.
//         let _ = spec_affirm(0 <= start);
//         let _ = spec_affirm(start <= end);
//         let _ = spec_affirm(end <= bfrs.len());
//         let gc_buffers = bfrs.slice(start, end);
        //let _ = spec_affirm(0 <= buffer_gc as int <= flush_upto as int <= self->buffers.len() );
        let gc_buffers = self->buffers.slice(buffer_gc as int, flush_upto as int);
        let gc_flushed = self->flushed.update(idx, flush_upto).shift_left(buffer_gc);

        BetreeNode::Node{
            buffers: gc_buffers,
            pivots: self->pivots,
            children: self->children.update(idx, new_child),
            flushed: gc_flushed
        }
    }

    #[verifier::opaque]
    pub open spec fn valid_compact_key_domain(self, start: nat, end: nat, k: Key) -> bool
        recommends self.wf(), self is Node, start < end <= self->buffers.len()
    {
        &&& self.key_in_domain(k)
        &&& self.flushed_ofs(k) <= end
        &&& exists |buffer_idx| self->buffers.slice(start as int, end as int
            ).key_in_buffer_filtered(self.make_offset_map().decrement(start), 0, k, buffer_idx)
    }

    pub open spec fn can_compact(self, start: nat, end: nat, compacted_buffer: SimpleBuffer) -> bool 
    {
        &&& self.wf()
        &&& self is Node
        &&& start < end <= self->buffers.len()
        &&& forall |k| #[trigger] compacted_buffer.map.contains_key(k) <==> self.valid_compact_key_domain(start, end, k)
        &&& forall |k| compacted_buffer.map.contains_key(k) ==> ({
            let from = if self.flushed_ofs(k) <= start { 0 } else { self.flushed_ofs(k)-start };
            &&& #[trigger] compacted_buffer.query(k) == self->buffers.slice(start as int, end as int).query_from(k, from)
        })
    }

    pub open spec /*XXX(checked)*/ fn compact(self, start: nat, end: nat, compacted_buffer: SimpleBuffer) -> BetreeNode
    recommends
        self.can_compact(start, end, compacted_buffer),
    {
//         let sint = start as int;
//         let eint = end as int;
//         let _ = spec_affirm( 0 as int <= sint );
//         let _ = spec_affirm( sint <= eint );
//         let _ = spec_affirm( eint <= self->flushed.len() as int );
        // XXX (andrea?)
        // Why don't the prior three lines imply the next line?
        // OH! a bunch of type errors after we pass the verification errors
        // (by commenting out checked):
        // error[E0277]: can't compare `{integer}` with `builtin::int`
        // Can't figure out what to do about this one!
        // error[E0605]: non-primitive cast: `builtin::nat` as `builtin::int`
//         let _ = spec_affirm( 0 <= sint <= eint <= self->flushed.len() );
        BetreeNode::Node{
            buffers: self->buffers.update_subrange(start as int, end as int, compacted_buffer),
            pivots: self->pivots,
            children: self->children,
            flushed: self->flushed.adjust_compact(start as int, end as int)
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
        let _ = spec_affirm(self.wf_children());
        self->children[self->pivots.route(key)]
    }

    // NOTE(JL): map needs to be total because we don't know which keys are in the buffer 
    // out of range keys must be buffer len because we use offset map value to start query
    pub open spec(checked) fn make_offset_map(self) -> OffsetMap
    {
        OffsetMap{ offsets: Map::new(|k| true,
            |k| if self.key_in_domain(k) {
                self.flushed_ofs(k)
            } else {
                self->buffers.len()
            })
        }
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
        &&& forall |i:nat| i < self.lines.len() ==> {
            (#[trigger] self.lines[i as int].node is Node) <==> i < self.lines.len()-1
        }
        &&& self.lines.last().result == Message::Define{value: default_value()}
    }

    pub open spec(checked) fn all_lines_wf(self) -> bool
    {
        &&& forall |i| 0 <= i < self.lines.len() 
            ==> (#[trigger] self.lines[i]).wf()
        &&& forall |i| 0 <= i < self.lines.len()-1 
            ==> #[trigger] self.lines[i].node.key_in_domain(self.key)
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
        self.lines[i + 1].node == self.child_at(i)
    }

    pub open spec(checked) fn result_at(self, i: int) -> Message
        recommends 0 <= i < self.lines.len()
    {
        self.lines[i].result
    }

    pub open spec /*XXX(checked)*/ fn result_linked_at(self, i: int) -> bool
    recommends
        self.structure(),
        self.all_lines_wf(),
        0 <= i < self.lines.len()-1,
    {
        let start = self.lines[i].node.flushed_ofs(self.key);
        //XXX let _ = spec_affirm(start as int <= self.lines[i].node->buffers
        let msg = self.lines[i].node->buffers.query_from(self.key, start as int);
        self.lines[i].result == self.result_at(i+1).merge(msg)
    }

    pub open spec(checked) fn valid(self) -> bool
    {
        &&& self.structure()
        &&& self.all_lines_wf()
        &&& (forall |i| 0 <= i < self.lines.len()-1 ==> #[trigger] self.child_linked_at(i))
        &&& (forall |i| 0 <= i < self.lines.len()-1 ==> #[trigger] self.result_linked_at(i))
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
    // ensures out.wf(), out is Node,
    decreases self.depth
    {
        if self.depth == 0 {
            self.node
        } else {
            self.subpath().target()
        }
    }

    pub open spec /*XXX (checked)*/ fn can_substitute(self, replacement: BetreeNode) -> bool
    {
        &&& self.valid()
        &&& replacement.wf()
        &&& replacement is Node
        //XXX needs target() ensures wf
        &&& replacement.my_domain() == self.target().my_domain()
    }

    pub open spec /*XXX (checked)*/ fn replaced_children(self, replacement: BetreeNode) -> Seq<BetreeNode>
    recommends
        self.can_substitute(replacement), 
        0 < self.depth,
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
                buffers: self.node->buffers,
                pivots: self.node->pivots,
                children: self.replaced_children(replacement),
                flushed: self.node->flushed
            }
        }
    }
} // end impl Path


state_machine!{ FilteredBetree {
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

    transition!{ internal_flush(lbl: Label, path: Path, child_idx: nat, buffer_gc: nat) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path.target().can_flush(child_idx, buffer_gc);
        require path.node == pre.root;
        update root = path.substitute(path.target().flush(child_idx, buffer_gc));
    }}

    transition!{ internal_compact(lbl: Label, path: Path, start: nat, end: nat, compacted_buffer: SimpleBuffer) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path.target().can_compact(start, end, compacted_buffer);
        require path.node == pre.root;
        update root = path.substitute(path.target().compact(start, end, compacted_buffer));
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
}} // end FilteredBetree state machine


} // end verus!