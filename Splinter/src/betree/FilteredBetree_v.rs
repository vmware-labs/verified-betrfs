#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::OffsetMap_v::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MsgHistory_v::*;

verus! {
// In contrast to the PivotBetree above, upon flushing a buffer down the tree, 
// the FilteredBetree keeps the entire buffer but notes that it should filter out the keys in 
// that buffer for the child to which it was flushed.

pub type StampedBetree = Stamped<BetreeNode>;

pub open spec fn empty_image() -> StampedBetree {
    Stamped{ value: BetreeNode::Nil, seq_end: 0 }
}

#[is_variant]
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
    pub open spec fn local_structure(self) -> bool
    {
        &&& self.is_Node() ==> {
            &&& self.get_Node_pivots().wf()
            &&& self.get_Node_children().len() == self.get_Node_pivots().num_ranges()
            &&& self.get_Node_children().len() == self.get_Node_flushed().len()
            &&& self.get_Node_flushed().all_lte(self.get_Node_buffers().len()) // values in flushed are bounded by # of buffers
        }
    }

    pub open spec fn valid_child_index(self, child_idx: nat) -> bool
    {
        &&& self.is_Node()
        &&& child_idx < self.get_Node_pivots().num_ranges()   
    }

    pub open spec fn my_domain(self) -> Domain
    {
        Domain::Domain{
            start: self.get_Node_pivots().pivots[0],
            end: self.get_Node_pivots().pivots.last()
        }
    }

    // equivalent to DomainRoutedToChild
    pub open spec fn child_domain(self, child_idx: nat) -> Domain
    {
        Domain::Domain{
            start: self.get_Node_pivots().pivots[child_idx as int],
            end: self.get_Node_pivots().pivots[child_idx as int + 1]
        }
    }

    pub open spec fn linked_children(self) -> bool
    {
        &&& self.is_Node() ==> { 
            &&& forall |i:nat| #![auto] 
            ( 
                self.valid_child_index(i) 
                && self.get_Node_children()[i as int].is_Node() 
                && self.get_Node_children()[i as int].local_structure() 
            ) ==> {
                self.get_Node_children()[i as int].my_domain() == self.child_domain(i)
            }
        }
    }

    #[verifier(decreases_by)]
    pub proof fn wf_children_decreases(self)
    {
        assume(false);
    }

    pub open spec fn wf_children(self) -> bool
        recommends self.is_Node()
        decreases self, 0nat via Self::wf_children_decreases
    {
        let children = self.get_Node_children();
        forall |i:int| #![auto] 0 <= i < children.len() ==> children[i].wf()
    }

    pub open spec fn wf(self) -> bool
        decreases self, 1nat
    {
        &&& self.local_structure()
        &&& self.is_Node() ==> {
            &&& self.wf_children()
            &&& self.linked_children()
        }
    }

    pub open spec fn push_memtable(self, memtable: Memtable) -> StampedBetree
    {
        let buffers = BufferSeq{buffers: Seq::empty().push(memtable.buffer)};
        let new_root = self.promote(total_domain()).extend_buffer_seq(buffers);
        Stamped{value: new_root, seq_end: memtable.seq_end}
    }

    pub open spec fn extend_buffer_seq(self, buffers: BufferSeq) -> BetreeNode
        recommends self.is_Node()
    {
        BetreeNode::Node{
            buffers: self.get_Node_buffers().extend(buffers),
            pivots: self.get_Node_pivots(),
            children: self.get_Node_children(),
            flushed: self.get_Node_flushed()
        }
    }

    // returns the flushed offset (index into buffers) for a given key
    // buffers flushed to a child are no longer active for that child
    // renamed from ActiveBuffersForKey
    pub open spec fn flushed_ofs(self, key: Key) -> nat
        recommends self.key_in_domain(key)
    {
        let r = self.get_Node_pivots().route(key);
        self.get_Node_flushed().offsets[r]
    }

    pub open spec fn is_leaf(self) -> bool
    {
        &&& self.is_Node()
        &&& self.get_Node_children().len() == 1
        &&& self.get_Node_children()[0].is_Nil()
        &&& self.get_Node_flushed().len() == 1
        &&& self.get_Node_flushed().offsets[0] == 0
    }

    pub open spec fn is_index(self) -> bool
    {
        &&& self.is_Node()
        &&& forall |i:nat| i < self.get_Node_children().len() ==> self.get_Node_children()[i as int].is_Node()
    }

    pub open spec fn can_split_leaf(self, split_key: Key) -> bool
    {
        &&& self.wf()
        &&& self.is_leaf()
        &&& self.my_domain().contains(split_key)
        &&& self.my_domain().get_Domain_start() != to_element(split_key)
    }

    pub open spec fn split_leaf(self, split_key: Key) -> (BetreeNode, BetreeNode)
        recommends self.can_split_leaf(split_key)
    {
        let new_left = BetreeNode::Node{
            buffers: self.get_Node_buffers(),
            pivots: self.get_Node_pivots().update(1, to_element(split_key)),
            children: self.get_Node_children(),
            flushed: self.get_Node_flushed()
        };

        let new_right = BetreeNode::Node{
            buffers: self.get_Node_buffers(),
            pivots: self.get_Node_pivots().update(0, to_element(split_key)),
            children: self.get_Node_children(),
            flushed: self.get_Node_flushed()
        };

        (new_left, new_right)
    }

    pub open spec fn can_split_index(self, pivot_idx: nat) -> bool
    {
        &&& self.wf()
        &&& self.is_index()
        &&& pivot_idx < self.get_Node_pivots().len()-1
    }

    pub open spec fn  split_index(self, pivot_idx: nat) -> (BetreeNode, BetreeNode)
        recommends self.can_split_index(pivot_idx)
    {
        let idx = pivot_idx as int;
        let split_element = self.get_Node_pivots().pivots[idx];
        let new_left = BetreeNode::Node{
            buffers: self.get_Node_buffers(),
            pivots: self.get_Node_pivots().subrange(0, idx+1),
            children: self.get_Node_children().subrange(0, idx),
            flushed: self.get_Node_flushed().slice(0, idx)
        };

        let new_right = BetreeNode::Node{
            buffers: self.get_Node_buffers(),
            pivots: self.get_Node_pivots().subrange(idx, self.get_Node_pivots().len() as int),
            children: self.get_Node_children().subrange(idx, self.get_Node_children().len() as int),
            flushed: self.get_Node_flushed().slice(idx, self.get_Node_flushed().len() as int)
        };

        (new_left, new_right)
    }

    pub open spec fn can_split_parent(self, request: SplitRequest) -> bool
    {
        &&& self.wf()
        &&& self.is_Node()
        &&& match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                &&& self.valid_child_index(child_idx)
                &&& self.get_Node_children()[child_idx as int].can_split_leaf(split_key)
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                &&& self.valid_child_index(child_idx)
                &&& self.get_Node_children()[child_idx as int].can_split_index(child_pivot_idx)
            }
        }
    }

    pub open spec fn split_parent(self, request: SplitRequest) -> BetreeNode
        recommends self.can_split_parent(request)
    {
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                let idx = child_idx as int;
                let old_child = self.get_Node_children()[idx];
                let (new_left_child, new_right_child) = old_child.split_leaf(split_key);

                BetreeNode::Node{
                    buffers: self.get_Node_buffers(),
                    pivots: self.get_Node_pivots().insert(idx+1, to_element(split_key)),
                    children: self.get_Node_children().update(idx, new_left_child).insert(idx+1, new_right_child),
                    flushed: self.get_Node_flushed().dup(idx)
                }
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                let idx = child_idx as int;
                let old_child = self.get_Node_children()[idx];
                let (new_left_child, new_right_child) = old_child.split_index(child_pivot_idx);
                let split_element = old_child.get_Node_pivots().pivots[child_pivot_idx as int];

                BetreeNode::Node{
                    buffers: self.get_Node_buffers(),
                    pivots: self.get_Node_pivots().insert(idx+1, split_element),
                    children: self.get_Node_children().update(idx, new_left_child).insert(idx+1, new_right_child),
                    flushed: self.get_Node_flushed().dup(idx)
                }
            }
        }
    }

    pub open spec fn empty_root(domain: Domain) -> BetreeNode
        recommends domain.wf(), domain.is_Domain()
    {
        BetreeNode::Node{
            buffers: empty_buffer_seq(),
            pivots: domain_to_pivots(domain),
            children: Seq::empty().push(BetreeNode::Nil),
            flushed: BufferOffsets{offsets: Seq::empty().push(0)}
        }
    }

    pub open spec fn grow(self) -> BetreeNode
    {
        BetreeNode::Node{
            buffers: empty_buffer_seq(),
            pivots: domain_to_pivots(total_domain()),
            children: Seq::empty().push(self),
            flushed: BufferOffsets{offsets: Seq::empty().push(0)}
        }
    }

    pub open spec fn promote(self, domain: Domain) -> BetreeNode
    {
        if self.is_Nil() {
            BetreeNode::empty_root(domain)
        } else {
            self
        }
    }

    pub open spec fn active_keys(self, buffer_idx: nat) -> Set<Key>
        recommends self.wf(), self.is_Node(), buffer_idx < self.get_Node_buffers().len()
    {
        Set::new(|k: Key| exists |child_idx: nat| 
            #![auto]  (child_idx < self.get_Node_children().len()
            &&& self.get_Node_flushed().offsets[child_idx as int] <= buffer_idx
            &&& self.child_domain(child_idx).contains(k))
        )
    }

    pub open spec fn can_flush(self, child_idx: nat, buffer_gc: nat) -> bool
    {
        &&& self.wf()
        &&& self.is_Node()
        &&& self.valid_child_index(child_idx)
        &&& self.get_Node_flushed().update(child_idx as int, 
                self.get_Node_flushed().len()).all_gte(buffer_gc)
    }

    pub open spec fn flush(self, child_idx: nat, buffer_gc: nat) -> BetreeNode
        recommends self.can_flush(child_idx, buffer_gc)
    {
        let idx = child_idx as int;
        let flush_upto = self.get_Node_buffers().len(); 
        let flushed_ofs = self.get_Node_flushed().offsets[idx];
        
        // when we perform a flush to a child, all active buffers for that child (up to the most recent buffer) are flushed
        let buffers_to_child = self.get_Node_buffers().slice(flushed_ofs as int, flush_upto as int);
        let new_child = self.get_Node_children()[idx].promote(self.child_domain(child_idx)).extend_buffer_seq(buffers_to_child);

        // updates to parent node (self)
        // we take advantage of flush time to optionally garbage collect buffers that are no longer active by all children
        // buffer_gc tells us how many buffers (starting from oldest) we can garbage collect
        let gc_buffers = self.get_Node_buffers().slice(buffer_gc as int, flush_upto as int);
        let gc_flushed = self.get_Node_flushed().update(idx, flush_upto).shift_left(buffer_gc);

        BetreeNode::Node{
            buffers: gc_buffers,
            pivots: self.get_Node_pivots(),
            children: self.get_Node_children().update(idx, new_child),
            flushed: gc_flushed
        }
    }

    pub open spec fn compact(self, start: nat, end: nat, compacted_buffer: Buffer) -> BetreeNode
    {
        BetreeNode::Node{
            buffers: self.get_Node_buffers().update_subrange(start as int, end as int, compacted_buffer),
            pivots: self.get_Node_pivots(),
            children: self.get_Node_children(),
            flushed: self.get_Node_flushed().adjust_compact(start as int, end as int)
        }
    }

    pub open spec fn key_in_domain(self, key: Key) -> bool
    {
        &&& self.wf()
        &&& self.is_Node()
        &&& self.get_Node_pivots().bounded_key(key)
    }

    pub open spec fn child(self, key: Key) -> BetreeNode
        recommends self.key_in_domain(key)
    {
        self.get_Node_children()[self.get_Node_pivots().route(key)]
    }

    pub open spec fn make_offset_map(self) -> OffsetMap
    {
        OffsetMap{ offsets: Map::new(|k| true,
            |k| if self.get_Node_pivots().bounded_key(k) {
                self.flushed_ofs(k)
            } else {
                self.get_Node_buffers().len()
            })
        }
    }
} // end impl BetreeNode

pub struct QueryReceiptLine{
    pub node: BetreeNode,
    pub result: Message
}

impl QueryReceiptLine{
    pub open spec fn wf(self) -> bool
    {
        &&& self.node.wf()
        &&& self.result.is_Define()
    }
} // end impl QueryReceiptLine

pub struct QueryReceipt{
    pub key: Key,
    pub root: BetreeNode,
    pub lines: Seq<QueryReceiptLine>
}

impl QueryReceipt{
    pub open spec fn structure(self) -> bool
    {
        &&& 0 < self.lines.len()
        &&& self.lines[0].node == self.root
        &&& forall |i:nat| #![auto] i < self.lines.len() ==> {
            self.lines[i as int].node.is_Node() <==> i < self.lines.len()-1
        }
        &&& self.lines.last().result == Message::Define{value: default_value()}
    }

    pub open spec fn all_lines_wf(self) -> bool
    {
        &&& forall |i:nat| #![auto] i < self.lines.len() ==> self.lines[i as int].wf()
        &&& forall |i:nat| #![auto] i < self.lines.len()-1 ==> self.lines[i as int].node.key_in_domain(self.key)
    }

    pub open spec fn child_at(self, i: nat) -> BetreeNode
    {
        self.lines[i as int].node.child(self.key)
    }

    pub open spec fn child_linked_at(self, i: nat) -> bool
    {
        self.lines[i as int + 1].node == self.child_at(i)
    }

    pub open spec fn result_at(self, i: nat) -> Message
        recommends i < self.lines.len()
    {
        self.lines[i as int].result
    }

    pub open spec fn result_linked_at(self, i:nat) -> bool
    {
        let start = self.root.flushed_ofs(self.key);
        let msg = self.lines[i as int].node.get_Node_buffers().query_from(self.key, start as int);
        self.lines[i as int].result == Message::merge(msg, self.result_at(i+1))
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.structure()
        &&& self.all_lines_wf()
        &&& forall |i:nat| #![auto] i < self.lines.len()-1 ==> self.child_linked_at(i)
        &&& forall |i:nat| #![auto] i < self.lines.len()-1 ==> self.result_linked_at(i)
    }

    pub open spec fn result(self) -> Message
        recommends self.structure()
    {
        self.result_at(0)
    }

    pub open spec fn valid_for(self, root: BetreeNode, key: Key) -> bool
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
    pub open spec fn subpath(self) -> Path
        recommends 0 < self.depth
    {
        let depth = (self.depth - 1) as nat;
        Path{node: self.node.child(self.key), key: self.key, depth: depth}
    }

    pub open spec fn valid(self) -> bool
        decreases self.depth
    {
        &&& self.node.wf()
        &&& self.node.key_in_domain(self.key)
        &&& (0 < self.depth ==> self.node.is_index())
        &&& (0 < self.depth ==> self.subpath().valid())
    }

    pub open spec fn target(self) -> BetreeNode
        decreases self.depth
    {
        if self.depth == 0 {
            self.node
        } else {
            self.subpath().target()
        }
    }

    pub open spec fn valid_replacement(self, replacement: BetreeNode) -> bool
        recommends self.valid()
    {
        &&& replacement.wf()
        &&& replacement.is_Node()
        &&& replacement.my_domain() == self.target().my_domain()
    }

    pub open spec fn replaced_children(self, replacement: BetreeNode) -> Seq<BetreeNode>
        recommends self.valid(), 
            self.valid_replacement(replacement), 
            0 < self.depth
        decreases self.subpath().depth
    {
        let new_child = self.subpath().substitute(replacement);
        let r = self.node.get_Node_pivots().route(self.key);
        self.node.get_Node_children().update(r, new_child)
    }

    pub open spec fn substitute(self, replacement: BetreeNode) -> BetreeNode
        recommends self.valid(), self.valid_replacement(replacement)
        decreases self.depth, 1nat
    {
        if self.depth == 0 {
            replacement
        } else {
            BetreeNode::Node{
                buffers: self.node.get_Node_buffers(),
                pivots: self.node.get_Node_pivots(),
                children: self.replaced_children(replacement),
                flushed: self.node.get_Node_flushed()
            }
        }
    }
} // end impl Path


state_machine!{ PivotBetree {
    fields {
        pub memtable: Memtable,
        pub root: BetreeNode,
    }

    pub open spec fn wf(self) -> bool {
        &&& self.root.wf()
    }

    #[is_variant]
    pub enum Label
    {
        Query{end_lsn: LSN, key: Key, value: Value},
        Put{puts: MsgHistory},
        QueryEndLsn{end_lsn: LSN},
        FreezeAs{stamped_betree: StampedBetree},
        Internal{},   // Local No-op label
    }

    transition!{ query(lbl: Label, receipt: QueryReceipt) {
        require let Label::Query{end_lsn, key, value} = lbl;
        require end_lsn == pre.memtable.seq_end;
        require receipt.valid_for(pre.root, key);
        require Message::Define{value} == Message::merge(pre.memtable.query(key), receipt.result());
    }}

    transition!{ put(lbl: Label) {
        require let Label::Put{puts} = lbl;
        require puts.wf();
        require puts.seq_start == pre.memtable.seq_end;
        update memtable = pre.memtable.apply_puts(puts);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require let Label::QueryEndLsn{end_lsn} = lbl;
        require end_lsn == pre.memtable.seq_end;
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

    transition!{ internal_compact(lbl: Label, path: Path, start: nat, end: nat, compacted_buffer: Buffer) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require let BetreeNode::Node{buffers, pivots, children, flushed} = path.target();
        require start < end <= buffers.len();
        require compacted_buffer == buffers.slice(start as int, end as int).i_filtered(path.target().make_offset_map().decrement(start));
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
