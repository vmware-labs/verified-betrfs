#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::prelude::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::betree::Buffers_v::*;
use crate::betree::Memtable_v::*;
use crate::coordination_layer::StampedMap_v::*;

verus! {
// This is a functional model of a Betree, but it doesn't require that child
// maps be stored as contiguous ranges separated by a finite sets of pivots.
// That's complexity that we push down a layer, to the PivotBetree. Here,
// instead, we have a child for every possible key, as though every key is a
// pivot. That's not *exactly* right, since adjacent children
// (in fact, infinite ranges of adjacent children) will be identical:
// children for keys 40..70 may all carry (identical) buffers including
// keys in [40..70), since of course they're represented by the same node
// in PivotBetree, the next layer down the refinement stack.
//
// This trickiness mostly appears in the Path Substitution code, which has
// to decide which of the infinity children are getting replaced -- the answer
// depends on how the PivotBetree has decided to divvy up the child pointers.


pub type StampedBetree = Stamped<BetreeNode>;

pub open spec fn empty_image() -> StampedBetree {
    Stamped{ value: BetreeNode::Nil, seq_end: 0 }
}

pub struct ChildMap{ 
    pub map: Map<Key, BetreeNode> 
}

pub open spec fn constant_child_map(target: BetreeNode) -> ChildMap {
    ChildMap{ map: Map::new( |k| true, |k| target ) }
}

pub open spec fn empty_child_map() -> ChildMap {
    constant_child_map(BetreeNode::Nil)
}


#[is_variant]
pub enum BetreeNode {
    Nil,
    Node{ 
        buffers: BufferStack, 
        children: ChildMap},
}

impl BetreeNode {
    pub open spec fn child(self, key: Key) -> BetreeNode {
        self.get_Node_children().map[key]
    }

    pub open spec fn empty_root() -> BetreeNode {
        BetreeNode::Node {
            buffers: BufferStack{ buffers: Seq::empty()},
            children: empty_child_map()
        }
    }

    pub open spec fn promote(self) -> BetreeNode {
        if self.is_Nil() {
            Self::empty_root() 
        } else {
            self
        }
    }

    pub open spec fn push_buffer_stack(self, buffer_stack: BufferStack) -> BetreeNode {
        BetreeNode::Node{
            buffers: self.get_Node_buffers().push_buffer_stack(buffer_stack),
            children: self.get_Node_children(),
        }
    }

    pub open spec fn push_memtable(self, memtable: Memtable) -> StampedBetree {
        Stamped{
            value: self.promote().push_buffer_stack(
                BufferStack{ buffers: Seq::empty().push(memtable.buffer) }
            ),
            seq_end: memtable.seq_end
        }
    }

    pub open spec fn filter_buffers_and_children(self, filter: Set<Key>) -> BetreeNode {
        if self.is_Nil() {
            self
        } else {
            let filtered_children = ChildMap {
                map: Map::new( |k| true, |k| if filter.contains(k) { self.get_Node_children().map[k] } else { BetreeNode:: Nil } )
            };
            BetreeNode::Node {
                buffers: self.get_Node_buffers().apply_filter(filter),
                children: filtered_children,
            }
        }
    }

    pub open spec fn split(self, left_keys: Set<Key>, right_keys: Set<Key>) -> BetreeNode {
        // We suppose that a lower layer will use this when leftKeys+rightKeys are all
        // identical, so that the first two branches of the if expression each produce
        // a single BetreeNode (with a shared representation below).
        let map = Map::new( |k| true, |k| 
                if left_keys.contains(k) {self.child(k).filter_buffers_and_children(left_keys)} 
                else if right_keys.contains(k) {self.child(k).filter_buffers_and_children(right_keys)} 
                else {self.child(k)});
        BetreeNode::Node {
            buffers: self.get_Node_buffers(),
            children: ChildMap{ map }
        }
    }

    pub open spec fn flush(self, down_keys: Set<Key>) -> BetreeNode {
        let kept_buffers = self.get_Node_buffers().apply_filter(all_keys().difference(down_keys));
        let moved_buffers = self.get_Node_buffers().apply_filter(down_keys);
        let out_children_map = Map::new( |k| true, |k| 
            if down_keys.contains(k) {self.child(k).promote().push_buffer_stack(moved_buffers)}
            else {self.child(k)}
        );
        BetreeNode::Node {
            buffers: kept_buffers,
            children: ChildMap{ map: out_children_map}
        }
    }
} // end impl BetreeNode



pub struct QueryReceiptLine {
    pub node: BetreeNode,
    pub result: Message,
}

impl QueryReceiptLine {
    pub open spec fn wf(self) -> bool {
       self.result.is_Define()
    }
} //end impl QueryReceiptLine

// NB the top line is the line for the root node; hence Result()==ResultAt(0)
// The bottom line is always Nil
pub struct QueryReceipt {
    pub key: Key,
    pub root: BetreeNode,
    pub lines: Seq<QueryReceiptLine>,
}

impl QueryReceipt {
    pub open spec fn structure(self) -> bool {
        &&& 0 < self.lines.len()
        &&& self.lines[0].node == self.root
        &&& forall |i| #![auto] 0 <= i < self.lines.len() ==> (
            self.lines[i].node.is_Node() <==> i < self.lines.len() - 1
        )
    }

    pub open spec fn all_lines_wf(self) -> bool {
        forall |i| #![auto] 0 <= i < self.lines.len() ==> self.lines[i].wf()
    }

    pub open spec fn child_at(self, i: int) -> BetreeNode 
        recommends 
            self.all_lines_wf(),
            self.structure(),
            0 <= i < self.lines.len() - 1,
    {
        self.lines[i].node.child(self.key)
    }

    pub open spec fn child_linked_at(self, i: int) -> bool 
        recommends 
            self.all_lines_wf(),
            self.structure(),
            0 <= i < self.lines.len() - 1,
    {
        self.lines[i+1].node == self.child_at(i)
    }

    pub open spec fn result_at(self, i: int) -> Message 
        recommends 0 <= i < self.lines.len()
    {
        self.lines[i].result
    }

    pub open spec fn result_linked_at(self, i: int) -> bool 
        recommends 
            self.all_lines_wf(),
            self.structure(),
            0 <= i < self.lines.len() - 1,
    {
        self.result_at(i) == self.lines[i].node.get_Node_buffers().query(self.key).merge(self.result_at(i+1))
    }

    pub open spec fn valid(self) -> bool {
        &&& self.structure()
        &&& self.all_lines_wf()
        &&& forall |i| #![auto] 0 <= i < self.lines.len()-1 ==> self.child_linked_at(i)
        &&& forall |i| #![auto] 0 <= i < self.lines.len()-1 ==> self.result_linked_at(i)
    }

    pub open spec fn result(self) -> Message 
        recommends self.structure()
    {
        self.result_at(0)
    }

    pub open spec fn valid_for(self, root: BetreeNode, key: Key) -> bool {
        &&& self.valid()
        &&& self.root == root
        &&& self.key == key
    }
} // end impl QueryReceipt


// TODO: TONY left off here. Time to implement PagedBetree Variables and the state machine





} // end verus!