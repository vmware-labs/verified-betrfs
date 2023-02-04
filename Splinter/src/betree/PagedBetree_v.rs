#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::prelude::*;
use crate::betree::Buffers_v::*;
use crate::betree::Memtable_v::*;
use crate::spec::TotalKMMap_t::*;
use crate::coordination_layer::StampedMap_v::*;

verus! {
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


} // end impl BetreeNode

} // end verus!