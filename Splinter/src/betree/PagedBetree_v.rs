#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::prelude::*;
use crate::betree::Buffers_v::*;
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
    BetreeNode{ 
        buffers: BufferStack, 
        children: ChildMap},
}

impl BetreeNode {
    pub open spec fn child(self, key: Key) -> BetreeNode {
        self.get_BetreeNode_children().map[key]
    }

    // pub open spec fn push_memtable(memtable: )


} // end impl BetreeNode

} // end verus!