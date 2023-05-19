#![allow(unused_imports)]

use builtin::*;

use builtin_macros::*;

// use vstd::{calc_macro::*};


use vstd::prelude::*;
// use vstd::map::*;
// use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::coordination_layer::StampedMap_v::LSN;
// use crate::coordination_layer::MsgHistory_v::*;
// use crate::coordination_layer::AbstractMap_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v::*;
use crate::betree::PivotBetree_v;
use crate::betree::FilteredBetree_v::*;

verus! {

    // pub open spec fn a(num: nat) -> nat
    //     decreases num
    // {
    //     if num == 0 { 0 } else { a( (num-1) as nat) }
    // }

    // pub open spec fn b(s: Seq<nat>) -> Seq<nat>
    // {
    //     Seq::new(s.len(), |i:int| a(s[i]))
    // }

// add interpretation functions for betreenode
impl BetreeNode {
    pub open spec fn i_buffer(self, buffer_idx: int) -> Buffer
        recommends self.is_Node(), buffer_idx >= 0
    {
        let active_keys = self.active_keys(buffer_idx as nat);
        let buffer = self.get_Node_buffers().buffers[buffer_idx];
        buffer.apply_filter(active_keys)
    }

    // let's pretend we can 
    pub open spec fn i_buffer_seq(self) -> BufferSeq
        recommends self.is_Node()
    {
        let len = self.get_Node_buffers().len();
        BufferSeq{ buffers: Seq::new(len, |i:int| self.i_buffer(i)) }
    }

    // pub open spec fn i_children(self) -> Seq<PivotBetree_v::BetreeNode>
    //     recommends self.is_Node()
    //     decreases self, 0nat
    // {
    //     let len = self.get_Node_children().len();
    //     Seq::new(len, |i:int| self.get_Node_children()[i].i_node())
    // }

    // pub open spec fn i_node(self) -> PivotBetree_v::BetreeNode
    //     decreases self, 1nat
    // {
    //     if self.is_Nil() {
    //         PivotBetree_v::BetreeNode::Nil
    //     } else {
    //         PivotBetree_v::BetreeNode::Node{
    //             buffers: self.i_buffer_seq(),
    //             pivots: self.get_Node_pivots(),
    //             children: self.i_children()
    //         }
    //     }
    // }
} // end impl BetreeNode
}//verus
