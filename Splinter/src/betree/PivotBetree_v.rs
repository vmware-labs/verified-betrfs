#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::coordination_layer::StampedMap_v::*;

verus! {
// This is a functional model of a Betree with nodes with pivot table

// pub type StampedBetree = Stamped<BetreeNode>;

// pub open spec fn empty_image() -> StampedBetree {
//     Stamped{ value: BetreeNode::Nil, seq_end: 0 }
// }

// pub open spec fn empty_child_map() -> ChildMap {
//     constant_child_map(BetreeNode::Nil)
// }

#[is_variant]
pub enum BetreeNode {
    Nil,
    Node{
        buffers: BufferSeq,
        pivots: PivotTable,
        children: Seq<BetreeNode>
    },
}

impl BetreeNode {
    pub open spec fn local_structure(self) -> bool
    {
        &&& self.is_Node() ==> {
            &&& self.get_Node_pivots().wf()
            &&& self.get_Node_children().len() == self.get_Node_pivots().num_ranges()
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
    pub proof fn decreases_infinite_struct_workaround(self)
    {
        assume(false);
    }

    pub open spec fn wf_children(self) -> bool
        recommends self.is_Node()
        decreases self via Self::decreases_infinite_struct_workaround
    {
        &&& forall |i:nat| #![auto] i < self.get_Node_children().len() ==> {
            self.get_Node_children()[i as int].wf()
        }
    }

    // TODO(Jialin): not sure why this is needed

    #[verifier(decreases_by)]
    pub proof fn decreases_infinite_struct_workaround2(self)
    {
        assume(false);
    }

    pub open spec fn wf(self) -> bool
        decreases self via Self::decreases_infinite_struct_workaround2
    {
        &&& self.local_structure()
        &&& self.is_Node() ==> {
            &&& self.wf_children()
            &&& self.linked_children()
        }
    }

    pub open spec fn extend_buffer_seq(self, buffers: BufferSeq) -> BetreeNode
        recommends self.is_Node()
    {
        BetreeNode::Node{
            buffers: self.get_Node_buffers().extend(buffers),
            pivots: self.get_Node_pivots(),
            children: self.get_Node_children()
        }
    }

    pub open spec fn is_leaf(self) -> bool
    {
        &&& self.is_Node()
        &&& self.get_Node_children().len() == 1
        &&& self.get_Node_children()[0].is_Nil()
    }

    pub open spec fn is_index(self) -> bool
    {
        &&& self.is_Node()
        &&& forall |i:nat| i < self.get_Node_children().len() ==> self.get_Node_children()[i as int].is_Node()
    }

    pub open spec fn split_leaf(self, split_key: Key) -> (BetreeNode, BetreeNode)
        recommends self.is_leaf(),
            self.my_domain().contains(split_key),
            self.my_domain().get_Domain_start() != to_element(split_key)
    {
        let left_filter = Domain::Domain{ start: self.my_domain().get_Domain_start(), end: to_element(split_key) };
        let right_filter = Domain::Domain{ start: to_element(split_key), end: self.my_domain().get_Domain_end() };

        let new_left = BetreeNode::Node{
            buffers: self.get_Node_buffers().apply_filter(left_filter.key_set()),
            pivots: PivotTable{ pivots: self.get_Node_pivots().pivots.update(1, to_element(split_key)) },
            children: Seq::empty().push(BetreeNode::Nil)
        };

        let new_right = BetreeNode::Node{
            buffers: self.get_Node_buffers().apply_filter(right_filter.key_set()),
            pivots: PivotTable{ pivots: self.get_Node_pivots().pivots.update(0, to_element(split_key)) },
            children: Seq::empty().push(BetreeNode::Nil)
        };

        (new_left, new_right)
    }
} // end impl BetreeNode
} // end verus!
