#![allow(unused_imports)]

use builtin::*;

use builtin_macros::*;

// use vstd::{calc_macro::*};


use vstd::prelude::*;
// use vstd::map::*;
// use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::coordination_layer::StampedMap_v::LSN;
use crate::coordination_layer::MsgHistory_v::*;
use crate::coordination_layer::AbstractMap_v::*;
use crate::betree::PagedBetree_v::*;

verus! {

// add interpretation functions for betreenode
impl BetreeNode {
    // // TODO: revisit
    #[verifier(decreases_by)]
    pub proof fn decreases_infinite_struct_workaround(self, key: Key)
    {
        assume(height(self.child(key)) < height(self));
    }

    pub open spec fn build_query_receipt(self, key: Key) -> QueryReceipt
        recommends self.wf()
        decreases self via Self::decreases_infinite_struct_workaround
    {
        if self.is_Nil() {
            let msg = Message::Define{value: default_value()};
            let line = QueryReceiptLine{node: self, result: msg};
            QueryReceipt{key: key, root: self, lines: Seq::empty().push(line)}
        } else {
            let child_receipt = self.child(key).build_query_receipt(key);
            let msg = self.get_Node_buffers().query(key);
            let line = QueryReceiptLine{node: self, result: Message::merge(msg, child_receipt.result())};
            QueryReceipt{key: key, root: self, lines: Seq::empty().push(line) + child_receipt.lines}
        }
    }

    pub proof fn build_query_receipt_valid(self, key: Key) 
        requires self.wf()
        ensures self.build_query_receipt(key).valid()
        decreases self
    {
        if self.is_Node() {
            let child_receipt = self.child(key).build_query_receipt(key);
            let msg = self.get_Node_buffers().query(key);
            let line = QueryReceiptLine{node: self, result: Message::merge(msg, child_receipt.result())};

            assume(height(self.child(key)) < height(self)); // TODO: temp measure
            self.child(key).build_query_receipt_valid(key);
            
            let receipt = QueryReceipt{key: key, root: self, lines: Seq::empty().push(line) + child_receipt.lines};
            assert(receipt == self.build_query_receipt(key));

            assert forall |i: int| 0 < i < receipt.lines.len()-1
            implies ({
                &&& receipt.child_linked_at(i)
                &&& receipt.result_linked_at(i)
            }) by {
                assert(child_receipt.child_linked_at(i-1)); // trigger
                assert(child_receipt.result_linked_at(i-1)); // trigger
            }
        }
    }

    pub open spec fn i_node_at(self, key: Key) -> Message
        recommends self.wf()
    {
        self.build_query_receipt(key).result()
    }

    pub open spec fn i_node(self) -> TotalKMMap
    {
        TotalKMMap(Map::new(|k: Key| true, |k| self.i_node_at(k)))
    }
} // end impl BetreeNode
}//verus
