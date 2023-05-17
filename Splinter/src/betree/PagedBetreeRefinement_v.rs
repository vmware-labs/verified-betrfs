#![allow(unused_imports)]

use builtin::*;

use builtin_macros::*;

// use vstd::{calc_macro::*};


use vstd::prelude::*;
// use vstd::map::*;
// use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
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
        assume(false);
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
        // decreases self
    {
        if self.is_Node() {
            let child_receipt = self.child(key).build_query_receipt(key);
            let msg = self.get_Node_buffers().query(key);
            let line = QueryReceiptLine{node: self, result: Message::merge(msg, child_receipt.result())};
            // QueryReceipt{key: key, root: self, lines: Seq::empty().push(line) + child_receipt.lines}

            // self.child(key).build_query_receipt_valid(key);
            // let receipt = self.build_query_receipt(key);
            // assert(receipt.result_linked_at(0));
            assume(false);
        }
    }
} // end impl BetreeNode
}//verus
