#![allow(unused_imports)]

use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
// use vstd::map::*;
// use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MsgHistory_v::*;
use crate::coordination_layer::AbstractMap_v::*;
use crate::betree::PagedBetree_v::*;

verus! {

// add interpretation functions for betreenode
impl BetreeNode {
    // pub open spec fn ext_equal(self, other: BetreeNode) -> bool
    // {
    //     &&& self.is_Node() <==> other.is_Node()
    //     &&& self.is_Node() ==> {
    //         &&& self.get_Node_buffers().buffers.ext_equal(other.get_Node_buffers().buffers)
    //         &&& self.get_Node_children().map.ext_equal(other.get_Node_children().map)
    //     }
    // }

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

pub open spec fn i_stamped_betree(stamped: StampedBetree) -> StampedMap
{
    Stamped{value: stamped.value.i_node(), seq_end: stamped.seq_end}
}

impl QueryReceipt{
    pub proof fn equal_receipts(self, other: QueryReceipt)
        requires 
            self.valid(), other.valid(), 
            self.key == other.key, self.root == other.root,
        ensures self.result() == other.result()
    {
        if 1 < self.lines.len() {
            assume(false);
        }
    }
}

impl PagedBetree::Label {
    pub open spec fn i(self) -> AbstractMap::Label
    {
        match self {
            PagedBetree::Label::Query{end_lsn, key, value} => AbstractMap::Label::QueryLabel{end_lsn: end_lsn, key: key, value: value},
            PagedBetree::Label::Put{puts} => AbstractMap::Label::PutLabel{puts: puts},
            PagedBetree::Label::FreezeAs{stamped_betree} => AbstractMap::Label::FreezeAsLabel{stamped_map: i_stamped_betree(stamped_betree)},
            PagedBetree::Label::Internal{} => AbstractMap::Label::InternalLabel{},
        }
    }
} // end impl PagedBetree::Label

impl PagedBetree::State {
    pub open spec fn inv(self) -> bool {
        self.wf()
    }

    pub open spec fn i(self) -> AbstractMap::State
    {
        AbstractMap::State{stamped_map: Stamped{value: self.root.i_node(), seq_end: self.memtable.seq_end}}
    }

    pub proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires PagedBetree::State::initialize(self, stamped_betree)
        ensures self.inv(), AbstractMap::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
    }

    // pub proof fn memtable_distributes_over_betree(self)
    //     requires self.wf()
    //     ensures forall |k| 

    pub proof fn query_refines(self, post: Self, lbl: PagedBetree::Label, receipt: QueryReceipt)
        requires self.inv(), PagedBetree::State::query(self, post, lbl, receipt)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        let built_receipt = self.root.build_query_receipt(lbl.get_Query_key());
        self.root.build_query_receipt_valid(lbl.get_Query_key());

        assert(receipt.valid());
        assert(built_receipt.valid());

        assert(receipt.key == built_receipt.key);
        assert(receipt.root == built_receipt.root);

        assume(receipt.result() == built_receipt.result());

        assert(AbstractMap::State::query(self.i(), post.i(), lbl.i()));
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::query()));
    }

    pub proof fn next_refines(self, post: Self, lbl: PagedBetree::Label)
        requires self.inv(), PagedBetree::State::next(self, post, lbl),
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        match choose |step| PagedBetree::State::next_by(self, post, lbl, step)
        {
            PagedBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
            _ => {assume(false);} 
        }
    }
} // end impl PagedBetree::State

}//verus
 