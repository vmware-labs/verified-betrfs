#![allow(unused_imports)]

use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use vstd::map::*;
use vstd::set_lib::*;
use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::spec::TotalKMMap_t::*;
use crate::coordination_layer::StampedMap_v::*;
// use crate::coordination_layer::MsgHistory_v::*;
// use crate::coordination_layer::AbstractMap_v::*;
use crate::betree::Domain_v::*;
// use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::PagedBetree_v;
use crate::betree::PagedBetree_v::PagedBetree;
use crate::betree::PivotBetree_v::*;

verus! {

impl BetreeNode {
    #[verifier(decreases_by)]
    pub proof fn decreases_seq_struct_workaround(self, start: int)
    {
        assume(height(self.get_Node_children()[start]) < height(self));
    }

    pub open spec fn i_children_seq(self, start: int) -> Seq<PagedBetree_v::BetreeNode>
        recommends self.is_Node(), 0 <= start <= self.get_Node_children().len()
        decreases self, 0nat, self.get_Node_children().len()-start via Self::decreases_seq_struct_workaround
    {
        decreases_when(0 <= start <= self.get_Node_children().len());
        if start == self.get_Node_children().len() {
            Seq::empty()
        } else {
            let child = self.get_Node_children()[start].i();
            Seq::new(1, |i| child) + self.i_children_seq(start+1)
        }
    }

    pub open spec fn i_children(self) -> PagedBetree_v::ChildMap
        recommends self.is_Node()
        decreases self, 1nat
    {
        let seq_result = self.i_children_seq(0);
    
        PagedBetree_v::ChildMap{map: Map::new(|k: Key| true, 
            |k: Key| if self.key_in_domain(k) {
                let r = self.get_Node_pivots().route(k);
                seq_result[r]
            } else {
                PagedBetree_v::BetreeNode::Nil
            }
        )}
    }

    pub open spec fn i(self) -> PagedBetree_v::BetreeNode
        decreases self
    {
        if self.is_Nil() {
            PagedBetree_v::BetreeNode::Nil{}
        } else {
            PagedBetree_v::BetreeNode::Node{buffers: self.get_Node_buffers(), children: self.i_children()}
        }
    }

    pub proof fn i_children_seq_wf(self, start: int)
        requires self.wf(), self.is_Node(), 0 <= start <= self.get_Node_children().len()
        ensures self.i_children_seq(start).len() == self.get_Node_children().len() - start,
            forall |i: int| 0 <= i < self.i_children_seq(start).len() 
            ==> #[trigger] self.i_children_seq(start)[i].wf()
        decreases self, 0nat, self.get_Node_children().len()-start 
    {
        if start < self.get_Node_children().len() {
            let result = self.i_children_seq(start);
            let child = self.get_Node_children()[start];
            let sub_seq = self.i_children_seq(start+1);

            assume(height(child) < height(self));

            child.i_wf();
            self.i_children_seq_wf(start+1);
        }
    }

    pub proof fn i_wf(self)
        requires self.wf()
        ensures self.i().wf()
        decreases self, 1nat
    {
        if self.is_Node() {
            let children = self.i().get_Node_children();
            let seq_result = self.i_children_seq(0);
            self.i_children_seq_wf(0);

            assert forall |k: Key| (#[trigger] children.map[k]).wf() by {
                if self.key_in_domain(k) {
                    let r = self.get_Node_pivots().route(k);
                    self.get_Node_pivots().route_lemma(k);
                    assert(0 <= r <= self.get_Node_pivots().len());
                }
            }
        }
    }

} // end impl BetreeNode

pub open spec fn i_stamped_betree(stamped: StampedBetree) -> PagedBetree_v::StampedBetree
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceipt{
}

impl Path{
    pub open spec fn routing(self) -> Seq<Set<Key>>
        recommends self.valid()
        decreases self.depth
    {
        if self.depth == 0 {
            Seq::empty()
        } else {
            let pivots = self.node.get_Node_pivots();
            let keys = pivots.pivot_range_keyset(pivots.route(self.key));
            Seq::new(1, |i:int| keys) + self.subpath().routing() 
        }
    }

    pub open spec fn i(self) -> PagedBetree_v::Path
    {
        PagedBetree_v::Path{node: self.node.i(), key: self.key, routing: self.routing()}
    }

    pub proof fn subpath_commutes_with_i(self)
        requires self.valid(), 0 < self.depth
        ensures self.subpath().i() == self.i().subpath()
    {
        assert(self.subpath().i().ext_equal(self.i().subpath())); // panics
    }
}

impl PivotBetree::Label {
    pub open spec fn i(self) -> PagedBetree::Label
    {
        match self {
            PivotBetree::Label::Query{end_lsn, key, value} => PagedBetree::Label::Query{end_lsn: end_lsn, key: key, value: value},
            PivotBetree::Label::Put{puts} => PagedBetree::Label::Put{puts: puts},
            PivotBetree::Label::FreezeAs{stamped_betree} => PagedBetree::Label::FreezeAs{stamped_betree: i_stamped_betree(stamped_betree)},
            PivotBetree::Label::Internal{} => PagedBetree::Label::Internal{},
        }
    }
} // end impl PivotBetree::Label


impl PivotBetree::State {
    pub open spec fn inv(self) -> bool {
        &&& self.wf()
        &&& (self.root.is_Node() ==> self.root.my_domain() == total_domain())
    }

    pub open spec fn i(self) -> PagedBetree::State
    {
        PagedBetree::State{root: self.root.i(), memtable: self.memtable}
    }
} // end impl PivotBetree::State

}//verus
 