#![allow(unused_imports)]

use builtin::*;

use builtin_macros::*;
use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;
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

    pub proof fn i_children_seq_lemma(self, start: int)
        requires self.wf(), self.is_Node(), 0 <= start <= self.get_Node_children().len()
        ensures self.i_children_seq(start).len() == self.get_Node_children().len() - start,
            forall |i: int| 0 <= i < self.i_children_seq(start).len() 
            ==> {
                &&& (#[trigger] self.i_children_seq(start)[i]).wf()
                &&& self.i_children_seq(start)[i] == self.get_Node_children()[i+start].i()
            }
        decreases self, 0nat, self.get_Node_children().len()-start 
    {
        if start < self.get_Node_children().len() {
            let result = self.i_children_seq(start);
            let child = self.get_Node_children()[start];
            let sub_seq = self.i_children_seq(start+1);

            assume(height(child) < height(self));

            child.i_wf();
            self.i_children_seq_lemma(start+1);
        }
    }

    // used as a trigger but not in defn of i_children bc closure can't take recursive fn
    pub open spec fn i_child(self, k: Key) -> PagedBetree_v::BetreeNode
        recommends self.is_Node()
    {
        if self.key_in_domain(k) {
            self.child(k).i()
        } else {
            PagedBetree_v::BetreeNode::Nil{}
        }
    }

    pub proof fn i_children_lemma(self)
        requires self.is_Node(), self.wf()
        ensures forall |k:Key| {
            (#[trigger] self.i_children().map[k]).wf()
            && self.i_children().map[k] == self.i_child(k)
        }
        decreases self, 1nat
    {
        let seq_result = self.i_children_seq(0);
        self.i_children_seq_lemma(0);
    
        assert forall |k:Key| {
            (#[trigger] self.i_children().map[k]).wf()
            && self.i_children().map[k] == self.i_child(k)
        } by {
            if self.key_in_domain(k) {
                let r = self.get_Node_pivots().route(k);
                self.get_Node_pivots().route_lemma(k);

                assert(self.i_children().map[k] == seq_result[r]);
                assert(self.i_children().map[k] == self.i_child(k));
            }
        }
    }

    pub proof fn i_wf(self)
        requires self.wf()
        ensures self.i().wf()
        decreases self, 2nat
    {
        if self.is_Node() {
            self.i_children_lemma();
        }
    }

    pub open spec fn children_have_matching_domains(self, other_children: Seq<BetreeNode>) -> bool
        recommends self.wf(), self.is_index()
    {
        &&& other_children.len() == self.get_Node_children().len()
        &&& forall |i:int| #![auto] 0 <= i < other_children.len() ==> other_children[i].wf()
        &&& (forall |i:int| #![auto] 0 <= i < self.get_Node_children().len() ==> {
            &&& other_children[i].wf()
            &&& other_children[i].is_Node()
            &&& other_children[i].my_domain() == self.get_Node_children()[i].my_domain()
        })
    }

} // end impl BetreeNode

pub open spec fn i_stamped_betree(stamped: StampedBetree) -> PagedBetree_v::StampedBetree
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine{
    pub open spec fn i(self) -> PagedBetree_v::QueryReceiptLine
        recommends self.wf()
    {
        PagedBetree_v::QueryReceiptLine{node: self.node.i(), result: self.result}
    }
}

impl QueryReceipt{
    pub open spec fn i(self) -> PagedBetree_v::QueryReceipt
        recommends self.valid()
    {
        PagedBetree_v::QueryReceipt{
            key: self.key,
            root: self.root.i(),
            lines: Seq::new(self.lines.len(), |i:int| self.lines[i].i())
        }
    }

    pub proof fn valid_receipt_refines(self)
        requires self.valid()
        ensures self.i().valid()
    {
        let i_receipt = self.i();

        assert forall |i:int| 0 <= i < i_receipt.lines.len()
        implies #[trigger] i_receipt.lines[i].wf() by {
            self.lines[i].node.i_wf();
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.child_linked_at(i) by {
            assert(self.child_linked_at(i));
            self.lines[i].node.i_children_lemma();
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.result_linked_at(i) by {
            assert(self.result_linked_at(i));
        }
    }


    // pub open spec fn drop_first(self) -> QueryReceipt
    //     recommends 1 < self.lines.len()
    // {
    //     QueryReceipt{
    //         key: self.key,
    //         root: self.root.child(self.key),
    //         lines: self.lines.subrange(1, self.lines.len() as int)
    //     }
    // }

    // pub proof fn drop_first_valid(self)
    //     requires self.valid(), 1 < self.lines.len()
    //     ensures self.drop_first().valid()
    // {
    //     let out = self.drop_first();
    //     assert(self.child_linked_at(0));
    //     assert forall |i: int| 0 <= i < out.lines.len()-1
    //     implies ({
    //         &&& out.child_linked_at(i)
    //         &&& out.result_linked_at(i)
    //     }) by {
    //         assert(self.child_linked_at(i+1)); // trigger
    //         assert(self.result_linked_at(i+1)); // trigger
    //     }
    // }

    // pub proof fn equal_receipts(self, other: QueryReceipt)
    //     requires 
    //         self.valid(), other.valid(), 
    //         self.key == other.key, self.root == other.root,
    //     ensures self.result() == other.result()
    //     decreases self.lines.len()
    // {
    //     if 1 < self.lines.len() {
    //         assert(self.result_linked_at(0));
    //         assert(other.result_linked_at(0));

    //         self.drop_first_valid();
    //         other.drop_first_valid();
    //         self.drop_first().equal_receipts(other.drop_first());
    //     }
    // }
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

    pub proof fn routing_lemma(self)
        requires self.valid()
        ensures self.routing().len() == self.depth
        decreases self.depth
    {
        if 0 < self.depth {
            self.subpath().routing_lemma();
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
        self.node.i_wf();
        self.node.i_children_lemma();

        self.routing_lemma();
        assert_seqs_equal!(self.subpath().i().routing, self.i().subpath().routing);
    }

    pub proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
        decreases self.depth
    {
        self.node.i_children_lemma();
        if 0 < self.depth {
            self.subpath_commutes_with_i();
            self.subpath().i_valid();
        }
    }

    pub proof fn target_wf(self)
        requires self.valid()
        ensures self.target().wf(), self.target().is_Node()
        decreases self.depth
    {
        if self.depth > 0 {
            self.subpath().target_wf();
        }
    }
    
    pub proof fn target_commutes_with_i(self)
        requires self.valid()
        ensures self.i().valid(), self.i().target() == self.target().i()
        decreases self.depth
    {
        self.i_valid();
        if 0 < self.depth {
            self.subpath().target_commutes_with_i();
            self.subpath_commutes_with_i();
        }
    }

    pub proof fn substitute_preserves_wf(self, replacement: BetreeNode)
        requires self.valid(), self.valid_replacement(replacement)
        ensures self.substitute(replacement).wf()
        decreases self.depth, 1nat
    {
        if 0 < self.depth {
            self.subpath().substitute_preserves_wf(replacement);
    
            let result = self.substitute(replacement);
            if result.is_Node() {
                self.replaced_children_matching_domains(replacement);
                assert forall |i:nat| i < self.node.get_Node_children().len() ==> { // trigger
                    #[trigger] self.node.valid_child_index(i)
                    && self.node.get_Node_children()[i as int].is_Node()
                    && self.node.get_Node_children()[i as int].wf()
                } by { }

                assert forall |i:nat|  
                ( 
                    #[trigger] result.valid_child_index(i) 
                    && result.get_Node_children()[i as int].is_Node() 
                    && result.get_Node_children()[i as int].local_structure() 
                ) implies {
                    result.get_Node_children()[i as int].my_domain() == result.child_domain(i)
                } by {
                    assert(self.node.valid_child_index(i));
                }

                assert(result.linked_children());
            }
        }
    }

    pub proof fn replaced_children_matching_domains(self, replacement: BetreeNode)
        requires self.valid(), self.valid_replacement(replacement), 0 < self.depth
        ensures self.node.children_have_matching_domains(self.replaced_children(replacement))
        decreases self.depth, 0nat
    {
        self.node.get_Node_pivots().route_lemma(self.key);
        self.subpath().substitute_preserves_wf(replacement);

        let old_children = self.node.get_Node_children();
        let new_children = self.replaced_children(replacement);
        assert(old_children.len() == new_children.len());
        
        if 0 < self.subpath().depth {
            self.subpath().replaced_children_matching_domains(replacement);
        }
    }

    pub proof fn substitute_refines(self, replacement: BetreeNode)
        requires self.valid(), self.valid_replacement(replacement)
        ensures self.substitute(replacement).wf(), 
            self.i().valid(), replacement.i().wf(),
            self.substitute(replacement).i() == self.i().substitute(replacement.i())
        decreases self.depth
    {
        self.i_valid();
        self.substitute_preserves_wf(replacement);
        replacement.i_wf();

        if 0 < self.depth {
            self.substitute(replacement).i_children_lemma();
            assert(self.substitute(replacement).i_children().wf());

            self.i().substitute_preserves_wf(replacement.i());
            assert(self.i().replaced_children(replacement.i()).wf());

            self.subpath().substitute_refines(replacement);

            assert forall |k:Key| (
                #[trigger] self.substitute(replacement).i_children().map[k]
                == self.i().replaced_children(replacement.i()).map[k]
            ) by {
                if self.node.key_in_domain(k) {
                    let pivots = self.node.get_Node_pivots();
                    pivots.route_lemma(k);
                    pivots.route_lemma(self.key);

                    if pivots.route(k) == pivots.route(self.key) {
                        self.subpath_commutes_with_i();
                    } else {
                        self.node.i_children_lemma();
                    }
                }
            }

            assert_maps_equal!(self.substitute(replacement).i().get_Node_children().map,
                self.i().substitute(replacement.i()).get_Node_children().map
            );
        }
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

    pub proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires PivotBetree::State::initialize(self, stamped_betree)
        ensures PagedBetree::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        stamped_betree.value.i_wf();
    }

    pub proof fn query_refines(self, post: Self, lbl: PivotBetree::Label, receipt: QueryReceipt)
        requires self.inv(), PivotBetree::State::query(self, post, lbl, receipt)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        receipt.valid_receipt_refines();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::query(receipt.i())));
    }

    pub proof fn put_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::put(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::put()));
    }

    // pub proof fn freeze_as_refines(self, post: Self, lbl: PivotBetree::Label)
    //     requires self.inv(), PivotBetree::State::freeze_as(self, post, lbl)
    //     ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(PagedBetree::State::next);
    //     reveal(PagedBetree::State::next_by);

    //     self.root.push_empty_memtable_refines(self.memtable);
    //     assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::freeze_as()));
    // }

    // pub proof fn internal_flush_memtable_noop(self, post: Self, lbl: PivotBetree::Label)
    //     requires self.inv(), PivotBetree::State::internal_flush_memtable(self, post, lbl)
    //     ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(PagedBetree::State::next);
    //     reveal(PagedBetree::State::next_by);

    //     post.root.push_empty_memtable_refines(post.memtable);
    //     assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal()));
    // }

    // pub proof fn equivalent_roots(self, post: Self)
    //     requires self.wf(), post.wf(), 
    //         self.memtable == post.memtable, 
    //         self.root.i() == post.root.i()
    //     ensures self.i() == post.i()
    // {
    //     self.root.memtable_distributes_over_betree(self.memtable);
    //     post.root.memtable_distributes_over_betree(post.memtable);
    // }

    // pub proof fn internal_grow_noop(self, post: Self, lbl: PivotBetree::Label)
    //     requires self.inv(), PivotBetree::State::internal_grow(self, post, lbl)
    //     ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(PagedBetree::State::next);
    //     reveal(PagedBetree::State::next_by);

    //     assert(post.root.i().ext_equal(self.root.i()));
    //     self.equivalent_roots(post);
    //     assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal()));
    // }

    // pub proof fn internal_split_noop(self, post: Self, lbl: PivotBetree::Label, path: Path, left_keys: Set<Key>, right_keys: Set<Key>)
    //     requires self.inv(), PivotBetree::State::internal_split(self, post, lbl, path, left_keys, right_keys)
    //     ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(PagedBetree::State::next);
    //     reveal(PagedBetree::State::next_by);

    //     let target = path.target();
    //     path.target_wf();

    //     let top = target.split(left_keys, right_keys);
    //     target.split_wf(left_keys, right_keys);

    //     assert forall |k: Key| true ==>
    //     ({ target.i_node_at(k) == top.i_node_at(k) })
    //     by {
    //         if left_keys.contains(k) {
    //             target.child(k).apply_filter_equivalence(left_keys, k);
    //         } else if right_keys.contains(k) {
    //             target.child(k).apply_filter_equivalence(right_keys, k);
    //         }
    //     }

    //     assert(target.i().ext_equal(top.i()));
    //     path.substitute_equivalence(top);
    //     self.equivalent_roots(post);
    //     assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal()));
    // }

    // pub proof fn internal_flush_noop(self, post: Self, lbl: PivotBetree::Label, path: Path, down_keys: Set<Key>)
    //     requires self.inv(), PivotBetree::State::internal_flush(self, post, lbl, path, down_keys)
    //     ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(PagedBetree::State::next);
    //     reveal(PagedBetree::State::next_by);

    //     let target = path.target();
    //     path.target_wf();

    //     let top = target.flush(down_keys);
    //     target.flush_wf(down_keys);

    //     let kept_keys = all_keys().difference(down_keys);

    //     assert forall |k: Key| true ==>
    //     ({ target.i_node_at(k) == top.i_node_at(k) })
    //     by {
    //         if down_keys.contains(k) {
    //             target.get_Node_buffers().filtered_buffer_seq_query_lemma(kept_keys, k, 0);
    //             assert(target.get_Node_children().wf());
                
    //             let moved_buffers = target.get_Node_buffers().apply_filter(down_keys);
    //             let child = target.get_Node_children().map[k];
    //             child.extend_buffer_seq_lemma(moved_buffers, k);
    //             target.get_Node_buffers().filtered_buffer_seq_query_lemma(down_keys, k, 0);
    //         } else {
    //             target.get_Node_buffers().filtered_buffer_seq_query_lemma(kept_keys, k, 0);
    //         }
    //     }
        
    //     assert(target.i().ext_equal(top.i()));
    //     path.substitute_equivalence(top);
    //     self.equivalent_roots(post);
    //     assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal()));
    // }

    // pub proof fn internal_compact_noop(self, post: Self, lbl: PivotBetree::Label, path: Path, compacted_buffers: BufferSeq)
    //     requires self.inv(), PivotBetree::State::internal_compact(self, post, lbl, path, compacted_buffers)
    //     ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(PagedBetree::State::next);
    //     reveal(PagedBetree::State::next_by);

    //     path.target_wf();
    //     let compact_node = path.target().compact(compacted_buffers);
    //     assert(compact_node.i().ext_equal(path.target().i()));
    //     path.substitute_equivalence(compact_node);
    //     self.equivalent_roots(post);
    //     assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal()));
    // }

    // pub proof fn internal_noop_noop(self, post: Self, lbl: PivotBetree::Label)
    //     requires self.inv(), PivotBetree::State::internal_noop(self, post, lbl)
    //     ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(PagedBetree::State::next);
    //     reveal(PagedBetree::State::next_by);
    //     assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal()));
    // }

    pub proof fn next_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::next(self, post, lbl),
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        match choose |step| PivotBetree::State::next_by(self, post, lbl, step)
        {
            PivotBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
            PivotBetree::Step::put() => { self.put_refines(post, lbl); }
    //         PivotBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
    //         PivotBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_noop(post, lbl); }
    //         PivotBetree::Step::internal_grow() => { self.internal_grow_noop(post, lbl); }
    //         PivotBetree::Step::internal_split(path, left_keys, right_keys) => { self.internal_split_noop(post, lbl, path, left_keys, right_keys); }
    //         PivotBetree::Step::internal_flush(path, down_keys) => { self.internal_flush_noop(post, lbl, path, down_keys); }
    //         PivotBetree::Step::internal_compact(path, compacted_buffers) => { self.internal_compact_noop(post, lbl, path, compacted_buffers); }
    //         PivotBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
            _ => { assume(false); } 
        }
    }
} // end impl PivotBetree::State

}//verus
 