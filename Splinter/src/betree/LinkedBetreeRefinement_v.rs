#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::map::*;
use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::Buffer_v::*;
// use crate::betree::BufferSeq_v;
use crate::betree::LinkedBufferSeq_v;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::FilteredBetree_v;
use crate::betree::FilteredBetree_v::FilteredBetree;
use crate::betree::LinkedBetree_v::*;
use crate::betree::SplitRequest_v::*;

verus! {

impl BetreeNode {
    // pub open spec(checked) fn i_buffer_seq(self, buffer_dv: BufferDiskView) -> BufferSeq_v::BufferSeq
    //     recommends self.buffers.valid(buffer_dv)
    // {
    //     let buffers = Seq::new(self.buffers.len(), |i| buffer_dv.get(self.buffers[i]));
    //     BufferSeq_v::BufferSeq{ buffers: buffers }
    // }

    // pub proof fn i_children_lemma_auto()
    //     ensures 
    //         forall |node: Self| node.wf() && node.is_Node() 
    //         ==> {
    //             &&& node.i().wf_children()
    //             &&& (#[trigger] node.get_Node_children()).len() == node.i_children().len()
    //             &&& forall |i| node.valid_child_index(i)
    //                 ==> (#[trigger]node.i_children()[i as int]) == node.get_Node_children()[i as int].i()
    //         }
    // {
    //     assert forall |node: Self| node.wf() && node.is_Node()
    //     implies {
    //         &&& node.i().wf_children()
    //         &&& (#[trigger] node.get_Node_children()).len() == node.i_children().len()
    //         &&& forall |i| (#[trigger]node.valid_child_index(i))
    //             ==> node.i_children()[i as int] == node.get_Node_children()[i as int].i()
    //     } by {
    //         node.i_children_lemma();
    //     }
    // }

    // pub proof fn i_wf(self)
    //     requires self.wf()
    //     ensures self.i().wf(), self.is_Node() ==> self.my_domain() == self.i().my_domain()
    //     decreases self, 2nat
    // {
    //     if self.is_Node() {
    //         self.i_children_lemma();
    //         assert(self.wf_children()); // trigger
   
    //         assert forall |i|
    //         ( 
    //             (#[trigger] self.i().valid_child_index(i))
    //             && self.i().get_Node_children()[i as int].is_Node()
    //             && self.i().get_Node_children()[i as int].local_structure() 
    //         ) implies {
    //             self.i().get_Node_children()[i as int].my_domain() == self.child_domain(i)
    //         } by {
    //             assert(self.valid_child_index(i));
    //         }

    //         assert(self.i().wf_children()); // trigger
    //         assert(self.i().linked_children());
    //     }
    // }

    // pub proof fn i_wf_auto()
    //     ensures 
    //         forall |node: Self| node.wf() ==> {
    //             &&& (#[trigger]node.i()).wf()
    //             &&& node.is_Node() ==> node.my_domain() == node.i().my_domain()
    //         }
    // {
    //     assert forall |node: Self| node.wf()
    //     implies {
    //         &&& (#[trigger]node.i()).wf()
    //         &&& node.is_Node() ==> node.my_domain() == node.i().my_domain()
    //     } by {
    //         node.i_wf();
    //     }
    // }

    // pub proof fn i_buffer_domain(self)
    //     requires self.wf(), self.is_Node()
    //     ensures forall |k| #[trigger] self.i_buffer().map.contains_key(k) <==> 
    //         exists |idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx)
    // {
    //     self.get_Node_buffers().i_filtered_from_domain(self.make_offset_map(), 0);
    // }

    // pub proof fn query_from_refines(self, key: Key)
    //     requires self.wf(), self.is_Node(), self.key_in_domain(key),
    //     ensures self.get_Node_buffers().query_from(key, self.flushed_ofs(key) as int) == self.i().get_Node_buffer().query(key)
    // {
    //     PivotTable::route_lemma_auto();
    //     let offset_map = self.make_offset_map();
    //     self.get_Node_buffers().query_from_same_as_i_filtered(key, 0, offset_map);
    // }

    // pub proof fn query_from_refines_auto()
    //     ensures forall |k: Key, node: BetreeNode| #![auto] node.wf() && node.is_Node() && node.key_in_domain(k)
    //         ==> node.get_Node_buffers().query_from(k, node.flushed_ofs(k) as int) == node.i().get_Node_buffer().query(k)
    // {
    //     assert forall  #![auto] |k: Key, node: BetreeNode| node.wf() && node.is_Node() && node.key_in_domain(k)
    //     implies node.get_Node_buffers().query_from(k, node.flushed_ofs(k) as int) == node.i().get_Node_buffer().query(k)
    //     by {
    //         node.query_from_refines(k);
    //     }
    // }

    // pub open spec /*XXX(checked)*/ fn children_have_matching_domains(self, other_children: Seq<BetreeNode>) -> bool
    //     recommends self.wf(), self.is_index()
    // {
    //     &&& other_children.len() == self.get_Node_children().len()
    //     &&& (forall |i| (#[trigger] self.valid_child_index(i)) ==> {
    //         &&& other_children[i as int].wf()
    //         &&& other_children[i as int].is_Node()
    //         //XXX need to instantiate linked_children
    //         &&& other_children[i as int].my_domain() == self.get_Node_children()[i as int].my_domain()
    //     })
    // }

    // pub proof fn i_preserves_domain(self, other: BetreeNode, k: Key)
    //     requires self.key_in_domain(k), other.key_in_domain(k),
    //         self.flushed_ofs(k) == other.flushed_ofs(k),
    //         self.get_Node_buffers() == other.get_Node_buffers()
    //     ensures
    //         self.i().get_Node_buffer().map.contains_key(k) == other.i().get_Node_buffer().map.contains_key(k),
    //         self.i().get_Node_buffer().map.contains_key(k) ==> self.i().get_Node_buffer().map[k] == other.i().get_Node_buffer().map[k]
    // {
    //     self.i_buffer_domain();
    //     other.i_buffer_domain();

    //     if self.i().get_Node_buffer().map.contains_key(k) {
    //         let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx);
    //         assert(other.get_Node_buffers().key_in_buffer_filtered(other.make_offset_map(), 0, k, idx));
    //         assert(other.i().get_Node_buffer().map.contains_key(k));
    //     }
        
    //     if other.i().get_Node_buffer().map.contains_key(k) {
    //         let idx = choose |idx| other.get_Node_buffers().key_in_buffer_filtered(other.make_offset_map(), 0, k, idx);
    //         assert(self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx));
    //         assert(self.i().get_Node_buffer().map.contains_key(k));
    //     }

    //     BetreeNode::query_from_refines_auto();
    // }

    // pub proof fn i_preserves_domain_auto(self)
    // ensures forall |other: Self, k: Key| 
    //         #![auto] self.key_in_domain(k) && other.key_in_domain(k)
    //         && self.flushed_ofs(k) == other.flushed_ofs(k)
    //         && self.get_Node_buffers() == other.get_Node_buffers()
    //     ==> ({
    //         &&& self.i().get_Node_buffer().map.contains_key(k) == other.i().get_Node_buffer().map.contains_key(k)
    //         &&& self.i().get_Node_buffer().map.contains_key(k) ==> self.i().get_Node_buffer().map[k] == other.i().get_Node_buffer().map[k]
    //     })
    // {
    //     assert forall #![auto] |other: Self, k: Key| 
    //         self.key_in_domain(k) && other.key_in_domain(k)
    //         && self.flushed_ofs(k) == other.flushed_ofs(k)
    //         && self.get_Node_buffers() == other.get_Node_buffers()
    //     implies ({
    //         &&& self.i().get_Node_buffer().map.contains_key(k) == other.i().get_Node_buffer().map.contains_key(k)
    //         &&& self.i().get_Node_buffer().map.contains_key(k) ==> self.i().get_Node_buffer().map[k] == other.i().get_Node_buffer().map[k]
    //     }) by {
    //         self.i_preserves_domain(other, k);
    //     }
    // }

    // pub proof fn child_domain_implies_key_in_domain(self, child_idx: nat)
    //     requires self.wf(), self.is_Node(), child_idx < self.get_Node_children().len() 
    //     ensures forall |k: Key| #![auto] self.child_domain(child_idx).contains(k) ==> self.key_in_domain(k)
    // {
    //     let child_domain = self.child_domain(child_idx);
    //     assert forall #![auto] |k: Key| child_domain.contains(k)
    //     implies self.key_in_domain(k)
    //     by {
    //         if self.get_Node_pivots().num_ranges() == 1 {
    //             assert(child_domain == self.my_domain());
    //         } else {
    //             if child_idx == 0 {
    //                 assert(Element::lt(child_domain.get_Domain_end(), self.my_domain().get_Domain_end()));
    //             } else if child_idx + 1 == self.get_Node_pivots().num_ranges() {
    //                 assert(Element::lt(self.my_domain().get_Domain_start(), child_domain.get_Domain_start()));
    //             } else {
    //                 assert(Element::lt(self.my_domain().get_Domain_start(), child_domain.get_Domain_start()));
    //                 assert(Element::lt(child_domain.get_Domain_end(), self.my_domain().get_Domain_end()));
    //             }
    //         }
    //     }
    // }

    // pub proof fn extend_buffer_seq_wf(self, buffers: BufferSeq)
    //     requires self.wf(), self.is_Node()
    //     ensures self.extend_buffer_seq(buffers).wf()
    // {
    //     let result = self.extend_buffer_seq(buffers);
    //     assert(self.wf_children());
    //     assert forall |i| #[trigger] result.valid_child_index(i) ==> self.valid_child_index(i) by {}
    //     assert(result.wf_children());
    // }

    // pub proof fn extend_buffer_seq_refines_merge_buffer(self, buffers: BufferSeq)
    //     requires self.wf(), self.is_Node()
    //     ensures self.extend_buffer_seq(buffers).i() == self.i().merge_buffer(buffers.i().apply_filter(self.my_domain().key_set()))
    // {
    //     let filter = self.my_domain().key_set();
    //     let a = self.extend_buffer_seq(buffers);
    //     self.extend_buffer_seq_wf(buffers);

    //     let b = self.i().merge_buffer(buffers.i().apply_filter(filter));

    //     BetreeNode::i_children_lemma_auto();
    //     assert(a.i().get_Node_children() =~= b.get_Node_children());

    //     let offset_map = self.make_offset_map();
    //     let a_offset_map = a.make_offset_map();

    //     self.i_buffer_domain();
    //     a.i_buffer_domain();

    //     assert forall |k| 
    //     ({
    //         &&& a.i().get_Node_buffer().map.contains_key(k) <==> #[trigger] b.get_Node_buffer().map.contains_key(k)
    //         &&& a.i().get_Node_buffer().map.contains_key(k) ==> a.i().get_Node_buffer().map[k] == b.get_Node_buffer().map[k]
    //     }) by {
    //         PivotTable::route_lemma_auto();
    //         if a.i().get_Node_buffer().map.contains_key(k) {
    //             let idx = choose |idx| a.get_Node_buffers().key_in_buffer_filtered(a_offset_map, 0, k, idx);
    //             assert(a.get_Node_buffers().key_in_buffer_filtered(offset_map, 0, k, idx));
    //             if idx < self.get_Node_buffers().len() {
    //                 assert(self.get_Node_buffers().key_in_buffer_filtered(offset_map, 0, k, idx));
    //             } else {
    //                 let buffer_idx = idx-self.get_Node_buffers().len();
    //                 assert(a.get_Node_buffers()[idx].map.contains_key(k));
    //                 assert(a.get_Node_buffers()[idx] == buffers[buffer_idx]);
    //                 assert(buffers.key_in_buffer(0, k, buffer_idx));
    //                 buffers.i_from_domain(0);
    //             }

    //             assert(a.i().get_Node_buffer().map[k] == b.get_Node_buffer().map[k]) by {
    //                 a.query_from_refines(k);
    //                 self.query_from_refines(k);
    //                 buffers.query_agrees_with_i(k, 0);
    //                 assert(buffers.query(k) == buffers.i().query(k));
    //                 BufferSeq::extend_buffer_seq_lemma(buffers, self.get_Node_buffers(), k, offset_map.offsets[k] as int);
    //             }
    //         }

    //         if b.get_Node_buffer().map.contains_key(k) {
    //             if buffers.i().map.contains_key(k) {
    //                 buffers.i_from_domain(0);
    //                 let buffer_idx = choose |buffer_idx| buffers.key_in_buffer(0, k, buffer_idx);
    //                 let idx = buffer_idx + self.get_Node_buffers().len();
    //                 assert(a.get_Node_buffers().key_in_buffer_filtered(a_offset_map, 0, k, idx));
    //             } else {
    //                 assert(self.i().get_Node_buffer().map.contains_key(k));
    //                 let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(offset_map, 0, k, idx);
    //                 assert(a.get_Node_buffers().key_in_buffer_filtered(a_offset_map, 0, k, idx));
    //             }
    //         }
    //     }
    //     assert(a.i().get_Node_buffer().map.dom() =~= b.get_Node_buffer().map.dom());
    //     assert(a.i().get_Node_buffer() =~= b.get_Node_buffer());
    // }

    // pub proof fn promote_commutes_with_i(self, domain: Domain)
    //     requires self.wf(), domain.wf(), domain.is_Domain()
    //     ensures self.promote(domain).i() == self.i().promote(domain)
    // {
    //     BetreeNode::i_wf_auto();
    //     BetreeNode::i_children_lemma_auto();
    //     PivotTable::route_lemma_auto();

    //     assert(self.promote(domain).i().get_Node_buffer() =~= self.i().promote(domain).get_Node_buffer());
    // }

    // pub open spec(checked) fn split_element(self, request: SplitRequest) -> Element
    //     recommends self.can_split_parent(request)
    // {
    //     let child = self.get_Node_children()[request.get_child_idx() as int];
    //     match request {
    //         SplitRequest::SplitLeaf{child_idx, split_key} => to_element(split_key),
    //         SplitRequest::SplitIndex{child_idx, child_pivot_idx} => child.get_Node_pivots().pivots[child_pivot_idx as int]
    //     }
    // }

    // pub proof fn split_leaf_wf(self, split_key: Key)
    //     requires self.can_split_leaf(split_key)
    //     ensures self.split_leaf(split_key).0.wf(), self.split_leaf(split_key).1.wf()
    // {
    //     assert(self.split_leaf(split_key).0.wf_children());
    //     assert(self.split_leaf(split_key).1.wf_children());
    // }

    // pub proof fn split_index_wf(self, pivot_idx: nat)
    //     requires self.can_split_index(pivot_idx)
    //     ensures self.split_index(pivot_idx).0.wf(), self.split_index(pivot_idx).1.wf()
    // {
    //     let (new_left, new_right) = self.split_index(pivot_idx);
    //     assert forall |i| new_left.valid_child_index(i) ==> self.valid_child_index(i) by {}
    //     assert forall |i| new_right.valid_child_index(i) ==> self.valid_child_index(i+pivot_idx) by {}
    //     assert(new_left.wf_children());
    //     assert(new_right.wf_children());
    // }

    // pub proof fn split_parent_wf(self, request: SplitRequest) 
    //     requires self.can_split_parent(request)
    //     ensures self.split_parent(request).wf()
    // { 
    //     let child_idx = request.get_child_idx();
    //     let old_child = self.get_Node_children()[child_idx as int];
    //     let new_parent = self.split_parent(request);

    //     self.get_Node_pivots().insert_wf(child_idx as int + 1, self.split_element(request));

    //     assert forall |i| #[trigger] new_parent.valid_child_index(i) ==> 
    //     ({
    //         &&& i < child_idx ==> self.valid_child_index(i) 
    //         &&& i > child_idx + 1 ==> self.valid_child_index((i-1) as nat)
    //     }) by {}

    //     match request {
    //         SplitRequest::SplitLeaf{child_idx, split_key} => old_child.split_leaf_wf(split_key),
    //         SplitRequest::SplitIndex{child_idx, child_pivot_idx} => old_child.split_index_wf(child_pivot_idx),
    //     }
    //     assert(new_parent.wf_children());
    //     assert(new_parent.linked_children());
    // }

    // pub proof fn split_leaf_commutes_with_i(self, split_key: Key)
    //     requires self.can_split_leaf(split_key)
    //     ensures 
    //         self.split_leaf(split_key).0.i() == self.i().split_leaf(split_key).0,
    //         self.split_leaf(split_key).1.i() == self.i().split_leaf(split_key).1,
    // {
    //     BetreeNode::i_wf_auto();
    //     PivotTable::route_lemma_auto();

    //     let (left, right) = self.split_leaf(split_key);
    //     let (i_left, i_right) = self.i().split_leaf(split_key);
    //     self.split_leaf_wf(split_key);

    //     left.i_buffer_domain();
    //     right.i_buffer_domain();
    //     self.i_buffer_domain();
    //     self.i_preserves_domain_auto();

    //     assert(left.i().get_Node_buffer().map.dom() =~= i_left.get_Node_buffer().map.dom());
    //     assert(right.i().get_Node_buffer().map.dom() =~= i_right.get_Node_buffer().map.dom());
    //     assert(left.i().get_Node_buffer() =~= i_left.get_Node_buffer());
    //     assert(right.i().get_Node_buffer() =~= i_right.get_Node_buffer());
    // }
    
    // // #[verifier::spinoff_prover]
    // pub proof fn split_index_commutes_with_i(self, pivot_idx: nat)
    //     requires self.can_split_index(pivot_idx)
    //     ensures
    //         self.split_index(pivot_idx).0.i() == self.i().split_index(pivot_idx).0,
    //         self.split_index(pivot_idx).1.i() == self.i().split_index(pivot_idx).1,
    // {
    //     BetreeNode::i_wf_auto();
    //     PivotTable::route_lemma_auto();
    //     PivotTable::route_is_lemma_auto();

    //     Element::lt_transitive_forall();
    //     Element::lte_transitive_forall();

    //     let (left, right) = self.split_index(pivot_idx);
    //     let (i_left, i_right) = self.i().split_index(pivot_idx);
    //     self.split_index_wf(pivot_idx);

    //     self.i_buffer_domain();
    //     left.i_buffer_domain();
    //     right.i_buffer_domain();

    //     assert(left.i().get_Node_buffer() =~= i_left.get_Node_buffer()) 
    //     by {
    //         self.i_preserves_domain_auto();
    //         left.i_preserves_domain_auto();
    //     }

    //     assert(right.i().get_Node_buffer() =~= i_right.get_Node_buffer())
    //     by {
    //         self.i_preserves_domain_auto();
    //         right.i_preserves_domain_auto();
    //     }

    //     BetreeNode::i_children_lemma_auto();
    //     assert(left.i().get_Node_children() =~= i_left.get_Node_children());
    //     assert(right.i().get_Node_children() =~= i_right.get_Node_children());
    // }

    // // #[verifier::spinoff_prover]
    // pub proof fn split_parent_buffers_commutes_with_i(self, request: SplitRequest)
    //     requires self.can_split_parent(request), self.i().can_split_parent(request)
    //     ensures self.i().split_parent(request).get_Node_buffer() == self.split_parent(request).i().get_Node_buffer()
    // {
    //     self.split_parent_wf(request);
    //     self.i().split_parent_wf(request);
    //     BetreeNode::i_wf_auto();

    //     let new_parent = self.split_parent(request);
    //     let i_new_parent = self.i().split_parent(request);
    //     let split_child_idx = request.get_child_idx() as int;

    //     self.i_buffer_domain();
    //     new_parent.i_buffer_domain();

    //     assert forall |k| 
    //     ({
    //         &&& new_parent.i().get_Node_buffer().map.contains_key(k) <==> #[trigger] i_new_parent.get_Node_buffer().map.contains_key(k)
    //         &&& new_parent.i().get_Node_buffer().map.contains_key(k) ==> 
    //             new_parent.i().get_Node_buffer().map[k] == i_new_parent.get_Node_buffer().map[k]
    //     }) by {

    //         if new_parent.i().get_Node_buffer().map.contains_key(k) {
    //             let r = new_parent.get_Node_pivots().route(k);
    //             new_parent.get_Node_pivots().route_lemma(k);

    //             if r <= split_child_idx {
    //                 if r == split_child_idx {
    //                     assert(Element::lt(new_parent.get_Node_pivots()[r+1], self.get_Node_pivots().pivots[r+1]));
    //                 }
    //                 self.get_Node_pivots().route_is_lemma(k, r);
    //             } else {
    //                 assert(Element::lt(new_parent.get_Node_pivots().pivots[r-1], new_parent.get_Node_pivots().pivots[r]));
    //                 self.get_Node_pivots().route_is_lemma(k, r-1);
    //             }
    //             assert(self.flushed_ofs(k) == new_parent.flushed_ofs(k));
    //             new_parent.i_preserves_domain(self, k);
    //         }

    //         if i_new_parent.get_Node_buffer().map.contains_key(k) {
    //             assert(self.i().get_Node_buffer().map.contains_key(k));
    //             assert(self.key_in_domain(k));
    //             assert(new_parent.key_in_domain(k));

    //             let r = self.get_Node_pivots().route(k);
    //             self.get_Node_pivots().route_lemma(k);
    //             if r < split_child_idx {
    //                 new_parent.get_Node_pivots().route_is_lemma(k, r);
    //             } else if r == split_child_idx {
    //                 if Element::lt(to_element(k), new_parent.get_Node_pivots().pivots[r+1]) {
    //                     new_parent.get_Node_pivots().route_is_lemma(k, r);
    //                 } else {
    //                     new_parent.get_Node_pivots().route_is_lemma(k, r+1);
    //                 }
    //             } else {
    //                 new_parent.get_Node_pivots().route_is_lemma(k, r+1);
    //             }
    //             assert(self.flushed_ofs(k) == new_parent.flushed_ofs(k));
    //             self.i_preserves_domain(new_parent, k);
    //         }
    //     }
    //     assert(new_parent.i().get_Node_buffer().map.dom() =~= i_new_parent.get_Node_buffer().map.dom());
    //     assert(new_parent.i().get_Node_buffer() =~= i_new_parent.get_Node_buffer());
    // }

    // // #[verifier::spinoff_prover]
    // pub proof fn split_parent_commutes_with_i(self, request: SplitRequest)
    //     requires self.can_split_parent(request)
    //     ensures 
    //         self.i().can_split_parent(request),
    //         self.i().split_parent(request) == self.split_parent(request).i()
    // {
    //     self.split_parent_wf(request);
    //     BetreeNode::i_wf_auto();
    //     BetreeNode::i_children_lemma_auto();

    //     let split_child_idx = request.get_child_idx() as int;
    //     let child = self.get_Node_children()[request.get_child_idx() as int];

    //     if request.is_SplitLeaf() {
    //         child.split_leaf_commutes_with_i(request.get_SplitLeaf_split_key());
    //     } else {
    //         child.split_index_commutes_with_i(request.get_SplitIndex_child_pivot_idx());
    //     }

    //     self.split_parent_buffers_commutes_with_i(request);
    //     assert(self.split_parent(request).i().get_Node_children() =~= self.i().split_parent(request).get_Node_children());
    // }

    // pub proof fn flush_wf(self, child_idx: nat, buffer_gc: nat)
    //     requires self.can_flush(child_idx, buffer_gc)
    //     ensures self.flush(child_idx, buffer_gc).wf()
    // {
    //     let result = self.flush(child_idx, buffer_gc);

    //     let idx = child_idx as int;
    //     let flush_upto = self.get_Node_buffers().len(); 

    //     let updated_flushed = self.get_Node_flushed().update(idx, flush_upto);
    //     assert(updated_flushed.offsets[idx] == flush_upto);
    //     updated_flushed.shift_left_preserves_lte(buffer_gc, flush_upto);
    //     assert(result.local_structure());

    //     let flushed_ofs = self.get_Node_flushed().offsets[idx];
    //     let buffers_to_child = self.get_Node_buffers().slice(flushed_ofs as int, flush_upto as int);

    //     let child = self.get_Node_children()[idx];
    //     let child_domain = self.child_domain(child_idx);
    //     let new_child = child.promote(child_domain).extend_buffer_seq(buffers_to_child);

    //     assert(child.wf()); // trigger
    //     child.promote(child_domain).extend_buffer_seq_wf(buffers_to_child);
    //     assert(new_child.wf());
    //     assert forall |i| #[trigger] result.valid_child_index(i) ==> self.valid_child_index(i) by {}
    // }

    // pub proof fn flush_commutes_with_i(self, child_idx: nat, buffer_gc: nat)
    //     requires self.can_flush(child_idx, buffer_gc)
    //     ensures self.flush(child_idx, buffer_gc).i() == self.i().flush(child_idx)
    // {
    //     self.flush_wf(child_idx, buffer_gc);
    //     BetreeNode::i_wf_auto();
    //     BetreeNode::i_children_lemma_auto();
    //     PivotTable::route_lemma_auto();

    //     let idx = child_idx as int;
    //     let flush_upto = self.get_Node_buffers().len();

    //     let flushed_ofs = self.get_Node_flushed().offsets[idx];
    //     let buffers_to_child = self.get_Node_buffers().slice(flushed_ofs as int, flush_upto as int);

    //     let child = self.get_Node_children()[idx];
    //     let child_domain = self.child_domain(child_idx);
    //     let new_child = child.promote(child_domain).extend_buffer_seq(buffers_to_child);

    //     assert(child.wf()); // trigger
    //     child.promote_commutes_with_i(child_domain);
    //     assert(child.promote(child_domain).i() == child.i().promote(child_domain));
    //     child.promote(child_domain).extend_buffer_seq_refines_merge_buffer(buffers_to_child);
    //     assert(new_child.i() == child.i().promote(child_domain).merge_buffer(buffers_to_child.i().apply_filter(child_domain.key_set())));

    //     self.i_buffer_domain();
    //     self.child_domain_implies_key_in_domain(child_idx);

    //     assert forall #![auto] |k| child_domain.contains(k)
    //     implies ({
    //         &&& buffers_to_child.i().map.contains_key(k) <==> self.i_buffer().map.contains_key(k)
    //         &&& buffers_to_child.i().query(k) == self.i_buffer().query(k)
    //     }) by {
    //         self.get_Node_pivots().route_is_lemma(k, idx);
    //         assert(self.flushed_ofs(k) == flushed_ofs);

    //         if buffers_to_child.i().map.contains_key(k) {
    //             buffers_to_child.i_from_domain(0);
    //             let buffer_idx = choose |buffer_idx| buffers_to_child.key_in_buffer(0, k, buffer_idx);
    //             assert(self.get_Node_buffers().key_in_buffer(flushed_ofs as int, k, buffer_idx + flushed_ofs));
    //             assert(self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, buffer_idx + flushed_ofs));
    //             assert(self.i_buffer().map.contains_key(k));
    //         }

    //         if self.i_buffer().map.contains_key(k) {
    //             let buffer_idx = choose |buffer_idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, buffer_idx);
    //             assert(buffers_to_child.key_in_buffer(0, k, buffer_idx-flushed_ofs));
    //             buffers_to_child.i_from_domain(0);
    //             assert(buffers_to_child.i().map.contains_key(k));
    //         }

    //         buffers_to_child.query_agrees_with_i(k, 0);
    //         self.query_from_refines(k);
    //         assert(buffers_to_child.query(k) == buffers_to_child.i().query(k));
    //         assert(self.i_buffer().query(k) == self.get_Node_buffers().query_from(k, flushed_ofs as int));
    //         BufferSeq::common_buffer_seqs(buffers_to_child, self.get_Node_buffers(), 0, flushed_ofs as int, k);
    //     }
    //     assert(buffers_to_child.i().apply_filter(child_domain.key_set()) =~= self.i_buffer().apply_filter(child_domain.key_set()));
    //     assert(self.flush(child_idx, buffer_gc).i().get_Node_children() =~= self.i().flush(child_idx).get_Node_children());

    //     let a = self.flush(child_idx, buffer_gc);
    //     let b = self.i().flush(child_idx);
    //     let keep_keys = all_keys().difference(child_domain.key_set());

    //     a.i_buffer_domain();

    //     assert forall |k|
    //     ({
    //         &&& #[trigger] a.i().get_Node_buffer().map.contains_key(k) <==> b.get_Node_buffer().map.contains_key(k)
    //         &&& a.i().get_Node_buffer().map.contains_key(k) ==> a.i().get_Node_buffer().map[k] == b.get_Node_buffer().map[k]
    //     }) by {
    //         if a.i().get_Node_buffer().map.contains_key(k) {
    //             if child_domain.contains(k) {
    //                 a.get_Node_pivots().route_is_lemma(k, child_idx as int);
    //                 assert(a.flushed_ofs(k) == a.get_Node_buffers().len());
    //                 assert(false);
    //             }
    //             assert(keep_keys.contains(k));
    //             let idx = choose |idx| a.get_Node_buffers().key_in_buffer_filtered(a.make_offset_map(), 0, k, idx);
    //             let r = a.get_Node_pivots().route(k);
    //             assert(r != child_idx);
    //             assert(a.flushed_ofs(k) == self.flushed_ofs(k) - buffer_gc);
    //             assert(self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx + buffer_gc));
    //             assert(b.get_Node_buffer().map.contains_key(k));

    //             self.query_from_refines(k);
    //             a.query_from_refines(k);
    //             BufferSeq::common_buffer_seqs(a.get_Node_buffers(), self.get_Node_buffers(), a.flushed_ofs(k) as int, buffer_gc as int, k);
    //         }

    //         if b.get_Node_buffer().map.contains_key(k) {
    //             assert(keep_keys.contains(k));
    //             assert(self.key_in_domain(k));
    //             assert(a.flushed_ofs(k) == self.flushed_ofs(k) - buffer_gc);
    //             let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx);
    //             assert(a.get_Node_buffers().key_in_buffer_filtered(a.make_offset_map(), 0, k, idx - buffer_gc));
    //             assert(a.i().get_Node_buffer().map.contains_key(k));
    //         }
    //     }
    //     assert(a.i().get_Node_buffer().map.dom() =~= b.get_Node_buffer().map.dom());
    //     assert(a.i().get_Node_buffer() =~= b.get_Node_buffer());
    // }

    // pub proof fn compact_wf(self, start: nat, end: nat, compacted_buffer: Buffer)
    //     requires self.can_compact(start, end, compacted_buffer)
    //     ensures self.compact(start, end, compacted_buffer).wf()
    // {
    //     let result = self.compact(start, end, compacted_buffer);
    //     assert forall |i| #[trigger] result.valid_child_index(i) ==> self.valid_child_index(i) by {}
    // }

    // pub proof fn compact_buffer_property(self, start: nat, end: nat, compacted_buffer: Buffer)
    //     requires self.can_compact(start, end, compacted_buffer)
    //     ensures compacted_buffer == self.get_Node_buffers().slice(start as int, end as int).i_filtered(self.make_offset_map().decrement(start))
    // {
    //     let slice_ofs_map = self.make_offset_map().decrement(start);
    //     let compact_slice = self.get_Node_buffers().slice(start as int, end as int);
    //     let compact_slice_i = compact_slice.i_filtered(slice_ofs_map);

    //     compact_slice.i_filtered_from_domain(slice_ofs_map, 0);
    //     assert forall |k| #[trigger] compacted_buffer.map.contains_key(k)
    //     implies compacted_buffer.map[k] == compact_slice_i.map[k] 
    //     by {
    //         compact_slice.query_from_same_as_i_filtered(k, 0, slice_ofs_map);
    //     }
    //     assert(compacted_buffer =~= compact_slice_i);
    // }

    // #[verifier::spinoff_prover]
    // pub proof fn compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: Buffer)
    //     requires self.can_compact(start, end, compacted_buffer)
    //     ensures self.compact(start, end, compacted_buffer).i() == self.i()
    // {
    //     let result = self.compact(start, end, compacted_buffer);
    //     self.compact_wf(start, end, compacted_buffer);

    //     BetreeNode::i_wf_auto();
    //     BetreeNode::i_children_lemma_auto();
        
    //     assert(result.i().get_Node_children() =~= self.i().get_Node_children());

    //     let ofs_map = self.make_offset_map();
    //     let slice_ofs_map = ofs_map.decrement(start);
    //     let result_ofs_map = result.make_offset_map();
    //     let compact_slice = self.get_Node_buffers().slice(start as int, end as int);

    //     self.compact_buffer_property(start, end, compacted_buffer);

    //     assert forall |k|
    //     ({
    //         &&& #[trigger] result.i().get_Node_buffer().map.contains_key(k) <==> self.i().get_Node_buffer().map.contains_key(k)
    //         &&& result.i().get_Node_buffer().map.contains_key(k) ==> result.i().get_Node_buffer().map[k] == self.i().get_Node_buffer().map[k]
    //     }) by {
    //         result.i_buffer_domain();
    //         self.i_buffer_domain();
    //         compact_slice.i_filtered_from_domain(slice_ofs_map, 0);

    //         if result.i().get_Node_buffer().map.contains_key(k) {
    //             assert(self.key_in_domain(k));
    //             self.get_Node_pivots().route_lemma(k);
    //             let idx = choose |idx| result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, idx);
    //             if idx < start {
    //                 assert(self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, idx));
    //             } else if idx < start+1 {
    //                 let slice_idx = choose |slice_idx| compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, slice_idx);
    //                 assert(self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, start + slice_idx));
    //             } else {
    //                 assert(self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, idx + (end - start - 1)));
    //             }
    //             assert(self.i().get_Node_buffer().map.contains_key(k));

    //             self.query_from_refines(k);
    //             result.query_from_refines(k);

    //             let ofs = self.flushed_ofs(k) as int;
    //             let compacted_bufferseq = BufferSeq{buffers: seq![compacted_buffer]};
    //             assert(compacted_bufferseq.query_from(k, 1) == Message::Update{delta: nop_delta()});
    //             assert(compacted_buffer.query(k) == compacted_bufferseq.query_from(k, 0));

    //             if ofs < start {
    //                 if !compacted_buffer.map.contains_key(k) {
    //                     assert forall #![auto] |i| 0 <= i < compact_slice.len()
    //                     implies !compact_slice[i].map.contains_key(k)
    //                     by {
    //                         if compact_slice[i].map.contains_key(k) {
    //                             assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, i));
    //                             assert(false);
    //                         }
    //                     }
    //                     compact_slice.not_present_query_lemma(k, 0);
    //                 }
    //                 assert(compact_slice.query(k) == compacted_buffer.query(k));

    //                 let left = self.get_Node_buffers().slice(0, start as int);
    //                 BufferSeq::extend_buffer_seq_lemma(compact_slice, left, k, ofs);
    //                 BufferSeq::extend_buffer_seq_lemma(compacted_bufferseq, left, k, ofs);

    //                 assert(left.extend(compact_slice) =~= self.get_Node_buffers().slice(0, end as int));
    //                 assert(left.extend(compacted_bufferseq) =~= result.get_Node_buffers().slice(0, start as int + 1));

    //                 let right = self.get_Node_buffers().slice(end as int, self.get_Node_buffers().len() as int);
    //                 BufferSeq::extend_buffer_seq_lemma(right, self.get_Node_buffers().slice(0, end as int), k, ofs);
    //                 BufferSeq::extend_buffer_seq_lemma(right, result.get_Node_buffers().slice(0, start as int + 1), k, ofs);

    //                 assert(self.get_Node_buffers().slice(0, end as int).extend(right) =~= self.get_Node_buffers());
    //                 assert(result.get_Node_buffers().slice(0, start as int + 1).extend(right) =~= result.get_Node_buffers());
    //                 assert(result.i().get_Node_buffer().map[k] == self.i().get_Node_buffer().map[k]);
    //             } else if ofs < end {
    //                 if !compacted_buffer.map.contains_key(k) {
    //                     assert forall #![auto] |i| ofs-start <= i < compact_slice.len()
    //                     implies !compact_slice[i].map.contains_key(k)
    //                     by {
    //                         if compact_slice[i].map.contains_key(k) {
    //                             assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, i));
    //                             assert(false);
    //                         }
    //                     }
    //                     compact_slice.not_present_query_lemma(k, ofs-start);
    //                 }
    //                 assert(compact_slice.query_from(k, ofs-start) == compacted_buffer.query(k));

    //                 let right = self.get_Node_buffers().slice(end as int, self.get_Node_buffers().len() as int);
    //                 BufferSeq::extend_buffer_seq_lemma(right, compacted_bufferseq, k, 0);
    //                 BufferSeq::extend_buffer_seq_lemma(right, compact_slice, k, ofs-start);
    //                 BufferSeq::common_buffer_seqs(compact_slice.extend(right), self.get_Node_buffers(), ofs-start, start as int, k);
    //                 BufferSeq::common_buffer_seqs(compacted_bufferseq.extend(right), result.get_Node_buffers(), 0, start as int, k);
    //                 assert(result.i().get_Node_buffer().map[k] == self.i().get_Node_buffer().map[k]);
    //             } else {
    //                 BufferSeq::common_buffer_seqs(self.get_Node_buffers(), result.get_Node_buffers(), ofs, start+1-end, k);
    //             }
    //         }

    //         if self.i().get_Node_buffer().map.contains_key(k) {
    //             let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, idx);
    //             result.get_Node_pivots().route_lemma(k);
    //             if idx < start {
    //                 assert(result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, idx));
    //             } else if idx < end {
    //                 assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, idx-start));
    //                 assert(result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, start as int));
    //             } else {
    //                 assert(result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, idx - (end - start - 1)));
    //             }
    //             assert(result.i().get_Node_buffer().map.contains_key(k));
    //         }
    //     }
    //     assert(result.i().get_Node_buffer().map.dom() =~= self.i().get_Node_buffer().map.dom());
    //     assert(result.i().get_Node_buffer() =~= self.i().get_Node_buffer());
    // }
} // end impl BetreeNode

impl DiskView{
    pub open spec(checked) fn fresh_ranking_extension(self, r1: Ranking, r2: Ranking) -> bool
    {
        &&& r1.le(r2)
        &&& forall |addr| #![auto] !r1.contains_key(addr) && r2.contains_key(addr) ==> !self.entries.contains_key(addr)
    }

    pub proof fn subdisk_implies_ranking_validity(self, big: DiskView, ranking: Ranking)
        requires self.wf(), self.is_subdisk(big), big.valid_ranking(ranking)
        ensures self.valid_ranking(ranking)
    {
        assert forall |addr| self.entries.contains_key(addr) && #[trigger] ranking.contains_key(addr)
        implies self.node_children_respects_rank(ranking, addr)
        by {
            assert(big.entries.dom().contains(addr)); // trigger
            assert(self.entries.dom().contains(addr));
        }
    }
}

impl LinkedBetree{
    pub open spec(checked) fn disk_tight_wrt_reachable_betree_addrs(self) -> bool
        recommends self.acyclic()
    {
        self.dv.entries.dom() =~= self.reachable_betree_addrs()
    }

    pub open spec(checked) fn disk_tight_wrt_reachable_buffer_addrs(self) -> bool
        recommends self.acyclic()
    {
        self.buffer_dv.entries.dom() =~= self.reachable_buffer_addrs()
    }

    pub open spec(checked) fn inv(self) -> bool
    {
        &&& self.acyclic()
        &&& self.disk_tight_wrt_reachable_betree_addrs()
        &&& self.disk_tight_wrt_reachable_buffer_addrs()
        &&& self.has_root() ==> self.root().my_domain() == total_domain()
    }

    pub open spec /*XXX(checked)*/ fn i_children_seq(self, ranking: Ranking, start: nat) -> Seq<FilteredBetree_v::BetreeNode>
        recommends self.has_root(),
            self.valid_ranking(ranking),
            start <= self.root().children.len()
        decreases self.get_rank(ranking), 0nat, self.root().children.len() - start 
            when start <= self.root().children.len()
                && (self.root().valid_child_index(start) ==> 
                    self.child_at_idx(start).get_rank(ranking) < self.get_rank(ranking))
    {
        if start == self.root().children.len() {
            seq![]
        } else {
            let child = self.child_at_idx(start).i_node(ranking);
            seq![child] + self.i_children_seq(ranking, start+1)
        }
    }

    pub open spec/*XXX(checked)*/ fn i_children(self, ranking: Ranking) -> Seq<FilteredBetree_v::BetreeNode>
        recommends self.has_root(), self.valid_ranking(ranking)
        decreases self.get_rank(ranking), 1nat
    {
        self.i_children_seq(ranking, 0)
    }

    pub open spec/*XXX(checked)*/ fn i_node(self, ranking: Ranking) -> FilteredBetree_v::BetreeNode
        recommends self.valid_ranking(ranking)
        decreases self.get_rank(ranking), 2nat
    {
        if !self.has_root() {
            FilteredBetree_v::BetreeNode::Nil{}
        } else {
            let root = self.root();
            FilteredBetree_v::BetreeNode::Node{
                buffers: root.buffers.i(self.buffer_dv),
                pivots: root.pivots,
                children: self.i_children(ranking),
                flushed: root.flushed,
            }
        }
    }

    pub open spec(checked) fn i(self) -> FilteredBetree_v::BetreeNode
        recommends self.acyclic()
    {
        self.i_node(self.the_ranking())
    }

    pub proof fn i_children_seq_lemma(self, ranking: Ranking, start: nat)
        requires self.has_root(), 
            self.valid_ranking(ranking),
            start <= self.root().children.len()
        ensures 
            self.i_children_seq(ranking, start).len() == self.root().children.len()-start,
            forall |i| 0 <= i < self.i_children_seq(ranking, start).len() 
            ==> {
                &&& (#[trigger] self.i_children_seq(ranking, start)[i]).wf()
                &&& self.i_children_seq(ranking, start)[i] == self.child_at_idx((i+start) as nat).i_node(ranking)
            }
        decreases self.get_rank(ranking), 0nat, self.root().children.len()-start 
    {
        if start < self.root().children.len() {
            assert(self.root().valid_child_index(start)); // trigger
            self.child_at_idx(start).i_node_wf(ranking);
            self.i_children_seq_lemma(ranking, start+1);
        } 
    }

    pub proof fn i_children_lemma(self, ranking: Ranking)
        requires self.has_root(), self.valid_ranking(ranking)
        ensures 
            self.i_node(ranking).wf_children(),
            self.i_children(ranking).len() == self.root().children.len(),
            forall |i| (#[trigger]self.root().valid_child_index(i))
                ==> self.i_children(ranking)[i as int] == self.child_at_idx(i).i_node(ranking)
        decreases self.get_rank(ranking), 1nat
    {
        self.i_children_seq_lemma(ranking, 0);
    }  

    pub proof fn i_node_wf(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures self.i_node(ranking).wf()
        decreases self.get_rank(ranking), 2nat
    {
        if self.has_root() {
            self.i_children_lemma(ranking);
            let out = self.i_node(ranking);

            assert forall |i| (
                #[trigger] out.valid_child_index(i)
                && out.get_Node_children()[i as int].is_Node()
                && out.get_Node_children()[i as int].local_structure()    
            ) implies (
                out.get_Node_children()[i as int].my_domain() == out.child_domain(i)
            ) by {
                assert(self.root().valid_child_index(i));
            }
        }
    }

    pub proof fn i_wf(self)
        requires self.acyclic()
        ensures self.i().wf()
    {
        self.i_node_wf(self.the_ranking());
    }

    pub proof fn child_at_idx_acyclic(self, idx: nat)
        requires self.acyclic(), self.has_root(), self.root().valid_child_index(idx)
        ensures self.child_at_idx(idx).acyclic()
    {
        assert(self.child_at_idx(idx).valid_ranking(self.the_ranking()));
    }

    pub proof fn child_for_key_valid_index(self, k: Key)
        requires self.wf(), self.has_root(), self.root().key_in_domain(k)
        ensures 0 <= self.root().pivots.route(k),
            self.root().valid_child_index(self.root().pivots.route(k) as nat)
    {
        self.root().pivots.route_lemma(k);
    }

    pub proof fn child_for_key_acyclic(self, k: Key)
        requires self.acyclic(), self.has_root(), self.root().key_in_domain(k)
        ensures self.child_for_key(k).acyclic()
    {
        self.child_for_key_valid_index(k);
        assert(self.child_for_key(k).valid_ranking(self.the_ranking()));
    }

    pub proof fn i_children_ignores_ranking(self, r1: Ranking, r2: Ranking)
        requires self.wf(), self.has_root(),
            self.valid_ranking(r1), 
            self.valid_ranking(r2),
        ensures self.i_children(r1) == self.i_children(r2)
        decreases self.get_rank(r1), 0nat
    {
        let a = self.i_children(r1);
        let b = self.i_children(r2);

        self.i_children_lemma(r1);
        self.i_children_lemma(r2);

        assert forall |i| 0 <= i < a.len()
        implies a[i] == b[i]
        by {
            assert(self.root().valid_child_index(i as nat));
            assert(a[i] == self.child_at_idx(i as nat).i_node(r1));
            self.child_at_idx(i as nat).i_node_ignores_ranking(r1, r2);
        }
        assert(a =~= b);
    }

    pub proof fn i_node_ignores_ranking(self, r1: Ranking, r2: Ranking)
        requires self.wf(), self.valid_ranking(r1), self.valid_ranking(r2)
        ensures self.i_node(r1) == self.i_node(r2)
        decreases self.get_rank(r1), 1nat
    {
        if self.has_root() {
            self.i_children_ignores_ranking(r1, r2);
        }
    }

    pub proof fn child_at_idx_commutes_with_i(self, idx: nat) 
        requires 
            self.acyclic(),
            self.has_root(),
            self.root().valid_child_index(idx), 
            self.i().valid_child_index(idx),
        ensures 
            self.child_at_idx(idx).i() == self.i().get_Node_children()[idx as int]
    {
        let child = self.child_at_idx(idx);
        self.child_at_idx_acyclic(idx);
        self.i_children_lemma(self.the_ranking());
        child.i_node_ignores_ranking(self.the_ranking(), child.the_ranking());
    }

    pub proof fn child_for_key_commutes_with_i(self, k: Key)
        requires self.acyclic(), self.has_root(), self.root().key_in_domain(k)
        ensures 
            self.child_for_key(k).acyclic(),
            self.child_for_key(k).i() == self.i().child(k)
    {
        PivotTable::route_lemma_auto();
        self.child_for_key_acyclic(k);
        self.child_for_key_valid_index(k);
        self.i_children_lemma(self.the_ranking());
        self.child_at_idx_commutes_with_i(self.root().pivots.route(k) as nat);
    }

    pub proof fn indexiness_commutes_with_i(self)
        requires self.acyclic(), self.has_root()
        ensures 
            self.root().is_index() ==> self.i().is_index(),
            self.root().is_leaf() ==> self.i().is_leaf()
    {
        self.i_wf();
        self.i_children_lemma(self.the_ranking());

        if self.root().is_index() {
            assert forall |i:nat| 0 <= i < self.i().get_Node_children().len()
            implies #[trigger] self.i().get_Node_children()[i as int].is_Node()
            by {
                assert(self.root().valid_child_index(i));
            }
        }
    }

    pub proof fn betree_subdisk_implies_same_i_with_ranking(self, big: LinkedBetree, ranking: Ranking)
        requires 
            self.wf(), big.wf(),
            self.root == big.root,
            self.dv.is_subdisk(big.dv),
            self.buffer_dv.is_subdisk(big.buffer_dv),
            big.valid_ranking(ranking),
        ensures
            self.valid_ranking(ranking),
            self.i_node(ranking) == big.i_node(ranking)
        decreases self.get_rank(ranking), big.get_rank(ranking)
    {
        self.dv.subdisk_implies_ranking_validity(big.dv, ranking);
        assert(self.valid_ranking(ranking));

        if self.has_root() {
            self.root().buffers.subdisk_implies_same_i(self.buffer_dv, big.buffer_dv);

            self.i_children_lemma(ranking);
            big.i_children_lemma(ranking);

            let a = self.i_node(ranking).get_Node_children();
            let b = big.i_node(ranking).get_Node_children();
            assert(a.len() == b.len());

            assert forall |i| 0 <= i < a.len()
            implies a[i] == b[i]
            by {
                assert(self.root().valid_child_index(i as nat));
                assert(big.root().valid_child_index(i as nat));

                self.child_at_idx_acyclic(i as nat);
                big.child_at_idx_acyclic(i as nat);

                self.child_at_idx(i as nat).betree_subdisk_implies_same_i_with_ranking(big.child_at_idx(i as nat), ranking);
   
            }
            assert(a =~= b);
        }
    }

    pub proof fn reachable_addrs_using_ranking_recur_body_lemma(self, ranking: Ranking, child_idx: nat)
        requires self.can_recurse_for_reachable(ranking, child_idx)
        ensures 
            forall |i| child_idx <= i < self.child_count() ==>
                (#[trigger]self.child_at_idx(i).reachable_addrs_using_ranking(ranking)
                ).subset_of(self.reachable_addrs_using_ranking_recur(ranking, child_idx))
        decreases self.child_count() - child_idx
    {
        if child_idx < self.child_count() {
            assert(self.root().valid_child_index(child_idx)); // trigger
            self.reachable_addrs_using_ranking_recur_body_lemma(ranking, child_idx+1);
        }
    }

    pub open spec(checked) fn child_subtree_contains_addr(self, ranking: Ranking, addr: Address, start: nat, i: nat) -> bool
        recommends self.wf(), self.valid_ranking(ranking)
    {
        &&& start <= i < self.child_count()
        &&& self.child_at_idx(i).valid_ranking(ranking)
        &&& self.child_at_idx(i).reachable_addrs_using_ranking(ranking).contains(addr)
    }

    pub proof fn reachable_addrs_using_ranking_recur_closed(self, ranking: Ranking, child_idx: nat)
        requires self.can_recurse_for_reachable(ranking, child_idx)
        ensures
            forall |addr| #[trigger] self.reachable_addrs_using_ranking_recur(ranking, child_idx).contains(addr)
                ==> (exists |i| self.child_subtree_contains_addr(ranking, addr, child_idx, i))
        decreases self.get_rank(ranking), self.child_count() - child_idx
    {
        if child_idx < self.child_count() {
            assert(self.root().valid_child_index(child_idx)); // trigger
            self.child_at_idx_acyclic(child_idx);

            let child = self.child_at_idx(child_idx);
            assert(child.valid_ranking(ranking));

            let child_addrs = self.child_at_idx(child_idx).reachable_addrs_using_ranking(ranking);
            let right_subtree_addrs = self.reachable_addrs_using_ranking_recur(ranking, child_idx + 1);

            self.child_at_idx(child_idx).reachable_addrs_using_ranking_closed(ranking);
            self.reachable_addrs_using_ranking_recur_closed(ranking, child_idx+1);

            assert forall |addr| #[trigger] self.reachable_addrs_using_ranking_recur(ranking, child_idx).contains(addr)
            implies (exists |i|  #[trigger]self.child_subtree_contains_addr(ranking, addr, child_idx, i))
            by {
                if right_subtree_addrs.contains(addr) {
                    let i = choose |i| #[trigger] self.child_subtree_contains_addr(ranking, addr, child_idx+1, i);
                    assert(self.child_subtree_contains_addr(ranking, addr, child_idx, i));
                } else {
                    assert(child_addrs.contains(addr));
                    assert(child.has_root() ==> child_addrs.contains(child.root.unwrap()));
                    assert(self.child_subtree_contains_addr(ranking, addr, child_idx, child_idx));
                }
            }
        }
    } 

    pub proof fn reachable_addrs_using_ranking_closed(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures 
            self.has_root() ==> self.reachable_addrs_using_ranking(ranking).contains(self.root.unwrap()),
            forall |addr| #[trigger] self.reachable_addrs_using_ranking(ranking).contains(addr) && Some(addr) != self.root
                ==> (exists |i| self.child_subtree_contains_addr(ranking, addr, 0, i))
        decreases self.get_rank(ranking)
    {
        if self.has_root() {
            let sub_tree_addrs = self.reachable_addrs_using_ranking_recur(ranking, 0);
            self.reachable_addrs_using_ranking_recur_closed(ranking, 0);
            assert(sub_tree_addrs.insert(self.root.unwrap()) =~= self.reachable_addrs_using_ranking(ranking));
        }
    }

    pub proof fn reachable_addrs_are_closed(self, ranking: Ranking, addr: Address)
        requires 
            self.wf(), self.has_root(), 
            self.valid_ranking(ranking),
            self.reachable_addrs_using_ranking(ranking).contains(addr),
            self.dv.entries.dom().contains(addr),
        ensures ({
            let node = self.dv.entries[addr];
            &&& forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int].is_Some() 
                ==> self.reachable_addrs_using_ranking(ranking).contains(node.children[i as int].unwrap())
        })
        decreases self.get_rank(ranking)
    {
        let node = self.dv.entries[addr];
        let reachable_addrs = self.reachable_addrs_using_ranking(ranking);
        self.reachable_addrs_using_ranking_closed(ranking);

        assert forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int].is_Some() 
        implies reachable_addrs.contains(node.children[i as int].unwrap())
        by {
            if addr == self.root.unwrap() {
                self.child_at_idx(i).reachable_addrs_using_ranking_closed(ranking);
                assert(self.child_at_idx(i).has_root());
                self.reachable_addrs_using_ranking_recur_body_lemma(ranking, 0);
                assert(reachable_addrs.contains(node.children[i as int].unwrap()));
            } else {
                assert(self.reachable_addrs_using_ranking(ranking).contains(addr));
                let i = choose |i| self.child_subtree_contains_addr(ranking, addr, 0, i);
                assert(self.root().valid_child_index(i)); // trigger
                self.child_at_idx(i).reachable_addrs_are_closed(ranking, addr);
                self.reachable_addrs_using_ranking_recur_body_lemma(ranking, 0);
            }
        }
    }

    pub proof fn build_tight_preserves_wf(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures self.build_tight_tree().wf()
        decreases self.get_rank(ranking)
    {
        let result = self.build_tight_tree();

        assert forall |addr| #[trigger] result.dv.entries.contains_key(addr)
        implies {
            &&& result.dv.node_has_nondangling_child_ptrs(result.dv.entries[addr])
            &&& result.dv.node_has_linked_children(result.dv.entries[addr])
        } by {
            self.reachable_addrs_are_closed(self.the_ranking(), addr);
        }

        assert(result.dv.wf());
        assert(result.dv.is_nondangling_ptr(result.root));
        assert(result.dv.is_fresh(result.buffer_dv.repr()));
        assume(result.dv.no_dangling_buffer_ptr(result.buffer_dv));
    }

} // end impl LinkedBetree

pub open spec(checked) fn i_stamped_betree(stamped: StampedBetree) -> FilteredBetree_v::StampedBetree
    recommends stamped.value.acyclic()
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::QueryReceiptLine
        recommends self.linked.acyclic()
    {
        FilteredBetree_v::QueryReceiptLine{ node: self.linked.i(), result: self.result }
    }
}

impl QueryReceipt{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::QueryReceipt
        recommends self.valid()
    {
        let ranking = self.linked.the_ranking();
        // Note(verus): spec(checked) is not checked when calling as a closure
        FilteredBetree_v::QueryReceipt{
            key: self.key,
            root: self.linked.i(),
            lines: Seq::new(self.lines.len(), |i:int| self.lines[i].i())
        }
    }

    pub proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
    {
        PivotTable::route_lemma_auto();

        let i_receipt = self.i();
        let ranking = self.linked.the_ranking();

        assert forall #![auto] |i:int| 0 <= i < i_receipt.lines.len()
        implies i_receipt.lines[i].wf()
        by {
            self.lines[i].linked.i_wf();
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies {
            &&& #[trigger] i_receipt.lines[i].node.key_in_domain(self.key)
            &&& i_receipt.child_linked_at(i) 
        } by {
            assert(self.node(i).key_in_domain(self.key)); // trigger
            self.lines[i].linked.child_for_key_commutes_with_i(self.key);
            assert(self.child_linked_at(i)); // trigger
            assert(self.result_linked_at(i)); // trigger
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.result_linked_at(i) by {
            assert(self.result_linked_at(i)); // trigger
            let node = self.node(i);
            let start = node.flushed_ofs(self.key) as int;
            node.buffers.query_from_commutes_with_i(self.linked.buffer_dv, self.key, start);
        }
        assert(i_receipt.all_lines_wf()); // trigger
    }
}

pub proof fn path_addrs_to_set_additive(path_addrs: PathAddrs)
    requires path_addrs.len() > 0
    ensures path_addrs.to_set() == set![path_addrs[0]] + path_addrs.subrange(1, path_addrs.len() as int).to_set()
{
    let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
    let a = set![path_addrs[0]] + sub_path_addrs.to_set();
    let b = path_addrs.to_set();

    // TODO(verus): lack additive seq to set lemma
    assert forall |addr| a.contains(addr) <==> b.contains(addr)
    by {
        if a.contains(addr) {
            if sub_path_addrs.contains(addr) {
                let idx = choose |idx| 0 <= idx < sub_path_addrs.len() && sub_path_addrs[idx] == addr;
                assert(sub_path_addrs[idx] == path_addrs[idx + 1]);
            }
        }
        if b.contains(addr) {
            let idx = choose |idx| 0 <= idx < path_addrs.len() && path_addrs[idx] == addr;
            if idx > 0 {
                assert(sub_path_addrs[idx-1] == path_addrs[idx]);
            }
        }
    }
    assert(a =~= b);
}

impl Path{
    pub open spec(checked) fn i(self) -> FilteredBetree_v::Path
        recommends self.valid()
    {
        FilteredBetree_v::Path{node: self.linked.i(), key: self.key, depth: self.depth}
    }

    pub proof fn valid_ranking_throughout(self, ranking: Ranking)
        requires self.valid(), self.linked.valid_ranking(ranking)
        ensures 0 < self.depth ==> self.subpath().linked.valid_ranking(ranking),
            self.target().valid_ranking(ranking)
        decreases self.depth
    {
        if 0 < self.depth {
            self.linked.child_for_key_valid_index(self.key);
            self.subpath().valid_ranking_throughout(ranking);
        }
    }

    pub proof fn subpath_commutes_with_i(self)
        requires 0 < self.depth, self.valid()
        ensures
            self.subpath().linked.acyclic(), 
            self.subpath().i() == self.i().subpath()
    {
        self.valid_ranking_throughout(self.linked.the_ranking());
        self.linked.child_for_key_commutes_with_i(self.key);
    }

    pub proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
        decreases self.depth
    {
        self.linked.i_wf();
        if 0 < self.depth {
            self.valid_ranking_throughout(self.linked.the_ranking());
            self.subpath().i_valid();
            self.subpath_commutes_with_i();
            self.linked.indexiness_commutes_with_i();
        }
    }

    pub proof fn target_commutes_with_i(self) 
        requires self.valid(), self.linked.acyclic()
        ensures 
            self.target().acyclic(),
            self.i().valid(), 
            self.i().target() == self.target().i()
        decreases self.depth
    {
        self.valid_ranking_throughout(self.linked.the_ranking());
        self.i_valid();
        if 0 < self.depth {
            self.subpath().target_commutes_with_i();
            self.subpath_commutes_with_i();
        }
    }

    pub proof fn betree_diskview_diff(self, replacement: LinkedBetree, path_addrs: PathAddrs)
        requires 
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
        ensures 
            self.substitute(replacement, path_addrs).dv.entries.dom() =~= replacement.dv.entries.dom() + path_addrs.to_set()
        decreases self.depth
    {
        let result = self.substitute(replacement, path_addrs);

        if 0 < self.depth {
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().betree_diskview_diff(replacement, sub_path_addrs);
            path_addrs_to_set_additive(path_addrs);
        }
    }

    pub proof fn substitute_preserves_wf(self, replacement: LinkedBetree, path_addrs: PathAddrs)
        requires 
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
            self.linked.is_fresh(path_addrs.to_set()),
            replacement.is_fresh(path_addrs.to_set()),
        ensures ({
            let result = self.substitute(replacement, path_addrs);
            &&& result.wf()
            &&& result.has_root()
            &&& result.root().my_domain() == self.linked.root().my_domain()
            &&& self.linked.dv.is_subdisk(result.dv)
            &&& self.linked.buffer_dv.is_subdisk(result.buffer_dv)
            &&& result.dv.entries.dom() =~= (self.linked.dv.entries.dom() + replacement.dv.entries.dom() + path_addrs.to_set())
        })
        decreases self.depth, 1nat
    {
        if 0 < self.depth {
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().substitute_preserves_wf(replacement, sub_path_addrs);
            path_addrs_to_set_additive(path_addrs);

            let result = self.substitute(replacement, path_addrs);
            let node = result.dv.entries[path_addrs[0]];

            let r = node.pivots.route(self.key);
            PivotTable::route_lemma_auto();
            assert(self.linked.dv.entries.contains_key(self.linked.root.unwrap())); // trigger

            assert forall |i| #[trigger] node.valid_child_index(i)
            implies {
                &&& result.dv.is_nondangling_ptr(node.children[i as int])
                &&& result.dv.child_linked(node, i)
            } by {
                assert(self.linked.root().valid_child_index(i)); // trigger
                if i != r {
                    assert(self.linked.dv.is_nondangling_ptr(node.children[i as int]));
                    assert(self.linked.dv.child_linked(self.linked.root(), i));
                    assert(result.dv.is_nondangling_ptr(node.children[i as int]));
                    assert(result.dv.child_linked(node, i));
                }
            }
            self.betree_diskview_diff(replacement, path_addrs);
            assert(self.linked.root().buffers.valid(self.linked.buffer_dv)); // trigger            
            assert(result.root().buffers.valid(result.buffer_dv));
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn ranking_after_substitution(self, replacement: LinkedBetree, path_addrs: PathAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
            replacement.valid_ranking(ranking),
            ranking.contains_key(self.linked.root.unwrap()),
            path_addrs.to_set().disjoint(ranking.dom()),
            self.linked.is_fresh(path_addrs.to_set()),
            replacement.is_fresh(path_addrs.to_set()),
        ensures 
            self.substitute(replacement, path_addrs).valid_ranking(new_ranking),
            self.linked.dv.fresh_ranking_extension(ranking, new_ranking),
            new_ranking.dom() =~= ranking.dom() + path_addrs.to_set()
        decreases self.depth
    {
        self.substitute_preserves_wf(replacement, path_addrs);
        PivotTable::route_lemma_auto();

        if self.depth == 0 {
            ranking
        } else {
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().substitute_preserves_wf(replacement, sub_path_addrs);

            self.linked.dv.subdisk_implies_ranking_validity(replacement.dv, ranking);
            assert(self.linked.valid_ranking(ranking));
            self.valid_ranking_throughout(ranking);

            let r = self.linked.root().pivots.route(self.key);
            assert(self.linked.root().valid_child_index(r as nat)); // trigger
            assert(self.subpath().linked.has_root());

            let intermediate_ranking = self.subpath().ranking_after_substitution(replacement, sub_path_addrs, ranking);
            let new_root_addr = path_addrs[0];
            let old_root_rank = intermediate_ranking[self.linked.root.unwrap()];
            let subtree_root_rank = intermediate_ranking[subtree.root.unwrap()];
            let new_root_rank = old_root_rank + subtree_root_rank + 1;
          
            let new_ranking = intermediate_ranking.insert(new_root_addr, new_root_rank);
            let result = self.substitute(replacement, path_addrs);

            assert forall |addr| #[trigger] new_ranking.contains_key(addr) && result.dv.entries.contains_key(addr)
            implies result.dv.node_children_respects_rank(new_ranking, addr)
            by {
                self.betree_diskview_diff(replacement, path_addrs);
                if addr == new_root_addr {
                    let node = result.dv.entries[addr];
                    assert forall |i| #[trigger] node.valid_child_index(i) && node.children[i as int].is_Some()
                    implies {
                        &&& new_ranking.contains_key(node.children[i as int].unwrap())
                        &&& new_ranking[node.children[i as int].unwrap()] < new_ranking[addr]
                    } by {
                        assert(self.linked.root().valid_child_index(i)); // trigger
                        if i != r {
                            assert(intermediate_ranking.contains_key(node.children[i as int].unwrap()));
                            assert(intermediate_ranking.contains_key(self.linked.root.unwrap()));
                            assert(self.linked.root().valid_child_index(i));

                            assert(new_ranking.contains_key(node.children[i as int].unwrap()));
                            assert(new_ranking[node.children[i as int].unwrap()] < new_ranking[addr]);
                        }
                    }
                }
            }
            path_addrs_to_set_additive(path_addrs);
            new_ranking
        }
    }

    pub proof fn substitute_commutes_with_i(self, replacement: LinkedBetree, path_addrs: PathAddrs, ranking: Ranking)
        requires 
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
            self.linked.valid_ranking(ranking),
            replacement.valid_ranking(ranking),
            ranking.contains_key(self.linked.root.unwrap()),
            path_addrs.to_set().disjoint(ranking.dom()),
            self.linked.is_fresh(path_addrs.to_set()),
            replacement.is_fresh(path_addrs.to_set()),
        ensures 
            self.substitute(replacement, path_addrs).acyclic(), 
            self.i().can_substitute(replacement.i()),
            self.substitute(replacement, path_addrs).i() === self.i().substitute(replacement.i())
        decreases self.depth
    {        
        self.i_valid();
        replacement.i_wf();

        if 0 < self.depth {
            let new_ranking = self.ranking_after_substitution(replacement, path_addrs, ranking);
            let result = self.substitute(replacement, path_addrs);

            self.substitute_preserves_wf(replacement, path_addrs);
            assert(result.valid_ranking(new_ranking));

            result.i_node_ignores_ranking(result.the_ranking(), new_ranking);
            self.target_commutes_with_i();

            PivotTable::route_lemma_auto();
            result.i_children_lemma(result.the_ranking());
            self.linked.i_children_lemma(self.linked.the_ranking());

            let r = self.linked.root().pivots.route(self.key);
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            let new_children = self.linked.root().children.update(r, subtree.root);

            assert forall |i| 0 <= i < result.i().get_Node_children().len()
            implies #[trigger] result.i().get_Node_children()[i] == self.i().substitute(replacement.i()).get_Node_children()[i]
            by {
                assert(self.linked.root().valid_child_index(i as nat));
                assert(result.root().valid_child_index(i as nat));

                self.linked.child_at_idx_acyclic(i as nat);
                result.child_at_idx_acyclic(i as nat);

                let child = self.linked.child_at_idx(i as nat);
                let new_child = result.child_at_idx(i as nat);
                if i == r {
                    result.child_at_idx_commutes_with_i(i as nat);
                    new_child.i_node_ignores_ranking(result.the_ranking(), new_child.the_ranking());
                    
                    self.subpath().substitute_commutes_with_i(replacement, sub_path_addrs, ranking);
                    self.subpath().betree_diskview_diff(replacement, sub_path_addrs);
                    self.betree_diskview_diff(replacement, path_addrs);
                    self.subpath_commutes_with_i();

                    subtree.dv.subdisk_implies_ranking_validity(new_child.dv, new_child.the_ranking());
                    subtree.betree_subdisk_implies_same_i_with_ranking(new_child, new_child.the_ranking());
                    subtree.i_node_ignores_ranking(subtree.the_ranking(), new_child.the_ranking());
                } else {
                    child.dv.subdisk_implies_ranking_validity(new_child.dv, new_ranking);
                    child.betree_subdisk_implies_same_i_with_ranking(new_child, new_ranking);
                    child.i_node_ignores_ranking(new_ranking, self.linked.the_ranking());
                    new_child.i_node_ignores_ranking(new_ranking, result.the_ranking());
                }
            }
            assert(result.i().get_Node_children() =~= self.i().substitute(replacement.i()).get_Node_children());
            result.root().buffers.subdisk_implies_same_i(self.linked.buffer_dv, result.buffer_dv);
            assert(result.i().get_Node_buffers() =~= self.i().substitute(replacement.i()).get_Node_buffers());
        }
    }

    // pub proof fn substitute_noop(self, replacement: BetreeNode)
    //     requires self.valid(), replacement.wf(), 
    //         self.target().i() == replacement.i()
    //     ensures 
    //         self.substitute(replacement).wf(),
    //         self.substitute(replacement).i() == self.node.i()
    //     decreases self.depth
    // {
    //     self.target_wf();
    //     self.substitute_preserves_wf(replacement);

    //     PivotTable::route_lemma_auto();
    //     BetreeNode::i_children_lemma_auto();

    //     if 0 < self.depth {
    //         self.subpath().substitute_noop(replacement);
    //         assert(self.substitute(replacement).i().get_Node_children() =~= self.node.i().get_Node_children());
    //         assert(self.substitute(replacement).make_offset_map() =~= self.node.make_offset_map());
    //     }
    // }
}

impl LinkedBetreeVars::Label {
    pub open spec(checked) fn i(self) -> FilteredBetree::Label
    {
        match self {
            LinkedBetreeVars::Label::Query{end_lsn, key, value} => FilteredBetree::Label::Query{end_lsn: end_lsn, key: key, value: value},
            LinkedBetreeVars::Label::Put{puts} => FilteredBetree::Label::Put{puts: puts},
            LinkedBetreeVars::Label::FreezeAs{stamped_betree} =>
                FilteredBetree::Label::FreezeAs{stamped_betree:
                    if stamped_betree.value.acyclic() { 
                        i_stamped_betree(stamped_betree) 
                    } else { arbitrary() } },
                    LinkedBetreeVars::Label::Internal{} => FilteredBetree::Label::Internal{},
        }
    }
} // end impl LinkedBetreeVars::Label

impl LinkedBetreeVars::State {
    pub open spec(checked) fn inv(self) -> bool 
    {
        &&& self.wf()
        &&& self.linked.inv()
    }

    pub open spec(checked) fn i(self) -> FilteredBetree::State
        recommends self.wf(), self.linked.acyclic()
    {
        FilteredBetree::State{root: self.linked.i(), memtable: self.memtable}
    }

    pub proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires LinkedBetreeVars::State::initialize(self, stamped_betree), stamped_betree.value.inv()
        ensures FilteredBetree::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        self.linked.i_wf();
    }

    pub proof fn query_refines(self, post: Self, lbl: LinkedBetreeVars::Label, receipt: QueryReceipt)
        requires self.inv(), LinkedBetreeVars::State::query(self, post, lbl, receipt)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        receipt.i_valid();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::query(receipt.i())));
    }

    pub proof fn put_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), LinkedBetreeVars::State::put(self, post, lbl)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::put()));
    }

    pub proof fn freeze_as_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
        requires self.inv(), LinkedBetreeVars::State::freeze_as(self, post, lbl)
        ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        self.linked.i_wf();
        assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::freeze_as()));
    }

    // pub proof fn internal_flush_memtable_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
    //     requires self.inv(), LinkedBetreeVars::State::internal_flush_memtable(self, post, lbl)
    //     ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(FilteredBetree::State::next);
    //     reveal(FilteredBetree::State::next_by);

        // first need to show inv is real

    //     self.root.i_wf();
    //     self.root.promote_commutes_with_i(total_domain());

    //     let promote = self.root.promote(total_domain());
    //     let buffers = BufferSeq{buffers: seq![self.memtable.buffer]};

    //     promote.extend_buffer_seq_wf(buffers);
    //     promote.extend_buffer_seq_refines_merge_buffer(buffers);

    //     let a = self.root.push_memtable(self.memtable).i();
    //     let b = self.root.i().push_memtable(self.memtable);
        
    //     BetreeNode::i_children_lemma_auto();
    //     assert(a.get_Node_children() =~= b.get_Node_children());

    //     assert(buffers.i().apply_filter(total_domain().key_set()) =~= buffers.i());
    //     assert(buffers.i_from(1) == Buffer::empty()); // trigger
    //     assert(buffers.i() =~= buffers[0]);
    //     assert(a.get_Node_buffer() == b.get_Node_buffer());
    //     assume(false);
    //     assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush_memtable()));
    // }

    // pub proof fn internal_grow_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
    //     requires self.inv(), LinkedBetreeVars::State::internal_grow(self, post, lbl)
    //     ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(FilteredBetree::State::next);
    //     reveal(FilteredBetree::State::next_by);

    //     BetreeNode::i_wf_auto();
    //     PivotTable::route_lemma_auto();
    //     post.root.i_children_lemma();
    //     assert(post.i().root =~= self.i().root.grow());
    //     assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_grow()));
    // }

    // pub proof fn internal_split_refines(self, post: Self, lbl: LinkedBetreeVars::Label, path: Path, request: SplitRequest)
    //     requires self.inv(), LinkedBetreeVars::State::internal_split(self, post, lbl, path, request)
    //     ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(FilteredBetree::State::next);
    //     reveal(FilteredBetree::State::next_by);

    //     BetreeNode::i_wf_auto();

    //     path.target().split_parent_wf(request);
    //     path.substitute_commutes_with_i(path.target().split_parent(request));

    //     path.i_valid();
    //     path.target_commutes_with_i();
    //     path.target().split_parent_commutes_with_i(request);

    //     assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_split(path.i(), request)));
    // }

    // pub proof fn internal_flush_refines(self, post: Self, lbl: LinkedBetreeVars::Label, path: Path, child_idx: nat, buffer_gc: nat)
    //     requires self.inv(), LinkedBetreeVars::State::internal_flush(self, post, lbl, path, child_idx, buffer_gc)
    //     ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(FilteredBetree::State::next);
    //     reveal(FilteredBetree::State::next_by);

    //     BetreeNode::i_wf_auto();
    //     path.target().flush_wf(child_idx, buffer_gc);
    //     path.substitute_commutes_with_i(path.target().flush(child_idx, buffer_gc));

    //     path.i_valid();
    //     path.target_commutes_with_i();
    //     path.target().flush_commutes_with_i(child_idx, buffer_gc);

    //     assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_flush(path.i(), child_idx)));
    // }

    // pub proof fn internal_compact_refines(self, post: Self, lbl: LinkedBetreeVars::Label, path: Path, start: nat, end: nat, compacted_buffer: Buffer)
    //     requires self.inv(), LinkedBetreeVars::State::internal_compact(self, post, lbl, path, start, end, compacted_buffer)
    //     ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(FilteredBetree::State::next);
    //     reveal(FilteredBetree::State::next_by);

    //     BetreeNode::i_wf_auto();
    //     path.target().compact_wf(start, end, compacted_buffer);
    //     path.target().compact_commutes_with_i(start, end, compacted_buffer);
    //     path.substitute_noop(path.target().compact(start, end, compacted_buffer));        

    //     assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop()));
    // }

    // pub proof fn internal_noop_noop(self, post: Self, lbl: LinkedBetreeVars::Label)
    //     requires self.inv(), LinkedBetreeVars::State::internal_noop(self, post, lbl)
    //     ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i())
    // {
    //     reveal(FilteredBetree::State::next);
    //     reveal(FilteredBetree::State::next_by);

    //     BetreeNode::i_wf_auto();
    //     assert(FilteredBetree::State::next_by(self.i(), post.i(), lbl.i(), FilteredBetree::Step::internal_noop()));
    // }

    // pub proof fn next_refines(self, post: Self, lbl: LinkedBetreeVars::Label)
    //     requires self.inv(), LinkedBetreeVars::State::next(self, post, lbl),
    //     ensures post.inv(), FilteredBetree::State::next(self.i(), post.i(), lbl.i()),
    // {
    //     reveal(LinkedBetreeVars::State::next);
    //     reveal(LinkedBetreeVars::State::next_by);

    //     match choose |step| LinkedBetreeVars::State::next_by(self, post, lbl, step)
    //     {
    //         LinkedBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
    //         LinkedBetree::Step::put() => { self.put_refines(post, lbl); }
    //         LinkedBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
    //         LinkedBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_refines(post, lbl); }
    //         LinkedBetree::Step::internal_grow() => { self.internal_grow_refines(post, lbl); }
    //         LinkedBetree::Step::internal_split(path, split_request) => { self.internal_split_refines(post, lbl, path, split_request); }
    //         LinkedBetree::Step::internal_flush(path, child_idx, buffer_gc) => { self.internal_flush_refines(post, lbl, path, child_idx, buffer_gc); }
    //         LinkedBetree::Step::internal_compact(path, start, end, compacted_buffer) => { self.internal_compact_refines(post, lbl, path, start, end, compacted_buffer); }
    //         LinkedBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
    //         _ => { assert(false); } 
    //     }
    // }
} // end impl LinkedBetreeVars::State

}//verus
