#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::map::*;
use vstd::seq_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::PivotBetree_v;
use crate::betree::PivotBetree_v::PivotBetree;
use crate::betree::FilteredBetree_v::*;
use crate::betree::SplitRequest_v::*;

verus! {

impl BetreeNode {
    pub open spec fn i_buffer(self) -> Buffer
        recommends self.wf(), self.is_Node()
    {
        let offset_map = self.make_offset_map();
        self.get_Node_buffers().i_filtered(offset_map)
    }

    pub open spec fn i_children_seq(self, start: int) -> Seq<PivotBetree_v::BetreeNode>
    recommends self.is_Node(), 0 <= start <= self.get_Node_children().len()
    decreases self, 0nat, self.get_Node_children().len()-start 
        when self.is_Node() && 0 <= start <= self.get_Node_children().len()
    {
        if start == self.get_Node_children().len() {
            seq![]
        } else {
            let child = self.get_Node_children()[start].i();
            seq![child] + self.i_children_seq(start+1)
        }
    }

    pub open spec fn i_children(self) -> Seq<PivotBetree_v::BetreeNode>
        recommends self.is_Node()
        decreases self, 1nat
    {
        self.i_children_seq(0)
    }

    pub open spec fn i(self) -> PivotBetree_v::BetreeNode
        recommends self.wf()
        decreases self
    {
        if self.is_Nil() {
            PivotBetree_v::BetreeNode::Nil{}
        } else {
            PivotBetree_v::BetreeNode::Node{
                pivots: self.get_Node_pivots(),
                buffer: self.i_buffer(), 
                children: self.i_children()
            }
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

            child.i_wf();
            self.i_children_seq_lemma(start+1);
        }
    }

    pub proof fn i_children_lemma(self)
        requires self.is_Node(), self.wf()
        ensures 
            self.get_Node_children().len() == self.i_children().len(),
            forall |i| 0 <= i < self.get_Node_children().len()
            ==> {
                &&& (#[trigger] self.i_children()[i]).wf()
                &&& self.i_children()[i] == self.get_Node_children()[i].i()
            }
        decreases self, 1nat
    {
        self.i_children_seq_lemma(0);
    }

    pub proof fn i_children_lemma_auto()
        ensures 
            forall |node: Self| node.wf() && node.is_Node() 
            ==> {
                &&&  (#[trigger]node.get_Node_children()).len() == node.i_children().len()
                &&&  forall |i| 0 <= i < node.get_Node_children().len() 
                ==> {
                    &&& (#[trigger] node.i_children()[i]).wf()
                    &&& node.i_children()[i] == node.get_Node_children()[i].i()
                }
            }
    {
        assert forall |node: Self| node.wf() && node.is_Node()
        implies {
            &&& (#[trigger] node.get_Node_children()).len() == node.i_children().len()
            &&& (forall |i| 0 <= i < node.get_Node_children().len() ==> {
                &&& (#[trigger] node.i_children()[i]).wf()
                &&& node.i_children()[i] == node.get_Node_children()[i].i()
            })
        } by {
            node.i_children_lemma();
        }
    }

    pub proof fn i_wf(self)
        requires self.wf()
        ensures self.i().wf(), self.is_Node() ==> self.my_domain() == self.i().my_domain()
        decreases self, 2nat
    {
        if self.is_Node() {
            self.i_children_lemma();
            assert(self.wf_children()); // trigger
        }
    }

    pub proof fn i_wf_auto()
        ensures 
            forall |node: Self| node.wf() ==> {
                &&& (#[trigger]node.i()).wf()
                &&& node.is_Node() ==> node.my_domain() == node.i().my_domain()
            }
    {
        assert forall |node: Self| node.wf()
        implies {
            &&& (#[trigger]node.i()).wf()
            &&& node.is_Node() ==> node.my_domain() == node.i().my_domain()
        } by {
            node.i_wf();
        }
    }

    pub proof fn query_from_same_as_i_filtered(self, key: Key, buffer_idx: int, offset_map: OffsetMap)
        requires 
            self.wf(), 
            self.is_Node(),
            self.key_in_domain(key),
            0 <= buffer_idx <= self.get_Node_buffers().len(),
            offset_map.is_total(),
            self.flushed_ofs(key) <= buffer_idx ==> offset_map.offsets[key] == 0,
            self.flushed_ofs(key) > buffer_idx ==> offset_map.offsets[key] == self.flushed_ofs(key) - buffer_idx
        ensures ({
            let start = self.flushed_ofs(key) as int;
            let query_idx = if buffer_idx < start { start } else { buffer_idx };
            &&& self.get_Node_buffers().i_filtered_from(offset_map, buffer_idx).query(key) == self.get_Node_buffers().query_from(key, query_idx)
        })
        decreases self.get_Node_buffers().len() - buffer_idx
    {
        PivotTable::route_lemma_auto();
        if buffer_idx < self.get_Node_buffers().len() {
            self.query_from_same_as_i_filtered(key, buffer_idx+1, offset_map.decrement(1));
        }
    }

    pub proof fn query_from_refines(self, key: Key)
        requires self.wf(), self.is_Node(), self.key_in_domain(key),
        ensures ({
            let start = self.flushed_ofs(key);
            let msg = self.get_Node_buffers().query_from(key, start as int);
            &&& msg == self.i().get_Node_buffer().query(key)
        })
    {
        let offset_map = self.make_offset_map();
        self.query_from_same_as_i_filtered(key, 0, offset_map);
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

//     pub proof fn active_keys_in_my_domain(self, buffer_idx: int)
//         requires self.wf(), self.is_Node(), 0 <= buffer_idx < self.get_Node_buffers().len()
//         ensures forall |k| self.active_keys(buffer_idx).contains(k) ==> #[trigger] self.my_domain().contains(k)
//     {
//         assert forall |k| self.active_keys(buffer_idx).contains(k)
//         implies #[trigger] self.my_domain().contains(k)
//         by {
//             let child_idx = choose |child_idx| self.active_key_cond(k, child_idx, buffer_idx);
//             let child_domain = self.child_domain(child_idx as nat);

//             assert(child_domain.contains(k));
//             if self.get_Node_pivots().num_ranges() == 1 {
//                 assert(child_domain == self.my_domain());
//             } else {
//                 if child_idx == 0 {
//                     assert(Element::lt(child_domain.get_Domain_end(), self.my_domain().get_Domain_end()));
//                 } else if child_idx + 1 == self.get_Node_pivots().num_ranges() {
//                     assert(Element::lt(self.my_domain().get_Domain_start(), child_domain.get_Domain_start()));
//                 } else {
//                     assert(Element::lt(self.my_domain().get_Domain_start(), child_domain.get_Domain_start()));
//                     assert(Element::lt(child_domain.get_Domain_end(), self.my_domain().get_Domain_end()));
//                 }
//             }
//         }
//     }

//     pub proof fn extend_buffer_seq_commutes_with_i(self, buffers: BufferSeq)
//         requires self.wf(), self.is_Node()
//         ensures self.extend_buffer_seq(buffers).i() == 
//                 self.i().extend_buffer_seq(buffers.apply_filter(self.my_domain().key_set()))
//     {
//         let filter = self.my_domain().key_set();
//         let a = self.extend_buffer_seq(buffers).i();
//         let b = self.i().extend_buffer_seq(buffers.apply_filter(filter));

//         BetreeNode::i_children_lemma_auto();
//         assert(a.get_Node_children() =~= b.get_Node_children());

//         let old_len = self.get_Node_buffers().len();
//         assert forall |i| 0 <= i < a.get_Node_buffers().len() 
//         implies #[trigger] a.get_Node_buffers()[i] == b.get_Node_buffers()[i]
//         by {
//             if i < old_len {
//                 assert forall |k: Key| #[trigger] self.active_keys(i).contains(k) <==> 
//                     self.extend_buffer_seq(buffers).active_keys(i).contains(k)
//                 by {
//                     if self.active_keys(i).contains(k) {
//                         let child_idx = choose |child_idx| self.active_key_cond(k, child_idx, i);
//                         assert(self.extend_buffer_seq(buffers).active_key_cond(k, child_idx, i));
//                     }
//                     if self.extend_buffer_seq(buffers).active_keys(i).contains(k) {
//                         let child_idx = choose |child_idx| self.extend_buffer_seq(buffers).active_key_cond(k, child_idx, i);
//                         assert(self.active_key_cond(k, child_idx, i));
//                     }
//                 }
//                 assert(self.active_keys(i) =~= self.extend_buffer_seq(buffers).active_keys(i));
//             } else {
//                 self.extend_buffer_seq(buffers).active_keys_in_my_domain(i);
//                 assert forall |k: Key| 
//                     #[trigger] a.get_Node_buffers()[i].map.contains_key(k) <==> b.get_Node_buffers()[i].map.contains_key(k)
//                 by {
//                     if a.get_Node_buffers()[i].map.contains_key(k) {
//                         assert(self.extend_buffer_seq(buffers).active_keys(i).contains(k));
//                     }
//                     if b.get_Node_buffers()[i].map.contains_key(k) {
//                         PivotTable::route_lemma_auto();
//                         assert(self.extend_buffer_seq(buffers).active_key_cond(k, self.get_Node_pivots().route(k), i));
//                         assert(a.get_Node_buffers()[i].map.contains_key(k));
//                     }
//                 }
//                 assert(a.get_Node_buffers()[i] =~= b.get_Node_buffers()[i]);
//             }
//         }
//         assert(a.get_Node_buffers() =~= b.get_Node_buffers());
//     }

//     // pub proof fn empty_root_refines()
//     //     ensures Self::empty_root(total_domain()).i() == PivotBetree_v::BetreeNode::empty_root(total_domain())
//     // {
//     //     let empty = Self::empty_root(total_domain());
//     //     let i_empty = PivotBetree_v::BetreeNode::empty_root(total_domain());

//     //     assert(empty.wf_children()); // trigger
//     //     empty.i_children_lemma();
//     //     assert(empty.i().get_Node_buffers() =~= i_empty.get_Node_buffers());
//     // }

//     pub proof fn promote_commutes_with_i(self, domain: Domain)
//         requires self.wf(), domain.wf(), domain.is_Domain()
//         ensures self.promote(domain).i() == self.i().promote(domain)
//     {
//         BetreeNode::i_wf_auto();
//         BetreeNode::i_children_lemma_auto();
//         PivotTable::route_lemma_auto();
//         assert(self.promote(domain).i().get_Node_buffers() =~= self.i().promote(domain).get_Node_buffers());
//     }

    pub open spec fn split_element(self, request: SplitRequest) -> Element
        recommends self.can_split_parent(request)
    {
        let child = self.get_Node_children()[request.get_child_idx() as int];
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => to_element(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => child.get_Node_pivots().pivots[child_pivot_idx as int]
        }
    }

    pub proof fn split_parent_wf(self, request: SplitRequest) 
        requires self.can_split_parent(request)
        ensures self.split_parent(request).wf()
    { 
        let child_idx = request.get_child_idx();
        let new_parent = self.split_parent(request);

        assert forall |i| 0 <= i < new_parent.get_Node_children().len()
        implies (#[trigger]new_parent.get_Node_children()[i]).wf()
        by {
            if i > child_idx+1 {
                assert(new_parent.get_Node_children()[i] == self.get_Node_children()[i-1]);
            }
        }
        self.get_Node_pivots().insert_wf(child_idx as int + 1, self.split_element(request));
    }

//     pub proof fn split_leaf_commutes_with_i(self, split_key: Key)
//         requires self.can_split_leaf(split_key)
//         ensures 
//             self.split_leaf(split_key).0.i() == self.i().split_leaf(split_key).0,
//             self.split_leaf(split_key).1.i() == self.i().split_leaf(split_key).1,
//     {
//         BetreeNode::i_wf_auto();
//         BetreeNode::i_children_lemma_auto();

//         let (left, right) = self.split_leaf(split_key);
//         let (i_left, i_right) = self.i().split_leaf(split_key);

//         assert forall |i| 0 <= i < left.get_Node_buffers().len()
//         implies #[trigger] left.i_buffer(i) == i_left.get_Node_buffers()[i]
//         by {
//             let active_keys = Set::new(|k: Key| self.active_key_cond(k, 0, i));
//             let left_active_keys = Set::new(|k: Key| left.active_key_cond(k, 0, i));
//             assert(self.active_keys(i) =~= active_keys);
//             assert(left.active_keys(i) =~= left_active_keys);
//             assert(left.i_buffer(i) =~= i_left.get_Node_buffers()[i]);
//         }
//         assert(left.i().get_Node_buffers() =~= i_left.get_Node_buffers());

//         assert forall |i| 0 <= i < right.get_Node_buffers().len()
//         implies #[trigger] right.i_buffer(i) =~= i_right.get_Node_buffers()[i]
//         by {
//             let active_keys = Set::new(|k: Key| self.active_key_cond(k, 0, i));
//             let right_active_keys = Set::new(|k: Key| right.active_key_cond(k, 0, i));
//             assert(self.active_keys(i) =~= active_keys);
//             assert(right.active_keys(i) =~= right_active_keys);
//         }
//         assert(right.i().get_Node_buffers() =~= i_right.get_Node_buffers());
//     }
    
//     pub proof fn split_index_commutes_with_i(self, pivot_idx: nat)
//         requires self.can_split_index(pivot_idx)
//         ensures
//             self.split_index(pivot_idx).0.i() == self.i().split_index(pivot_idx).0,
//             self.split_index(pivot_idx).1.i() == self.i().split_index(pivot_idx).1,
//     {
//         BetreeNode::i_wf_auto();
//         BetreeNode::i_children_lemma_auto();

//         Element::lt_transitive_forall();
//         Element::lte_transitive_forall();

//         let (left, right) = self.split_index(pivot_idx);
//         let (i_left, i_right) = self.i().split_index(pivot_idx);

//         let split_element = self.get_Node_pivots().pivots[pivot_idx as int];
//         let left_filter = Domain::Domain{ start: self.my_domain().get_Domain_start(), end: split_element };
//         let right_filter = Domain::Domain{ start: split_element, end: self.my_domain().get_Domain_end() };

//         assert forall |i| 0 <= i < left.get_Node_buffers().len()
//         implies #[trigger] left.i_buffer(i) =~= i_left.get_Node_buffers()[i]
//         by {
//             assert forall |k| #[trigger] left.i_buffer(i).map.contains_key(k) 
//                 <==> i_left.get_Node_buffers()[i].map.contains_key(k)
//             by {
//                 if left.i_buffer(i).map.contains_key(k) {
//                     assert(left.active_keys(i).contains(k));
//                     let child_idx = choose |child_idx| left.active_key_cond(k, child_idx, i);
//                     let child_domain = self.child_domain(child_idx as nat);

//                     assert(self.active_key_cond(k, child_idx, i));
//                     assert(child_domain.contains(k));

//                     if child_idx > 0 {
//                         assert(Element::lt(left_filter.get_Domain_start(), child_domain.get_Domain_start()));
//                     }
//                     if child_idx + 1 < pivot_idx {
//                         assert(Element::lt(child_domain.get_Domain_end(), left_filter.get_Domain_end()));
//                     }
//                     assert(left_filter.contains(k));
//                     assert(i_left.get_Node_buffers()[i].map.contains_key(k));
//                 }

//                 if i_left.get_Node_buffers()[i].map.contains_key(k) {
//                     assert(left_filter.contains(k));

//                     let child_idx = choose |child_idx| self.active_key_cond(k, child_idx, i);
//                     if child_idx < left.get_Node_children().len() {
//                         assert(left.active_key_cond(k, child_idx, i));
//                     } else {
//                         let child_domain = self.child_domain(child_idx as nat);
//                         assert(child_domain.contains(k));
//                         assert(child_domain.get_Domain_start() == self.get_Node_pivots().pivots[child_idx]);

//                         if pivot_idx < child_idx {
//                             assert(Element::lt(left_filter.get_Domain_end(), child_domain.get_Domain_start()));
//                         }
//                         assert(Element::lte(child_domain.get_Domain_start(), split_element));
//                         assert(false);
//                     }
//                 }
//             }
//         }
//         assert(left.i().get_Node_buffers() =~= i_left.get_Node_buffers());
//         assert(left.i().get_Node_children() =~= i_left.get_Node_children());


//         assert forall |i| 0 <= i < right.get_Node_buffers().len()
//         implies #[trigger] right.i_buffer(i) =~= i_right.get_Node_buffers()[i]
//         by {
//             assert forall |k | #[trigger] right.i_buffer(i).map.contains_key(k) 
//                 <==> i_right.get_Node_buffers()[i].map.contains_key(k)
//             by {
//                 let left_len = left.get_Node_children().len();
//                 if right.i_buffer(i).map.contains_key(k) {
//                     assert(right.active_keys(i).contains(k));
//                     let child_idx = choose |child_idx| right.active_key_cond(k, child_idx, i);
//                     let old_child_idx = left_len + child_idx;
//                     let child_domain = self.child_domain(old_child_idx as nat);

//                     assert(self.active_key_cond(k, old_child_idx, i));
//                     assert(child_domain.contains(k));

//                     if child_idx > 0 {
//                         assert(Element::lt(right_filter.get_Domain_start(), child_domain.get_Domain_start()));
//                     }

//                     assert(Element::lte(right_filter.get_Domain_start(), to_element(k)));
//                     assert(Element::lt(to_element(k), child_domain.get_Domain_end()));

//                     if child_idx + 1 < right.get_Node_children().len() {
//                         assert(Element::lt(child_domain.get_Domain_end(), right_filter.get_Domain_end()));
//                     }
//                     assert(right_filter.contains(k));
//                 }

//                 if i_right.get_Node_buffers()[i].map.contains_key(k) {
//                     assert(right_filter.contains(k));
//                     let old_child_idx = choose |old_child_idx| self.active_key_cond(k, old_child_idx, i);
//                     if old_child_idx < left.get_Node_children().len() {
//                         let child_domain = self.child_domain(old_child_idx as nat);
//                         assert(child_domain.contains(k));
//                         if old_child_idx + 1 < pivot_idx {
//                             assert(Element::lt(child_domain.get_Domain_end(), right_filter.get_Domain_start()));
//                         }
//                         assert(Element::lte(right_filter.get_Domain_start(), to_element(k)));
//                         assert(false);
//                     } else {
//                         assert(right.active_key_cond(k, old_child_idx-left_len, i));
//                         assert(right.i_buffer(i).map.contains_key(k));
//                     }
//                 }
//             }
//         }
//         assert(right.i().get_Node_buffers() =~= i_right.get_Node_buffers());
//         assert(right.i().get_Node_children() =~= i_right.get_Node_children());
//     }

//     #[verifier::spinoff_prover]
//     pub proof fn split_parent_buffers_commutes_with_i(self, request: SplitRequest)
//         requires self.can_split_parent(request), self.i().can_split_parent(request)
//         ensures self.i().split_parent(request).get_Node_buffers() == self.split_parent(request).i().get_Node_buffers()
//     {
//         self.split_parent_wf(request);
//         BetreeNode::i_wf_auto();

//         let new_parent = self.split_parent(request);
//         let i_new_parent = self.i().split_parent(request);
//         assert(self.get_Node_pivots().len()+1 == new_parent.get_Node_pivots().len());

//         let split_child_idx = request.get_child_idx() as int;
//         let split_child_domain = self.child_domain(split_child_idx as nat);
//         let new_left_child_domain = new_parent.child_domain(split_child_idx as nat);
//         let new_right_child_domain = new_parent.child_domain((split_child_idx+1)as nat);

//         assert(split_child_domain.get_Domain_start() == new_left_child_domain.get_Domain_start());
//         assert(split_child_domain.get_Domain_end() == new_right_child_domain.get_Domain_end());
//         assert(Element::lt(new_left_child_domain.get_Domain_end(), split_child_domain.get_Domain_end()));
//         assert(Element::lt(split_child_domain.get_Domain_start(), new_right_child_domain.get_Domain_start()));
        
//         assert forall |i| 0 <= i < new_parent.get_Node_buffers().len()
//         implies #[trigger] new_parent.i_buffer(i) =~= self.i().get_Node_buffers()[i]
//         by {
//             assert forall |k| #[trigger] new_parent.active_keys(i).contains(k) <==> self.active_keys(i).contains(k)
//             by {
//                 if new_parent.active_keys(i).contains(k) && !self.active_keys(i).contains(k)
//                 {
//                     let new_child_idx = choose |new_child_idx| new_parent.active_key_cond(k, new_child_idx, i);
//                     if new_child_idx < split_child_idx {
//                         assert(self.active_key_cond(k, new_child_idx, i));
//                         assert(false);
//                     } else if new_child_idx > split_child_idx+1 {
//                         assert(self.active_key_cond(k, new_child_idx-1, i));
//                         assert(false);
//                     } else {
//                         assert(self.active_key_cond(k, split_child_idx, i));
//                         assert(false);
//                     }
//                 }

//                 if !new_parent.active_keys(i).contains(k) && self.active_keys(i).contains(k) 
//                 {
//                     let child_idx = choose |child_idx| self.active_key_cond(k, child_idx, i);
//                     if child_idx < split_child_idx {
//                         assert(new_parent.active_key_cond(k, child_idx, i));
//                         assert(false);
//                     } else if child_idx > split_child_idx {
//                         assert(new_parent.active_key_cond(k, child_idx+1, i));
//                         assert(false);
//                     } else {
//                         assert(split_child_domain.contains(k));
//                         if Element::lt(to_element(k), new_left_child_domain.get_Domain_end()) {
//                             assert(new_left_child_domain.contains(k));
//                             assert(new_parent.active_key_cond(k, child_idx, i));
//                             assert(false);
//                         } else {
//                             assert(new_right_child_domain.contains(k));
//                             assert(new_parent.active_key_cond(k, child_idx+1, i));
//                             assert(false);
//                         }
//                     }
//                 }
//             }
//         }
//         assert(new_parent.i().get_Node_buffers() =~= self.i().get_Node_buffers());
//         assert(self.i().get_Node_buffers() =~= i_new_parent.get_Node_buffers());
//     }

//     pub proof fn split_parent_commutes_with_i(self, request: SplitRequest)
//         requires self.can_split_parent(request)
//         ensures 
//             self.i().can_split_parent(request),
//             self.i().split_parent(request) == self.split_parent(request).i()
//     {
//         self.split_parent_wf(request);
//         BetreeNode::i_wf_auto();
//         BetreeNode::i_children_lemma_auto();

//         let split_child_idx = request.get_child_idx() as int;
//         let child = self.get_Node_children()[request.get_child_idx() as int];

//         if request.is_SplitLeaf() {
//             child.split_leaf_commutes_with_i(request.get_SplitLeaf_split_key());
//         } else {
//             child.split_index_commutes_with_i(request.get_SplitIndex_child_pivot_idx());
//         }
//         assert(self.split_parent(request).i().get_Node_children() =~= self.i().split_parent(request).get_Node_children());      
  
//         self.split_parent_buffers_commutes_with_i(request);
//     }

    pub proof fn flush_wf(self, child_idx: nat, buffer_gc: nat)
        requires self.can_flush(child_idx, buffer_gc)
        ensures self.flush(child_idx, buffer_gc).wf()
    {
        let result = self.flush(child_idx, buffer_gc);

        let idx = child_idx as int;
        let flush_upto = self.get_Node_buffers().len(); 

        let updated_flushed = self.get_Node_flushed().update(idx, flush_upto);
        assert(updated_flushed.offsets[idx] == flush_upto);
        updated_flushed.shift_left_preserves_lte(buffer_gc, flush_upto);
        assert(result.local_structure());

        let flushed_ofs = self.get_Node_flushed().offsets[idx];
        let buffers_to_child = self.get_Node_buffers().slice(flushed_ofs as int, flush_upto as int);

        let child = self.get_Node_children()[idx];
        let child_domain = self.child_domain(child_idx);
        let new_child = child.promote(child_domain).extend_buffer_seq(buffers_to_child);

        assert(child.wf()); // trigger
        assert(new_child.wf());
    }

//     pub proof fn flush_commutes_with_i(self, child_idx: nat, buffer_gc: nat)
//         requires self.can_flush(child_idx, buffer_gc)
//         ensures self.flush(child_idx, buffer_gc).i() == self.i().flush(child_idx)
//     {
//         assume(false);
//         // self.flush_wf(child_idx, buffer_gc);
//         // BetreeNode::i_wf_auto();
//         // BetreeNode::i_children_lemma_auto();

//         // let idx = child_idx as int;
//         // let flush_upto = self.get_Node_buffers().len();

//         // let flushed_ofs = self.get_Node_flushed().offsets[idx];
//         // let buffers_to_child = self.get_Node_buffers().slice(flushed_ofs as int, flush_upto as int);

//         // let child = self.get_Node_children()[idx];
//         // let child_domain = self.child_domain(child_idx);
//         // let new_child = child.promote(child_domain).extend_buffer_seq(buffers_to_child);

//         // assert(child.wf()); // trigger
//         // child.promote_commutes_with_i(child_domain);
//         // assert(child.promote(child_domain).i() == child.i().promote(child_domain));
//         // child.promote(child_domain).extend_buffer_seq_commutes_with_i(buffers_to_child);
//         // assert(new_child.i() == child.i().promote(child_domain).extend_buffer_seq(buffers_to_child.apply_filter(child_domain.key_set())));

//         // assert(self.i().child_domain(child_idx) == child_domain);
//      }   

} // end impl BetreeNode

pub open spec fn i_stamped_betree(stamped: StampedBetree) -> PivotBetree_v::StampedBetree
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine{
    pub open spec fn i(self) -> PivotBetree_v::QueryReceiptLine
        recommends self.wf()
    {
        PivotBetree_v::QueryReceiptLine{node: self.node.i(), result: self.result}
    }
}

impl QueryReceipt{
    pub open spec fn i(self) -> PivotBetree_v::QueryReceipt
        recommends self.valid()
    {
        PivotBetree_v::QueryReceipt{
            key: self.key,
            root: self.root.i(),
            lines: Seq::new(self.lines.len(), |i:int| self.lines[i].i())
        }
    }

    pub proof fn valid_receipt_refines(self)
        requires self.valid()
        ensures self.i().valid()
    {
        BetreeNode::i_wf_auto();
        BetreeNode::i_children_lemma_auto();
        PivotTable::route_lemma_auto();

        let i_receipt = self.i();
        assert forall |i| 0 <= i < i_receipt.lines.len()-1
        implies {
            &&& #[trigger] i_receipt.lines[i].node.key_in_domain(self.key)
            &&& i_receipt.child_linked_at(i) 
        } by {
            assert(i_receipt.lines[i].wf());
            assert(self.child_linked_at(i));
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.result_linked_at(i) by {
            assert(self.result_linked_at(i)); // trigger
            self.lines[i].node.query_from_refines(self.key);
        }

        assert(i_receipt.all_lines_wf()); // trigger
    }
}

impl Path{
    pub open spec fn i(self) -> PivotBetree_v::Path
    {
        PivotBetree_v::Path{node: self.node.i(), key: self.key, depth: self.depth}
    }

    pub proof fn subpath_commutes_with_i(self)
        requires self.valid(), 0 < self.depth
        ensures self.subpath().i() == self.i().subpath()
    {
        self.node.i_wf();
        self.node.i_children_lemma();
        self.node.get_Node_pivots().route_lemma(self.key);
    }

    pub proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
        decreases self.depth
    {
        self.node.i_wf();
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
        ensures self.substitute(replacement).wf(),
            self.substitute(replacement).is_Node()
        decreases self.depth, 1nat
    {
        if 0 < self.depth {
            self.subpath().substitute_preserves_wf(replacement);
    
            let result = self.substitute(replacement);
            if result.is_Node() {
                self.replaced_children_matching_domains(replacement);
                assert forall |i:nat| i < self.node.get_Node_children().len() ==> { // trigger
                    self.node.valid_child_index(i)
                    && (#[trigger] self.node.get_Node_children()[i as int].is_Node())
                    && self.node.get_Node_children()[i as int].wf()
                } by { }

                assert(result.linked_children());
            }
        }
    }

    pub proof fn replaced_children_matching_domains(self, replacement: BetreeNode)
        requires self.valid(), self.valid_replacement(replacement), 0 < self.depth
        ensures self.node.children_have_matching_domains(self.replaced_children(replacement))
        decreases self.depth, 0nat
    {
        PivotTable::route_lemma_auto();
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
        self.target_wf();
        self.substitute_preserves_wf(replacement);
        replacement.i_wf();

        PivotTable::route_lemma_auto();
        BetreeNode::i_children_lemma_auto();

        if 0 < self.depth {
            assert(self.substitute(replacement).i().wf_children());

            self.target_commutes_with_i();
            self.i().substitute_preserves_wf(replacement.i());
            assert(self.substitute(replacement).i().wf_children());

            self.subpath_commutes_with_i();
            self.subpath().substitute_refines(replacement);

            assert(self.substitute(replacement).i().get_Node_children()
                =~= self.i().substitute(replacement.i()).get_Node_children()
            );

            // assert forall |i| 0 <= i < self.node.get_Node_buffers().len()
            // implies #[trigger] self.substitute(replacement).i().get_Node_buffers()[i] == self.node.i().get_Node_buffers()[i]
            // by {
            //     let a = self.substitute(replacement).active_keys(i);
            //     let b = self.node.active_keys(i);

            //     self.replaced_children_matching_domains(replacement);
            //     assert forall |k: Key| a.contains(k) <==> b.contains(k)
            //     by {
            //         if a.contains(k) {
            //             let child_idx = choose |child_idx| self.substitute(replacement).active_key_cond(k, child_idx, i);
            //             assert(self.node.active_key_cond(k, child_idx, i));
            //         }
            //         if b.contains(k) {
            //             let child_idx = choose |child_idx| self.node.active_key_cond(k, child_idx, i);
            //             assert(self.substitute(replacement).active_key_cond(k, child_idx, i));
            //         }
            //     }
            //     assert(self.substitute(replacement).active_keys(i) =~= self.node.active_keys(i));
            // }
            assume(self.substitute(replacement).i().get_Node_buffer() =~= self.node.i().get_Node_buffer()); // TODO
        }
    }
}

impl FilteredBetree::Label {
    pub open spec fn i(self) -> PivotBetree::Label
    {
        match self {
            FilteredBetree::Label::Query{end_lsn, key, value} => PivotBetree::Label::Query{end_lsn: end_lsn, key: key, value: value},
            FilteredBetree::Label::Put{puts} => PivotBetree::Label::Put{puts: puts},
            FilteredBetree::Label::FreezeAs{stamped_betree} => PivotBetree::Label::FreezeAs{stamped_betree: i_stamped_betree(stamped_betree)},
            FilteredBetree::Label::Internal{} => PivotBetree::Label::Internal{},
        }
    }
} // end impl FilteredBetree::Label

// // pub proof fn flush_commutes_with_i(path: Path, child_idx: nat)
// //     requires path.valid(), path.target().can_flush(child_idx)
// //     ensures path.target().i().flush(path.target().child_domain(child_idx).key_set())
// //         == path.target().flush(child_idx).i()
// // {
// //     let target = path.target();
// //     path.target_wf();
// //     target.flush_wf(child_idx);

// //     let child = target.get_Node_children()[child_idx as int];
// //     let child_domain = target.child_domain(child_idx);
// //     let moved_buffers = target.get_Node_buffers().apply_filter(child_domain.key_set());

// //     if child.is_Nil() {
// //         child.nil_promote_and_extend_commutes_with_i(child_domain, moved_buffers);
// //     } else {
// //         child.node_promote_and_extend_commutes_with_i(child_domain, moved_buffers);
// //     }

// //     assert forall |k| true
// //     implies #[trigger] target.flush(child_idx).i().get_Node_children().map[k] 
// //         == target.i().flush(child_domain.key_set()).get_Node_children().map[k]
// //     by {
// //         target.i_children_lemma();
// //         target.flush(child_idx).i_children_lemma();

// //         if child_domain.contains(k) {
// //             target.flush(child_idx).get_Node_pivots().route_is_lemma(k, child_idx as int);
// //             assert(target.key_in_domain(k));
// //         } else {
// //             if target.my_domain().contains(k) {
// //                 let r = target.get_Node_pivots().route(k);
// //                 target.get_Node_pivots().route_lemma(k);
// //             }
// //         }
// //     }

// //     assert(target.flush(child_idx).i().get_Node_children().map =~= 
// //         target.i().flush(child_domain.key_set()).get_Node_children().map);
// // }

// // pub proof fn compact_commutes_with_i(path: Path, compacted_buffers: BufferSeq)
// //     requires path.valid(), path.target().is_Node(),
// //         path.target().get_Node_buffers().i() == compacted_buffers.i()
// //     ensures path.target().i().compact(compacted_buffers)
// //         == path.target().compact(compacted_buffers).i()
// // {
// //     let target = path.target();
// //     path.target_wf();

// //     assert forall |k| true
// //     implies #[trigger] target.compact(compacted_buffers).i().get_Node_children().map[k] 
// //         == target.i().compact(compacted_buffers).get_Node_children().map[k]
// //     by {
// //         if target.my_domain().contains(k) {
// //             target.i_children_lemma();
// //             target.compact(compacted_buffers).i_children_lemma();
// //         }
// //     }

// //     assert(target.compact(compacted_buffers).i().get_Node_children().map =~= 
// //         target.i().compact(compacted_buffers).get_Node_children().map);
// // }

impl FilteredBetree::State {
    pub open spec fn inv(self) -> bool {
        &&& self.wf()
        &&& (self.root.is_Node() ==> self.root.my_domain() == total_domain())
    }

    pub open spec fn i(self) -> PivotBetree::State
    {
        PivotBetree::State{root: self.root.i(), memtable: self.memtable}
    }

    pub proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires FilteredBetree::State::initialize(self, stamped_betree)
        ensures PivotBetree::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        stamped_betree.value.i_wf();
    }

    pub proof fn query_refines(self, post: Self, lbl: FilteredBetree::Label, receipt: QueryReceipt)
        requires self.inv(), FilteredBetree::State::query(self, post, lbl, receipt)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        receipt.valid_receipt_refines();
        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::query(receipt.i())));
    }

    pub proof fn put_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::put(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::put()));
    }

    pub proof fn freeze_as_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::freeze_as(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        self.root.i_wf();
        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::freeze_as()));
    }

//     pub proof fn internal_flush_memtable_refines(self, post: Self, lbl: FilteredBetree::Label)
//         requires self.inv(), FilteredBetree::State::internal_flush_memtable(self, post, lbl)
//         ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
//     {
//         reveal(PivotBetree::State::next);
//         reveal(PivotBetree::State::next_by);

//         self.root.i_wf();

//         let a = self.root.push_memtable(self.memtable).value.i();
//         let b = self.root.i().push_memtable(self.memtable).value;
//         let promote = self.root.promote(total_domain());
//         let buffers = BufferSeq{buffers: seq![self.memtable.buffer]};
        
//         BetreeNode::i_children_lemma_auto();
//         assert(a.get_Node_children() =~= b.get_Node_children());

//         promote.extend_buffer_seq_commutes_with_i(buffers);
//         assert(promote.my_domain() == total_domain());
//         assert(forall |k| total_domain().contains(k));
//         assert(buffers[0].apply_filter(total_domain().key_set()) =~= buffers[0]);
//         assert(buffers.apply_filter(total_domain().key_set()) =~= buffers);
//         assert(a.get_Node_buffers() =~= b.get_Node_buffers());

//         assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_flush_memtable()));
//     }

    pub proof fn internal_grow_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_grow(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        BetreeNode::i_wf_auto();
        PivotTable::route_lemma_auto();
        post.root.i_children_lemma();

        assert(post.i().root.get_Node_children() =~= self.i().root.grow().get_Node_children());
        assert(post.i().root.get_Node_buffer() =~= self.i().root.grow().get_Node_buffer());
        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_grow()));
    }

//     pub proof fn internal_split_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, request: SplitRequest)
//         requires self.inv(), FilteredBetree::State::internal_split(self, post, lbl, path, request)
//         ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
//     {
//         reveal(PivotBetree::State::next);
//         reveal(PivotBetree::State::next_by);

//         BetreeNode::i_wf_auto();

//         path.target().split_parent_wf(request);
//         path.substitute_refines(path.target().split_parent(request));

//         path.i_valid();
//         path.target_commutes_with_i();
//         path.target().split_parent_commutes_with_i(request);

//         assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_split(path.i(), request)));
//     }

//     pub proof fn internal_flush_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, child_idx: nat, buffer_gc: nat)
//         requires self.inv(), FilteredBetree::State::internal_flush(self, post, lbl, path, child_idx, buffer_gc)
//         ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
//     {
//         reveal(PivotBetree::State::next);
//         reveal(PivotBetree::State::next_by);

//         BetreeNode::i_wf_auto();
//         path.target().flush_wf(child_idx, buffer_gc);
//         path.substitute_refines(path.target().flush(child_idx, buffer_gc));

//         path.i_valid();
//         path.target_commutes_with_i();
//         path.target().flush_commutes_with_i(child_idx, buffer_gc);

//         assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_flush(path.i(), child_idx)));
//     }

// //     pub proof fn internal_compact_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, compacted_buffers: BufferSeq)
// //         requires self.inv(), FilteredBetree::State::internal_compact(self, post, lbl, path, compacted_buffers)
// //         ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
// //     {
// //         reveal(PivotBetree::State::next);
// //         reveal(PivotBetree::State::next_by);

// //         self.root.i_wf();
// //         path.target_wf();
// //         path.substitute_refines(path.target().compact(compacted_buffers));

// //         post.root.i_wf();
// //         path.i_valid();
// //         path.target_commutes_with_i();

// //         compact_commutes_with_i(path, compacted_buffers);
// //         assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_compact(path.i(), compacted_buffers)));
// //     }

    pub proof fn internal_noop_noop(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_noop(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        BetreeNode::i_wf_auto();
        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_noop()));
    }

//     pub proof fn next_refines(self, post: Self, lbl: FilteredBetree::Label)
//         requires self.inv(), FilteredBetree::State::next(self, post, lbl),
//         ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i()),
//     {
//         reveal(FilteredBetree::State::next);
//         reveal(FilteredBetree::State::next_by);

//         match choose |step| FilteredBetree::State::next_by(self, post, lbl, step)
//         {
//             FilteredBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
//             FilteredBetree::Step::put() => { self.put_refines(post, lbl); }
//             FilteredBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
//             FilteredBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_refines(post, lbl); }
//             FilteredBetree::Step::internal_grow() => { self.internal_grow_refines(post, lbl); }
//             FilteredBetree::Step::internal_split(path, split_request) => { self.internal_split_refines(post, lbl, path, split_request); }
//             FilteredBetree::Step::internal_flush(path, child_idx, buffer_gc) => { self.internal_flush_refines(post, lbl, path, child_idx, buffer_gc); }
//             // FilteredBetree::Step::internal_compact(path, compacted_buffers) => { self.internal_compact_refines(post, lbl, path, compacted_buffers); }
//             FilteredBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
//             _ => { assume(false); } 
//         }
//     }
} // end impl FilteredBetree::State

}//verus
