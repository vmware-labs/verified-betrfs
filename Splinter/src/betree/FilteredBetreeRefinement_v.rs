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
    pub open spec(checked) fn i_buffer(self) -> Buffer
        recommends self.wf(), self.is_Node()
    {
        let offset_map = self.make_offset_map();
        self.get_Node_buffers().i_filtered(offset_map)
    }

    pub open spec /*XXX(checked)*/ fn i_children_seq(self, start: int) -> Seq<PivotBetree_v::BetreeNode>
    recommends self.is_Node(), 0 <= start <= self.get_Node_children().len()
    decreases self, 0nat, self.get_Node_children().len()-start 
        when self.is_Node() && 0 <= start <= self.get_Node_children().len()
    {
        if start == self.get_Node_children().len() {
            seq![]
        } else {
            //XXX need to instantiate linked_children
            let child = self.get_Node_children()[start].i();
            seq![child] + self.i_children_seq(start+1)
        }
    }

    pub open spec(checked) fn i_children(self) -> Seq<PivotBetree_v::BetreeNode>
        recommends self.is_Node()
        decreases self, 1nat
    {
        self.i_children_seq(0)
    }

    pub open spec(checked) fn i(self) -> PivotBetree_v::BetreeNode
    recommends
        self.wf(),
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

    pub proof fn i_buffer_domain(self)
        requires self.wf(), self.is_Node()
        ensures forall |k| #[trigger] self.i_buffer().map.contains_key(k) <==> 
            exists |idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx)
    {
        self.get_Node_buffers().i_filtered_from_domain(self.make_offset_map(), 0);
    }

    pub proof fn query_from_refines(self, key: Key)
        requires self.wf(), self.is_Node(), self.key_in_domain(key),
        ensures self.get_Node_buffers().query_from(key, self.flushed_ofs(key) as int) == self.i().get_Node_buffer().query(key)
    {
        PivotTable::route_lemma_auto();
        let offset_map = self.make_offset_map();
        self.get_Node_buffers().query_from_same_as_i_filtered(key, 0, offset_map);
    }

    pub proof fn query_from_refines_auto()
        ensures forall |k: Key, node: BetreeNode| #![auto] node.wf() && node.is_Node() && node.key_in_domain(k)
            ==> node.get_Node_buffers().query_from(k, node.flushed_ofs(k) as int) == node.i().get_Node_buffer().query(k)
    {
        assert forall  #![auto] |k: Key, node: BetreeNode| node.wf() && node.is_Node() && node.key_in_domain(k)
        implies node.get_Node_buffers().query_from(k, node.flushed_ofs(k) as int) == node.i().get_Node_buffer().query(k)
        by {
            node.query_from_refines(k);
        }
    }

    pub open spec /*XXX(checked)*/ fn children_have_matching_domains(self, other_children: Seq<BetreeNode>) -> bool
        recommends self.wf(), self.is_index()
    {
        &&& other_children.len() == self.get_Node_children().len()
        &&& forall |i:int| #![auto] 0 <= i < other_children.len() ==> other_children[i].wf()
        &&& (forall |i:int| #![auto] 0 <= i < self.get_Node_children().len() ==> {
            &&& other_children[i].wf()
            &&& other_children[i].is_Node()
            //XXX need to instantiate linked_children
            &&& other_children[i].my_domain() == self.get_Node_children()[i].my_domain()
        })
    }

    pub proof fn i_preserves_domain(self, other: BetreeNode, k: Key)
        requires self.key_in_domain(k), other.key_in_domain(k),
            self.flushed_ofs(k) == other.flushed_ofs(k),
            self.get_Node_buffers() == other.get_Node_buffers()
        ensures
            self.i().get_Node_buffer().map.contains_key(k) == other.i().get_Node_buffer().map.contains_key(k),
            self.i().get_Node_buffer().map.contains_key(k) ==> self.i().get_Node_buffer().map[k] == other.i().get_Node_buffer().map[k]
    {
        self.i_buffer_domain();
        other.i_buffer_domain();

        if self.i().get_Node_buffer().map.contains_key(k) {
            let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx);
            assert(other.get_Node_buffers().key_in_buffer_filtered(other.make_offset_map(), 0, k, idx));
            assert(other.i().get_Node_buffer().map.contains_key(k));
        }
        
        if other.i().get_Node_buffer().map.contains_key(k) {
            let idx = choose |idx| other.get_Node_buffers().key_in_buffer_filtered(other.make_offset_map(), 0, k, idx);
            assert(self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx));
            assert(self.i().get_Node_buffer().map.contains_key(k));
        }

        BetreeNode::query_from_refines_auto();
    }

    pub proof fn i_preserves_domain_auto(self)
    ensures forall |other: Self, k: Key| 
            #![auto] self.key_in_domain(k) && other.key_in_domain(k)
            && self.flushed_ofs(k) == other.flushed_ofs(k)
            && self.get_Node_buffers() == other.get_Node_buffers()
        ==> ({
            &&& self.i().get_Node_buffer().map.contains_key(k) == other.i().get_Node_buffer().map.contains_key(k)
            &&& self.i().get_Node_buffer().map.contains_key(k) ==> self.i().get_Node_buffer().map[k] == other.i().get_Node_buffer().map[k]
        })
    {
        assert forall #![auto] |other: Self, k: Key| 
            self.key_in_domain(k) && other.key_in_domain(k)
            && self.flushed_ofs(k) == other.flushed_ofs(k)
            && self.get_Node_buffers() == other.get_Node_buffers()
        implies ({
            &&& self.i().get_Node_buffer().map.contains_key(k) == other.i().get_Node_buffer().map.contains_key(k)
            &&& self.i().get_Node_buffer().map.contains_key(k) ==> self.i().get_Node_buffer().map[k] == other.i().get_Node_buffer().map[k]
        }) by {
            self.i_preserves_domain(other, k);
        }
    }

    pub proof fn child_domain_implies_key_in_domain(self, child_idx: nat)
        requires self.wf(), self.is_Node(), child_idx < self.get_Node_children().len() 
        ensures forall |k: Key| #![auto] self.child_domain(child_idx).contains(k) ==> self.key_in_domain(k)
    {
        let child_domain = self.child_domain(child_idx);
        assert forall #![auto] |k: Key| child_domain.contains(k)
        implies self.key_in_domain(k)
        by {
            if self.get_Node_pivots().num_ranges() == 1 {
                assert(child_domain == self.my_domain());
            } else {
                if child_idx == 0 {
                    assert(Element::lt(child_domain.get_Domain_end(), self.my_domain().get_Domain_end()));
                } else if child_idx + 1 == self.get_Node_pivots().num_ranges() {
                    assert(Element::lt(self.my_domain().get_Domain_start(), child_domain.get_Domain_start()));
                } else {
                    assert(Element::lt(self.my_domain().get_Domain_start(), child_domain.get_Domain_start()));
                    assert(Element::lt(child_domain.get_Domain_end(), self.my_domain().get_Domain_end()));
                }
            }
        }
    }

    pub proof fn extend_buffer_seq_refines_merge_buffer(self, buffers: BufferSeq)
        requires self.wf(), self.is_Node()
        ensures self.extend_buffer_seq(buffers).i() == self.i().merge_buffer(buffers.i().apply_filter(self.my_domain().key_set()))
    {
        let filter = self.my_domain().key_set();
        let a = self.extend_buffer_seq(buffers);
        let b = self.i().merge_buffer(buffers.i().apply_filter(filter));

        BetreeNode::i_children_lemma_auto();
        assert(a.i().get_Node_children() =~= b.get_Node_children());

        let offset_map = self.make_offset_map();
        let a_offset_map = a.make_offset_map();

        self.i_buffer_domain();
        a.i_buffer_domain();

        assert forall |k| 
        ({
            &&& a.i().get_Node_buffer().map.contains_key(k) <==> #[trigger] b.get_Node_buffer().map.contains_key(k)
            &&& a.i().get_Node_buffer().map.contains_key(k) ==> a.i().get_Node_buffer().map[k] == b.get_Node_buffer().map[k]
        }) by {
            PivotTable::route_lemma_auto();
            if a.i().get_Node_buffer().map.contains_key(k) {
                let idx = choose |idx| a.get_Node_buffers().key_in_buffer_filtered(a_offset_map, 0, k, idx);
                assert(a.get_Node_buffers().key_in_buffer_filtered(offset_map, 0, k, idx));
                if idx < self.get_Node_buffers().len() {
                    assert(self.get_Node_buffers().key_in_buffer_filtered(offset_map, 0, k, idx));
                } else {
                    let buffer_idx = idx-self.get_Node_buffers().len();
                    assert(a.get_Node_buffers()[idx].map.contains_key(k));
                    assert(a.get_Node_buffers()[idx] == buffers[buffer_idx]);
                    assert(buffers.key_in_buffer(0, k, buffer_idx));
                    buffers.i_from_domain(0);
                }

                assert(a.i().get_Node_buffer().map[k] == b.get_Node_buffer().map[k]) by {
                    a.query_from_refines(k);
                    self.query_from_refines(k);
                    buffers.query_agrees_with_i(k, 0);
                    assert(buffers.query(k) == buffers.i().query(k));
                    BufferSeq::extend_buffer_seq_lemma(buffers, self.get_Node_buffers(), k, offset_map.offsets[k] as int);
                }
            }

            if b.get_Node_buffer().map.contains_key(k) {
                if buffers.i().map.contains_key(k) {
                    buffers.i_from_domain(0);
                    let buffer_idx = choose |buffer_idx| buffers.key_in_buffer(0, k, buffer_idx);
                    let idx = buffer_idx + self.get_Node_buffers().len();
                    assert(a.get_Node_buffers().key_in_buffer_filtered(a_offset_map, 0, k, idx));
                } else {
                    assert(self.i().get_Node_buffer().map.contains_key(k));
                    let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(offset_map, 0, k, idx);
                    assert(a.get_Node_buffers().key_in_buffer_filtered(a_offset_map, 0, k, idx));
                }
            }
        }
        assert(a.i().get_Node_buffer().map.dom() =~= b.get_Node_buffer().map.dom());
        assert(a.i().get_Node_buffer() =~= b.get_Node_buffer());
    }

    pub proof fn promote_commutes_with_i(self, domain: Domain)
        requires self.wf(), domain.wf(), domain.is_Domain()
        ensures self.promote(domain).i() == self.i().promote(domain)
    {
        BetreeNode::i_wf_auto();
        BetreeNode::i_children_lemma_auto();
        PivotTable::route_lemma_auto();

        assert(self.promote(domain).i().get_Node_buffer() =~= self.i().promote(domain).get_Node_buffer());
    }

    pub open spec(checked) fn split_element(self, request: SplitRequest) -> Element
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

    // #[verifier::spinoff_prover]
    pub proof fn split_leaf_commutes_with_i(self, split_key: Key)
        requires self.can_split_leaf(split_key)
        ensures 
            self.split_leaf(split_key).0.i() == self.i().split_leaf(split_key).0,
            self.split_leaf(split_key).1.i() == self.i().split_leaf(split_key).1,
    {
        BetreeNode::i_wf_auto();
        PivotTable::route_lemma_auto();

        let (left, right) = self.split_leaf(split_key);
        let (i_left, i_right) = self.i().split_leaf(split_key);

        left.i_buffer_domain();
        right.i_buffer_domain();
        self.i_buffer_domain();
        self.i_preserves_domain_auto();

        assert(right.i().get_Node_buffer().map.dom() =~= i_right.get_Node_buffer().map.dom());
        assert(left.i().get_Node_buffer() =~= i_left.get_Node_buffer());
        assert(right.i().get_Node_buffer() =~= i_right.get_Node_buffer());
    }
    
    #[verifier::spinoff_prover]
    pub proof fn split_index_commutes_with_i(self, pivot_idx: nat)
        requires self.can_split_index(pivot_idx)
        ensures
            self.split_index(pivot_idx).0.i() == self.i().split_index(pivot_idx).0,
            self.split_index(pivot_idx).1.i() == self.i().split_index(pivot_idx).1,
    {
        BetreeNode::i_wf_auto();
        PivotTable::route_lemma_auto();
        PivotTable::route_is_lemma_auto();

        Element::lt_transitive_forall();
        Element::lte_transitive_forall();

        let (left, right) = self.split_index(pivot_idx);
        let (i_left, i_right) = self.i().split_index(pivot_idx);

        self.i_buffer_domain();
        left.i_buffer_domain();
        right.i_buffer_domain();

        assert(left.i().get_Node_buffer() =~= i_left.get_Node_buffer()) 
        by {
            self.i_preserves_domain_auto();
            left.i_preserves_domain_auto();
        }

        assert(right.i().get_Node_buffer() =~= i_right.get_Node_buffer())
        by {
            self.i_preserves_domain_auto();
            right.i_preserves_domain_auto();
        }

        BetreeNode::i_children_lemma_auto();
        assert(left.i().get_Node_children() =~= i_left.get_Node_children());
        assert(right.i().get_Node_children() =~= i_right.get_Node_children());
    }

    pub proof fn split_parent_buffers_commutes_with_i_key(self, request: SplitRequest, k: Key)
        requires self.can_split_parent(request), self.i().can_split_parent(request)
        ensures 
            self.split_parent(request).i().get_Node_buffer().map.contains_key(k) 
                == self.i().split_parent(request).get_Node_buffer().map.contains_key(k),
            self.split_parent(request).i().get_Node_buffer().map.contains_key(k) ==> 
                self.split_parent(request).i().get_Node_buffer().map[k] ==  self.i().split_parent(request).get_Node_buffer().map[k]
    {
        self.split_parent_wf(request);
        self.i().split_parent_wf(request);
        BetreeNode::i_wf_auto();
        Element::lt_transitive_forall();
        PivotTable::route_lemma_auto();

        let new_parent = self.split_parent(request);
        let i_new_parent = self.i().split_parent(request);
        let split_child_idx = request.get_child_idx() as int;

        self.i_buffer_domain();
        new_parent.i_buffer_domain();

        if new_parent.i().get_Node_buffer().map.contains_key(k) {
            let r = new_parent.get_Node_pivots().route(k);
            if r <= split_child_idx {
                self.get_Node_pivots().route_is_lemma(k, r);
            } else {
                assert(Element::lt(new_parent.get_Node_pivots().pivots[r-1], new_parent.get_Node_pivots().pivots[r]));
                self.get_Node_pivots().route_is_lemma(k, r-1);
            }
            assert(self.flushed_ofs(k) == new_parent.flushed_ofs(k));
            new_parent.i_preserves_domain(self, k);
        }

        if i_new_parent.get_Node_buffer().map.contains_key(k) {
            assert(self.i().get_Node_buffer().map.contains_key(k));
            assert(self.key_in_domain(k));
            assert(new_parent.key_in_domain(k));

            let r = self.get_Node_pivots().route(k);
            if r < split_child_idx {
                new_parent.get_Node_pivots().route_is_lemma(k, r);
            } else if r == split_child_idx {
                if Element::lt(to_element(k), new_parent.get_Node_pivots().pivots[r+1]) {
                    new_parent.get_Node_pivots().route_is_lemma(k, r);
                } else {
                    new_parent.get_Node_pivots().route_is_lemma(k, r+1);
                }
            } else {
                new_parent.get_Node_pivots().route_is_lemma(k, r+1);
            }
            assert(self.flushed_ofs(k) == new_parent.flushed_ofs(k));
            self.i_preserves_domain(new_parent, k);
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn split_parent_buffers_commutes_with_i(self, request: SplitRequest)
        requires self.can_split_parent(request), self.i().can_split_parent(request)
        ensures self.i().split_parent(request).get_Node_buffer() == self.split_parent(request).i().get_Node_buffer()
    {
        self.split_parent_wf(request);
        self.i().split_parent_wf(request);
        BetreeNode::i_wf_auto();

        let new_parent = self.split_parent(request);
        let i_new_parent = self.i().split_parent(request);
        assert forall |k| 
        ({
            &&& new_parent.i().get_Node_buffer().map.contains_key(k) <==> #[trigger] i_new_parent.get_Node_buffer().map.contains_key(k)
            &&& new_parent.i().get_Node_buffer().map.contains_key(k) ==> 
                new_parent.i().get_Node_buffer().map[k] == i_new_parent.get_Node_buffer().map[k]
        }) by {
            self.split_parent_buffers_commutes_with_i_key(request, k);
        }
        assert(new_parent.i().get_Node_buffer().map.dom() =~= i_new_parent.get_Node_buffer().map.dom());
        assert(new_parent.i().get_Node_buffer() =~= i_new_parent.get_Node_buffer());
    }

    #[verifier::spinoff_prover]
    pub proof fn split_parent_commutes_with_i(self, request: SplitRequest)
        requires self.can_split_parent(request)
        ensures 
            self.i().can_split_parent(request),
            self.i().split_parent(request) == self.split_parent(request).i()
    {
        self.split_parent_wf(request);
        BetreeNode::i_wf_auto();
        BetreeNode::i_children_lemma_auto();

        let split_child_idx = request.get_child_idx() as int;
        let child = self.get_Node_children()[request.get_child_idx() as int];

        if request.is_SplitLeaf() {
            child.split_leaf_commutes_with_i(request.get_SplitLeaf_split_key());
        } else {
            child.split_index_commutes_with_i(request.get_SplitIndex_child_pivot_idx());
        }

        self.split_parent_buffers_commutes_with_i(request);
        assert(self.split_parent(request).i().get_Node_children() =~= self.i().split_parent(request).get_Node_children());
    }

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

    pub proof fn flush_commutes_with_i(self, child_idx: nat, buffer_gc: nat)
        requires self.can_flush(child_idx, buffer_gc)
        ensures self.flush(child_idx, buffer_gc).i() == self.i().flush(child_idx)
    {
        self.flush_wf(child_idx, buffer_gc);
        BetreeNode::i_wf_auto();
        BetreeNode::i_children_lemma_auto();
        PivotTable::route_lemma_auto();

        let idx = child_idx as int;
        let flush_upto = self.get_Node_buffers().len();

        let flushed_ofs = self.get_Node_flushed().offsets[idx];
        let buffers_to_child = self.get_Node_buffers().slice(flushed_ofs as int, flush_upto as int);

        let child = self.get_Node_children()[idx];
        let child_domain = self.child_domain(child_idx);
        let new_child = child.promote(child_domain).extend_buffer_seq(buffers_to_child);

        assert(child.wf()); // trigger
        child.promote_commutes_with_i(child_domain);
        assert(child.promote(child_domain).i() == child.i().promote(child_domain));
        child.promote(child_domain).extend_buffer_seq_refines_merge_buffer(buffers_to_child);
        assert(new_child.i() == child.i().promote(child_domain).merge_buffer(buffers_to_child.i().apply_filter(child_domain.key_set())));

        self.i_buffer_domain();
        self.child_domain_implies_key_in_domain(child_idx);

        assert forall #![auto] |k| child_domain.contains(k)
        implies ({
            &&& buffers_to_child.i().map.contains_key(k) <==> self.i_buffer().map.contains_key(k)
            &&& buffers_to_child.i().query(k) == self.i_buffer().query(k)
        }) by {
            self.get_Node_pivots().route_is_lemma(k, idx);
            assert(self.flushed_ofs(k) == flushed_ofs);

            if buffers_to_child.i().map.contains_key(k) {
                buffers_to_child.i_from_domain(0);
                let buffer_idx = choose |buffer_idx| buffers_to_child.key_in_buffer(0, k, buffer_idx);
                assert(self.get_Node_buffers().key_in_buffer(flushed_ofs as int, k, buffer_idx + flushed_ofs));
                assert(self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, buffer_idx + flushed_ofs));
                assert(self.i_buffer().map.contains_key(k));
            }

            if self.i_buffer().map.contains_key(k) {
                let buffer_idx = choose |buffer_idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, buffer_idx);
                assert(buffers_to_child.key_in_buffer(0, k, buffer_idx-flushed_ofs));
                buffers_to_child.i_from_domain(0);
                assert(buffers_to_child.i().map.contains_key(k));
            }

            buffers_to_child.query_agrees_with_i(k, 0);
            self.query_from_refines(k);
            assert(buffers_to_child.query(k) == buffers_to_child.i().query(k));
            assert(self.i_buffer().query(k) == self.get_Node_buffers().query_from(k, flushed_ofs as int));
            BufferSeq::common_buffer_seqs(buffers_to_child, self.get_Node_buffers(), 0, flushed_ofs as int, k);
        }
        assert(buffers_to_child.i().apply_filter(child_domain.key_set()) =~= self.i_buffer().apply_filter(child_domain.key_set()));
        assert(self.flush(child_idx, buffer_gc).i().get_Node_children() =~= self.i().flush(child_idx).get_Node_children());

        let a = self.flush(child_idx, buffer_gc);
        let b = self.i().flush(child_idx);
        let keep_keys = all_keys().difference(child_domain.key_set());

        a.i_buffer_domain();

        assert forall |k|
        ({
            &&& #[trigger] a.i().get_Node_buffer().map.contains_key(k) <==> b.get_Node_buffer().map.contains_key(k)
            &&& a.i().get_Node_buffer().map.contains_key(k) ==> a.i().get_Node_buffer().map[k] == b.get_Node_buffer().map[k]
        }) by {
            if a.i().get_Node_buffer().map.contains_key(k) {
                if child_domain.contains(k) {
                    a.get_Node_pivots().route_is_lemma(k, child_idx as int);
                    assert(a.flushed_ofs(k) == a.get_Node_buffers().len());
                    assert(false);
                }
                assert(keep_keys.contains(k));
                let idx = choose |idx| a.get_Node_buffers().key_in_buffer_filtered(a.make_offset_map(), 0, k, idx);
                let r = a.get_Node_pivots().route(k);
                assert(r != child_idx);
                assert(a.flushed_ofs(k) == self.flushed_ofs(k) - buffer_gc);
                assert(self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx + buffer_gc));
                assert(b.get_Node_buffer().map.contains_key(k));

                self.query_from_refines(k);
                a.query_from_refines(k);
                BufferSeq::common_buffer_seqs(a.get_Node_buffers(), self.get_Node_buffers(), a.flushed_ofs(k) as int, buffer_gc as int, k);
            }

            if b.get_Node_buffer().map.contains_key(k) {
                assert(keep_keys.contains(k));
                assert(self.key_in_domain(k));
                assert(a.flushed_ofs(k) == self.flushed_ofs(k) - buffer_gc);
                let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(self.make_offset_map(), 0, k, idx);
                assert(a.get_Node_buffers().key_in_buffer_filtered(a.make_offset_map(), 0, k, idx - buffer_gc));
                assert(a.i().get_Node_buffer().map.contains_key(k));
            }
        }
        assert(a.i().get_Node_buffer().map.dom() =~= b.get_Node_buffer().map.dom());
        assert(a.i().get_Node_buffer() =~= b.get_Node_buffer());
    }

    pub proof fn compact_wf(self, start: nat, end: nat, compacted_buffer: Buffer)
        requires self.can_compact(start, end, compacted_buffer)
        ensures self.compact(start, end, compacted_buffer).wf()
    {
    }

    pub proof fn compact_buffer_property(self, start: nat, end: nat, compacted_buffer: Buffer)
        requires self.can_compact(start, end, compacted_buffer)
        ensures compacted_buffer == self.get_Node_buffers().slice(start as int, end as int).i_filtered(self.make_offset_map().decrement(start))
    {
        let slice_ofs_map = self.make_offset_map().decrement(start);
        let compact_slice = self.get_Node_buffers().slice(start as int, end as int);
        let compact_slice_i = compact_slice.i_filtered(slice_ofs_map);

        compact_slice.i_filtered_from_domain(slice_ofs_map, 0);
        assert forall |k| #[trigger] compacted_buffer.map.contains_key(k)
        implies compacted_buffer.map[k] == compact_slice_i.map[k] 
        by {
            compact_slice.query_from_same_as_i_filtered(k, 0, slice_ofs_map);
        }
        assert(compacted_buffer =~= compact_slice_i);
    }

    pub proof fn compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: Buffer)
        requires self.can_compact(start, end, compacted_buffer)
        ensures self.compact(start, end, compacted_buffer).i() == self.i()
    {
        let result = self.compact(start, end, compacted_buffer);

        BetreeNode::i_wf_auto();
        BetreeNode::i_children_lemma_auto();
        PivotTable::route_lemma_auto();

        assert(result.i().get_Node_children() =~= self.i().get_Node_children());

        let ofs_map = self.make_offset_map();
        let slice_ofs_map = ofs_map.decrement(start);
        let result_ofs_map = result.make_offset_map();
        let compact_slice = self.get_Node_buffers().slice(start as int, end as int);

        self.compact_buffer_property(start, end, compacted_buffer);

        assert forall |k|
        ({
            &&& #[trigger] result.i().get_Node_buffer().map.contains_key(k) <==> self.i().get_Node_buffer().map.contains_key(k)
            &&& result.i().get_Node_buffer().map.contains_key(k) ==> result.i().get_Node_buffer().map[k] == self.i().get_Node_buffer().map[k]
        }) by {
            result.i_buffer_domain();
            self.i_buffer_domain();
            compact_slice.i_filtered_from_domain(slice_ofs_map, 0);

            if result.i().get_Node_buffer().map.contains_key(k) {
                assert(self.key_in_domain(k));
                let idx = choose |idx| result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, idx);
                if idx < start {
                    assert(self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, idx));
                } else if idx < start+1 {
                    let slice_idx = choose |slice_idx| compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, slice_idx);
                    assert(self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, start + slice_idx));
                } else {
                    assert(self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, idx + (end - start - 1)));
                }
                assert(self.i().get_Node_buffer().map.contains_key(k));

                self.query_from_refines(k);
                result.query_from_refines(k);

                let ofs = self.flushed_ofs(k) as int;
                let compacted_bufferseq = BufferSeq{buffers: seq![compacted_buffer]};
                assert(compacted_bufferseq.query_from(k, 1) == Message::Update{delta: nop_delta()});
                assert(compacted_buffer.query(k) == compacted_bufferseq.query_from(k, 0));

                if ofs < start {
                    if !compacted_buffer.map.contains_key(k) {
                        assert forall #![auto] |i| 0 <= i < compact_slice.len()
                        implies !compact_slice[i].map.contains_key(k)
                        by {
                            if compact_slice[i].map.contains_key(k) {
                                assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, i));
                                assert(false);
                            }
                        }
                        compact_slice.not_present_query_lemma(k, 0);
                    }
                    assert(compact_slice.query(k) == compacted_buffer.query(k));

                    let left = self.get_Node_buffers().slice(0, start as int);
                    BufferSeq::extend_buffer_seq_lemma(compact_slice, left, k, ofs);
                    BufferSeq::extend_buffer_seq_lemma(compacted_bufferseq, left, k, ofs);

                    assert(left.extend(compact_slice) =~= self.get_Node_buffers().slice(0, end as int));
                    assert(left.extend(compacted_bufferseq) =~= result.get_Node_buffers().slice(0, start as int + 1));

                    let right = self.get_Node_buffers().slice(end as int, self.get_Node_buffers().len() as int);
                    BufferSeq::extend_buffer_seq_lemma(right, self.get_Node_buffers().slice(0, end as int), k, ofs);
                    BufferSeq::extend_buffer_seq_lemma(right, result.get_Node_buffers().slice(0, start as int + 1), k, ofs);

                    assert(self.get_Node_buffers().slice(0, end as int).extend(right) =~= self.get_Node_buffers());
                    assert(result.get_Node_buffers().slice(0, start as int + 1).extend(right) =~= result.get_Node_buffers());
                    assert(result.i().get_Node_buffer().map[k] == self.i().get_Node_buffer().map[k]);
                } else if ofs < end {
                    if !compacted_buffer.map.contains_key(k) {
                        assert forall #![auto] |i| ofs-start <= i < compact_slice.len()
                        implies !compact_slice[i].map.contains_key(k)
                        by {
                            if compact_slice[i].map.contains_key(k) {
                                assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, i));
                                assert(false);
                            }
                        }
                        compact_slice.not_present_query_lemma(k, ofs-start);
                    }
                    assert(compact_slice.query_from(k, ofs-start) == compacted_buffer.query(k));

                    let right = self.get_Node_buffers().slice(end as int, self.get_Node_buffers().len() as int);
                    BufferSeq::extend_buffer_seq_lemma(right, compacted_bufferseq, k, 0);
                    BufferSeq::extend_buffer_seq_lemma(right, compact_slice, k, ofs-start);
                    BufferSeq::common_buffer_seqs(compact_slice.extend(right), self.get_Node_buffers(), ofs-start, start as int, k);
                    BufferSeq::common_buffer_seqs(compacted_bufferseq.extend(right), result.get_Node_buffers(), 0, start as int, k);
                    assert(result.i().get_Node_buffer().map[k] == self.i().get_Node_buffer().map[k]);
                } else {
                    BufferSeq::common_buffer_seqs(self.get_Node_buffers(), result.get_Node_buffers(), ofs, start+1-end, k);
                }
            }

            if self.i().get_Node_buffer().map.contains_key(k) {
                let idx = choose |idx| self.get_Node_buffers().key_in_buffer_filtered(ofs_map, 0, k, idx);
                if idx < start {
                    assert(result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, idx));
                } else if idx < end {
                    assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, idx-start));
                    assert(result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, start as int));
                } else {
                    assert(result.get_Node_buffers().key_in_buffer_filtered(result_ofs_map, 0, k, idx - (end - start - 1)));
                }
                assert(result.i().get_Node_buffer().map.contains_key(k));
            }
        }
        assert(result.i().get_Node_buffer().map.dom() =~= self.i().get_Node_buffer().map.dom());
        assert(result.i().get_Node_buffer() =~= self.i().get_Node_buffer());


    }
} // end impl BetreeNode

// TODO(jialin): Why isn't this just impl StampedBetree { fn i() }?
pub open spec(checked) fn i_stamped_betree(stamped: StampedBetree) -> PivotBetree_v::StampedBetree
recommends
    stamped.value.wf(),
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine{
    pub open spec(checked) fn i(self) -> PivotBetree_v::QueryReceiptLine
        recommends self.wf()
    {
        PivotBetree_v::QueryReceiptLine{node: self.node.i(), result: self.result}
    }
}

impl QueryReceipt{
    pub open spec(checked) fn i(self) -> PivotBetree_v::QueryReceipt
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
    pub open spec(checked) fn i(self) -> PivotBetree_v::Path
    recommends
        self.valid(),
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

    #[verifier::spinoff_prover]
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
        assert(forall |i| #![auto] 0 <= i < new_children.len() ==> new_children[i].wf());
        
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
            assert(self.substitute(replacement).make_offset_map() =~= self.node.make_offset_map());
        }
    }

    pub proof fn substitute_noop(self, replacement: BetreeNode)
        requires self.valid(), replacement.wf(), 
            self.target().i() == replacement.i()
        ensures 
            self.substitute(replacement).wf(),
            self.substitute(replacement).i() == self.node.i()
        decreases self.depth
    {
        self.target_wf();
        self.substitute_preserves_wf(replacement);

        PivotTable::route_lemma_auto();
        BetreeNode::i_children_lemma_auto();

        if 0 < self.depth {
            self.subpath().substitute_noop(replacement);
            assert(self.substitute(replacement).i().get_Node_children() =~= self.node.i().get_Node_children());
            assert(self.substitute(replacement).make_offset_map() =~= self.node.make_offset_map());
        }
    }
}

impl FilteredBetree::Label {
    pub open spec(checked) fn i(self) -> PivotBetree::Label
    {
        match self {
            FilteredBetree::Label::Query{end_lsn, key, value} => PivotBetree::Label::Query{end_lsn: end_lsn, key: key, value: value},
            FilteredBetree::Label::Put{puts} => PivotBetree::Label::Put{puts: puts},
            FilteredBetree::Label::FreezeAs{stamped_betree} =>
                PivotBetree::Label::FreezeAs{stamped_betree:
                    if stamped_betree.value.wf() { i_stamped_betree(stamped_betree) }
                    else { arbitrary() } },
            FilteredBetree::Label::Internal{} => PivotBetree::Label::Internal{},
        }
    }
} // end impl FilteredBetree::Label

impl FilteredBetree::State {
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& (self.root.is_Node() ==> self.root.my_domain() == total_domain())
    }

    pub open spec(checked) fn i(self) -> PivotBetree::State
    recommends
        self.wf(),
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

    pub proof fn internal_flush_memtable_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_flush_memtable(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        self.root.i_wf();

        let a = self.root.push_memtable(self.memtable).value.i();
        let b = self.root.i().push_memtable(self.memtable).value;
        let promote = self.root.promote(total_domain());
        let buffers = BufferSeq{buffers: seq![self.memtable.buffer]};
        
        BetreeNode::i_children_lemma_auto();
        assert(a.get_Node_children() =~= b.get_Node_children());

        self.root.promote_commutes_with_i(total_domain());
        promote.extend_buffer_seq_refines_merge_buffer(buffers);

        assert(buffers.i().apply_filter(total_domain().key_set()) =~= buffers.i());
        assert(buffers.i_from(1) == Buffer::empty()); // trigger
        assert(buffers.i() =~= buffers[0]);
        assert(a.get_Node_buffer() == b.get_Node_buffer());

        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_flush_memtable()));
    }

    pub proof fn internal_grow_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_grow(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        BetreeNode::i_wf_auto();
        PivotTable::route_lemma_auto();
        post.root.i_children_lemma();
        assert(post.i().root =~= self.i().root.grow());
        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_grow()));
    }

    pub proof fn internal_split_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, request: SplitRequest)
        requires self.inv(), FilteredBetree::State::internal_split(self, post, lbl, path, request)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        BetreeNode::i_wf_auto();

        path.target().split_parent_wf(request);
        path.substitute_refines(path.target().split_parent(request));

        path.i_valid();
        path.target_commutes_with_i();
        path.target().split_parent_commutes_with_i(request);

        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_split(path.i(), request)));
    }

    pub proof fn internal_flush_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, child_idx: nat, buffer_gc: nat)
        requires self.inv(), FilteredBetree::State::internal_flush(self, post, lbl, path, child_idx, buffer_gc)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        BetreeNode::i_wf_auto();
        path.target().flush_wf(child_idx, buffer_gc);
        path.substitute_refines(path.target().flush(child_idx, buffer_gc));

        path.i_valid();
        path.target_commutes_with_i();
        path.target().flush_commutes_with_i(child_idx, buffer_gc);

        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_flush(path.i(), child_idx)));
    }

    pub proof fn internal_compact_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, start: nat, end: nat, compacted_buffer: Buffer)
        requires self.inv(), FilteredBetree::State::internal_compact(self, post, lbl, path, start, end, compacted_buffer)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        BetreeNode::i_wf_auto();
        path.target().compact_wf(start, end, compacted_buffer);
        path.target().compact_commutes_with_i(start, end, compacted_buffer);
        path.substitute_noop(path.target().compact(start, end, compacted_buffer));        

        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_noop()));
    }

    pub proof fn internal_noop_noop(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_noop(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        BetreeNode::i_wf_auto();
        assert(PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_noop()));
    }

    pub proof fn next_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::next(self, post, lbl),
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);

        match choose |step| FilteredBetree::State::next_by(self, post, lbl, step)
        {
            FilteredBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
            FilteredBetree::Step::put() => { self.put_refines(post, lbl); }
            FilteredBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
            FilteredBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_refines(post, lbl); }
            FilteredBetree::Step::internal_grow() => { self.internal_grow_refines(post, lbl); }
            FilteredBetree::Step::internal_split(path, split_request) => { self.internal_split_refines(post, lbl, path, split_request); }
            FilteredBetree::Step::internal_flush(path, child_idx, buffer_gc) => { self.internal_flush_refines(post, lbl, path, child_idx, buffer_gc); }
            FilteredBetree::Step::internal_compact(path, start, end, compacted_buffer) => { self.internal_compact_refines(post, lbl, path, start, end, compacted_buffer); }
            FilteredBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
            _ => { assert(false); } 
        }
    }
} // end impl FilteredBetree::State

}//verus
