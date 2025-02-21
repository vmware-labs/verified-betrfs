// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::PagedBetree_v;
use crate::betree::PagedBetree_v::PagedBetree;
use crate::betree::PivotBetree_v::*;
use crate::betree::SplitRequest_v::*;

verus! {

broadcast use PivotTable::route_lemma, PivotTable::route_is_lemma;

impl BetreeNode {
    pub open spec(checked) fn i_children_seq(self, start: int) -> Seq<PagedBetree_v::BetreeNode>
        recommends self is Node, 0 <= start <= self->children.len()
        decreases self, 0nat, self->children.len()-start
        when self is Node && 0 <= start <= self->children.len()
    {
        if start == self->children.len() {
            seq![]
        } else {
            let child = self->children[start].i();
            seq![child] + self.i_children_seq(start+1)
        }
    }

    pub open spec(checked) fn i_children(self) -> PagedBetree_v::ChildMap
        recommends self is Node
        decreases self, 1nat
    {
        let seq_result = self.i_children_seq(0);
    
        PagedBetree_v::ChildMap{map: Map::new(|k: Key| true, 
            |k: Key| if self.key_in_domain(k) {
                let r = self->pivots.route(k);
                seq_result[r]
            } else {
                PagedBetree_v::BetreeNode::Nil
            }
        )}
    }

    pub open spec(checked) fn i(self) -> PagedBetree_v::BetreeNode
        decreases self
    {
        if self is Nil {
            PagedBetree_v::BetreeNode::Nil{}
        } else {
            PagedBetree_v::BetreeNode::Node{buffer: self->buffer, children: self.i_children()}
        }
    }

    // used as a trigger but not in defn of i_children bc closure can't take recursive fn
    pub open spec(checked) fn i_child(self, k: Key) -> PagedBetree_v::BetreeNode
        recommends self is Node
    {
        if self.key_in_domain(k) {
            self.child(k).i()
        } else {
            PagedBetree_v::BetreeNode::Nil{}
        }
    }

    proof fn i_children_seq_lemma(self, start: int)
        requires 
            self.wf(), 
            self is Node, 
            0 <= start <= self->children.len()
        ensures
            self.i_children_seq(start).len() == self->children.len() - start,
            forall |i| 0 <= i < self.i_children_seq(start).len()
            ==> {
                &&& (#[trigger] self.i_children_seq(start)[i]).wf()
                &&& self.i_children_seq(start)[i] == self->children[i+start].i()
            }
        decreases self, 0nat, self->children.len()-start 
    {
        if start < self->children.len() {
            assert(self.valid_child_index(start as nat)); // trigger

            let result = self.i_children_seq(start);
            let child = self->children[start];
            let sub_seq = self.i_children_seq(start+1);

            child.i_wf();
            self.i_children_seq_lemma(start+1);
        }
    }

    proof fn i_children_seq_same(self, other: BetreeNode, start: int)
        requires self.wf(), self is Node, 0 <= start <= self->children.len(),
            other.wf(), other is Node, other->children == self->children
        ensures self.i_children_seq(start) == other.i_children_seq(start)
        decreases self->children.len()-start
    {
        if start < self->children.len() {
            self.i_children_seq_same(other, start+1);
        }
    }

    proof fn i_children_lemma(self)
        requires self is Node, self.wf()
        ensures forall |k:Key| {
            (#[trigger] self.i_children().map[k]).wf()
            && self.i_children().map[k] == self.i_child(k)
        }
        decreases self, 1nat
    {
        let seq_result = self.i_children_seq(0);
        self.i_children_seq_lemma(0);

//        assert forall |k:Key| {
//            (#[trigger] self.i_children().map[k]).wf()
//            && self.i_children().map[k] == self.i_child(k)
//        } by {
//            if self.key_in_domain(k) {
//                let r = self->pivots.route(k);
////                assert(self.i_children().map[k] == seq_result[r]);
////                assert(self.i_children().map[k] == self.i_child(k));
//            }
//        }
    }

    proof fn i_wf(self)
        requires self.wf()
        ensures self.i().wf()
        decreases self, 2nat
    {
        if self is Node {
            self.i_children_lemma();
        }
    }

    pub open spec /*XXX(checked)*/ fn children_have_matching_domains(self, other_children: Seq<BetreeNode>) -> bool
    recommends
        self.wf(),
        self.is_index(),
    {
        &&& other_children.len() == self->children.len()
        &&& (forall |i| #[trigger] self.valid_child_index(i) ==> {
            &&& other_children[i as int].wf()
            &&& other_children[i as int] is Node
            //XXX self->children[i] is wf by instantiating linked_children
            &&& other_children[i as int].my_domain() == self->children[i as int].my_domain()
        })
    }

    proof fn empty_root_refines()
        ensures Self::empty_root(total_domain()).i() == PagedBetree_v::BetreeNode::empty_root()
    {
        let empty = Self::empty_root(total_domain());
        let empty_child_map = PagedBetree_v::empty_child_map();

        assert(empty.wf_children()); // trigger
        empty.i_children_lemma();

        assert(empty.i()->children.map =~= empty_child_map.map);
//        assert(empty.i() == PagedBetree_v::BetreeNode::empty_root());
    }

    pub open spec(checked) fn split_element(self, request: SplitRequest) -> Element
        recommends self.wf(), self.can_split_parent(request)
    {
        let old_child = self->children[request.get_child_idx() as int];
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => to_element(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => old_child->pivots.pivots[child_pivot_idx as int]
        }
    }

    proof fn split_leaf_wf(self, split_key: Key)
        requires self.can_split_leaf(split_key)
        ensures self.split_leaf(split_key).0.wf(), self.split_leaf(split_key).1.wf()
    {
        assert(self.split_leaf(split_key).0.wf_children());
        assert(self.split_leaf(split_key).1.wf_children());
    }
    
    proof fn split_index_wf(self, pivot_idx: nat)
        requires self.can_split_index(pivot_idx)
        ensures self.split_index(pivot_idx).0.wf(), self.split_index(pivot_idx).1.wf()
    {
        let (new_left, new_right) = self.split_index(pivot_idx);
        assert forall |i| new_left.valid_child_index(i) ==> self.valid_child_index(i) by {}
        assert forall |i| new_right.valid_child_index(i) ==> self.valid_child_index(i+pivot_idx) by {}
//        assert(new_left.wf_children());
//        assert(new_right.wf_children());
    }
    
    pub proof fn split_parent_wf(self, request: SplitRequest) 
        requires self.can_split_parent(request)
        ensures self.split_parent(request).wf()
    {
        let child_idx = request.get_child_idx();
        let old_child = self->children[child_idx as int];
        let new_parent = self.split_parent(request);

        self->pivots.insert_wf(child_idx as int + 1, self.split_element(request));

        assert forall |i| #[trigger] new_parent.valid_child_index(i) ==> 
        ({
            &&& i < child_idx ==> self.valid_child_index(i) 
            &&& i > child_idx + 1 ==> self.valid_child_index((i-1) as nat)
        }) by {}

        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => old_child.split_leaf_wf(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => old_child.split_index_wf(child_pivot_idx),
        }
//        assert(new_parent.wf_children());
//        assert(new_parent.linked_children());
    }

    pub open spec(checked) fn split_keys(self, request: SplitRequest) -> (Set<Key>, Set<Key>)
        recommends self.can_split_parent(request)
    {
        let child_idx = request.get_child_idx();
        let child_domain = self.child_domain(child_idx);

        let split_element = self.split_element(request);
        let left_keys = Set::new(|k| child_domain.contains(k) && Element::lt(to_element(k), split_element));
        let right_keys = Set::new(|k| child_domain.contains(k) && !left_keys.contains(k));

        (left_keys, right_keys)
    }

    proof fn split_keys_agrees_with_domains(self, request: SplitRequest)
        requires self.can_split_parent(request)
        ensures ({
            let child_domain = self.child_domain(request.get_child_idx());
            let split_element = self.split_element(request);
            let left_domain = Domain::Domain{start: child_domain->start, end: split_element};
            let right_domain = Domain::Domain{start: split_element, end: child_domain->end};
            &&& left_domain.key_set() == self.split_keys(request).0
            &&& right_domain.key_set() == self.split_keys(request).1
        })
    {
        let child_domain = self.child_domain(request.get_child_idx());
        let split_element = self.split_element(request);
        let left_domain = Domain::Domain{start: child_domain->start, end: split_element};
        let right_domain = Domain::Domain{start: split_element, end: child_domain->end};
        let (left_keys, right_keys) = self.split_keys(request);

        assert(Element::lt(split_element, child_domain->end)); // trigger
//        assert forall |k:Key| #[trigger] left_keys.contains(k) <==> left_domain.contains(k)
//        by {
//            if left_domain.contains(k) {
////                assert(left_domain->start == child_domain->start);
//                assert(child_domain.contains(k));
////                assert(left_keys.contains(k));
//            }
//        }
        assert(left_keys =~= left_domain.key_set());

        if request is SplitIndex {
            assert(Element::lt(child_domain->start, split_element));
        }
//        assert(Element::lte(child_domain->start, split_element));

        assert forall |k:Key| #[trigger] right_keys.contains(k) <==> right_domain.contains(k)
        by {
            if right_domain.contains(k) {
//                assert(!left_keys.contains(k));
//                assert(child_domain.contains(k));
//                assert(right_keys.contains(k));
            }
        }
        assert(right_keys =~= right_domain.key_set());
    }

    proof fn split_commutes_with_i_left(self, request: SplitRequest, key: Key)
        requires 
            self.can_split_parent(request),
            self.my_domain().contains(key),
            self.split_keys(request).0.contains(key)
        ensures 
            self.split_parent(request).i_children().map[key] 
            == self.i().split(self.split_keys(request).0, self.split_keys(request).1).child(key)
    {
        self.split_parent_wf(request);

        let (left_keys, _) = self.split_keys(request);
        let split_element = self.split_element(request);
        self.split_keys_agrees_with_domains(request);

        self.i_children_lemma();
        self.split_parent(request).i_children_lemma();

        let a = self.child(key).i().filter_buffer_and_children(left_keys);
        if request is SplitLeaf {
            let split_key = to_key(split_element);
            let b = self.child(key).split_leaf(split_key).0;
            
            self.child(key).split_leaf_wf(split_key);

            assert forall |k| #[trigger] a->children.map[k] == b.i()->children.map[k] by {}
            assert(a->children.map =~= b.i()->children.map);
        } else {
            let child_pivot_idx = request->child_pivot_idx;
            let b = self.child(key).split_index(child_pivot_idx).0;

            self.child(key).split_index_wf(child_pivot_idx);

            b.i_children_lemma();
            self.child(key).i_children_lemma();
            assert(a->children.map =~= b.i()->children.map);
        }
    }

    proof fn split_commutes_with_i_right(self, request: SplitRequest, key: Key)
        requires
            self.can_split_parent(request),
            self.my_domain().contains(key), 
            self.split_keys(request).1.contains(key)
        ensures 
            self.split_parent(request).i_children().map[key] 
            == self.i().split(self.split_keys(request).0, self.split_keys(request).1).child(key)
    {
        self.split_parent_wf(request);

        let (_, right_keys) = self.split_keys(request);
        let split_element = self.split_element(request);
        self.split_keys_agrees_with_domains(request);

        self.i_children_lemma();
        self.split_parent(request).i_children_lemma();

        let a = self.child(key).i().filter_buffer_and_children(right_keys);
        if request is SplitLeaf {
            let split_key = to_key(split_element);
            let b = self.child(key).split_leaf(split_key).1;
            self.child(key).split_leaf_wf(split_key);

//            assert forall |k| #[trigger] a->children.map[k] == b.i()->children.map[k] by {}
            assert(a->children.map =~= b.i()->children.map);
        } else {
            let child_pivot_idx = request->child_pivot_idx;
            let b = self.child(key).split_index(child_pivot_idx).1;
            self.child(key).split_index_wf(child_pivot_idx);

            b.i_children_lemma();
            self.child(key).i_children_lemma();

            assert forall |k| #[trigger] a->children.map[k] == b.i()->children.map[k]
            by {
                if right_keys.contains(k) {
//                    assert(b->pivots.bounded_key(k)); // trigger
                    let r = b->pivots.route(k);
                }
            }
            assert(a->children.map =~= b.i()->children.map);
        }
    }

    proof fn split_commutes_with_i_nonsplit(self, request: SplitRequest, key: Key)
        requires 
            self.can_split_parent(request),
            self.my_domain().contains(key), 
            !self.split_keys(request).0.contains(key),
            !self.split_keys(request).1.contains(key)
        ensures ({
            let (left_keys, right_keys) = self.split_keys(request);
            &&& self.split_parent(request).i_children().map[key] == self.i().split(left_keys, right_keys).child(key)
        })
    {
        let (left_keys, right_keys) = self.split_keys(request);
        let result = self.split_parent(request);
        let i_result = self.i().split(left_keys, right_keys);

        self.split_parent_wf(request);
        let child_idx = request.get_child_idx();
        let r = self->pivots.route(key);

        if r < child_idx {
            assert(Element::lte(result->pivots.pivots[r], to_element(key))); // trigger for route_is_lemma

        }

        self.i_children_lemma();
        result.i_children_lemma();
//        assert(result.i_children().map[key] == i_result.child(key));
    }

    proof fn split_commutes_with_i(self, request: SplitRequest)
        requires self.can_split_parent(request)
        ensures ({
            let (left_keys, right_keys) = self.split_keys(request);
            &&& self.split_parent(request).i() == self.i().split(left_keys, right_keys)
        })
    {
        self.split_parent_wf(request);
        let (left_keys, right_keys) = self.split_keys(request);
//        assert(self.split_parent(request).my_domain() == self.my_domain());

        let parent_i = self.split_parent(request).i();
        let i_parent = self.i().split(left_keys, right_keys);

        assert forall |k: Key| true
        implies i_parent->children.map[k] == parent_i->children.map[k]
        by {
            if self.my_domain().contains(k) {
                if left_keys.contains(k) {
                    self.split_commutes_with_i_left(request, k);
                } else if right_keys.contains(k) {
                    self.split_commutes_with_i_right(request, k);
                } else {
                    self.split_commutes_with_i_nonsplit(request, k);
                }
            } else {
//                assert(i_parent->children.map[k] is Nil);
//                assert(parent_i->children.map[k] is Nil);
            }
        }
        assert(i_parent->children.map =~= parent_i->children.map);
    }

    proof fn promote_and_merge_wf(self, domain: Domain, buffer: SimpleBuffer)
        requires self.wf(), domain.wf(), domain is Domain
        ensures self.promote(domain).merge_buffer(buffer).wf()
    {
        let result = self.promote(domain).merge_buffer(buffer);
//        assert(self.promote(domain).wf());
        assert forall |i| #[trigger] result.valid_child_index(i) ==> self.promote(domain).valid_child_index(i) by {}
//        assert(result.wf());
    }

    proof fn flush_wf(self, child_idx: nat)
        requires self.can_flush(child_idx)
        ensures self.flush(child_idx).wf()
    {
        let result = self.flush(child_idx);
        let child_domain = self.child_domain(child_idx);
        let moved_buffer = self->buffer.apply_filter(child_domain.key_set());

        let old_child = self->children[child_idx as int];
        let new_child = old_child.promote(child_domain).merge_buffer(moved_buffer);
        old_child.promote_and_merge_wf(child_domain, moved_buffer);
        assert forall |i| #[trigger] result.valid_child_index(i) ==> self.valid_child_index(i) by {}
    }

    proof fn promote_and_merge_commutes_with_i(self, domain: Domain, new_buffer: SimpleBuffer)
        requires self.wf(), domain.wf(), domain is Domain
        ensures self.promote(domain).merge_buffer(new_buffer).i() == self.i().promote().merge_buffer(new_buffer)
    {
        self.i_wf();

        let a = self.promote(domain).merge_buffer(new_buffer);
        let b = self.i().promote().merge_buffer(new_buffer);

        if self is Node {
            assert forall |i| #[trigger] a.valid_child_index(i) ==> self.promote(domain).valid_child_index(i) by {}
            self.i_children_seq_same(a, 0);
        } else {
            a.i_children_lemma();
            
        }
        assert(a.i()->children.map =~= b->children.map);
    }

    proof fn flush_commutes_with_i(self, child_idx: nat)
        requires self.can_flush(child_idx)
        ensures self.i().flush(self.child_domain(child_idx).key_set()) == self.flush(child_idx).i()
    {
        self.flush_wf(child_idx);

        let child = self->children[child_idx as int];
        let child_domain = self.child_domain(child_idx);
        let moved_buffer = self->buffer.apply_filter(child_domain.key_set());
        child.promote_and_merge_commutes_with_i(child_domain, moved_buffer);

        self.i_children_lemma();
        self.flush(child_idx).i_children_lemma();

        assert(self.flush(child_idx).i()->children.map =~= self.i().flush(child_domain.key_set())->children.map);
    }
} // end impl BetreeNode

pub open spec(checked) fn i_stamped_betree(stamped: StampedBetree) -> PagedBetree_v::StampedBetree
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine{
    pub open spec(checked) fn i(self) -> PagedBetree_v::QueryReceiptLine
        recommends self.wf()
    {
        PagedBetree_v::QueryReceiptLine{node: self.node.i(), result: self.result}
    }
}

impl QueryReceipt{
    pub open spec(checked) fn i(self) -> PagedBetree_v::QueryReceipt
        recommends self.valid()
    {
        PagedBetree_v::QueryReceipt{
            key: self.key,
            root: self.root.i(),
            lines: Seq::new(self.lines.len(), |i:int| self.lines[i].i())
        }
    }

    proof fn i_valid(self)
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
}

impl Path{
    pub open spec /*XXX(checked)*/ fn routing(self) -> Seq<Set<Key>>
        recommends self.valid()
        decreases self.depth
    {
        if self.depth == 0 {
            seq![]
        } else {
            let pivots = self.node->pivots;
            //XXX self->pivots.route_lemma(key)
            let keys = pivots.pivot_range_keyset(pivots.route(self.key));
            seq![keys] + self.subpath().routing() 
        }
    }

    proof fn routing_lemma(self)
        requires self.valid()
        ensures self.routing().len() == self.depth
        decreases self.depth
    {
        if 0 < self.depth {
            self.subpath().routing_lemma();
        }
    }

    pub open spec/*XXX(checked)*/ fn i(self) -> PagedBetree_v::Path
    {
        //XXX call routing_lemma?
        PagedBetree_v::Path{node: self.node.i(), key: self.key, routing: self.routing()}
    }

    proof fn subpath_commutes_with_i(self)
        requires self.valid(), 0 < self.depth
        ensures self.subpath().i() == self.i().subpath()
    {
        self.node.i_wf();
        self.node.i_children_lemma();

        self.routing_lemma();
        assert(self.subpath().i().routing =~= self.i().subpath().routing);
    }

    proof fn i_valid(self)
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

    proof fn target_wf(self)
        requires self.valid()
        ensures self.target().wf(), self.target() is Node
        decreases self.depth
    {
        if self.depth > 0 {
            self.subpath().target_wf();
        }
    }
    
    proof fn target_commutes_with_i(self)
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
        requires self.can_substitute(replacement)
        ensures self.substitute(replacement).wf()
        decreases self.depth, 1nat
    {
        if 0 < self.depth {
            self.subpath().substitute_preserves_wf(replacement);
    
            let result = self.substitute(replacement);
            if result is Node {
                self.replaced_children_matching_domains(replacement);
                assert(self.node.wf_children());
                assert forall |i| #[trigger] result.valid_child_index(i) ==> self.node.valid_child_index(i) by {}
//                assert(result.wf_children());
            }
        }
    }

    // #[verifier::spinoff_prover]
    proof fn replaced_children_matching_domains(self, replacement: BetreeNode)
        requires self.can_substitute(replacement), 0 < self.depth
        ensures self.node.children_have_matching_domains(self.replaced_children(replacement))
        decreases self.depth, 0nat
    {
        self.subpath().substitute_preserves_wf(replacement);

        let old_children = self.node->children;
        let new_children = self.replaced_children(replacement);
        
        if 0 < self.subpath().depth {
            self.subpath().replaced_children_matching_domains(replacement);
        } else {
//            assert forall |i| #[trigger] self.node.valid_child_index(i) ==> new_children[i as int].wf() by {}
        }
    }

    proof fn substitute_commutes_with_i(self, replacement: BetreeNode)
        requires self.can_substitute(replacement)
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
//            assert(self.substitute(replacement).i_children().wf());

            self.i().substitute_preserves_wf(replacement.i());
//            assert(self.i().replaced_children(replacement.i()).wf());
            self.subpath().substitute_commutes_with_i(replacement);

            self.subpath_commutes_with_i();
            self.node.i_children_lemma();
            assert(self.substitute(replacement).i()->children.map 
                =~= self.i().substitute(replacement.i())->children.map
            );
        }
    }
}

impl PivotBetree::Label {
    pub open spec(checked) fn i(self) -> PagedBetree::Label
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
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& (self.root is Node ==> self.root.my_domain() == total_domain())
    }

    pub open spec(checked) fn i(self) -> PagedBetree::State
    {
        PagedBetree::State{root: self.root.i(), memtable: self.memtable}
    }

    proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires PivotBetree::State::initialize(self, stamped_betree)
        ensures PagedBetree::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        stamped_betree.value.i_wf();
    }

    proof fn query_refines(self, post: Self, lbl: PivotBetree::Label, receipt: QueryReceipt)
        requires self.inv(), PivotBetree::State::query(self, post, lbl, receipt)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        receipt.i_valid();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::query(receipt.i())));
    }

    proof fn put_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::put(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::put()));
    }

    proof fn freeze_as_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::freeze_as(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::freeze_as()));
    }

    proof fn internal_flush_memtable_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::internal_flush_memtable(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        self.root.promote_and_merge_wf(total_domain(), self.memtable.buffer);

        let a = self.root.push_memtable(self.memtable).i();
        let b = self.root.i().push_memtable(self.memtable).value;

        BetreeNode::empty_root_refines();
        let equiv_children_node = if self.root is Node { self.root } else { BetreeNode::empty_root(total_domain()) };
        equiv_children_node.i_children_seq_same(self.root.push_memtable(self.memtable), 0);

//        assert(a->buffer =~= b->buffer);
        assert(a->children.map =~= b->children.map);

        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_flush_memtable()));
    }

    proof fn internal_grow_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::internal_grow(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        post.root.i_wf();
        
        post.root.i_children_lemma();
        assert(post.i().root->children.map =~= PagedBetree_v::constant_child_map(self.root.i()).map);
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_grow()));
    }

    proof fn internal_split_refines(self, post: Self, lbl: PivotBetree::Label, path: Path, request: SplitRequest)
        requires self.inv(), PivotBetree::State::internal_split(self, post, lbl, path, request)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        path.target().i_wf();
        path.target().split_parent_wf(request);
        path.substitute_commutes_with_i(path.target().split_parent(request));

        post.root.i_wf();
        path.i_valid();
        path.target_commutes_with_i();
        path.target().split_commutes_with_i(request);

        let (left_keys, right_keys) = path.target().split_keys(request);
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_split(path.i(), left_keys, right_keys)));
    }

    proof fn internal_flush_refines(self, post: Self, lbl: PivotBetree::Label, path: Path, child_idx: nat)
        requires self.inv(), PivotBetree::State::internal_flush(self, post, lbl, path, child_idx)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        path.target_wf();
        path.target().flush_wf(child_idx);
        path.substitute_commutes_with_i(path.target().flush(child_idx));

        post.root.i_wf();
        path.i_valid();
        path.target_commutes_with_i();
        path.target().flush_commutes_with_i(child_idx);

        let flushed_keys = path.target().child_domain(child_idx).key_set();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_flush(path.i(), flushed_keys)));
    }

    proof fn internal_noop_noop(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::internal_noop(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        post.root.i_wf();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_noop()));
    }

    proof fn next_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::next(self, post, lbl),
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PivotBetree::State::next);
        reveal(PivotBetree::State::next_by);

        match choose |step| PivotBetree::State::next_by(self, post, lbl, step)
        {
            PivotBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
            PivotBetree::Step::put() => { self.put_refines(post, lbl); }
            PivotBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
            PivotBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_refines(post, lbl); }
            PivotBetree::Step::internal_grow() => { self.internal_grow_refines(post, lbl); }
            PivotBetree::Step::internal_split(path, split_request) => { self.internal_split_refines(post, lbl, path, split_request); }
            PivotBetree::Step::internal_flush(path, child_idx) => { self.internal_flush_refines(post, lbl, path, child_idx); }
            PivotBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
            _ => { assert(false); } 
        }
    }
} // end impl PivotBetree::State

}//verus
