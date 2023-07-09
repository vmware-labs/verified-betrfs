use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::BufferSeq_v::*;
use crate::betree::PagedBetree_v;
use crate::betree::PagedBetree_v::PagedBetree;
use crate::betree::PivotBetree_v::*;
use crate::betree::SplitRequest_v::*;

verus! {

impl BetreeNode {
    pub open spec fn i_children_seq(self, start: int) -> Seq<PagedBetree_v::BetreeNode>
        recommends self.is_Node(), 0 <= start <= self.get_Node_children().len()
        decreases self, 0nat, self.get_Node_children().len()-start
    {
        decreases_when(self.is_Node() && 0 <= start <= self.get_Node_children().len());
        if start == self.get_Node_children().len() {
            seq![]
        } else {
            let child = self.get_Node_children()[start].i();
            seq![child] + self.i_children_seq(start+1)
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

    pub proof fn i_children_seq_same(self, other: BetreeNode, start: int)
        requires self.wf(), self.is_Node(), 0 <= start <= self.get_Node_children().len(),
            other.wf(), other.is_Node(), other.get_Node_children() == self.get_Node_children()
        ensures self.i_children_seq(start) == other.i_children_seq(start)
        decreases self.get_Node_children().len()-start
    {
        if start < self.get_Node_children().len() {
            self.i_children_seq_same(other, start+1);
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
        PivotTable::route_lemma_auto();

        assert forall |k:Key| {
            (#[trigger] self.i_children().map[k]).wf()
            && self.i_children().map[k] == self.i_child(k)
        } by {
            if self.key_in_domain(k) {
                let r = self.get_Node_pivots().route(k);
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

    pub proof fn empty_root_refines()
        ensures Self::empty_root(total_domain()).i() == PagedBetree_v::BetreeNode::empty_root()
    {
        let empty = Self::empty_root(total_domain());
        let empty_child_map = PagedBetree_v::empty_child_map();

        assert(empty.wf_children()); // trigger
        empty.i_children_lemma();
        PivotTable::route_lemma_auto();

        assert(empty.i().get_Node_children().map =~= empty_child_map.map);
        assert(empty.i() == PagedBetree_v::BetreeNode::empty_root());
    }

    pub open spec fn split_element(self, request: SplitRequest) -> Element
        recommends self.wf(), self.can_split_parent(request)
    {
        let old_child = self.get_Node_children()[request.get_child_idx() as int];
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => to_element(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => old_child.get_Node_pivots().pivots[child_pivot_idx as int]
        }
    }

    pub proof fn split_parent_wf(self, request: SplitRequest) 
        requires self.wf(), self.can_split_parent(request)
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

    pub proof fn flush_wf(self, child_idx: nat)
        requires self.can_flush(child_idx)
        ensures self.flush(child_idx).wf()
    {
        let child_domain = self.child_domain(child_idx);
        let moved_buffers = self.get_Node_buffers().apply_filter(child_domain.key_set());

        let old_child = self.get_Node_children()[child_idx as int];
        let new_child = old_child.promote(child_domain).extend_buffer_seq(moved_buffers);

        assert(old_child.wf());
        assert(old_child.promote(child_domain).wf());
        assert(new_child.wf());
    }

    // Note: exposing condition to reduce verification time, but why? are recommends checked here?
    pub proof fn nil_promote_and_extend_commutes_with_i(self, domain: Domain, buffers: BufferSeq)
        requires self.wf(), self.is_Nil(), domain.wf(), domain.is_Domain()
        ensures self.promote(domain).extend_buffer_seq(buffers).i() == self.i().promote().extend_buffer_seq(buffers) 
    {
        self.i_wf();
        assert(self.promote(domain).extend_buffer_seq(buffers).wf());

        let a = self.promote(domain).extend_buffer_seq(buffers);
        let b = self.i().promote().extend_buffer_seq(buffers);

        a.i_children_lemma();
        PivotTable::route_lemma_auto();
        assert(a.i().get_Node_children().map =~= b.get_Node_children().map);
    }

    pub proof fn node_promote_and_extend_commutes_with_i(self, domain: Domain, buffers: BufferSeq)
        requires self.wf(), self.is_Node()
        ensures self.promote(domain).extend_buffer_seq(buffers).i() == self.i().promote().extend_buffer_seq(buffers)
    {
        self.i_wf();
        assert(self.promote(domain) == self);
        assert(self.i().promote() == self.i());
        assert(self.promote(domain).extend_buffer_seq(buffers).wf());

        let a = self.promote(domain).extend_buffer_seq(buffers);
        let b = self.i().promote().extend_buffer_seq(buffers);

        assert forall |k| true 
        implies #[trigger] a.i().get_Node_children().map[k] == b.get_Node_children().map[k]
        by {
            if a.key_in_domain(k) {
                assert(self.i().promote().get_Node_children() == b.get_Node_children());
                assert(self.i().promote().get_Node_children() == self.i().get_Node_children());
                assert(b.get_Node_children().map[k] == self.i().get_Node_children().map[k]);

                assert(self.extend_buffer_seq(buffers).get_Node_children() == a.get_Node_children());
                assert(self.extend_buffer_seq(buffers).get_Node_children() == self.get_Node_children());
                assert(a.get_Node_children() == self.get_Node_children());
                self.i_children_seq_same(a, 0);
            }
        }
        assert(a.i().get_Node_children().map =~= b.get_Node_children().map);
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
}

impl Path{
    pub open spec fn routing(self) -> Seq<Set<Key>>
        recommends self.valid()
        decreases self.depth
    {
        if self.depth == 0 {
            seq![]
        } else {
            let pivots = self.node.get_Node_pivots();
            let keys = pivots.pivot_range_keyset(pivots.route(self.key));
            seq![keys] + self.subpath().routing() 
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
        assert(self.subpath().i().routing =~= self.i().subpath().routing);
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
        self.substitute_preserves_wf(replacement);

        replacement.i_wf();
        PivotTable::route_lemma_auto();

        if 0 < self.depth {
            self.substitute(replacement).i_children_lemma();
            assert(self.substitute(replacement).i_children().wf());

            self.i().substitute_preserves_wf(replacement.i());
            assert(self.i().replaced_children(replacement.i()).wf());
            self.subpath().substitute_refines(replacement);

            self.subpath_commutes_with_i();
            self.node.i_children_lemma();
            assert(self.substitute(replacement).i().get_Node_children().map 
                =~= self.i().substitute(replacement.i()).get_Node_children().map
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

// returns left and right keys for a split
pub open spec fn split_keys(path: Path, request: SplitRequest) -> (Set<Key>, Set<Key>)
    recommends path.valid(), path.target().can_split_parent(request)
{
    let child_idx = request.get_child_idx();
    let child_domain = path.target().child_domain(child_idx);

    let split_element = path.target().split_element(request);
    let left_keys = Set::new(|k| child_domain.contains(k) && Element::lt(to_element(k), split_element));
    let right_keys = Set::new(|k| child_domain.contains(k) && !left_keys.contains(k));

    (left_keys, right_keys)
}

pub proof fn split_keys_agrees_with_domains(path: Path, request: SplitRequest)
    requires path.valid(), path.target().can_split_parent(request)
    ensures ({
        let child_domain = path.target().child_domain(request.get_child_idx());
        let split_element = path.target().split_element(request);
        let left_domain = Domain::Domain{start: child_domain.get_Domain_start(), end: split_element};
        let right_domain = Domain::Domain{start: split_element, end: child_domain.get_Domain_end()};
        &&& left_domain.key_set() == split_keys(path, request).0
        &&& right_domain.key_set() == split_keys(path, request).1
    })
{
    let child_domain = path.target().child_domain(request.get_child_idx());
    let split_element = path.target().split_element(request);
    let left_domain = Domain::Domain{start: child_domain.get_Domain_start(), end: split_element};
    let right_domain = Domain::Domain{start: split_element, end: child_domain.get_Domain_end()};
    let (left_keys, right_keys) = split_keys(path, request);

    assert(Element::lt(split_element, child_domain.get_Domain_end())); // trigger
    assert forall |k:Key| #[trigger] left_keys.contains(k) <==> left_domain.contains(k)
    by {
        if left_domain.contains(k) {
            assert(left_domain.get_Domain_start() == child_domain.get_Domain_start());
            assert(child_domain.contains(k));
            assert(left_keys.contains(k));
        }
    }
    assert(left_keys =~= left_domain.key_set());

    if request.is_SplitIndex() {
        assert(Element::lt(child_domain.get_Domain_start(), split_element));
    }
    assert(Element::lte(child_domain.get_Domain_start(), split_element));

    assert forall |k:Key| #[trigger] right_keys.contains(k) <==> right_domain.contains(k)
    by {
        if right_domain.contains(k) {
            assert(!left_keys.contains(k));
            assert(child_domain.contains(k));
            assert(right_keys.contains(k));
        }
    }
    assert(right_keys =~= right_domain.key_set());
}

pub proof fn split_commutes_with_i_left(path: Path, request: SplitRequest, key: Key)
    requires path.valid(), path.target().can_split_parent(request),
        path.target().my_domain().contains(key), split_keys(path, request).0.contains(key)
    ensures path.target().i().split(split_keys(path, request).0, split_keys(path, request).1).child(key)
        == path.target().split_parent(request).i_children().map[key]
{
    let target = path.target();
    target.split_parent_wf(request);

    let child_idx = request.get_child_idx();
    let (left_keys, _) = split_keys(path, request);
    let split_element = path.target().split_element(request);
    split_keys_agrees_with_domains(path, request);

    target.i_children_lemma();
    target.split_parent(request).i_children_lemma();

    PivotTable::route_lemma_auto();
    PivotTable::route_is_lemma_auto();
    target.split_parent(request).get_Node_pivots().route_is_lemma(key, child_idx as int);

    let a = target.child(key).i().filter_buffers_and_children(left_keys);
    if request.is_SplitLeaf() {
        let b = target.child(key).split_leaf(to_key(split_element)).0;
        assert forall |k| #[trigger] a.get_Node_children().map[k] == b.i().get_Node_children().map[k] by {}
        assert(a.get_Node_children().map =~= b.i().get_Node_children().map);
    } else {
        let child_pivot_idx = request.get_SplitIndex_child_pivot_idx();
        let b = target.child(key).split_index(child_pivot_idx).0;
        b.i_children_lemma();
        target.child(key).i_children_lemma();

        // assert forall |k| true
        // implies #[trigger] a.get_Node_children().map[k] == b.i().get_Node_children().map[k]
        // by {
        //     if left_keys.contains(k) {
        //         let r = b.get_Node_pivots().route(k);
        //         target.child(key).get_Node_pivots().route_is_lemma(k, r);
        //     }
        // }
        assert(a.get_Node_children().map =~= b.i().get_Node_children().map);
    }
}

pub proof fn split_commutes_with_i_right(path: Path, request: SplitRequest, key: Key)
    requires path.valid(), path.target().can_split_parent(request),
        path.target().my_domain().contains(key), split_keys(path, request).1.contains(key)
    ensures path.target().i().split(split_keys(path, request).0, split_keys(path, request).1).child(key)
        == path.target().split_parent(request).i_children().map[key]
{
    let target = path.target();
    target.split_parent_wf(request);

    let child_idx = request.get_child_idx();
    let (_, right_keys) = split_keys(path, request);
    let split_element = path.target().split_element(request);
    split_keys_agrees_with_domains(path, request);

    target.i_children_lemma();
    target.split_parent(request).i_children_lemma();

    PivotTable::route_lemma_auto();
    PivotTable::route_is_lemma_auto();
    target.split_parent(request).get_Node_pivots().route_is_lemma(key, child_idx as int + 1);

    let a = target.child(key).i().filter_buffers_and_children(right_keys);
    if request.is_SplitLeaf() {
        let b = target.child(key).split_leaf(to_key(split_element)).1;
        assert forall |k| #[trigger] a.get_Node_children().map[k] == b.i().get_Node_children().map[k] by {}
        assert(a.get_Node_children().map =~= b.i().get_Node_children().map);
    } else {
        let child_pivot_idx = request.get_SplitIndex_child_pivot_idx();
        let b = target.child(key).split_index(child_pivot_idx).1;
        b.i_children_lemma();
        target.child(key).i_children_lemma();

        assert forall |k| #[trigger] a.get_Node_children().map[k] == b.i().get_Node_children().map[k]
        by {
            if right_keys.contains(k) {
                let r = b.get_Node_pivots().route(k);
                target.child(key).get_Node_pivots().route_is_lemma(k, r + child_pivot_idx);
            }
        }
        assert(a.get_Node_children().map =~= b.i().get_Node_children().map);
    }
}

pub proof fn split_commutes_with_i_nonsplit(path: Path, request: SplitRequest, key: Key)
    requires path.valid(), path.target().can_split_parent(request),
        path.target().my_domain().contains(key), 
        !split_keys(path, request).0.contains(key),
        !split_keys(path, request).1.contains(key)
    ensures path.target().i().split(split_keys(path, request).0, split_keys(path, request).1).child(key)
        == path.target().split_parent(request).i_children().map[key]
{
    let target = path.target();
    let new_target = target.split_parent(request);
    target.split_parent_wf(request);

    let child_idx = request.get_child_idx();
    let r = target.get_Node_pivots().route(key);
    PivotTable::route_lemma_auto();

    if r < child_idx {
        new_target.get_Node_pivots().route_is_lemma(key, r);
    } else {
        new_target.get_Node_pivots().route_is_lemma(key, r+1);
    }

    target.i_children_lemma();
    new_target.i_children_lemma();
    assert(new_target.child(key) == target.child(key));
}

pub proof fn split_commutes_with_i(path: Path, request: SplitRequest)
    requires path.valid(), path.target().can_split_parent(request)
    ensures path.target().i().split(split_keys(path, request).0, split_keys(path, request).1)
        == path.target().split_parent(request).i()
{
    let target = path.target();
    let new_target = target.split_parent(request);
    target.split_parent_wf(request);

    let (left_keys, right_keys) = split_keys(path, request);
    assert forall |k: Key| true 
    implies (#[trigger] target.i().split(left_keys, right_keys).get_Node_children().map[k])
        == new_target.i_children().map[k]
    by {
        if target.my_domain().contains(k) {
            if left_keys.contains(k) {
                split_commutes_with_i_left(path, request, k);
            } else if right_keys.contains(k) {
                split_commutes_with_i_right(path, request, k);
            } else {
                split_commutes_with_i_nonsplit(path, request, k);
            }
        }
    }

    assert(target.i().split(left_keys, right_keys).get_Node_children().map 
        =~= target.split_parent(request).i_children().map);
}

pub proof fn flush_commutes_with_i(path: Path, child_idx: nat)
    requires path.valid(), path.target().can_flush(child_idx)
    ensures path.target().i().flush(path.target().child_domain(child_idx).key_set())
        == path.target().flush(child_idx).i()
{
    let target = path.target();
    path.target_wf();
    target.flush_wf(child_idx);

    let child = target.get_Node_children()[child_idx as int];
    let child_domain = target.child_domain(child_idx);
    let moved_buffers = target.get_Node_buffers().apply_filter(child_domain.key_set());

    if child.is_Nil() {
        child.nil_promote_and_extend_commutes_with_i(child_domain, moved_buffers);
    } else {
        child.node_promote_and_extend_commutes_with_i(child_domain, moved_buffers);
    }

    PivotTable::route_lemma_auto();
    PivotTable::route_is_lemma_auto();
    target.i_children_lemma();
    target.flush(child_idx).i_children_lemma();

    assert(target.flush(child_idx).i().get_Node_children().map 
        =~=target.i().flush(child_domain.key_set()).get_Node_children().map);
}

pub proof fn compact_commutes_with_i(path: Path, compacted_buffers: BufferSeq)
    requires path.valid(), path.target().is_Node(),
        path.target().get_Node_buffers().i() == compacted_buffers.i()
    ensures path.target().i().compact(compacted_buffers)
        == path.target().compact(compacted_buffers).i()
{
    let target = path.target();
    path.target_wf();

    assert forall |k| true
    implies #[trigger] target.compact(compacted_buffers).i().get_Node_children().map[k] 
        == target.i().compact(compacted_buffers).get_Node_children().map[k]
    by {
        if target.my_domain().contains(k) {
            target.i_children_lemma();
            target.compact(compacted_buffers).i_children_lemma();
        }
    }

    assert(target.compact(compacted_buffers).i().get_Node_children().map =~= 
        target.i().compact(compacted_buffers).get_Node_children().map);
}

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

    pub proof fn freeze_as_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::freeze_as(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::freeze_as()));
    }

    pub proof fn internal_flush_memtable_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::internal_flush_memtable(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        assert(post.root.wf());

        let a = self.root.push_memtable(self.memtable).value.i();
        let b = self.root.i().push_memtable(self.memtable).value;

        BetreeNode::empty_root_refines();
        let equiv_children_node = if self.root.is_Node() { self.root } else { BetreeNode::empty_root(total_domain()) };
        equiv_children_node.i_children_seq_same(self.root.push_memtable(self.memtable).value, 0);

        assert(a.get_Node_buffers() =~= b.get_Node_buffers());
        assert(a.get_Node_children().map =~= b.get_Node_children().map);

        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_flush_memtable()));
    }

    pub proof fn internal_grow_refines(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::internal_grow(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        post.root.i_wf();
        PivotTable::route_lemma_auto();
        post.root.i_children_lemma();
        assert(post.i().root.get_Node_children().map =~= PagedBetree_v::constant_child_map(self.root.i()).map);
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_grow()));
    }

    pub proof fn internal_split_refines(self, post: Self, lbl: PivotBetree::Label, path: Path, request: SplitRequest)
        requires self.inv(), PivotBetree::State::internal_split(self, post, lbl, path, request)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        path.target().i_wf();
        path.target().split_parent_wf(request);
        path.substitute_refines(path.target().split_parent(request));

        post.root.i_wf();
        path.i_valid();
        path.target_commutes_with_i();
        split_commutes_with_i(path, request);

        let (left_keys, right_keys) = split_keys(path, request);
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_split(path.i(), left_keys, right_keys)));
    }

    pub proof fn internal_flush_refines(self, post: Self, lbl: PivotBetree::Label, path: Path, child_idx: nat)
        requires self.inv(), PivotBetree::State::internal_flush(self, post, lbl, path, child_idx)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        path.target_wf();
        path.target().flush_wf(child_idx);
        path.substitute_refines(path.target().flush(child_idx));

        post.root.i_wf();
        path.i_valid();
        path.target_commutes_with_i();

        flush_commutes_with_i(path, child_idx);
        let flushed_keys = path.target().child_domain(child_idx).key_set();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_flush(path.i(), flushed_keys)));
    }

    pub proof fn internal_compact_refines(self, post: Self, lbl: PivotBetree::Label, path: Path, compacted_buffers: BufferSeq)
        requires self.inv(), PivotBetree::State::internal_compact(self, post, lbl, path, compacted_buffers)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        path.target_wf();
        path.substitute_refines(path.target().compact(compacted_buffers));

        post.root.i_wf();
        path.i_valid();
        path.target_commutes_with_i();

        compact_commutes_with_i(path, compacted_buffers);
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_compact(path.i(), compacted_buffers)));
    }

    pub proof fn internal_noop_noop(self, post: Self, lbl: PivotBetree::Label)
        requires self.inv(), PivotBetree::State::internal_noop(self, post, lbl)
        ensures post.inv(), PagedBetree::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        self.root.i_wf();
        post.root.i_wf();
        assert(PagedBetree::State::next_by(self.i(), post.i(), lbl.i(), PagedBetree::Step::internal_noop()));
    }

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
            PivotBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
            PivotBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_refines(post, lbl); }
            PivotBetree::Step::internal_grow() => { self.internal_grow_refines(post, lbl); }
            PivotBetree::Step::internal_split(path, split_request) => { self.internal_split_refines(post, lbl, path, split_request); }
            PivotBetree::Step::internal_flush(path, child_idx) => { self.internal_flush_refines(post, lbl, path, child_idx); }
            PivotBetree::Step::internal_compact(path, compacted_buffers) => { self.internal_compact_refines(post, lbl, path, compacted_buffers); }
            PivotBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
            _ => { assert(false); } 
        }
    }
} // end impl PivotBetree::State

}//verus
