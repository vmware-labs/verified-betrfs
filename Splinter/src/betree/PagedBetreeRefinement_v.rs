// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
// #![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::map::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::AbstractMap_v::*;
use crate::betree::PagedBetree_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::Memtable_v::*;

verus! {
impl BetreeNode {
    pub open spec /*XXX(checked)*/ fn build_query_receipt(self, key: Key) -> QueryReceipt
    recommends
        self.wf(),
    decreases self when self.wf()
    {
        if self is Nil {
            let msg = Message::Define{value: default_value()}; 
            let line = QueryReceiptLine{node: self, result: msg};
            QueryReceipt{key: key, root: self, lines: seq![line]}
        } else {
            let child_receipt = self.child(key).build_query_receipt(key);
        // TODO(jonh) [spec_checked] self.child(key).build_query_receipt_valid(key)
            let msg = self->buffer.query(key);
            let line = QueryReceiptLine{node: self, result: child_receipt.result().merge(msg)};
            QueryReceipt{key: key, root: self, lines: seq![line] + child_receipt.lines}
        }
    }

    proof fn build_query_receipt_valid(self, key: Key)
    requires
        self.wf(),
    ensures
        self.build_query_receipt(key).valid(),
    decreases self
    {
        if self is Node {
            let child_receipt = self.child(key).build_query_receipt(key);
            self.child(key).build_query_receipt_valid(key);

            let msg = self->buffer.query(key);
            let line = QueryReceiptLine{node: self, result: child_receipt.result().merge(msg)};
            let receipt = QueryReceipt{key: key, root: self, lines: seq![line] + child_receipt.lines};

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

    pub open spec /*XXX (checked)*/ fn i_at(self, key: Key) -> Message
        recommends self.wf()
    {
        // TODO(jonh) [spec_checked] self.child(key).build_query_receipt_valid(key)
        self.build_query_receipt(key).result()
    }

    pub open spec(checked) fn i(self) -> TotalKMMap
    {
        TotalKMMap(Map::new(|k: Key| true, |k| self.i_at(k)))
    }

    proof fn memtable_distributes_over_betree(self, memtable: Memtable)
        requires self.wf()
        ensures map_apply(memtable, self.i()) == self.push_memtable(memtable).value.i()
    {
        let map_a = map_apply(memtable, self.i());
        let map_b = self.push_memtable(memtable).value.i();
        assert(map_a =~= map_b);
    }

    proof fn push_empty_memtable_refines(self, memtable: Memtable)
        requires self.wf(), memtable.is_empty()
        ensures i_stamped_betree(Stamped{value: self, seq_end: memtable.seq_end})
            == i_stamped_betree(self.push_memtable(memtable))
    {
        assert(self.i() =~= self.push_memtable(memtable).value.i());
    }

    proof fn merge_buffer_lemma(self, new_buffer: SimpleBuffer, key: Key)
        requires self.wf()
        ensures self.promote().merge_buffer(new_buffer).i_at(key) 
            == self.i_at(key).merge(new_buffer.query(key))
    {
    }

    proof fn filter_buffer_and_children_wf(self, filter: Set<Key>) 
        requires self.wf()
        ensures self.filter_buffer_and_children(filter).wf()
    {
        if self is Node {
            assert(self.filter_buffer_and_children(filter)->children.wf());
        }
    }

    proof fn split_wf(self, left_keys: Set<Key>, right_keys: Set<Key>)
        requires self.wf(), self is Node
        ensures self.split(left_keys, right_keys).wf()
    {
        let child_map = self.split(left_keys, right_keys)->children;

        assert forall |k: Key| (#[trigger] child_map.map[k]).wf()
        by {
            if left_keys.contains(k) {
                self.child(k).filter_buffer_and_children_wf(left_keys);
            } else if right_keys.contains(k) {
                self.child(k).filter_buffer_and_children_wf(right_keys);
            } else {
                self.child(k);
            }
        }

//        assert(total_keys(child_map.map.dom()));
//        assert(child_map.wf());
    }
    
    proof fn apply_filter_equivalence(self, filter: Set<Key>, key: Key)
        requires self.wf(), filter.contains(key)
        ensures self.filter_buffer_and_children(filter).i_at(key) == self.i_at(key)
    {
        let receipt = self.build_query_receipt(key);
        self.build_query_receipt_valid(key);
    }

    proof fn flush_wf(self, down_keys: Set<Key>)
        requires self.wf(), self is Node
        ensures self.flush(down_keys).wf()
    {
        let child_map = self.flush(down_keys)->children;
        assert(self->children.wf());
        assert forall |k: Key| (#[trigger] child_map.map[k]).wf() by { }
    }
} // end impl BetreeNode

pub open spec(checked) fn map_apply(memtable: Memtable, base: TotalKMMap) -> TotalKMMap
{
    TotalKMMap(Map::new(|k: Key| true, |k: Key| base[k].merge(memtable.query(k))))
}

pub open spec(checked) fn i_stamped_betree(stamped: StampedBetree) -> StampedMap
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceipt{
    pub open spec(checked) fn drop_first(self) -> QueryReceipt
    recommends
        self.root.wf(),
        self.root is Node,
        1 < self.lines.len(),
    {
        QueryReceipt{
            key: self.key,
            root: self.root.child(self.key),
            lines: self.lines.subrange(1, self.lines.len() as int)
        }
    }

    proof fn drop_first_valid(self)
        requires self.valid(), 1 < self.lines.len()
        ensures self.drop_first().valid()
    {
        let out = self.drop_first();
        assert(self.child_linked_at(0));
        assert forall |i: int| 0 <= i < out.lines.len()-1
        implies ({
            &&& out.child_linked_at(i)
            &&& out.result_linked_at(i)
        }) by {
            assert(self.child_linked_at(i+1)); // trigger
            assert(self.result_linked_at(i+1)); // trigger
        }
    }

    proof fn equal_receipts(self, other: QueryReceipt)
        requires 
            self.valid(), other.valid(), 
            self.key == other.key, self.root == other.root,
        ensures self.result() == other.result()
        decreases self.lines.len()
    {
        if 1 < self.lines.len() {
            assert(self.result_linked_at(0));
            assert(other.result_linked_at(0));

            self.drop_first_valid();
            other.drop_first_valid();
            self.drop_first().equal_receipts(other.drop_first());
        }
    }
}

impl Path{
    proof fn target_wf(self)
        requires self.valid()
        ensures self.target().wf(), self.target() is Node
        decreases self.routing.len()
    {
        if self.routing.len() > 0 {
            self.subpath().target_wf();
        }
    }

    pub proof fn substitute_preserves_wf(self, replacement: BetreeNode)
        requires self.valid(), replacement.wf(),
        ensures self.substitute(replacement).wf()
        decreases self.routing.len()
    {
        if self.routing.len() > 0 {
            self.subpath().substitute_preserves_wf(replacement);
        }
    }

    proof fn substitute_receipt_equivalence(self, replacement: BetreeNode, key: Key)
        requires self.valid(), replacement.wf(),
            self.substitute(replacement).wf(),
            self.target().i() == replacement.i()
        ensures self.node.i_at(key) == self.substitute(replacement).i_at(key)
        decreases self.routing.len()
    {
        assert(self.target().i_at(key) == self.target().i()[key]); // trigger
//        assert(self.target().i_at(key) == replacement.i_at(key)); // trigger

        if self.routing.len() > 0 {
            if self.routing[0].contains(key) {
                let receipt = self.node.build_query_receipt(key);
                self.node.build_query_receipt_valid(key);
                
                receipt.drop_first_valid();
//                assert(receipt.drop_first().root == self.subpath().node);

                self.subpath().node.build_query_receipt_valid(key);
                self.subpath().node.build_query_receipt(key).equal_receipts(receipt.drop_first());

                self.subpath().substitute(replacement).build_query_receipt_valid(key);
                self.substitute(replacement).build_query_receipt_valid(key);
                self.substitute(replacement).build_query_receipt(key).drop_first_valid();

                self.subpath().substitute(replacement).build_query_receipt(key).equal_receipts(
                    self.substitute(replacement).build_query_receipt(key).drop_first()
                );

                self.subpath().substitute_receipt_equivalence(replacement, key);
            } else {
//                assert(self.node.i_at(key) == self.substitute(replacement).i_at(key));
            }
        }
    }

    proof fn substitute_equivalence(self, replacement: BetreeNode)
        requires self.valid(), replacement.wf(),
            self.target().i() == replacement.i()
        ensures self.substitute(replacement).wf(),
            self.node.i() == self.substitute(replacement).i()
    {
        self.substitute_preserves_wf(replacement);

        assert forall |k: Key| (#[trigger] self.node.i_at(k)) 
            == self.substitute(replacement).i_at(k)
        by {
            self.substitute_receipt_equivalence(replacement, k);
        }

        assert(self.node.i() =~= self.substitute(replacement).i());
    }
}

impl PagedBetree::Label {
    pub open spec(checked) fn i(self) -> AbstractMap::Label
    {
        match self {
            PagedBetree::Label::Query{end_lsn, key, value} => AbstractMap::Label::QueryLabel{end_lsn: end_lsn, key: key, value: value},
            PagedBetree::Label::Put{puts} => AbstractMap::Label::PutLabel{puts: puts},
            PagedBetree::Label::FreezeAs{stamped_betree} => AbstractMap::Label::FreezeAsLabel{stamped_map: i_stamped_betree(stamped_betree)},
            PagedBetree::Label::Internal{} => AbstractMap::Label::InternalLabel{},
        }
    }
} // end impl PagedBetree::Label

proof fn composite_single_put(puts1: MsgHistory, puts2: MsgHistory, stamped_map: StampedMap)
    requires puts1.wf(), puts2.wf(), puts2.len() == 1,
        puts1.can_follow(stamped_map.seq_end),
        puts2.can_follow(puts1.seq_end)
    ensures puts1.concat(puts2).apply_to_stamped_map(stamped_map) 
        == puts2.apply_to_stamped_map(puts1.apply_to_stamped_map(stamped_map))
{
    let last_lsn = (puts2.seq_end - 1) as nat;
    assert_maps_equal!(puts1.msgs, puts1.concat(puts2).discard_recent(last_lsn).msgs);
//    assert(puts1 == puts1.concat(puts2).discard_recent(last_lsn));
    assert(puts2.discard_recent(last_lsn).apply_to_stamped_map(puts1.apply_to_stamped_map(stamped_map))
        == puts1.apply_to_stamped_map(stamped_map));

    puts1.concat(puts2).apply_to_stamped_map_length_lemma(stamped_map);
    puts1.apply_to_stamped_map_length_lemma(stamped_map);
    puts2.apply_to_stamped_map_length_lemma(puts1.apply_to_stamped_map(stamped_map));
}

impl PagedBetree::State {
    pub open spec(checked) fn inv(self) -> bool {
        self.wf()
    }

    pub open spec(checked) fn i(self) -> AbstractMap::State
    {
        AbstractMap::State{stamped_map: i_stamped_betree(self.root.push_memtable(self.memtable))}
    }

    proof fn init_refines(self, stamped_betree: StampedBetree) 
        requires PagedBetree::State::initialize(self, stamped_betree)
        ensures self.inv(), AbstractMap::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        self.root.push_empty_memtable_refines(self.memtable);
    }

    proof fn query_refines(self, post: Self, lbl: PagedBetree::Label, receipt: QueryReceipt)
        requires self.inv(), PagedBetree::State::query(self, post, lbl, receipt)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        let built_receipt = self.root.build_query_receipt(lbl->key);
        self.root.build_query_receipt_valid(lbl->key);
        receipt.equal_receipts(built_receipt);

        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::query()));
    }

    proof fn apply_single_put_is_map_plus_history(self, post: Self, puts: MsgHistory)
        requires self.wf(), post.wf(), puts.wf(), puts.len() == 1,
            puts.seq_start == self.memtable.seq_end,
            post.memtable == self.memtable.apply_puts(puts),
            post.root == self.root
        ensures post.i().stamped_map == MsgHistory::map_plus_history(self.i().stamped_map, puts)
    {
        let KeyedMessage{key, message} = puts.msgs[puts.seq_start];
        let map_a = post.root.push_memtable(post.memtable).value.i();
        self.memtable.apply_puts_end(puts);
        assert(self.memtable.apply_puts(puts.discard_recent(puts.seq_start)) == self.memtable);

        let map_b = puts.apply_to_stamped_map(self.i().stamped_map).value;
        MsgHistory::map_plus_history_lemma(self.i().stamped_map, puts);

        let sub_map_b = puts.discard_recent(puts.seq_start).apply_to_stamped_map(self.i().stamped_map).value;
//        assert(map_b == sub_map_b.insert(key, sub_map_b[key].merge(message)));
    
        assert(map_a.0 =~= map_b.0);
//        assert(post.i().stamped_map.value == map_a);
//        assert(MsgHistory::map_plus_history(self.i().stamped_map, puts).value == map_b);
    }

    proof fn apply_put_is_map_plus_history(self, post: Self, puts: MsgHistory)
        requires self.wf(), post.wf(), puts.wf(),
            puts.seq_start == self.memtable.seq_end,
            post.memtable == self.memtable.apply_puts(puts),
            post.root == self.root
        ensures post.i().stamped_map == MsgHistory::map_plus_history(self.i().stamped_map, puts)
        decreases puts.len()
    {
        if 0 < puts.len() {
            let last = (puts.seq_end-1) as nat;
            let last_put = puts.discard_old(last);
            let short_puts = puts.discard_recent(last);
            let intermediate_post = PagedBetree::State{root: self.root, memtable: self.memtable.apply_puts(short_puts)};

            self.apply_put_is_map_plus_history(intermediate_post, short_puts);
            self.memtable.apply_puts_end(short_puts);
//            assert(last_put.can_follow(intermediate_post.memtable.seq_end));

            self.memtable.apply_puts_additive(short_puts, last_put);
            assert(short_puts.concat(last_put).msgs =~= puts.msgs);
//            assert(post.memtable == intermediate_post.memtable.apply_puts(last_put));

            intermediate_post.apply_single_put_is_map_plus_history(post, last_put);
            composite_single_put(short_puts, last_put, self.i().stamped_map);
        }
    }

    proof fn put_refines(self, post: Self, lbl: PagedBetree::Label)
        requires self.inv(), PagedBetree::State::put(self, post, lbl)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        self.apply_put_is_map_plus_history(post, lbl->puts);
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::put()));
    }

    proof fn freeze_as_refines(self, post: Self, lbl: PagedBetree::Label)
        requires self.inv(), PagedBetree::State::freeze_as(self, post, lbl)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        self.root.push_empty_memtable_refines(self.memtable);
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::freeze_as()));
    }

    proof fn internal_flush_memtable_noop(self, post: Self, lbl: PagedBetree::Label)
        requires self.inv(), PagedBetree::State::internal_flush_memtable(self, post, lbl)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        post.root.push_empty_memtable_refines(post.memtable);
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::internal()));
    }

    proof fn equivalent_roots(self, post: Self)
        requires self.wf(), post.wf(), 
            self.memtable == post.memtable, 
            self.root.i() == post.root.i()
        ensures self.i() == post.i()
    {
        self.root.memtable_distributes_over_betree(self.memtable);
        post.root.memtable_distributes_over_betree(post.memtable);
    }

    proof fn internal_grow_noop(self, post: Self, lbl: PagedBetree::Label)
        requires self.inv(), PagedBetree::State::internal_grow(self, post, lbl)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        assert(post.root.i() =~= self.root.i());
        self.equivalent_roots(post);
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::internal()));
    }

    proof fn internal_split_noop(self, post: Self, lbl: PagedBetree::Label, path: Path, left_keys: Set<Key>, right_keys: Set<Key>)
        requires self.inv(), PagedBetree::State::internal_split(self, post, lbl, path, left_keys, right_keys)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        let target = path.target();
        path.target_wf();

        let top = target.split(left_keys, right_keys);
        target.split_wf(left_keys, right_keys);

        assert forall |k: Key| target.i_at(k) == top.i_at(k)
        by {
            if left_keys.contains(k) {
                target.child(k).apply_filter_equivalence(left_keys, k);
            } else if right_keys.contains(k) {
                target.child(k).apply_filter_equivalence(right_keys, k);
            }
        }

        assert(target.i() =~= top.i());
        path.substitute_equivalence(top);
        self.equivalent_roots(post);
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::internal()));
    }

    proof fn internal_flush_noop(self, post: Self, lbl: PagedBetree::Label, path: Path, down_keys: Set<Key>)
        requires self.inv(), PagedBetree::State::internal_flush(self, post, lbl, path, down_keys)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        let target = path.target();
        path.target_wf();

        let top = target.flush(down_keys);
        target.flush_wf(down_keys);

        let kept_keys = all_keys().difference(down_keys);

        assert forall |k: Key| target.i_at(k) == top.i_at(k)
        by {
            if down_keys.contains(k) {                
                let moved_buffer = target->buffer.apply_filter(down_keys);
                let child = target->children.map[k];
                child.merge_buffer_lemma(moved_buffer, k);
            }
        }
        
        assert(target.i() =~= top.i());
        path.substitute_equivalence(top);
        self.equivalent_roots(post);
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::internal()));
    }

    proof fn internal_noop_noop(self, post: Self, lbl: PagedBetree::Label)
        requires self.inv(), PagedBetree::State::internal_noop(self, post, lbl)
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i())
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);
        assert(AbstractMap::State::next_by(self.i(), post.i(), lbl.i(), AbstractMap::Step::internal()));
    }

    proof fn next_refines(self, post: Self, lbl: PagedBetree::Label)
        requires self.inv(), PagedBetree::State::next(self, post, lbl),
        ensures post.inv(), AbstractMap::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PagedBetree::State::next);
        reveal(PagedBetree::State::next_by);

        match choose |step| PagedBetree::State::next_by(self, post, lbl, step)
        {
            PagedBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
            PagedBetree::Step::put() => { self.put_refines(post, lbl); }
            PagedBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
            PagedBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_noop(post, lbl); }
            PagedBetree::Step::internal_grow() => { self.internal_grow_noop(post, lbl); }
            PagedBetree::Step::internal_split(path, left_keys, right_keys) => { self.internal_split_noop(post, lbl, path, left_keys, right_keys); }
            PagedBetree::Step::internal_flush(path, down_keys) => { self.internal_flush_noop(post, lbl, path, down_keys); }
            PagedBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
            _ => { assert(false); } 
        }
    }
} // end impl PagedBetree::State

}//verus
 
