#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::{map::*,multiset::*};
use vstd::math;

use state_machines_macros::state_machine;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;

use crate::betree::Buffer_v::*;
use crate::betree::LinkedBufferSeq_v;
use crate::betree::LinkedBufferSeq_v::BufferSeq;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::*;
use crate::allocation_layer::Likes_v::*;


verus! {
// introduces likes for betree
impl LinkedBetree {
    pub open spec /*XXX (checked)*/ fn children_likes(self, i: nat, ranking: Ranking) -> Likes
        recommends
            self.wf(),
            self.valid_ranking(ranking),
            self.has_root(),
            i <= self.root().children.len()
        decreases
            self.get_rank(ranking),
            self.root().children.len() - i
        when 
            i <= self.root().children.len()
            && (i < self.root().children.len() ==> 
                self.child_at_idx(i).get_rank(ranking) < self.get_rank(ranking))
    {
        if i == self.root().children.len() {
            no_likes()
        } else {
            let child_likes = self.child_at_idx(i).transitive_likes_defn(ranking);
            let more_likes = self.children_likes(i+1, ranking);
            child_likes.add(more_likes)
        }
    }

    pub open spec /*XXX (checked)*/ fn transitive_likes_defn(self, ranking: Ranking) -> Likes
        recommends 
            self.wf(),
            self.valid_ranking(ranking)
        decreases
            self.get_rank(ranking)
    {
        if !self.has_root() { 
            no_likes() 
        } else {
            let root_likes = Multiset::from_set(set![self.root.unwrap()]);
            let buffer_likes =  Multiset::from_set(self.root().buffers.buffers.to_set());      
            let children_likes = self.children_likes(0, ranking);      
            root_likes.add(buffer_likes).add(children_likes)
        }
    }

    pub open spec(checked) fn transitive_likes(self) -> Likes
        recommends self.acyclic()
    {
        self.transitive_likes_defn(self.the_ranking())
    }

    pub open spec(checked) fn restrict_dom(self, keep_addrs: Set<Address>) -> Self
    {
        LinkedBetree{
            root: self.root,
            dv: DiskView{ entries: self.dv.entries.restrict(keep_addrs) },
            buffer_dv: BufferDiskView{ entries: self.buffer_dv.entries.restrict(keep_addrs) },
        }
    }
}

state_machine!{ LikesBetree {
    fields {
        pub betree: LinkedBetreeVars::State,
        // no need to split it up because we are still dealing with buffers
        // buffer ptr represents the entire b+ tree
        pub betree_likes: Likes,
        // // internal refs, track # of times each betree node is referenced by another node
        // // should be 1 for tree, can be more after clone makes it a DAG
        // pub betree_likes: Likes,
        // // outgoing refs, track # of times each buffer is referenced by a betree node
        // pub buffer_likes: Likes,
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.betree.wf()
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool {
        &&& self.betree_likes.dom().disjoint(addrs)
    }

    #[is_variant]
    pub enum Label
    {
        Query{end_lsn: LSN, key: Key, value: Value},
        Put{puts: MsgHistory},
        FreezeAs{stamped_betree: StampedBetree},
        Internal{},   // Local No-op label
    }

    pub open spec fn lbl_i(lbl: Label) -> LinkedBetreeVars::Label {
        match lbl {
            Label::Query{end_lsn, key, value}
                => LinkedBetreeVars::Label::Query{end_lsn, key, value},
            Label::Put{puts}
                => LinkedBetreeVars::Label::Put{puts},
            Label::FreezeAs{stamped_betree}
                => LinkedBetreeVars::Label::FreezeAs{stamped_betree},
            Label::Internal{}
                => LinkedBetreeVars::Label::Internal{},
        }
    }

    transition!{ query(lbl: Label, receipt: QueryReceipt) {
        require lbl is Query;
        require LinkedBetreeVars::State::next(pre.betree, pre.betree, Self::lbl_i(lbl));
    }}

    transition!{ put(lbl: Label, new_betree: LinkedBetreeVars::State) {
        require lbl is Put;
        require LinkedBetreeVars::State::next(pre.betree, new_betree, Self::lbl_i(lbl));
        update betree = new_betree;
    }}

    transition!{ freeze_as(lbl: Label) {
        require lbl is FreezeAs;
        require LinkedBetreeVars::State::next(pre.betree, pre.betree, Self::lbl_i(lbl));
    }}

    transition!{ internal_flush_memtable(lbl: Label, new_addrs: TwoAddrs) {
        require lbl is Internal;
        require new_addrs.no_duplicates();
        require pre.is_fresh(new_addrs.repr());

        let old_root = 
            if !pre.betree.linked.has_root() { no_likes() }
            else { Multiset::empty().insert(pre.betree.linked.root.unwrap()) };
        let new_likes = Multiset::from_set(new_addrs.repr());
        let new_betree_likes = pre.betree_likes.sub(old_root).add(new_likes);
        let updated_linked = pre.betree.linked.push_memtable(pre.betree.memtable, new_addrs);

        update betree = LinkedBetreeVars::State{
            memtable: pre.betree.memtable.drain(),
            linked: updated_linked.restrict_dom(new_betree_likes.dom())
        };
        update betree_likes = new_betree_likes;
    }}

    transition!{ internal_grow(lbl: Label, new_root_addr: Address) {
        require lbl is Internal;
        require pre.is_fresh(Set::empty().insert(new_root_addr));
        let new_betree_likes = pre.betree_likes.insert(new_root_addr);

        update betree = LinkedBetreeVars::State{
            linked: pre.betree.linked.grow(new_root_addr),
            ..pre.betree
        };
        update betree_likes = new_betree_likes;
    }}

    transition!{ internal_split(lbl: Label, path: Path, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        require lbl is Internal;
        require LinkedBetreeVars::State::new_path_wf(path, &new_addrs, path_addrs);
        require path.target().can_split_parent(request);
        require path.linked == pre.betree.linked;
        require pre.is_fresh(new_addrs.repr() + path_addrs.to_set());

        // addrs_on_path covers betree nodes till the parent
        let split_child_addr = path.target().child_at_idx(request.get_child_idx()).root.unwrap();
        let deref_likes = Multiset::from_set(path.addrs_on_path().insert(split_child_addr));

        let new_likes = Multiset::from_set(new_addrs.repr() + path_addrs.to_set());
        let new_betree_likes = pre.betree_likes.sub(deref_likes).add(new_likes);

        // can substitute recommends failure only shows up if we test with an assert false
        let updated_linked = path.substitute(path.target().split_parent(request, new_addrs), path_addrs);

        update betree = LinkedBetreeVars::State{
            linked: updated_linked.restrict_dom(new_betree_likes.dom()),
            ..pre.betree
        };
        update betree_likes = new_betree_likes;
    }}

    transition!{ internal_flush(lbl: Label, path: Path, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require lbl is Internal;
        require LinkedBetreeVars::State::new_path_wf(path, &new_addrs, path_addrs);
        require path.target().can_flush(child_idx, buffer_gc);
        require path.linked == pre.betree.linked;
        require pre.is_fresh(new_addrs.repr() + path_addrs.to_set());

        let target = path.target().root();

        let flush_child_addr = target.children[child_idx as int].unwrap();
        let gced_buffers = Multiset::from_set(target.buffers.slice(0, buffer_gc as int).repr());
        let deref_likes = Multiset::from_set(path.addrs_on_path().insert(flush_child_addr)).add(gced_buffers);

        let active_idx = target.flushed.offsets[child_idx as int] as int;
        let buffers_len = target.buffers.len() as int;
        let flushed_buffers = Multiset::from_set(target.buffers.slice(active_idx, buffers_len).repr());
        let new_likes = Multiset::from_set(new_addrs.repr() + path_addrs.to_set()).add(flushed_buffers);

        let new_betree_likes = pre.betree_likes.sub(deref_likes).add(new_likes);
        let updated_linked = path.substitute(path.target().flush(child_idx, buffer_gc, new_addrs), path_addrs);

        update betree = LinkedBetreeVars::State{
            linked: updated_linked.restrict_dom(new_betree_likes.dom()),
            ..pre.betree
        };
        update betree_likes = new_betree_likes;
    }}

    transition!{ internal_compact(lbl: Label, path: Path, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require lbl is Internal;
        require LinkedBetreeVars::State::new_path_wf(path, &new_addrs, path_addrs);
        require path.target().can_compact(start, end, compacted_buffer);
        require path.linked == pre.betree.linked;
        require pre.is_fresh(new_addrs.repr() + path_addrs.to_set());

        let compacted_buffers = Multiset::from_set(path.target().root().buffers.slice(start as int, end as int).repr());
        let deref_likes = Multiset::from_set(path.addrs_on_path()).add(compacted_buffers);
        let new_likes = Multiset::from_set(new_addrs.repr() + path_addrs.to_set());

        let new_betree_likes = pre.betree_likes.sub(deref_likes).add(new_likes);
        let updated_linked = path.substitute(path.target().compact(start, end, compacted_buffer, new_addrs), path_addrs);

        update betree = LinkedBetreeVars::State{
            linked: updated_linked.restrict_dom(new_betree_likes.dom()),
            ..pre.betree
        };
        update betree_likes = new_betree_likes;
    }}

    transition!{ internal_noop(lbl: Label) {
        require lbl is Internal;
    }}

    init!{ initialize(stamped_betree: StampedBetree) {
        require stamped_betree.value.acyclic();
        init betree = LinkedBetreeVars::State{
            memtable: Memtable::empty_memtable(stamped_betree.seq_end),
            linked: stamped_betree.value,
        };
        init betree_likes = stamped_betree.value.transitive_likes();
    }}
}} // end LikesBetree state machine

} // end verus!
