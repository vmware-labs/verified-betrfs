// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::{map::*, seq_lib::*, set_lib::*, multiset::*};

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::*;
use crate::allocation_layer::Likes_v::*;
use crate::allocation_layer::LikesBetree_v::*;
use crate::allocation_layer::AllocationBetree_v::*;

verus! {

impl AllocationBetree::Label {
    pub open spec(checked) fn i(self) -> LikesBetree::Label
    {
        LikesBetree::Label::Label{linked_lbl: self->linked_lbl}
    }
} // end impl AllocationBetree::Label

impl<T: Buffer> LinkedBetreeVars::State<T> {
    pub proof fn internal_flush_memtable_aus_ensures(self, new_betree: LinkedBetreeVars::State<T>, new_buffer: T, new_addrs: TwoAddrs)
    requires
        self.inv(),
        LinkedBetreeVars::State::internal_flush_memtable(self, new_betree, 
            LinkedBetreeVars::Label::Internal{}, new_buffer, new_betree.linked, new_addrs),
        self.linked.is_fresh(new_addrs.repr()),
    ensures ({
        let pushed = self.linked.push_memtable(new_buffer, new_addrs);
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let (pushed_betree_likes, pushed_buffer_likes) = pushed.transitive_likes();
        let (post_betree_aus, post_buffer_aus) = AllocationBetree::State::flush_memtable_au_likes(
                self, new_betree, new_addrs, to_au_likes(betree_likes), to_au_likes(buffer_likes));

        &&& pushed.inv()
        &&& post_betree_aus == to_au_likes(pushed_betree_likes)
        &&& post_buffer_aus == to_au_likes(pushed_buffer_likes)
    })
    {
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let pushed = self.linked.push_memtable(new_buffer, new_addrs);
        let _ = self.linked.push_memtable_new_ranking(new_buffer, new_addrs, self.linked.the_ranking());
        assert( pushed.acyclic());
    
        let (pushed_betree_likes, pushed_buffer_likes) = pushed.transitive_likes();
        let discard_betree = self.linked.root_likes();
        let add_betree = new_betree.linked.root_likes();

        LikesBetree::State::push_memtable_likes_ensures(self, new_betree, new_buffer, new_addrs);
        assert(pushed_betree_likes == betree_likes.sub(discard_betree).add(add_betree));
        assert(pushed_buffer_likes == buffer_likes.insert(new_addrs.addr2));

        to_au_likes_commutative_over_sub(betree_likes, discard_betree);
        to_au_likes_commutative_over_add(betree_likes.sub(discard_betree), add_betree);
        assert(to_au_likes(pushed_betree_likes) == to_au_likes(betree_likes).sub(to_au_likes(discard_betree)).add(to_au_likes(add_betree)));
        
        to_au_likes_commutative_over_add(buffer_likes, Multiset::singleton(new_addrs.addr2));
        to_au_likes_singleton(new_addrs.addr2);
        assert(to_au_likes(pushed_buffer_likes) == to_au_likes(buffer_likes).insert(new_addrs.addr2.au));

        self.linked.push_memtable_ensures(new_buffer, new_addrs);
    }

    pub proof fn internal_grow_aus_ensures(self, new_betree: LinkedBetreeVars::State<T>, new_root_addr: Address)
    requires
        self.inv(),
        LinkedBetreeVars::State::internal_grow(self, new_betree, 
            LinkedBetreeVars::Label::Internal{}, new_root_addr),
        self.linked.is_fresh(set!{new_root_addr}),
    ensures ({
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let (post_betree_likes, post_buffer_likes) = new_betree.linked.transitive_likes();

        &&& new_betree.inv()
        &&& to_au_likes(post_betree_likes) == to_au_likes(betree_likes).insert(new_root_addr.au)
        &&& post_buffer_likes == buffer_likes
    })
    {
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let (post_betree_likes, post_buffer_likes) = new_betree.linked.transitive_likes();

        LikesBetree::State::grow_likes_ensures(self, new_betree, new_root_addr);
        assert(post_betree_likes == betree_likes.insert(new_root_addr));
        to_au_likes_singleton(new_root_addr);
        to_au_likes_commutative_over_add(betree_likes, Multiset::singleton(new_root_addr));

        LinkedBetreeVars::State::internal_grow_inductive(self, new_betree, 
            LinkedBetreeVars::Label::Internal{}, new_root_addr);
        assert(new_betree.linked.valid_buffer_dv());
    }

    pub proof fn internal_split_aus_ensures(self, new_betree: LinkedBetreeVars::State<T>, 
        path: Path<T>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs)
    requires
        self.inv(),
        LinkedBetreeVars::State::internal_split(self, new_betree, LinkedBetreeVars::Label::Internal{}, 
            new_betree.linked, path, request, new_addrs, path_addrs),
        self.linked.is_fresh(new_addrs.repr()),
        self.linked.is_fresh(path_addrs.to_set()),
    ensures ({
        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let (splitted_betree_likes, splitted_buffer_likes) = splitted.transitive_likes();
        let (post_betree_aus, post_buffer_aus) = AllocationBetree::State::internal_split_au_likes(
                path, request, new_addrs, path_addrs, to_au_likes(betree_likes), to_au_likes(buffer_likes));

        &&& splitted.inv()
        &&& post_betree_aus == to_au_likes(splitted_betree_likes)
        &&& post_buffer_aus == to_au_likes(splitted_buffer_likes)
    })
    {
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        LikesBetree::State::post_split_likes_ensures(self, new_betree, path, request, new_addrs, path_addrs);

        let (splitted_betree_likes, splitted_buffer_likes) = splitted.transitive_likes();
        to_au_likes_commutative_over_sub(betree_likes, split_discard_betree(path, request));
        to_au_likes_commutative_over_add(betree_likes.sub(split_discard_betree(path, request)), add_betree_likes(new_addrs, path_addrs));
        to_au_likes_commutative_over_add(buffer_likes, split_add_buffers(path, request));
        self.post_split_ensures(path, request, new_addrs, path_addrs);
    }

    pub proof fn internal_flush_aus_ensures(self, new_betree: LinkedBetreeVars::State<T>, 
        path: Path<T>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
    requires
        self.inv(),
        LinkedBetreeVars::State::internal_flush(self, new_betree, LinkedBetreeVars::Label::Internal{}, 
            new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs),
        self.linked.is_fresh(new_addrs.repr()),
        self.linked.is_fresh(path_addrs.to_set()),
    ensures ({
        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let (flushed_betree_likes, flushed_buffer_likes) = flushed.transitive_likes();
        let (post_betree_aus, post_buffer_aus) = AllocationBetree::State::internal_flush_au_likes(
                path, child_idx, buffer_gc, new_addrs, path_addrs, to_au_likes(betree_likes), to_au_likes(buffer_likes));

        &&& flushed.inv()
        &&& post_betree_aus == to_au_likes(flushed_betree_likes)
        &&& post_buffer_aus == to_au_likes(flushed_buffer_likes)
    })
    {
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        LikesBetree::State::post_flush_likes_ensures(self, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);

        let (flushed_betree_likes, flushed_buffer_likes) = flushed.transitive_likes();
        to_au_likes_commutative_over_sub(betree_likes, flush_discard_betree(path, child_idx));
        to_au_likes_commutative_over_add(betree_likes.sub(flush_discard_betree(path, child_idx)), add_betree_likes(new_addrs, path_addrs));
        to_au_likes_commutative_over_sub(buffer_likes, flush_discard_buffers(path, buffer_gc));
        to_au_likes_commutative_over_add(buffer_likes.sub(flush_discard_buffers(path, buffer_gc)), flush_add_buffers(path, child_idx));
        self.post_flush_ensures(path, child_idx, buffer_gc, new_addrs, path_addrs);
    }

    pub proof fn internal_compact_complete_aus_ensures(self, new_betree: LinkedBetreeVars::State<T>,
        path: Path<T>, start: nat, end: nat, compacted_buffer: T, new_addrs: TwoAddrs, path_addrs: PathAddrs)
    requires
        self.inv(),
        LinkedBetreeVars::State::internal_compact(self, new_betree, LinkedBetreeVars::Label::Internal{}, 
            new_betree.linked, path, start ,end, compacted_buffer, new_addrs, path_addrs),
        self.linked.is_fresh(new_addrs.repr()),
        self.linked.is_fresh(path_addrs.to_set()),
    ensures ({
        let compacted = LinkedBetreeVars::State::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs);
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let (compacted_betree_likes, compacted_buffer_likes) = compacted.transitive_likes();
        let (post_betree_aus, post_buffer_aus) = AllocationBetree::State::internal_compact_complete_au_likes(
                path, start, end, new_addrs, path_addrs, to_au_likes(betree_likes), to_au_likes(buffer_likes));

        &&& compacted.inv()
        &&& post_betree_aus == to_au_likes(compacted_betree_likes)
        &&& post_buffer_aus == to_au_likes(compacted_buffer_likes)
    })
    {
        let (betree_likes, buffer_likes) = self.linked.transitive_likes();
        let compacted = LinkedBetreeVars::State::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs);
        LikesBetree::State::post_compact_likes_ensures(self, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);

        let (compacted_betree_likes, compacted_buffer_likes) = compacted.transitive_likes();
        to_au_likes_commutative_over_sub(betree_likes, compact_discard_betree(path));
        to_au_likes_commutative_over_add(betree_likes.sub(compact_discard_betree(path)), compact_add_betree(new_addrs, path_addrs));
        to_au_likes_commutative_over_sub(buffer_likes, compact_discard_buffers(path, start, end));
        to_au_likes_commutative_over_add(buffer_likes.sub(compact_discard_buffers(path, start, end)), compact_add_buffers(new_addrs));
        self.post_compact_ensures(path, start, end, compacted_buffer, new_addrs, path_addrs);
    }
}

impl AllocationBetree::State {    
    pub open spec(checked) fn inv(self) -> bool {
        let (betree_likes, buffer_likes) = self.betree.linked.transitive_likes();

        &&& self.betree.inv()
        &&& self.betree_aus == to_au_likes(betree_likes)
        &&& self.buffer_aus == to_au_likes(buffer_likes)
    }
    
    pub open spec(checked) fn i(self) -> LikesBetree::State
    {
        let (betree_likes, buffer_likes) = self.betree.linked.transitive_likes();
        LikesBetree::State{
            betree: self.betree,
            betree_likes,
            buffer_likes,
        }
    }

    proof fn init_inv_refines(self, v: LinkedBetreeVars::State<SimpleBuffer>) 
        requires AllocationBetree::State::initialize(self, v), 
        ensures self.inv(), LikesBetree::State::initialize(self.i(), v), 
    {
    }

    proof fn au_likes_noop_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>)
    requires 
        pre.inv(),
        AllocationBetree::State::au_likes_noop(pre, post, lbl, new_betree),
    ensures
        post.inv(),
        LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::likes_noop(new_betree))
    {
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
        reveal(LikesBetree::State::next_by);
    }

    proof fn internal_flush_memtable_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
        new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs)
    requires 
        pre.inv(), 
        AllocationBetree::State::internal_flush_memtable(pre, post, lbl, new_betree, new_addrs),
    ensures
        post.inv(),
        LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
        LikesBetree::Step::internal_flush_memtable(new_betree, new_addrs))
    {
        reveal(LikesBetree::State::next_by);

        let buffer = pre.betree.memtable.buffer;
        let pushed = pre.betree.linked.push_memtable(buffer, new_addrs);
        pre.betree.internal_flush_memtable_aus_ensures(new_betree, buffer, new_addrs);
        pushed.valid_view_ensures(new_betree.linked);

        let (pushed_betree_likes, pushed_buffer_likes) = pushed.transitive_likes();
        LikesBetree::State::push_memtable_likes_ensures(pre.betree, new_betree, buffer, new_addrs);
        pushed.valid_view_implies_same_transitive_likes(post.betree.linked);

        pushed.tree_likes_domain(pushed.the_ranking());
        pushed.buffer_likes_domain(pushed_betree_likes);
        restrict_domain_au_ensures(pushed_buffer_likes, pushed.buffer_dv.entries);
        assert(new_betree.linked.valid_buffer_dv());
    }

    proof fn internal_grow_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
        new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address)
    requires 
        pre.inv(), 
        AllocationBetree::State::internal_grow(pre, post, lbl, new_betree, new_root_addr),
    ensures
        post.inv(),
        LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_grow(new_betree, new_root_addr))
    {
        reveal(LikesBetree::State::next_by);
        pre.betree.internal_grow_aus_ensures(new_betree, new_root_addr);
        LikesBetree::State::grow_likes_ensures(pre.betree, new_betree, new_root_addr);
    }

    proof fn internal_split_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
        new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        AllocationBetree::State::internal_split(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs),
    ensures
        post.inv(),
        LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            LikesBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs))
    {
        reveal(LikesBetree::State::next_by);

        let (betree_likes, buffer_likes) = pre.betree.linked.transitive_likes();
        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);

        pre.betree.internal_split_aus_ensures(new_betree, path, request, new_addrs, path_addrs);
        LikesBetree::State::post_split_likes_ensures(pre.betree, new_betree, path, request, new_addrs, path_addrs);

        let (splitted_betree_likes, splitted_buffer_likes) = splitted.transitive_likes();
        splitted.valid_view_ensures(new_betree.linked);
        splitted.valid_view_implies_same_transitive_likes(post.betree.linked);

        splitted.tree_likes_domain(splitted.the_ranking());
        splitted.buffer_likes_domain(splitted_betree_likes);
        restrict_domain_au_ensures(splitted_buffer_likes, splitted.buffer_dv.entries);
        assert(new_betree.linked.valid_buffer_dv());
    }

    proof fn internal_flush_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
        new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        AllocationBetree::State::internal_flush(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs),
    ensures
        post.inv(),
        LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            LikesBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs))
    {
        reveal(LikesBetree::State::next_by);
        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        LikesBetree::State::post_flush_likes_ensures(pre.betree, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);

        pre.betree.internal_flush_aus_ensures(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
        let (flushed_betree_likes, flushed_buffer_likes) = flushed.transitive_likes();

        flushed.valid_view_ensures(new_betree.linked);
        flushed.valid_view_implies_same_transitive_likes(post.betree.linked);

        flushed.tree_likes_domain(flushed.the_ranking());
        flushed.buffer_likes_domain(flushed_betree_likes);
        restrict_domain_au_ensures(flushed_buffer_likes, flushed.buffer_dv.entries);
        assert(new_betree.linked.valid_buffer_dv());
    }

    proof fn internal_compact_complete_inv_refines(pre: Self, post: Self, lbl: AllocationBetree::Label, 
        new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        AllocationBetree::State::internal_compact_complete(pre, post, lbl, new_betree, 
            path, start, end, compacted_buffer, new_addrs, path_addrs),
    ensures
        post.inv(),
        LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            LikesBetree::Step::internal_compact(new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs))
    {
        reveal(LikesBetree::State::next_by);

        let (betree_likes, buffer_likes) = pre.betree.linked.transitive_likes();
        let compacted = LinkedBetreeVars::State::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs);

        pre.betree.internal_compact_complete_aus_ensures(new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
        LikesBetree::State::post_compact_likes_ensures(pre.betree, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
        
        let (compacted_betree_likes, compacted_buffer_likes) = compacted.transitive_likes();
        compacted.valid_view_ensures(new_betree.linked);
        compacted.valid_view_implies_same_transitive_likes(post.betree.linked);

        pre.betree.post_compact_ensures(path, start, end, compacted_buffer, new_addrs, path_addrs);
        compacted.tree_likes_domain(compacted.the_ranking());
        compacted.buffer_likes_domain(compacted_betree_likes);
        restrict_domain_au_ensures(compacted_buffer_likes, compacted.buffer_dv.entries);
        assert(new_betree.linked.valid_buffer_dv());
    }

    proof fn next_refines(pre: Self, post: Self, lbl: AllocationBetree::Label) 
        requires 
            pre.inv(),
            AllocationBetree::State::next(pre, post, lbl),
        ensures
            post.inv(),
            LikesBetree::State::next(pre.i(), post.i(), lbl.i())
    {
        reveal(AllocationBetree::State::next);
        reveal(AllocationBetree::State::next_by);
        reveal(LikesBetree::State::next);
        reveal(LikesBetree::State::next_by);

        match choose |step| AllocationBetree::State::next_by(pre, post, lbl, step) {
            AllocationBetree::Step::au_likes_noop(new_betree) => { 
                Self::au_likes_noop_inv_refines(pre, post, lbl, new_betree);
            }
            AllocationBetree::Step::internal_flush_memtable(new_betree, new_addrs) => {
                Self::internal_flush_memtable_inv_refines(pre, post, lbl, new_betree, new_addrs);
            }
            AllocationBetree::Step::internal_grow(new_betree, new_root_addr) => {
                Self::internal_grow_inv_refines(pre, post, lbl, new_betree, new_root_addr);
            }
            AllocationBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs) => {
                Self::internal_split_inv_refines(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs);
            }
            AllocationBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs) => {
                Self::internal_flush_inv_refines(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
            }
            AllocationBetree::Step::internal_compact_complete(new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs) => {
                Self::internal_compact_complete_inv_refines(pre, post, lbl, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
            }
            AllocationBetree::Step::internal_buffer_noop(new_betree) => {
                pre.betree.linked.valid_view_ensures(new_betree.linked);
                pre.betree.linked.valid_view_implies_same_transitive_likes(new_betree.linked);

                let (betree_likes, buffer_likes) = pre.betree.linked.transitive_likes();

                pre.betree.linked.tree_likes_domain(pre.betree.linked.the_ranking());
                pre.betree.linked.buffer_likes_domain(betree_likes);
                restrict_domain_au_ensures(buffer_likes, pre.betree.linked.buffer_dv.entries);

                assert(post.inv());
                assert(LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_buffer_noop(new_betree)));
            }
            AllocationBetree::Step::internal_noop() => {
                assert(LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), LikesBetree::Step::internal_noop()));
            }
            _ => { assert(false); }
        }
    }
} // end impl AllocationBetree::State

}//verus
