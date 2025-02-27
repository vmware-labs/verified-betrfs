// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::map::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::{LinkedBetreeVars, TwoAddrs};
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

impl AllocationBetree::State {
    pub open spec(checked) fn i(self) -> LikesBetree::State
    {
        let (betree_likes, buffer_likes) = self.betree.linked.transitive_likes();
        LikesBetree::State{
            betree: self.betree,
            betree_likes,
            buffer_likes,
        }
    }

    // pub open spec fn inv(self) -> bool
    // {
    //     let (betree_likes, buffer_likes) = self.betree.linked.transitive_likes();

    //     &&& self.betree.linked.acyclic() // NOTE: relaxing from inv to acyclic, might not work
    //     &&& self.betree_aus == to_au_likes(betree_likes)
    //     &&& self.buffer_aus == to_au_likes(buffer_likes)

    //     // read only refs are not garbage collected
    //     // this might not be needed right now because we are not building anything at this layer
    //     // &&& forall |input| #[trigger] self.compactors.contains(input) ==> self.betree.linked.buffer_dv.valid_buffers(input.input_buffers)
    // }

    proof fn init_refines(self, v: LinkedBetreeVars::State<SimpleBuffer>) 
        requires AllocationBetree::State::initialize(self, v)
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
        let pushed = pre.betree.linked.push_memtable(new_betree.memtable.buffer, new_addrs);

        reveal(LikesBetree::State::next_by);

        assume(post.i().betree_likes.dom() <= restrict_domain_au(pushed.dv.entries, post.betree_aus.dom()));
        assume(post.i().buffer_likes.dom() <= restrict_domain_au(pushed.buffer_dv.entries, post.buffer_aus.dom()));

        assert(LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            LikesBetree::Step::internal_flush_memtable(new_betree, new_addrs)));
    }

//     proof fn next_refines(pre: Self, post: Self, lbl: AllocationBetree::Label) 
//         requires 
//             pre.inv(),
//             post.inv(),
//             AllocationBetree::State::next(pre, post, lbl),
//         ensures
//             pre.i().strong_step(istep),
//             LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), istep)
//     {
//         reveal(AllocationBetree::State::next);
//         reveal(AllocationBetree::State::next_by);
//         reveal(LikesBetree::State::next);
//         reveal(LikesBetree::State::next_by);

//         match choose |step| AllocationBetree::State::next_by(pre, post, lbl, step) {
//             AllocationBetree::Step::likes_noop(new_betree) => { 
//                 return choose |istep| LikesBetree::State::next_by(pre.i(), post.i(), lbl.i(), istep);
//             }
//             AllocationBetree::Step::internal_flush_memtable(new_betree, new_addrs) => {
//                 return Self::internal_flush_memtable_satisfies_strong_step(pre, post, lbl, new_betree, new_addrs);
//             }
//             AllocationBetree::Step::internal_grow(new_betree, new_root_addr) => {
//                 return LikesBetree::Step::internal_grow(new_root_addr);
//             }
//             AllocationBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs) => {
//                 return Self::internal_split_satisfies_strong_step(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs);
//             }
//             AllocationBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs) => {
//                 return Self::internal_flush_satisfies_strong_step(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
//             }
//             AllocationBetree::Step::internal_compact(new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs) => {
//                 return Self::internal_compact_satisfies_strong_step(pre, post, lbl, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
//             }
//             AllocationBetree::Step::internal_noop() => {
//                 return LikesBetree::Step::internal_noop();
//             }
//             _ => { assert(false); }
//         }
//         return arbitrary();
//     }
} // end impl AllocationBetree::State

}//verus
