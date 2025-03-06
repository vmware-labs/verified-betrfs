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
use crate::betree::LinkedBetree_v::LinkedBetreeVars;
use crate::allocation_layer::LikesBetree_v::*;

verus! {

impl LikesBetree::Label {
    pub open spec(checked) fn i(self) -> LinkedBetreeVars::Label
    {
        self->linked_lbl
    }
} // end impl LikesBetree::Label

impl LikesBetree::State {
    pub open spec(checked) fn i(self) -> LinkedBetreeVars::State<SimpleBuffer>
    {
        self.betree
    }

    proof fn init_refines(self, v: LinkedBetreeVars::State<SimpleBuffer>) 
        requires LikesBetree::State::initialize(self, v)
        ensures LinkedBetreeVars::State::initialize(self.i(), v)
    {
    }

    proof fn next_refines(pre: Self, post: Self, lbl: LikesBetree::Label) -> (istep: LinkedBetreeVars::Step<SimpleBuffer>)
        requires 
        pre.inv(),
            post.inv(),
            LikesBetree::State::next(pre, post, lbl),
        ensures
            pre.i().strong_step(istep),
            LinkedBetreeVars::State::next_by(pre.i(), post.i(), lbl.i(), istep)
    {
        reveal(LikesBetree::State::next);
        reveal(LikesBetree::State::next_by);
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);

        match choose |step| LikesBetree::State::next_by(pre, post, lbl, step) {
            LikesBetree::Step::likes_noop(new_betree) => { 
                return choose |istep| LinkedBetreeVars::State::next_by(pre.i(), post.i(), lbl.i(), istep);
            }
            LikesBetree::Step::internal_flush_memtable(new_betree, new_addrs) => {
                return Self::internal_flush_memtable_satisfies_strong_step(pre, post, lbl, new_betree, new_addrs);
            }
            LikesBetree::Step::internal_grow(new_betree, new_root_addr) => {
                return LinkedBetreeVars::Step::internal_grow(new_root_addr);
            }
            LikesBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs) => {
                return Self::internal_split_satisfies_strong_step(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs);
            }
            LikesBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs) => {
                return Self::internal_flush_satisfies_strong_step(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
            }
            LikesBetree::Step::internal_compact(new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs) => {
                return Self::internal_compact_satisfies_strong_step(pre, post, lbl, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs);
            }
            LikesBetree::Step::internal_buffer_noop(new_betree) => {
                return LinkedBetreeVars::Step::internal_buffer_noop(new_betree.linked);
            }
            LikesBetree::Step::internal_noop() => {
                return LinkedBetreeVars::Step::internal_noop();
            }
            _ => { assert(false); }
        }
        return arbitrary();
    }
} // end impl LikesBetree::State

}//verus
