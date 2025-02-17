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

    proof fn next_refines(self, post: Self, lbl: LikesBetree::Label) -> (istep: LinkedBetreeVars::Step<SimpleBuffer>)
        requires 
            self.inv(),
            post.inv(),
            LikesBetree::State::next(self, post, lbl),
        ensures
            self.i().strong_step(istep),
            LinkedBetreeVars::State::next_by(self.i(), post.i(), lbl.i(), istep)
    {
        assume(false);
        return arbitrary();

        // reveal(LikesBetree::State::next_by);
        // reveal(LinkedBetreeVars::State::next);

        // match step
        // {
        //     LikesBetree::Step::likes_noop(receipt) => {  } 
            // LinkedBetreeVars::Step::put() => 
            //     { self.put_refines(post, lbl); }
            // LinkedBetreeVars::Step::freeze_as() => 
            //     { self.freeze_as_refines(post, lbl); }
            // LinkedBetreeVars::Step::internal_flush_memtable(new_memtable, new_linked, new_addrs) => 
            //     { self.internal_flush_memtable_refines(post, lbl, new_memtable, new_linked, new_addrs); }
            // LinkedBetreeVars::Step::internal_grow(new_root_addr) => 
            //     { self.internal_grow_refines(post, lbl, new_root_addr); }
            // LinkedBetreeVars::Step::internal_split(new_linked, path, split_request, new_addrs, path_addrs) => 
            //     { self.internal_split_refines(post, lbl, new_linked, path, split_request, new_addrs, path_addrs); }
            // LinkedBetreeVars::Step::internal_flush(new_linked, path, child_idx, buffer_gc, new_addrs, path_addrs) => 
            //     { self.internal_flush_refines(post, lbl, new_linked, path, child_idx, buffer_gc, new_addrs, path_addrs); }
            // LinkedBetreeVars::Step::internal_compact(new_linked, path, start, end, compacted_buffer, new_addrs, path_addrs) => 
            //     { self.internal_compact_refines(post, lbl, new_linked, path, start, end, compacted_buffer, new_addrs, path_addrs); }
            // LinkedBetreeVars::Step::internal_noop() => 
            //     { self.internal_noop_noop(post, lbl); }
        //     _ => 
        //         { assume(false); } 
        // }
    }
} // end impl LikesBetree::State

}//verus
