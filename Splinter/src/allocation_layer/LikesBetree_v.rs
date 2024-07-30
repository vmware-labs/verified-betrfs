// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{prelude::*, seq_lib::*, set_lib::*, map_lib::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::LinkedSeq_v::*;
use crate::betree::BufferDisk_v;
use crate::betree::BufferDisk_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;
use crate::allocation_layer::Likes_v::*;

verus! {

/// Introduces likes to track the life time of disk data structures.
/// There are two disks (same as LinkedBetree): 
/// (1) dv containing BetreeNodes and (2) BufferDisk containing Buffers

impl<T> LinkedSeq<T> {
    pub open spec(checked) fn likes(self) -> Likes
    {
        self.addrs.to_multiset()
    }
}

impl<T> LinkedBetree<T> {
    pub open spec fn children_likes(self, ranking: Ranking, start: nat) -> Likes
        recommends 
            self.has_root(),
            self.valid_ranking(ranking),
            start <= self.root().children.len()
        decreases 
            self.get_rank(ranking), 0nat, self.root().children.len()-start 
            when ({
                &&& start <= self.root().children.len()
                &&& self.root().valid_child_index(start) ==> 
                    self.child_at_idx(start).get_rank(ranking) < self.get_rank(ranking)
            })
    {
        if start == self.root().children.len() {
            no_likes()
        } else {
            let likes = self.child_at_idx(start).transitive_likes_internal(ranking);
            likes.add(self.children_likes(ranking, start+1))
        }
    }

    pub open spec(checked) fn transitive_likes_internal(self, ranking: Ranking) -> Likes
        recommends self.valid_ranking(ranking)
        decreases self.get_rank(ranking)
    {
        if !self.has_root() { no_likes() }
        else {
            let root_likes = set![self.root.unwrap()].to_multiset();
            let buffer_likes = self.root().buffers.likes();
            let children_likes = self.children_likes(ranking, 0);

            root_likes.add(buffer_likes).add(children_likes)
        }
    }

    pub open spec(checked) fn transitive_likes(self) -> Likes
    {
        if !self.acyclic() { arbitrary() }
        else { self.transitive_likes_internal(self.the_ranking()) }
    }
}


state_machine!{ LikesBetree {
    fields {
        pub betree: LinkedBetree_v::LinkedBetreeVars::State,
        // imperatively maintained view of tree node reference
        // prior to clone should be a tree shape (equivalent to refcount)
        pub betree_likes: Likes,
        // imperatively maintained view of buffer pointers (outgoing)
        // used to track life time of each immutable buffer
        pub branch_likes: Likes,
    }

    
}
// go down the reachable address




}