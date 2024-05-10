// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::betree::LinkedBranch_v::*;
use crate::betree::PivotBranch_v;
// use crate::spec::KeyType_t::*;
// use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::Ranking;

verus! {

// Add intepretation function for each node in a LinkedBranch.
impl Node {
    /// Returns the PivotBranch_v::Node interpretation of the LinkedBranch::Node
    /// located at the provided address in the provided disk_view.
    // TODO: need to figure out why the decreases-when is not proving
    // pub open spec fn i(disk_view: DiskView, addr: Address, ranking: Ranking) -> PivotBranch_v::Node
    //     recommends
    //         disk_view.wf(),
    //         disk_view.valid_address(addr),
    //         disk_view.valid_ranking(ranking),
    //         ranking.contains_key(addr),
    //     decreases ranking[addr] when disk_view.wf() && disk_view.valid_address(addr) && disk_view.valid_ranking(ranking) && ranking.contains_key(addr)
    //         via Self::ranking_decreases
    // {
    //     let node = disk_view.entries[addr];
    //     match node {
    //         Node::Leaf{keys, msgs} => {
    //             PivotBranch_v::Node::Leaf{ keys: keys, msgs: msgs }
    //         },
    //         Node::Index{pivots, children} => {
    //             PivotBranch_v::Node::Index{
    //                 pivots: pivots,
    //                 children: Seq::new(
    //                     children.len(),
    //                     |i| Node::i(disk_view, children[i], ranking)
    //                 ),
    //             }
    //         },
    //     }
    // }

    // // Seems like a `decreases_by` gets its preconditions and postconditions from where it is called.
    // // Ah, it's because the `decreases_by` needs to have the exact same arguments as the spec function,
    // // and when passing you need to just pass function (not invoke it directly) 
    // // otherwise you get really confusing VIR dump.
    // #[verifier::decreases_by]
    // proof fn ranking_decreases(disk_view: DiskView, addr: Address, ranking: Ranking)
    // {
    //     let node = disk_view.entries[addr];
    //     assert(disk_view.valid_address(addr));
    //     assert(disk_view.valid_ranking(ranking));
    //     assert(ranking.contains_key(addr) && disk_view.entries.contains_key(addr));
    //     assert(disk_view.node_children_respects_rank(ranking, addr));

    //     match node {
    //         Node::Leaf{keys, msgs} => {},
    //         Node::Index{pivots, children} => {
    //             assert(forall |i: nat| 0 <= i < children.len() ==> node.valid_child_index(i));
    //         },
    //     }
    // }
}

} // verus!
