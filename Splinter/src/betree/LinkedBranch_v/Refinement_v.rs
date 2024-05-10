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

impl LinkedBranch {
    /// Returns the PivotBranch_v::Node interpretation of the LinkedBranch
    pub open spec/*XXX (checked)*/ fn i(self) -> PivotBranch_v::Node
        recommends
            self.acyclic(),
    {
        // Need the_ranking ensures to restore checked
        let ranking = self.the_ranking();
        self.i_internal(ranking)
    }

    pub open spec(checked) fn i_internal(self, ranking: Ranking) -> PivotBranch_v::Node
        recommends
            self.wf(),
            self.valid_ranking(ranking),
        decreases self.get_rank(ranking)
        when self.wf() && self.valid_ranking(ranking)
    {
        match self.root() {
            Node::Leaf{keys, msgs} => {
                PivotBranch_v::Node::Leaf{ keys: keys, msgs: msgs }
            },
            Node::Index{pivots, children} => {
                PivotBranch_v::Node::Index{
                    pivots: pivots,
                    children: Seq::new(
                        children.len(),
                        // Need this weird hack to prove decreases because valid_ranking triggers
                        // on valid_child_index
                        |i|
                            // 0 <= i < children.len() ==> self.root().valid_child_index(i as nat)
                            if self.root().valid_child_index(i as nat) {
                                self.child_at_idx(i as nat).i_internal(ranking)
                            } else {
                                PivotBranch_v::invalid_node()
                            }
                    ),
                }
            },
        }
    }
}

} // verus!
