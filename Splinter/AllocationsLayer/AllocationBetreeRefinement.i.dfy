// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "AllocationBetree.i.dfy"

// a conditional refinement where it only refines if newly allocated AUs are fresh
module AllocationBetreeRefinment {
  import opened Options
  import opened LSNMod
  import opened AllocationBetreeMod
  import opened MiniAllocatorMod

  predicate IsFresh(v: Variables, aus: set<AU>)
  {
    && M.Set(v.betreeAULikes) !! aus
    // && M.Set(branchAULikes) !! aus
    && v.compactor.AUs() !! aus
    && G.ToAUs(v.allocBranchDiskView.Representation()) !! aus 
  }
}