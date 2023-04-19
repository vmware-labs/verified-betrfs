// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "AllocationBetree.i.dfy"
include "../Betree/LikesBetreeRefinement.i.dfy"

// a conditional refinement where it only refines if newly allocated AUs are fresh
module AllocationBetreeRefinement {
  import opened StampedMod
  import opened AllocationBetreeMod
  import LikesBetreeRefinement
  import LikesBetreeMod

  function I(v: Variables) : LikesBetreeMod.Variables
  {
    v.likesVars
  }

  function IStampedBetree(image: StampedBetree) : LikesBetreeMod.StampedBetree
  {
    Stamped(image.value.branched, image.seqEnd)
  }

  predicate Inv(v: Variables)
  {
    // placeholder
    && LikesBetreeRefinement.Inv(v.likesVars)
  }

  predicate IsFresh(v: Variables, aus: set<AU>)
  {
    && M.Set(v.betreeAULikes) !! aus
    // && M.Set(branchAULikes) !! aus
    && v.compactor.AUs() !! aus
    && G.ToAUs(v.allocBranchDiskView.Representation()) !! aus 
  }

  predicate FreshLabel(v: Variables,lbl: TransitionLabel)
  {
   && lbl.InternalAllocationsLabel? ==> IsFresh(v, lbl.allocs)
  }

  predicate ValidStampedBetree(stamped: StampedBetree)
  {
    && LikesBetreeRefinement.ValidStampedBetree(IStampedBetree(stamped))
  }

  lemma InitRefines(v: Variables, stamped: StampedBetree)
    requires Init(v, stamped)
    requires ValidStampedBetree(stamped)
    ensures Inv(v)
    ensures LikesBetreeMod.Init(I(v), IStampedBetree(stamped))
  {
    LikesBetreeRefinement.InitRefines(v.likesVars, IStampedBetree(stamped));
  }

  // lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
  //   requires Inv(v)
  //   requires Next(v, v', lbl)
  //   ensures Inv(v')
  // {
  // }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    requires FreshLabel(v, lbl)
    ensures Inv(v')
    ensures LikesBetreeMod.Next(I(v), I(v'), lbl.I())
  {
    // InvNext(v, v', lbl);
    assume false;
  }
}