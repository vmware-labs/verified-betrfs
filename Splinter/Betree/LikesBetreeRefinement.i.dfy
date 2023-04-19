// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LikesBetree.i.dfy"
include "BranchedBetreeRefinement.i.dfy"

// a conditional refinement where it only refines if newly allocated AUs are fresh
module LikesBetreeRefinement {
  import opened LikesBetreeMod
  import BranchedBetreeRefinement
  import BranchedBetreeMod

  function I(v: Variables) : BranchedBetreeMod.Variables
  {
    v.branchedVars
  }

  predicate Inv(v: Variables)
  {
    // placeholder
    && BranchedBetreeRefinement.Inv(v.branchedVars)
  }

  predicate ValidStampedBetree(stamped: StampedBetree)
  {
    && BranchedBetreeRefinement.InvBranchedBetree(stamped.value)
  }

  lemma InitRefines(v: Variables, stamped: StampedBetree)
    requires Init(v, stamped)
    requires ValidStampedBetree(stamped)
    ensures Inv(v)
    ensures BranchedBetreeMod.Init(I(v), stamped)
  {
    BranchedBetreeRefinement.InitRefines(v.branchedVars, stamped);
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
    ensures Inv(v')
    ensures BranchedBetreeMod.Next(I(v), I(v'), lbl.I())
  {
    // InvNext(v, v', lbl);
    assume false;
  }
}