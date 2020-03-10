include "PivotBetree.i.dfy"

//
// Refinement from PivotBetree for Betree.
// Note that this file just exposes the interpretation
// functions and lemmas.
//
// The meat of the logic is in PivotBetree
// and PivotBetreeSpecRefinement.
//

module PivotBetree_Refines_Betree {
  import PivotBetree
  import Betree
  import UI

  function Ik(k: PivotBetree.Constants) : Betree.Constants
  {
    PivotBetree.Ik(k)
  }

  function I(k: PivotBetree.Constants, s: PivotBetree.Variables) : Betree.Variables
  requires PivotBetree.ViewHasInvNodes(s.bcv.view)
  {
    PivotBetree.I(k, s)
  }

  lemma RefinesInit(k: PivotBetree.Constants, s: PivotBetree.Variables)
    requires PivotBetree.Init(k, s)
    ensures PivotBetree.Inv(k, s)
    ensures Betree.Init(Ik(k), I(k, s))
  {
    PivotBetree.RefinesInit(k, s);
  }

  lemma RefinesNext(k: PivotBetree.Constants, s: PivotBetree.Variables, s': PivotBetree.Variables, uiop: UI.Op)
    requires PivotBetree.Inv(k, s)
    requires PivotBetree.Next(k, s, s', uiop)
    ensures PivotBetree.Inv(k, s')
    ensures Betree.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    PivotBetree.RefinesNext(k, s, s', uiop);
  }
}
