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

  function I(s: PivotBetree.Variables) : Betree.Variables
  requires PivotBetree.ViewHasInvNodes(s.bcv.view)
  {
    PivotBetree.I(s)
  }

  lemma RefinesInit(s: PivotBetree.Variables)
    requires PivotBetree.Init(s)
    ensures PivotBetree.Inv(s)
    ensures Betree.Init(I( s))
  {
    PivotBetree.RefinesInit(s);
  }

  lemma RefinesNext(s: PivotBetree.Variables, s': PivotBetree.Variables, uiop: UI.Op)
    requires PivotBetree.Inv(s)
    requires PivotBetree.Next(s, s', uiop)
    ensures PivotBetree.Inv(s')
    ensures Betree.Next(I(s), I(s'), uiop)
  {
    PivotBetree.RefinesNext(s, s', uiop);
  }
}
