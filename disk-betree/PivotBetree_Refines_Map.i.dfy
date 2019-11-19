include "MapSpec.s.dfy"
include "PivotBetree_Refines_Betree.i.dfy"
include "Betree_Refines_Map.i.dfy"
//
// Composes the two refinements:
//
//   PivotBetree -> Betree
//   Betree -> Map
//
// To yield
//
//   PivotBetree -> Map
//

module PivotBetree_Refines_Map {
  import PB = PivotBetree
  import PivotBetreeRefinesBetree = PivotBetreeInvAndRefinement
  import BetreeRefinesMap = Betree_Refines_Map
  import MS = MapSpec
  type UIOp = MS.UI.Op

  function Ik(k: PB.Constants) : MS.Constants {
    BetreeRefinesMap.Ik(PivotBetreeRefinesBetree.Ik(k))
  }

  function I(k: PB.Constants, s: PB.Variables) : MS.Variables
  requires PivotBetreeRefinesBetree.Inv(k, s)
  {
    BetreeRefinesMap.I(
      PivotBetreeRefinesBetree.Ik(k),
      PivotBetreeRefinesBetree.I(k, s)
    )
  }

  lemma PivotBetreeRefinesMapInit(k: PB.Constants, s: PB.Variables)
    requires PB.Init(k, s)
    ensures PivotBetreeRefinesBetree.Inv(k, s)
    ensures MS.Init(Ik(k), I(k, s))
  {
    PivotBetreeRefinesBetree.RefinesInit(k, s);
    BetreeRefinesMap.RefinesInit(
      PivotBetreeRefinesBetree.Ik(k),
      PivotBetreeRefinesBetree.I(k, s));
  }

  lemma PivotBetreeRefinesMapNext(k: PB.Constants, s: PB.Variables, s': PB.Variables, uiop: UIOp)
    requires PivotBetreeRefinesBetree.Inv(k, s)
    requires PB.Next(k, s, s', uiop)
    ensures PivotBetreeRefinesBetree.Inv(k, s')
    ensures MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    PivotBetreeRefinesBetree.RefinesNext(k, s, s', uiop);
    BetreeRefinesMap.RefinesNext(
      PivotBetreeRefinesBetree.Ik(k),
      PivotBetreeRefinesBetree.I(k, s),
      PivotBetreeRefinesBetree.I(k, s'),
      uiop);
  }
}
