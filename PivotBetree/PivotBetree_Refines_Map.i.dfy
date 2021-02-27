// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../MapSpec/MapSpec.s.dfy"
include "../PivotBetree/PivotBetree_Refines_Betree.i.dfy"
include "../Betree/Betree_Refines_Map.i.dfy"
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
  import PivotBetreeRefinesBetree = PivotBetree_Refines_Betree
  import BetreeRefinesMap = Betree_Refines_Map
  import MS = MapSpec
  type UIOp = MS.UI.Op

  function I(s: PB.Variables) : MS.Variables
  requires PB.Inv(s)
  {
    BetreeRefinesMap.I(
      PivotBetreeRefinesBetree.I(s)
    )
  }

  lemma RefinesInit(s: PB.Variables)
    requires PB.Init(s)
    ensures PB.Inv(s)
    ensures MS.Init(I(s))
  {
    PivotBetreeRefinesBetree.RefinesInit(s);
    BetreeRefinesMap.RefinesInit(
      PivotBetreeRefinesBetree.I(s));
  }

  lemma RefinesNext(s: PB.Variables, s': PB.Variables, uiop: UIOp)
    requires PB.Inv(s)
    requires PB.Next(s, s', uiop)
    ensures PB.Inv(s')
    ensures MS.Next(I(s), I(s'), uiop)
  {
    PivotBetreeRefinesBetree.RefinesNext(s, s', uiop);
    BetreeRefinesMap.RefinesNext(
      PivotBetreeRefinesBetree.I(s),
      PivotBetreeRefinesBetree.I(s'),
      uiop);
  }
}
