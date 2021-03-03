// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "ByteSystem.i.dfy"
include "../BlockCacheSystem/BetreeJournalSystem.i.dfy"

module ByteSystem_Refines_BetreeJournalSystem {
  import ByteSystem
  import BetreeJournalSystem
  import UI

  function I(s: ByteSystem.Variables) : BetreeJournalSystem.Variables
  requires ByteSystem.Inv(s)
  {
    ByteSystem.I(s)
  }

  lemma RefinesInit(s: ByteSystem.Variables)
  requires ByteSystem.Init(s)
  ensures ByteSystem.Inv(s)
  ensures BetreeJournalSystem.Init(I(s))
  {
    ByteSystem.InitImpliesInv(s);
  }

  lemma RefinesNext(s: ByteSystem.Variables, s': ByteSystem.Variables, uiop: UI.Op)
  requires ByteSystem.Inv(s)
  requires ByteSystem.Next(s, s', uiop)
  ensures ByteSystem.Inv(s')
  ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
  {
    var step :| ByteSystem.NextStep(s, s', uiop, step);
    ByteSystem.NextStepPreservesInv(s, s', uiop, step);
  }
}
