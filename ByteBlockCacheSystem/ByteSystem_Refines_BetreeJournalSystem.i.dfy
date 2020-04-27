include "ByteSystem.i.dfy"
include "../BlockCacheSystem/BetreeJournalSystem.i.dfy"

module ByteSystem_Refines_BetreeJournalSystem {
  import ByteSystem
  import BetreeJournalSystem
  import UI

  function Ik(k: ByteSystem.Constants) : BetreeJournalSystem.Constants
  {
    ByteSystem.Ik(k)
  }

  function I(k: ByteSystem.Constants, s: ByteSystem.Variables) : BetreeJournalSystem.Variables
  requires ByteSystem.Inv(k, s)
  {
    ByteSystem.I(k, s)
  }

  lemma RefinesInit(k: ByteSystem.Constants, s: ByteSystem.Variables)
  requires ByteSystem.Init(k, s)
  ensures ByteSystem.Inv(k, s)
  ensures BetreeJournalSystem.Init(Ik(k), I(k, s))
  {
    ByteSystem.InitImpliesInv(k, s);
  }

  lemma RefinesNext(k: ByteSystem.Constants, s: ByteSystem.Variables, s': ByteSystem.Variables, uiop: UI.Op)
  requires ByteSystem.Inv(k, s)
  requires ByteSystem.Next(k, s, s', uiop)
  ensures ByteSystem.Inv(k, s')
  ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| ByteSystem.NextStep(k, s, s', uiop, step);
    ByteSystem.NextStepPreservesInv(k, s, s', uiop, step);
  }
}
