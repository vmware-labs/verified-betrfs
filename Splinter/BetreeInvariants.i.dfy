include "IOSystem.s.dfy"
include "ProgramInterp.i.dfy"
include "ProofObligations.s.dfy"
include "BetreeInterp.i.dfy"

// Sowmya -- there might be a lot of invariants for this part as opposed to the journal, so I decided to make another module for this
// If this ends up being sparse, we can just refactor it into BetreeInterpMod or ProgramMachineMod
// Module that contains Betree's invariants needed in the RefinementProof
module BetreeInvariantMod {
  import opened BetreeInterpMod
  import opened Options
  import opened MessageMod
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgSeqMod
  import IndirectionTableMod
  import opened BetreeMachineMod
  import Nat_Order

  // TODO; Might need to change this to table about both IM and IMStable
  lemma StableFraming(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:Superblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures IMStable(cache0, sb) == IMStable(cache1, sb)
  {
  }

}
