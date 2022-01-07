include "SplinterTreeInterp.i.dfy"
include "../lib/Base/KeyType.s.dfy"
include "../Spec/Message.s.dfy"

// Sowmya -- there might be a lot of invariants for this part as opposed to the journal, so I decided to make another module for this
// If this ends up being sparse, we can just refactor it into BetreeInterpMod or ProgramMachineMod
// Module that contains Betree's invariants needed in the RefinementProof
module SplinterTreeInvariantMod {
  import opened SplinterTreeInterpMod
  import opened Options
  import opened InterpMod
  import opened DiskTypesMod
  import opened ValueMessage
  import opened KeyType
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened SplinterTreeMachineMod
  import Nat_Order

//  // TODO; Might need to change this to table about both IM and IMStable
//  lemma StableFraming(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:Superblock)
//    requires DiskViewsEquivalentForSeq(cache0.dv, cache1.dv, IReadsSeq(v, cache0))
//    ensures IM(cache0, sb) == IM(cache1, sb)
//  {
//  }

}
