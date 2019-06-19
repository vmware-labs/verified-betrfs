include "BlockCache.dfy"
include "DiskBetree.dfy"

module BtreeGraphBlockCache {
  import G = BetreeGraph
}

module BtreeBlockCache {
  import G = BetreeGraph
  import BC = BetreeGraphBlockCache
  import DB = DiskBetree

  type Variables = BC.Variables
  type Constants = BC.Constants

  predicate Init(k: Constants, s: Variables) {
    BC.Init(k, s)
  }

  predicate Inv(k: Constants, s: Variables) {
    BC.Inv(k, s)
  }

  datatype Step =
    | BetreeMoveStep(step: DB.Step)

  predicate BetreeMove(k: Constants, s: Variables, s': Variables, step: DB.Step) {
    DB.NextStep(
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step) {
    match step {
      case BetreeMoveStep(step) => BetreeMove(k, s, s', step)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step: Step :: NextStep(k, s, s', step)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  requires Inv(k, s)
  {
    BC.InitImpliesInv(k, s);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  requires Inv(k, s')
  {
  }
}
