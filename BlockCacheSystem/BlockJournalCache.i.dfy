include "BetreeCache.i.dfy"
include "JournalCache.i.dfy"
include "BlockJournalDisk.i.dfy"

module {:extern} BlockJournalCache {
  import BetreeCache
  import JournalCache
  import D = BlockJournalDisk
  import opened ViewOp
  import UI

  datatype Constants = Constants(
    bc: BetreeCache.Constants,
    jc: JournalCache.Constants)

  datatype Variables = Variables(
    bc: BetreeCache.Variables,
    jc: JournalCache.Variables)

  predicate Init(k: Constants, s: Variables)
  {
    && BetreeCache.Init(k.bc, s.bc)
    && JournalCache.Init(k.jc, s.jc)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp, vop: VOp)
  {
    && VOpAgreesUIOp(vop, uiop)
    && BetreeCache.Next(k.bc, s.bc, s'.bc, dop.bdop, vop)
    && JournalCache.Next(k.jc, s.jc, s'.jc, dop.jdop, vop)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp)
  {
    exists vop :: NextStep(k, s, s', uiop, dop, vop)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && BetreeCache.Inv(k.bc, s.bc)
    && JournalCache.Inv(k.jc, s.jc)

    && (s.jc.LoadingSuperblock? ==> s.bc.Unready?)
    && ((s.jc.Ready? && s.jc.isFrozen) <==>
        (s.bc.Ready? && s.bc.frozenIndirectionTable.Some?))
    && (s.jc.Ready? && s.jc.frozenLoc.Some? ==>
      && s.bc.Ready?
      && s.bc.frozenIndirectionTableLoc == s.jc.frozenLoc
      && s.bc.outstandingIndirectionTableWrite.None?
    )
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    BetreeCache.InitImpliesInv(k.bc, s.bc);
    JournalCache.InitImpliesInv(k.jc, s.jc);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp)
  requires Inv(k, s)
  requires Next(k, s, s', uiop, dop)
  ensures Inv(k, s')
  {
    var vop :| NextStep(k, s, s', uiop, dop, vop);
    BetreeCache.NextPreservesInv(k.bc, s.bc, s'.bc, dop.bdop, vop);
    JournalCache.NextPreservesInv(k.jc, s.jc, s'.jc, dop.jdop, vop);
  }

}
