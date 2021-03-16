// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BetreeCache.i.dfy"
include "JournalCache.i.dfy"
include "BlockJournalDisk.i.dfy"

module {:extern} BlockJournalCache {
  import BetreeCache
  import JournalCache
  import D = BlockJournalDisk
  import opened ViewOp
  import UI

  datatype Variables = Variables(
    bc: BetreeCache.Variables,
    jc: JournalCache.Variables)

  predicate Init(s: Variables)
  {
    && BetreeCache.Init(s.bc)
    && JournalCache.Init(s.jc)
  }

  predicate NextStep(s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp, vop: VOp)
  {
    && VOpAgreesUIOp(vop, uiop)
    && BetreeCache.Next(s.bc, s'.bc, dop.bdop, vop)
    && JournalCache.Next(s.jc, s'.jc, dop.jdop, vop)
  }

  predicate Next(s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp)
  {
    exists vop :: NextStep(s, s', uiop, dop, vop)
  }

  predicate Inv(s: Variables)
  {
    && BetreeCache.Inv(s.bc)
    && JournalCache.Inv(s.jc)

    && (s.jc.LoadingSuperblock? ==> s.bc.Unready?)
    && ((s.jc.Ready? && s.jc.isFrozen) <==>
        (s.bc.Ready? && s.bc.frozenIndirectionTable.Some?))
    && (s.jc.Ready? && s.jc.frozenLoc.Some? ==>
      && s.bc.Ready?
      && s.bc.frozenIndirectionTableLoc == s.jc.frozenLoc
      && s.bc.outstandingIndirectionTableWrite.None?
    )
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
    BetreeCache.InitImpliesInv(s.bc);
    JournalCache.InitImpliesInv(s.jc);
  }

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp)
  requires Inv(s)
  requires Next(s, s', uiop, dop)
  ensures Inv(s')
  {
    var vop :| NextStep(s, s', uiop, dop, vop);
    BetreeCache.NextPreservesInv(s.bc, s'.bc, dop.bdop, vop);
    JournalCache.NextPreservesInv(s.jc, s'.jc, dop.jdop, vop);
  }

}
