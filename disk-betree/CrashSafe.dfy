include "BetreeInv.dfy"
include "MapSpec.dfy"
include "Betree.dfy"
include "BetreeInv.dfy"
include "BetreeRefinement.dfy"
include "CrashTypes.dfy"

abstract module CrashSafeBlockInterface {
  import BI = BetreeBlockInterface

  type Constants = BI.Constants
  datatype Variables = Variables(persistent: BI.Variables, ephemeral: BI.Variables)

  predicate Init(k: Constants, s: Variables)
  {
    && (exists block :: BI.Init(k, s.persistent, block))
    && s.ephemeral == s.persistent
  }

  datatype Step =
    | EphemeralMoveStep
    | SyncStep
    | CrashStep

  predicate EphemeralMove(k: Constants, s: Variables, s': Variables)
  {
    && s.persistent == s'.persistent
    && BI.Next(k, s.ephemeral, s'.ephemeral)
  }

  predicate Sync(k: Constants, s: Variables, s': Variables)
  {
    && s'.persistent == s.ephemeral
    && s'.ephemeral  == s.ephemeral
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    && s'.persistent == s.persistent
    && s'.ephemeral  == s.persistent
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    match step {
      case EphemeralMoveStep => EphemeralMove(k, s, s')
      case SyncStep => Sync(k, s, s')
      case CrashStep => Crash(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  predicate Inv(k: Constants, s: Variables) {
    && BI.Inv(k, s.persistent)
    && BI.Inv(k, s.ephemeral)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    //BI.InitImpliesInv(k, s.ephemeral);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    if (step.EphemeralMoveStep?) {
      BI.NextPreservesInv(k, s.ephemeral, s'.ephemeral);
    }
  }
}

abstract module CrashSafeBetree {
  import DB = Betree
  import DBI = BetreeInv
  import CrashTypes

  type Constants = DB.Constants
  datatype Variables = Variables(persistent: DB.Variables, ephemeral: DB.Variables)
  type UIOp = CrashTypes.CrashableUIOp<DB.UIOp>

  predicate Init(k: Constants, s: Variables)
  {
    && DB.Init(k, s.persistent)
    && s.ephemeral == s.persistent
  }

  datatype Step =
    | EphemeralMoveStep
    | SyncStep
    | CrashStep

  predicate EphemeralMove(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.NormalOp?
    && s.persistent == s'.persistent
    && DB.Next(k, s.ephemeral, s'.ephemeral, uiop.uiop)
  }

  predicate Sync(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.NormalOp?
    && uiop.uiop.NoOp?
    && s'.persistent == s.ephemeral
    && s'.ephemeral  == s.ephemeral
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.CrashOp?
    && s'.persistent == s.persistent
    && s'.ephemeral  == s.persistent
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
  {
    match step {
      case EphemeralMoveStep => EphemeralMove(k, s, s', uiop)
      case SyncStep => Sync(k, s, s', uiop)
      case CrashStep => Crash(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }

  predicate Inv(k: Constants, s: Variables) {
    && DBI.Inv(k, s.persistent)
    && DBI.Inv(k, s.ephemeral)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    DBI.InitImpliesInv(k, s.ephemeral);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  requires Inv(k, s)
  requires Next(k, s, s', uiop)
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    if (step.EphemeralMoveStep?) {
      DBI.NextPreservesInv(k, s.ephemeral, s'.ephemeral, uiop.uiop);
    }
  }
}

abstract module CrashSafeMap {
  import MS = MapSpec
  import CrashTypes

  type Constants = MS.Constants
  datatype Variables<Value> = Variables(persistent: MS.Variables<Value>, ephemeral: MS.Variables<Value>)
  type UIOp<Value> = CrashTypes.CrashableUIOp<MS.UI.Op<Value>>

  predicate Init<Value>(k: Constants, s: Variables<Value>)
  {
    && MS.Init(k, s.persistent)
    && s.ephemeral == s.persistent
  }

  datatype Step =
    | EphemeralMoveStep
    | SyncStep
    | CrashStep

  predicate EphemeralMove(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && s.persistent == s'.persistent
    && uiop.NormalOp?
    && MS.Next(k, s.ephemeral, s'.ephemeral, uiop.uiop)
  }

  predicate Sync(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.NormalOp?
    && uiop.uiop.NoOp?
    && s'.persistent == s.ephemeral
    && s'.ephemeral  == s.ephemeral
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.CrashOp?
    && s'.persistent == s.persistent
    && s'.ephemeral  == s.persistent
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
  {
    match step {
      case EphemeralMoveStep => EphemeralMove(k, s, s', uiop)
      case SyncStep => Sync(k, s, s', uiop)
      case CrashStep => Crash(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && exists step :: NextStep(k, s, s', uiop, step)
  }

  predicate Inv(k: Constants, s: Variables) {
    && MS.Inv(k, s.persistent)
    && MS.Inv(k, s.ephemeral)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    MS.InitImpliesInv(k, s.ephemeral);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  requires Inv(k, s)
  requires Next(k, s, s', uiop)
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    if (step.EphemeralMoveStep?) {
      MS.NextPreservesInv(k, s.ephemeral, s'.ephemeral, uiop.uiop);
    }
  }
}

abstract module CrashSafeBetreeMapRefinement {
  import A = CrashSafeBetree
  import B = CrashSafeMap
  import Ref = BetreeRefinement
  type UIOp = A.UIOp

  function Ik(k: A.Constants) : B.Constants
  {
    Ref.Ik(k)
  }

  function I(k: A.Constants, s: A.Variables) : B.Variables<A.DB.G.Value>
  requires A.Inv(k, s)
  {
    B.Variables(Ref.I(k, s.persistent), Ref.I(k, s.ephemeral))
  }

  lemma RefinesInit(k: A.Constants, s: A.Variables)
  requires A.Init(k, s)
  ensures A.Inv(k, s)
  ensures B.Init(Ik(k), I(k, s))
  {
    A.InitImpliesInv(k, s);
    Ref.BetreeRefinesMapInit(k, s.ephemeral);
  }

  lemma RefinesNextStep(k: A.Constants, s: A.Variables, s': A.Variables, uiop: UIOp, step: A.Step)
  requires A.Inv(k, s)
  requires A.NextStep(k, s, s', uiop, step)
  ensures A.Inv(k, s')
  ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    A.NextPreservesInv(k, s, s', uiop);
    match step {
      case EphemeralMoveStep => {
        Ref.BetreeRefinesMapNext(k, s.ephemeral, s'.ephemeral, uiop.uiop);
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.EphemeralMoveStep);
        assert B.Next(Ik(k), I(k, s), I(k, s'), uiop);
      }
      case SyncStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.SyncStep);
        assert B.Next(Ik(k), I(k, s), I(k, s'), uiop);
      }
      case CrashStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.CrashStep);
        assert B.Next(Ik(k), I(k, s), I(k, s'), uiop);
      }
    }
  }

  lemma RefinesNext(k: A.Constants, s: A.Variables, s':A.Variables, uiop: UIOp)
  requires A.Inv(k, s)
  requires A.Next(k, s, s', uiop)
  ensures A.Inv(k, s')
  ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    A.NextPreservesInv(k, s, s', uiop);
    var step :| A.NextStep(k, s, s', uiop, step);
    RefinesNextStep(k, s, s', uiop, step);
  }
}
