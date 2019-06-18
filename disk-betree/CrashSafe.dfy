include "DiskBetreeInv.dfy"
include "MapSpec.dfy"
include "DiskBetree.dfy"
include "DiskBetreeInv.dfy"
include "DiskBetreeRefinement.dfy"

module CrashSafeBlockInterface {
  import BI = BlockInterface

  type Constants = BI.Constants
  datatype Variables<T> = Variables(persistent: BI.Variables<T>, ephemeral: BI.Variables<T>)

  predicate Init<T(!new)>(k: Constants, s: Variables)
  {
    && (exists block :: BI.Init(k, s.persistent, block))
    && s.ephemeral == s.persistent
  }

  datatype Step<T> =
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

  predicate Next<T(!new)>(k: Constants, s: Variables, s': Variables) {
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

module CrashSafeDiskBetree {
  import DB = DiskBetree
  import DBI = DiskBetreeInv

  type Constants = DB.Constants
  datatype Variables<T> = Variables(persistent: DB.Variables<T>, ephemeral: DB.Variables<T>)

  predicate Init(k: Constants, s: Variables)
  {
    && DB.Init(k, s.persistent)
    && s.ephemeral == s.persistent
  }

  datatype Step<T> =
    | EphemeralMoveStep
    | SyncStep
    | CrashStep

  predicate EphemeralMove(k: Constants, s: Variables, s': Variables)
  {
    && s.persistent == s'.persistent
    && DB.Next(k, s.ephemeral, s'.ephemeral)
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

  predicate Next<T(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
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

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    if (step.EphemeralMoveStep?) {
      DBI.NextPreservesInv(k, s.ephemeral, s'.ephemeral);
    }
  }
}

module CrashSafeMap {
  import MS = MapSpec

  type Constants = MS.Constants
  datatype Variables<T> = Variables(persistent: MS.Variables<T>, ephemeral: MS.Variables<T>)

  predicate Init(k: Constants, s: Variables)
  {
    && MS.Init(k, s.persistent)
    && s.ephemeral == s.persistent
  }

  datatype Step<T> =
    | EphemeralMoveStep
    | SyncStep
    | CrashStep

  predicate EphemeralMove(k: Constants, s: Variables, s': Variables)
  {
    && s.persistent == s'.persistent
    && MS.Next(k, s.ephemeral, s'.ephemeral)
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

  predicate Next<T(!new)>(k: Constants, s: Variables, s': Variables) {
    && exists step :: NextStep(k, s, s', step)
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

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    if (step.EphemeralMoveStep?) {
      MS.NextPreservesInv(k, s.ephemeral, s'.ephemeral);
    }
  }
}

module CrashSafeBetreeMapRefinement {
  import A = CrashSafeDiskBetree
  import B = CrashSafeMap
  import Ref = DiskBetreeRefinement

  function Ik(k: A.Constants) : B.Constants
  {
    Ref.Ik(k)
  }

  function I(k: A.Constants, s: A.Variables) : B.Variables
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

  lemma RefinesNextStep(
      k: A.Constants, s: A.Variables, s': A.Variables, step: A.Step)
  requires A.Inv(k, s)
  requires A.NextStep(k, s, s', step)
  ensures A.Inv(k, s')
  ensures B.Next(Ik(k), I(k, s), I(k, s'))
  {
    A.NextPreservesInv(k, s, s');
    match step {
      case EphemeralMoveStep => {
        Ref.BetreeRefinesMapNext(k, s.ephemeral, s'.ephemeral);
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), B.EphemeralMoveStep);
        assert B.Next(Ik(k), I(k, s), I(k, s'));
      }
      case SyncStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), B.SyncStep);
        assert B.Next(Ik(k), I(k, s), I(k, s'));
      }
      case CrashStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), B.CrashStep);
        assert B.Next(Ik(k), I(k, s), I(k, s'));
      }
    }
  }

  lemma RefinesNext(k: A.Constants, s: A.Variables, s':A.Variables)
  requires A.Inv(k, s)
  requires A.Next(k, s, s')
  ensures A.Inv(k, s')
  ensures B.Next(Ik(k), I(k, s), I(k, s'))
  {
    A.NextPreservesInv(k, s, s');
    var step :| A.NextStep(k, s, s', step);
    RefinesNextStep(k, s, s', step);
  }
}
