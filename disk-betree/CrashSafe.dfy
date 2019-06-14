include "DiskBetreeInv.dfy"
include "MapSpec.dfy"
include "DiskBetree.dfy"
include "DiskBetreeInv.dfy"
include "DiskBetreeRefinement.dfy"

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
    && MS.Inv(k, s.ephemeral)
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
  import CSM = CrashSafeMap
  import CSDB = CrashSafeDiskBetree

  import Ref = DiskBetreeRefinement

  function Ik(k: CSDB.Constants) : CSM.Constants
  {
    Ref.Ik(k)
  }

  /*
  lemma CrashSafeBetreeRefinesCrashSafeMapNext(k: CSDB.Constants, s: CSDB.Variables, s':CSDB.Variables)
    requires CSDB.Inv(k, s)
    requires CSDB.Next(k, s, s')
    ensures CSDB.Inv(k, s')
    ensures CSM.Next(Ik(k), I(k, s), I(k, s'))
  {
    /*
    NextPreservesInvariant(k, s, s');
    var step :| CSDB.NextStep(k, s, s', step);
    BetreeRefinesMapNextStep(k, s, s', step);
    */
  }
  */

}
