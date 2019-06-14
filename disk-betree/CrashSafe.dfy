include "BlockInterface.dfy"
include "MapSpec.dfy"

abstract module CrashableBlockInterface {
  import BI : BlockInterface

  type Constants = BI.Constants
  datatype Variables<T> = Variables(persistent: BI.Variables<T>, ephemeral: BI.Variables<T>)

  predicate Init<T>(k: Constants, s: Variables, block: T)
  {
    && BI.Init(k, s.persistent, block)
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
