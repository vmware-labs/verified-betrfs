// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "LogSpec.dfy"

module CrashSafeLog {
  import LS = LogSpec

  type Constants = LS.Constants
  datatype Variables = Variables(persistent: LS.Variables, ephemeral: LS.Variables)

  predicate Init(k: Constants, s: Variables)
  {
    && LS.Init(k, s.persistent)
    && s.ephemeral == s.persistent
  }

  datatype Step =
    | EphemeralMoveStep
    | SyncStep
    | CrashStep

  predicate EphemeralMove(k: Constants, s: Variables, s': Variables)
  {
    && s.persistent == s'.persistent
    && LS.Next(k, s.ephemeral, s'.ephemeral)
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

  predicate Next(k: Constants, s: Variables, s': Variables)
  {
    && exists step :: NextStep(k, s, s', step)
  }
}
