// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CoordinationSystem.i.dfy"
include "CrashTolerantReprJournal.i.dfy"
include "CrashTolerantReprMap.i.dfy"

// TODO(jonh,robj): This file consists largely of copy-pastage from CoordinationSystem.
// Figure out how to refactor; maybe create subpredicates in CoordinationSystem to reuse here?
// Or maybe now it's just functor re-use.
// Or maybe it'll get interesting because we're going to begin talking about framing finally.

module GCCoordinationSystem {
  // import opened Options
  // import opened MapRemove_s
  import opened CrashTolerantMapSpecMod
  // import opened StampedMod
  // import opened MsgHistoryMod
  // import opened KeyType
  // import opened ValueMessage
  // import opened TotalKMMapMod
  import opened LSNMod
  import opened CrashTolerantReprJournal
  import opened CrashTolerantReprMap
  // import CoordinationSystem

  import Async = CrashTolerantMapSpecMod.uiopifc.async
  type UIOp = CrashTolerantMapSpecMod.uiopifc.UIOp

  type SyncReqs = map<CrashTolerantMapSpecMod.uiopifc.SyncReqId, LSN>

  datatype Ephemeral =
    | Unknown
    | Known(
      progress: Async.EphemeralState,
      syncReqs: SyncReqs,
      mapLsn: LSN  // invariant: agrees with mapp.stampedMap.seqEnd
    )
  {
  }

  datatype Variables = Variables(
    journal: CrashTolerantReprJournal.Variables,
    mapp: CrashTolerantReprMap.Variables,
    ephemeral: Ephemeral
  )
  {
    predicate WF()
    {
      && journal.WF()
      && mapp.WF()
      && (ephemeral.Known? == journal.ephemeral.Known? == mapp.ephemeral.Known?)
      // Provable from invariant:
      && (journal.inFlight.Some? ==> mapp.inFlight.Some?)
    }

    predicate Init()
    {
      && CrashTolerantReprJournal.Init(journal)
      && CrashTolerantReprMap.Init(mapp)
      && ephemeral.Unknown?
    }
  }

  function SimpleJournalLabel(clbl: CrashTolerantJournal.TransitionLabel) : CrashTolerantReprJournal.TransitionLabel
  {
    CrashTolerantReprJournal.TransitionLabel([], {}, clbl)
  }

  function SimpleMapLabel(clbl: CrashTolerantMap.TransitionLabel) : CrashTolerantReprMap.TransitionLabel
  {
    CrashTolerantReprMap.TransitionLabel([], {}, clbl)
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && uiop.NoopOp?
    && v'.ephemeral.Known?
    // todo(tony): allocs and freed are now constrained in two places, by SimpleJournalLabel(), and journal.LoadEphemeralFromPersistent. Danger.
    && CrashTolerantReprJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.LoadEphemeralFromPersistentLabel()))
    && CrashTolerantReprMap.Next(v.mapadt, v'.mapadt, SimpleMapLabel(CrashTolerantMap.LoadEphemeralFromPersistentLabel(v'.ephemeral.mapLsn)))
    && v'.ephemeral.progress == Async.InitEphemeralState()
    && v'.ephemeral.syncReqs == map[]
    // and thus all fields of v' are constrained.
  }

  



}
