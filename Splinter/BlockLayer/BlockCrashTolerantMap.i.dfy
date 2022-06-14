// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CrashTolerantMap.i.dfy"
include "../Betree/MarshalledBetree.i.dfy"

// TODO(jonh): This is a copy-paste of Splinter/CoordinationLayer/CrashTolerantMap. Functor-reuse?

module BlockCrashTolerantMap {
  import opened ValueMessage
  import opened KeyType
  import opened StampedMod
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Options
  import MarshalledBetreeMod
  import CrashTolerantMap

  type TransitionLabel = CrashTolerantMap.TransitionLabel

  type StoreImage = MarshalledBetreeMod.BetreeImage

  datatype Ephemeral =
    | Unknown
    | Known(v: MarshalledBetreeMod.Variables)

  datatype Variables = Variables(
    persistent: StoreImage,
    ephemeral: Ephemeral,
    inFlight: Option<StoreImage>
  )
  {
    predicate WF() {
      true
    }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.LoadEphemeralFromPersistentLabel?
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?

    && lbl.endLsn == v.persistent.superblock.seqEnd
    && MarshalledBetreeMod.Init(v'.ephemeral.v, v.persistent)
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate PutRecords(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.PutRecordsLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
  
    && MarshalledBetreeMod.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledBetreeMod.PutLabel(lbl.records))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.QueryLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && MarshalledBetreeMod.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledBetreeMod.QueryLabel(lbl.endLsn, lbl.key, lbl.value))
    && v' == v
  }

  predicate FreezeMapInternal(v: Variables, v': Variables, lbl: TransitionLabel, frozenMap: StoreImage)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    // Can't re-freeze until last in flight state reaches CommitComplete, since
    // an async superblock write may be in progress, and we need to maintain
    // guarantees about its in-flight map state.
    && v.inFlight.None?

    && MarshalledBetreeMod.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledBetreeMod.FreezeAsLabel(frozenMap))
    && v'.inFlight == Some(frozenMap)
    && v'.persistent == v.persistent // UNCHANGED
  }
  
  predicate EphemeralInternal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && MarshalledBetreeMod.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledBetreeMod.InternalLabel())
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate CommitStart(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.CommitStartLabel?
    && v.ephemeral.Known?
    && v.inFlight.Some?

    // Frozen map can't go backwards vs persistent map, lest we end up with
    // a gap to the ephemeral journal start.
    && v.persistent.superblock.seqEnd <= lbl.newBoundaryLsn
    // Frozen journal & frozen map agree on boundary.
    && lbl.newBoundaryLsn == v.inFlight.value.superblock.seqEnd

    && v' == v
  }

  predicate CommitComplete(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.CommitCompleteLabel?
    && v.inFlight.Some?

    && v' == v.(
      persistent := v.inFlight.value,
      // ephemeral unchanged
      inFlight := None)
  }

  predicate Crash(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.CrashLabel?
    && v' == v.(
      ephemeral := Unknown,
      inFlight := None)
  }

  datatype Step =
    | LoadEphemeralFromPersistentStep()
    | PutRecordsStep()
    | QueryStep()
    | FreezeMapInternalStep(frozenMap: StoreImage)
    | EphemeralInternalStep()
    | CommitStartStep()
    | CommitCompleteStep()
    | CrashStep()


  // Models mkfs
  predicate Init(v: Variables)
  {
    v == Variables(MarshalledBetreeMod.EmptyBetreeImage(), Unknown, None)
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', lbl)
      case PutRecordsStep() => PutRecords(v, v', lbl)
      case QueryStep() => Query(v, v', lbl)
      case FreezeMapInternalStep(frozenMap) => FreezeMapInternal(v, v', lbl, frozenMap)
      case EphemeralInternalStep() => EphemeralInternal(v, v', lbl)
      case CommitStartStep() => CommitStart(v, v', lbl)
      case CommitCompleteStep() => CommitComplete(v, v', lbl)
      case CrashStep() => Crash(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(v, v', lbl, step)
  }
}

