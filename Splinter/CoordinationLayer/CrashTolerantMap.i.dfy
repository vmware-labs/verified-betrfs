// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "AbstractMap.i.dfy"
include "MsgHistory.i.dfy"
include "LSNMod.i.dfy"

// TODO: rename this. It implies it implements an interface which it does NOT
// see CrashTolerant.s.dfy (this does not implement that)
module CrashTolerantMap {
  import opened ValueMessage
  import opened KeyType
  import opened StampedMod
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Options
  import AbstractMap

  // TODO: was this meant to be CrashTolerant? labels are
  // not working with the "nice" label hierarchy

  datatype TransitionLabel =
    | LoadEphemeralFromPersistentLabel(endLsn: LSN)
    | PutRecordsLabel(records: MsgHistory)
    | QueryLabel(endLsn: LSN, key: Key, value: Value)
    | InternalLabel()
    | CommitStartLabel(newBoundaryLsn: LSN)
    | CommitCompleteLabel()
    | CrashLabel()
  {
    predicate WF() {
      && (PutRecordsLabel? ==> records.WF())
    }
  }

  type StoreImage = StampedMap

  datatype Ephemeral =
    | Unknown  // This means None
    | Known(v: AbstractMap.Variables)

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

    && lbl.endLsn == v.persistent.seqEnd
    && AbstractMap.Init(v'.ephemeral.v, v.persistent)
    && v' == v.(
      ephemeral := v'.ephemeral // admit relational update from above
    )
  }

  predicate PutRecords(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.PutRecordsLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
  
    && AbstractMap.Next(v.ephemeral.v, v'.ephemeral.v, AbstractMap.PutLabel(lbl.records))
    && v' == v.(
      ephemeral := v'.ephemeral // admit relational update from above
    )
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.QueryLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && AbstractMap.Next(v.ephemeral.v, v'.ephemeral.v, AbstractMap.QueryLabel(lbl.endLsn, lbl.key, lbl.value))
    && v' == v
  }

  // freeze ephemeral map
  predicate FreezeMapInternal(v: Variables, v': Variables, lbl: TransitionLabel, frozenMap: StampedMap)
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

    && AbstractMap.FreezeAs(v.ephemeral.v, v'.ephemeral.v, AbstractMap.FreezeAsLabel(frozenMap))
    && v' == v.(
      ephemeral := v'.ephemeral, // admit relational update from above
      inFlight := Some(frozenMap)
    )
  }

  // use persistent map as our frozen map (no additional flushing needed)
  predicate FreezeFromPersistentInternal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalLabel?
    && v.ephemeral.Known?
    // Can't re-freeze until last in flight state reaches CommitComplete, since
    // an async superblock write may be in progress, and we need to maintain
    // guarantees about its in-flight map state.
    && v.inFlight.None?
    && v' == v.(
      inFlight := Some(v.persistent) // admit relational update from above
    )
  }
  
  predicate EphemeralInternal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && AbstractMap.Next(v.ephemeral.v, v'.ephemeral.v, AbstractMap.InternalLabel())
    && v' == v.(
      ephemeral := v'.ephemeral // admit relational update from above
    )
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
    && v.persistent.seqEnd <= lbl.newBoundaryLsn
    // Frozen journal & frozen map agree on boundary.
    && lbl.newBoundaryLsn == v.inFlight.value.seqEnd

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
    | FreezeMapInternalStep(frozenMap: StampedMap)
    | FreezeFromPersistentInternalStep()
    | EphemeralInternalStep()
    | CommitStartStep()
    | CommitCompleteStep()
    | CrashStep()


  // Models mkfs
  predicate Init(v: Variables)
  {
    v == Variables(StampedMod.Empty(), Unknown, None)
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', lbl)
      case PutRecordsStep() => PutRecords(v, v', lbl)
      case QueryStep() => Query(v, v', lbl)
      case FreezeMapInternalStep(frozenMap) => FreezeMapInternal(v, v', lbl, frozenMap)
      case FreezeFromPersistentInternalStep() => FreezeFromPersistentInternal(v, v', lbl)
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
