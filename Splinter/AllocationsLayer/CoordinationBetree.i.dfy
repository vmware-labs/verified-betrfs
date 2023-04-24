// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "AllocationBetree.i.dfy"

module CoordinationBetree {
  import opened ValueMessage
  import opened KeyType
  import opened StampedMod
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Options

  import GenericDisk
  import AllocBetree = AllocationBetreeMod
  
  type Address = GenericDisk.Address
  type AU = GenericDisk.AU

  datatype TransitionLabel =
    | LoadEphemeralFromPersistentLabel(endLsn: LSN)
    | PutRecordsLabel(records: MsgHistory)
    | QueryLabel(endLsn: LSN, key: Key, value: Value)
    | FreezeAsLabel(unobserved: set<AU>)
    | InternalLabel(allocs: set<AU>, deallocs: set<AU>)
    | CommitStartLabel(newBoundaryLsn: LSN)
    | CommitCompleteLabel()
    | CrashLabel()
  {
    predicate WF() {
      && (PutRecordsLabel? ==> records.WF())
    }
  }

  type StampedBetree = AllocBetree.StampedBetree

  datatype Ephemeral =
      | Unknown  // This means None
      | Known(v: AllocBetree.Variables)

  datatype Variables = Variables(
    persistent: StampedBetree,
    ephemeral: Ephemeral,
    inFlight: Option<StampedBetree>
  )
  {
    predicate WF() {
      true
    }

    function EphemeralAUs() : set<AU>
      requires ephemeral.Known?
    {
      ephemeral.v.AccessibleAUs()
    }

    function PersistentAUs() : set<AU>
    {
      persistent.value.AccessibleAUs()
    }

    function InFlightAUs() : set<AU>
      requires inFlight.Some?
    {
      inFlight.value.value.AccessibleAUs()
    } 
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.LoadEphemeralFromPersistentLabel?
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?

    && lbl.endLsn == v.persistent.seqEnd
    && AllocBetree.Init(v'.ephemeral.v, v.persistent)
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
  
    && AllocBetree.Next(v.ephemeral.v, v'.ephemeral.v, AllocBetree.PutLabel(lbl.records))
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

    && AllocBetree.Next(v.ephemeral.v, v'.ephemeral.v, AllocBetree.QueryLabel(lbl.endLsn, lbl.key, lbl.value))
    && v' == v
  }

  predicate FreezeMapInternal(v: Variables, v': Variables, lbl: TransitionLabel, frozenBetree: StampedBetree)
  {
    && v.WF()
    && lbl.WF()
    && lbl.FreezeAsLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    // Can't re-freeze until last in flight state reaches CommitComplete, since
    // an async superblock write may be in progress, and we need to maintain
    // guarantees about its in-flight map state.
    && v.inFlight.None?
    && AllocBetree.Next(v.ephemeral.v, v'.ephemeral.v, AllocBetree.FreezeAsLabel(frozenBetree, lbl.unobserved))
    && v'.inFlight == Some(frozenBetree)
    && v'.persistent == v.persistent // UNCHANGED
  }
  
  predicate EphemeralInternal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && AllocBetree.Next(v.ephemeral.v, v'.ephemeral.v, AllocBetree.InternalAllocationsLabel(lbl.allocs, lbl.deallocs))
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
    | FreezeMapInternalStep(frozenBetree: StampedBetree)
    | EphemeralInternalStep()
    | CommitStartStep()
    | CommitCompleteStep()
    | CrashStep()

  // Models mkfs
  predicate Init(v: Variables)
  {
    v == Variables(AllocBetree.EmptyImage(), Unknown, None)
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', lbl)
      case PutRecordsStep() => PutRecords(v, v', lbl)
      case QueryStep() => Query(v, v', lbl)
      case FreezeMapInternalStep(frozenBetree) => FreezeMapInternal(v, v', lbl, frozenBetree)
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
