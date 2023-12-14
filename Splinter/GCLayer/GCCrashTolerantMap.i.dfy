// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CrashTolerantMap.i.dfy"
include "../Betree/ReprBetree.i.dfy"

// TODO(jonh): This is a copy-paste of Splinter/CoordinationLayer/CrashTolerantMap. Functor-reuse?

module GCCrashTolerantMap {
  import opened StampedMod
  import opened Options
  import opened GenericDisk
  import LinkedBetreeMod
  import ReprBetree
  import CrashTolerantMap

  // type StampedBetree = Stamped<LinkedBetreeMod.LinkedBetree>
  type GCMap = ReprBetree.GCStampedBetree

  datatype TransitionLabel = TransitionLabel(allocations: set<Address>, freed: set<Address>, base: CrashTolerantMap.TransitionLabel)
  {
    predicate WF() {
      && base.WF()
    }
  }
  
  datatype Ephemeral =
    | Unknown
    | Known(v: ReprBetree.Variables)

  datatype Variables = Variables(
    persistent: GCMap,
    ephemeral: Ephemeral,
    inFlight: Option<GCMap>
  )
  {
    predicate WF() {
      true
    }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.LoadEphemeralFromPersistentLabel?
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?
    && lbl.allocations == {}
    && lbl.freed == {}

    && lbl.base.endLsn == v.persistent.stamped.seqEnd
    && ReprBetree.Init(v'.ephemeral.v, v.persistent)
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate PutRecords(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.PutRecordsLabel?
    && lbl.allocations == {}
    && lbl.freed == {}
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
  
    && ReprBetree.Next(v.ephemeral.v, v'.ephemeral.v, ReprBetree.PutLabel(lbl.base.records))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.QueryLabel?
    && lbl.allocations == {}
    && lbl.freed == {}
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && ReprBetree.Next(v.ephemeral.v, v'.ephemeral.v, ReprBetree.QueryLabel(lbl.base.endLsn, lbl.base.key, lbl.base.value))
    && v' == v
  }

  predicate FreezeMapInternal(v: Variables, v': Variables, lbl: TransitionLabel, frozenMap: GCMap)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.InternalLabel?
    && lbl.allocations == {}
    && lbl.freed == {}
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    // Can't re-freeze until last in flight state reaches CommitComplete, since
    // an async superblock write may be in progress, and we need to maintain
    // guarantees about its in-flight map state.
    && v.inFlight.None?

    && ReprBetree.Next(v.ephemeral.v, v'.ephemeral.v, ReprBetree.FreezeAsLabel(frozenMap))
    && v'.inFlight == Some(frozenMap)
    && v'.persistent == v.persistent // UNCHANGED
  }

  predicate EphemeralInternalNoGC(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.InternalLabel?  // allocs and freed given by ReprBetree.Next
    && lbl.allocations == {}
    && lbl.freed == {}
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && ReprBetree.Next(v.ephemeral.v, v'.ephemeral.v, ReprBetree.InternalLabel())
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate EphemeralInternalGC(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.InternalLabel?  // allocs and freed given by ReprBetree.Next
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && ReprBetree.Next(v.ephemeral.v, v'.ephemeral.v, ReprBetree.InternalMapGCLabel(lbl.allocations, lbl.freed))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }


  
  predicate CommitStart(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.CommitStartLabel?
    && lbl.allocations == {}
    && lbl.freed == {}
    && v.ephemeral.Known?
    && v.inFlight.Some?

    // Frozen map can't go backwards vs persistent map, lest we end up with
    // a gap to the ephemeral journal start.
    && v.persistent.stamped.seqEnd <= lbl.base.newBoundaryLsn
    // Frozen journal & frozen map agree on boundary.
    && lbl.base.newBoundaryLsn == v.inFlight.value.stamped.seqEnd

    && v' == v
  }

  predicate CommitComplete(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.CommitCompleteLabel?
    && lbl.allocations == {}
    && lbl.freed == {}
    && v.inFlight.Some?

    && v' == v.(
      // todo(tony): the old persistent shoud become freed/stranded?
      persistent := v.inFlight.value,
      // ephemeral unchanged
      inFlight := None)
  }

  predicate Crash(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.base.CrashLabel?
    && lbl.allocations == {}
    && lbl.freed == {}
    && v' == v.(
      ephemeral := Unknown,
      inFlight := None)
  }

  datatype Step =
    | LoadEphemeralFromPersistentStep()
    | PutRecordsStep()
    | QueryStep()
    | FreezeMapInternalStep(frozenMap: GCMap)
    | EphemeralInternalNoGCStep()
    | EphemeralInternalGCStep()
    | CommitStartStep()
    | CommitCompleteStep()
    | CrashStep()

  // Models mkfs
  predicate Init(v: Variables)
  {
    v == Variables(
      ReprBetree.GCStampedBetree({}, {}, LinkedBetreeMod.EmptyImage()), 
      Unknown, None)
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', lbl)
      case PutRecordsStep() => PutRecords(v, v', lbl)
      case QueryStep() => Query(v, v', lbl)
      case FreezeMapInternalStep(frozenMap) => FreezeMapInternal(v, v', lbl, frozenMap)
      case EphemeralInternalNoGCStep() => EphemeralInternalNoGC(v, v', lbl)
      case EphemeralInternalGCStep() => EphemeralInternalGC(v, v', lbl)
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

