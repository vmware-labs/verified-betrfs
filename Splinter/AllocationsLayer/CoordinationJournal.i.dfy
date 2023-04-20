// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "AllocationJournal.i.dfy"

module CoordinationJournal {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened StampedMod
  import opened MsgHistoryMod
  import opened LSNMod

  import GenericDisk
  import AllocationJournal

  type AU = GenericDisk.AU

  datatype TransitionLabel =
    | LoadEphemeralFromPersistentLabel()
    | ReadForRecoveryLabel(records: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(records: MsgHistory)
    | FreezeAsLabel(unobserved: set<AU>)
    | InternalLabel(allocs: set<AU>, deallocs: set<AU>)
    | QueryLsnPersistenceLabel(syncLsn: LSN)
    | CommitStartLabel(newBoundaryLsn: LSN, maxLsn: LSN)
    | CommitCompleteLabel(requireEnd: LSN, discarded: set<AU>)
    | CrashLabel()

  type StoreImage = AllocationJournal.JournalImage

  datatype Ephemeral =
    | Unknown  // This means Nones
    | Known(v: AllocationJournal.Variables)
  {
    predicate WF() {
      Known? ==> v.WF()
    }
  }

  datatype Variables = Variables(
    persistent: StoreImage,
    ephemeral: Ephemeral,
    inFlight: Option<StoreImage>
  )
  {
    predicate WF() {
      && persistent.WF()
      && ephemeral.WF()
      && (inFlight.Some? ==> inFlight.value.WF())
    }

    function EphemeralAUs() : set<AU>
      requires ephemeral.Known?
    {
      ephemeral.v.AccessibleAUs()
    }

    function PersistentAUs() : set<AU>
    {
      persistent.AccessibleAUs()
    }

    function InFlightAUs() : set<AU>
      requires inFlight.Some?
    {
      inFlight.value.AccessibleAUs()
    }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.LoadEphemeralFromPersistentLabel?
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?

    && AllocationJournal.Init(v'.ephemeral.v, v.persistent)
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.ReadForRecoveryLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
  
    && AllocationJournal.Next(v.ephemeral.v, v'.ephemeral.v, AllocationJournal.ReadForRecoveryLabel(lbl.records))
    && v' == v  // everything UNCHANGED
  }
  
  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.QueryEndLsnLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && AllocationJournal.Next(v.ephemeral.v, v'.ephemeral.v, AllocationJournal.QueryEndLsnLabel(lbl.endLsn))
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.PutLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && AllocationJournal.Next(v.ephemeral.v, v'.ephemeral.v, AllocationJournal.PutLabel(lbl.records))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate Internal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.InternalLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && AllocationJournal.Next(v.ephemeral.v, v'.ephemeral.v, 
      AllocationJournal.InternalAllocationsLabel(lbl.allocs, lbl.deallocs))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate QueryLsnPersistence(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.QueryLsnPersistenceLabel?
    && lbl.syncLsn <= v.persistent.tj.SeqEnd()
    && v' == v
  }

  predicate FreezeUnobserved(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.FreezeAsLabel?
    && v.ephemeral.Known?
    && v.inFlight.None?
    && lbl.unobserved == v.ephemeral.v.UnobservedAUs()
    && var frozenJournal := AllocationJournal.JournalImage(v.ephemeral.v.journal.journal.truncatedJournal, v.ephemeral.v.first);
    && v' == v.(
      inFlight := Some(frozenJournal)
    )
    // && v' == v
  }

  predicate CommitStart(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.CommitStartLabel?
    && v.ephemeral.Known?
    // Can't start a commit if one is in-flight, or we'd forget to maintain the
    // invariants for the in-flight one.
    // && v.inFlight.None?
    && v.inFlight.Some?
    && v'.ephemeral.Known?
    // && v'.inFlight.Some?

    && var frozenJournal := v.inFlight.value;
    && AllocationJournal.Next(v.ephemeral.v, v'.ephemeral.v, 
      AllocationJournal.FreezeForCommitLabel(frozenJournal))

    // Frozen journal stitches to frozen map
    && frozenJournal.tj.SeqStart() == lbl.newBoundaryLsn

    // Journal doesn't go backwards
    && v.persistent.tj.SeqEnd() <= frozenJournal.tj.SeqEnd()

    // There should be no way for the frozen journal to have passed the ephemeral map!
    && frozenJournal.tj.SeqStart() <= lbl.maxLsn

    && v' == v.(
      ephemeral := v'.ephemeral  // given by predicate above (but happens to be read-only / unchanged)
      // inFlight := Some(frozenJournal) // given by predicates above
      )
  }

  // Observe that the persistent journal is always a prefix of the Ephemeral Journal
  predicate CommitComplete(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.CommitCompleteLabel?
    && v.ephemeral.Known?
    && v.inFlight.Some?
    && v'.ephemeral.Known?

    && AllocationJournal.Next(v.ephemeral.v, v'.ephemeral.v,
        AllocationJournal.DiscardOldLabel(v.inFlight.value.tj.SeqStart(), lbl.requireEnd, lbl.discarded))

    && v' == v.(
      persistent := v.inFlight.value,
      ephemeral := v'.ephemeral,  // given by predicate above
      inFlight := None)
  }

  predicate Crash(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.CrashLabel?
    && v' == v.(
      ephemeral := Unknown,
      inFlight := None)
  }

  predicate Init(v: Variables)
  {
    v == Variables(AllocationJournal.EmptyJournalImage(), Unknown, None)
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    match lbl {
      case LoadEphemeralFromPersistentLabel() => LoadEphemeralFromPersistent(v, v', lbl)
      case ReadForRecoveryLabel(_) => ReadForRecovery(v, v', lbl)
      case QueryEndLsnLabel(_) => QueryEndLsn(v, v', lbl)
      case PutLabel(_) => Put(v, v', lbl)
      case InternalLabel(_, _) => Internal(v, v', lbl)
      case QueryLsnPersistenceLabel(_) => QueryLsnPersistence(v, v', lbl)
      case FreezeAsLabel(_) => FreezeUnobserved(v, v', lbl)
      case CommitStartLabel(_, _) => CommitStart(v, v', lbl)
      case CommitCompleteLabel(_, _) => CommitComplete(v, v', lbl)
      case CrashLabel() => Crash(v, v', lbl)
    }
  }
}

