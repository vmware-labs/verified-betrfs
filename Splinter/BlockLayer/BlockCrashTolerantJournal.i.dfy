// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Journal/MarshalledJournal.i.dfy"
include "../CoordinationLayer/CrashTolerantJournal.i.dfy"

// TODO(jonh): This is a copy-paste of Splinter/CoordinationSystem/CrashTolerantJournal. Functor-reuse?

module BlockCrashTolerantJournal {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened LSNMod
  import MarshalledJournal
  import CrashTolerantJournal

  // TODO lazy
  type TransitionLabel = CrashTolerantJournal.TransitionLabel
    
  type StoreImage = MarshalledJournal.JournalImage

  datatype Ephemeral =
    | Unknown
    | Known(v: MarshalledJournal.Variables)
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
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.LoadEphemeralFromPersistentLabel?
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?

    && MarshalledJournal.Init(v'.ephemeral.v, v.persistent)
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }
  
  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.ReadForRecoveryLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
  
    && MarshalledJournal.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.ReadForRecoveryLabel(lbl.records))
    && v' == v  // everything UNCHANGED
  }
  
  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.QueryEndLsnLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && MarshalledJournal.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.QueryEndLsnLabel(lbl.endLsn))
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.PutLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && MarshalledJournal.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.PutLabel(lbl.records))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate Internal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && MarshalledJournal.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.InternalLabel())
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate QueryLsnPersistence(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.QueryLsnPersistenceLabel?
    && lbl.syncLsn <= v.persistent.SeqEnd()
    && v' == v
  }

  predicate CommitStart(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.CommitStartLabel?
    && v.ephemeral.Known?
    // Can't start a commit if one is in-flight, or we'd forget to maintain the
    // invariants for the in-flight one.
    && v.inFlight.None?
    && v'.ephemeral.Known?
    && v'.inFlight.Some?

    && var frozenJournal := v'.inFlight.value;

    // Frozen journal stitches to frozen map
    && frozenJournal.SeqStart() == lbl.newBoundaryLsn

    // Journal doesn't go backwards
    && frozenJournal.WF()
    && v.persistent.SeqEnd() <= frozenJournal.SeqEnd()

    // There should be no way for the frozen journal to have passed the ephemeral map!
    && frozenJournal.SeqStart() <= lbl.maxLsn

    && MarshalledJournal.Next(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.FreezeForCommitLabel(frozenJournal))

    && v' == v.(
      ephemeral := v'.ephemeral,  // given by predicate above (but happens to be read-only / unchanged)
      inFlight := Some(frozenJournal) // given by predicates above
      )
  }

  predicate CommitComplete(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.CommitCompleteLabel?
    && v.ephemeral.Known?
    && v.inFlight.Some?
    && v'.ephemeral.Known?

    && MarshalledJournal.Next(v.ephemeral.v, v'.ephemeral.v,
        MarshalledJournal.DiscardOldLabel(v.inFlight.value.SeqStart(), lbl.requireEnd))

    && v' == v.(
      persistent := v.inFlight.value,
      ephemeral := v'.ephemeral,  // given by predicate above
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

  // Models mkfs
  predicate Init(v: Variables)
  {
    v == Variables(MarshalledJournal.EmptyJournalImage(), Unknown, None)
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    match lbl {
      case LoadEphemeralFromPersistentLabel() => LoadEphemeralFromPersistent(v, v', lbl)
      case ReadForRecoveryLabel(_) => ReadForRecovery(v, v', lbl)
      case QueryEndLsnLabel(_) => QueryEndLsn(v, v', lbl)
      case PutLabel(_) => Put(v, v', lbl)
      case InternalLabel() => Internal(v, v', lbl)
      case QueryLsnPersistenceLabel(_) => QueryLsnPersistence(v, v', lbl)
      case CommitStartLabel(_, _) => CommitStart(v, v', lbl)
      case CommitCompleteLabel(_) => CommitComplete(v, v', lbl)
      case CrashLabel() => Crash(v, v', lbl)
    }
  }
}

