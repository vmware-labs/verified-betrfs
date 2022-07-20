// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Journal/ReprJournal.i.dfy"
include "../Journal/LinkedJournal.i.dfy"
include "../CoordinationLayer/CrashTolerantJournal.i.dfy"

// TODO(jonh): This is a copy-paste of Splinter/CoordinationSystem/CrashTolerantJournal. Functor-reuse?

module CrashTolerantReprJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened GenericDisk
  import LinkedJournal
  import ReprJournal
  import CrashTolerantJournal

  datatype TransitionLabel = TransitionLabel(allocations: seq<Address>, freed: seq<Address>, base: CrashTolerantJournal.TransitionLabel)

  type StoreImage = LinkedJournal.TruncatedJournal

  datatype Ephemeral =
    | Unknown
    | Known(v: ReprJournal.Variables)
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

    // function Repr() : set<Address>
    // {
    //   if ephemeral.Known?
    //   then ephemeral.v.journal.truncatedJournal.Representation()
    //   else persistent.Representation()
    // }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && v.WF()
    && lbl.base.LoadEphemeralFromPersistentLabel?
    && lbl.allocations == []
    && lbl.freed == []
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?
    // State update
    && ReprJournal.Init(v'.ephemeral.v, v.persistent)
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && v.WF()
    && lbl.base.ReadForRecoveryLabel?
    && lbl.allocations == []
    && lbl.freed == []
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    // State update
    && ReprJournal.Next(v.ephemeral.v, v'.ephemeral.v, ReprJournal.ReadForRecoveryLabel(lbl.base.records))
    && v' == v  // everything UNCHANGED
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && v.WF()
    && lbl.base.QueryEndLsnLabel?
    && lbl.allocations == []
    && lbl.freed == []
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    // State update
    && ReprJournal.Next(v.ephemeral.v, v'.ephemeral.v, ReprJournal.QueryEndLsnLabel(lbl.base.endLsn))
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.PutLabel?
    && lbl.allocations == []
    && lbl.freed == []
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && ReprJournal.Next(v.ephemeral.v, v'.ephemeral.v, ReprJournal.PutLabel(lbl.base.records))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate Internal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.InternalLabel?
    && |lbl.allocations| == 1
    && lbl.freed == []
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && ReprJournal.Next(v.ephemeral.v, v'.ephemeral.v, ReprJournal.InternalLabel(lbl.allocations[0]))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate QueryLsnPersistence(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.QueryLsnPersistenceLabel?
    && lbl.allocations == []
    && lbl.freed == []
    && lbl.base.syncLsn <= v.persistent.SeqEnd()
    && v' == v
  }

  predicate CommitStart(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.CommitStartLabel?
    && lbl.allocations == []
    && lbl.freed == []
    && v.ephemeral.Known?
    // Can't start a commit if one is in-flight, or we'd forget to maintain the
    // invariants for the in-flight one.
    && v.inFlight.None?
    && v'.ephemeral.Known?
    && v'.inFlight.Some?

    && var frozenJournal := v'.inFlight.value;

    // Frozen journal stitches to frozen map
    && frozenJournal.SeqStart() == lbl.base.newBoundaryLsn

    // Journal doesn't go backwards
    && frozenJournal.WF()
    && v.persistent.SeqEnd() <= frozenJournal.SeqEnd()

    // There should be no way for the frozen journal to have passed the ephemeral map!
    && frozenJournal.SeqStart() <= lbl.base.maxLsn

    && ReprJournal.Next(v.ephemeral.v, v'.ephemeral.v, ReprJournal.FreezeForCommitLabel(frozenJournal))

    && v' == v.(
      ephemeral := v'.ephemeral,  // given by predicate above (but happens to be read-only / unchanged)
      inFlight := Some(frozenJournal) // given by predicates above
      )
  }

  predicate CommitComplete(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.CommitCompleteLabel?
    && lbl.allocations == []
    && v.ephemeral.Known?
    && v.inFlight.Some?
    && v'.ephemeral.Known?

    && ReprJournal.Next(v.ephemeral.v, v'.ephemeral.v,
        ReprJournal.DiscardOldLabel(v.inFlight.value.SeqStart(), lbl.base.requireEnd, lbl.freed))

    && v' == v.(
      persistent := v.inFlight.value,
      ephemeral := v'.ephemeral,  // given by predicate above
      inFlight := None)
  }

  predicate Crash(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.CrashLabel?
    && lbl.allocations == []
    && lbl.freed == []
    && v' == v.(
      ephemeral := Unknown,
      inFlight := None)
  }

  // Models mkfs
  predicate Init(v: Variables)
  {
    v == Variables(LinkedJournal.Mkfs(), Unknown, None)
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    match lbl.base {
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

