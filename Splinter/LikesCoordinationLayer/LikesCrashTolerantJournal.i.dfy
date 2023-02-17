include "../Journal/LikesJournal.i.dfy"
include "../CoordinationLayer/CrashTolerantJournal.i.dfy"

module LikesCrashTolerantJournal {
  import opened Options
  import opened GenericDisk
  import opened LikesMod
  import CrashTolerantJournal
  import LinkedJournal
  import LikesJournal

  // base label InternalLabel is the only one that has allocations
  datatype TransitionLabel = TransitionLabel(allocs: seq<Address>, base: CrashTolerantJournal.TransitionLabel)

  type StoreImage = LinkedJournal.TruncatedJournal

  datatype Ephemeral =
    | Unknown  // This means None
    | Known(v: LikesJournal.Variables)
  {
    predicate WF() {
      Known? ==> v.WF()
    }
  }

  datatype Variables = Variables(
    persistent: StoreImage,
    ephemeral: Ephemeral,
    inFlight: Option<StoreImage>
  ){
    predicate WF() {
      && persistent.WF()
      && ephemeral.WF()
      && (inFlight.Some? ==> inFlight.value.WF())
    }

    function Likes() : Likes {
      if ephemeral.Known?
      then ephemeral.v.ImperativeLikes()
      else LikesJournal.TjTransitiveLikes(persistent)
    }
  } // end datatype Variables

  
  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.LoadEphemeralFromPersistentLabel?
    && lbl.allocs == []
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?

    && LikesJournal.Init(v'.ephemeral.v, v.persistent)
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }
  
  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.ReadForRecoveryLabel?
    && lbl.allocs == []
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
  
    && LikesJournal.Next(v.ephemeral.v, v'.ephemeral.v, LikesJournal.ReadForRecoveryLabel(lbl.base.records))
    && v' == v  // everything UNCHANGED
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.QueryEndLsnLabel?
    && lbl.allocs == []
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && LikesJournal.Next(v.ephemeral.v, v'.ephemeral.v, LikesJournal.QueryEndLsnLabel(lbl.base.endLsn))
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.PutLabel?
    && lbl.allocs == []
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && LikesJournal.Next(v.ephemeral.v, v'.ephemeral.v, LikesJournal.PutLabel(lbl.base.records))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate Internal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.InternalLabel?
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && LikesJournal.Next(v.ephemeral.v, v'.ephemeral.v, LikesJournal.InternalLabel(lbl.allocs))
    && v'.persistent == v.persistent // UNCHANGED
    && v'.inFlight == v.inFlight // UNCHANGED
  }

  predicate QueryLsnPersistence(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.QueryLsnPersistenceLabel?
    && lbl.allocs == []
    && lbl.base.syncLsn <= v.persistent.SeqEnd()
    && v' == v
  }

  predicate CommitStart(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.CommitStartLabel?
    && lbl.allocs == []
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

    && LikesJournal.Next(v.ephemeral.v, v'.ephemeral.v, LikesJournal.FreezeForCommitLabel(frozenJournal))

    && v' == v.(
      ephemeral := v'.ephemeral,  // given by predicate above (but happens to be read-only / unchanged)
      inFlight := Some(frozenJournal) // given by predicates above
      )
  }

  predicate CommitComplete(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.CommitCompleteLabel?
    && lbl.allocs == []
    && v.ephemeral.Known?
    && v.inFlight.Some?
    && v'.ephemeral.Known?

    && LikesJournal.Next(v.ephemeral.v, v'.ephemeral.v,
        LikesJournal.DiscardOldLabel(v.inFlight.value.SeqStart(), lbl.base.requireEnd))

    && v' == v.(
      persistent := v.inFlight.value,
      ephemeral := v'.ephemeral,  // given by predicate above
      inFlight := None)
  }

  predicate Crash(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.base.CrashLabel?
    && lbl.allocs == []
    && v' == v.(
      ephemeral := Unknown,
      inFlight := None)
  }

  // Models mkfs
  predicate Init(v: Variables)
  {
    // TODO(tony): What is our default persistent here?
    v == Variables(LikesJournal.EmptyJournalImage(), Unknown, None)
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


} // end module LikesCrashTolerantJournal