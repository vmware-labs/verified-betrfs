// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BlockCrashTolerantJournal.i.dfy"
include "../Journal/MarshalledJournalRefinement.i.dfy"
include "../CoordinationLayer/CrashTolerantJournal.i.dfy"

module BlockCrashTolerantJournalRefinement {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened LSNMod
  import opened GenericDisk
  import CrashTolerantJournal 
  import PagedJournalRefinement 
  import AbstractJournal
  import PagedJournal
  import LinkedJournal
  import MarshalledJournal
  import LinkedJournalRefinement 
  import MarshalledJournalRefinement 
  import opened BlockCrashTolerantJournal 

  predicate DecodableImage(store: StoreImage)
  {
    && store.WF()
    && store.I().Decodable()
  }

  function IImage(store: StoreImage) : CrashTolerantJournal.StoreImage
    requires DecodableImage(store)
  {
    PagedJournalRefinement.ITruncatedJournal(
      LinkedJournalRefinement.ITruncatedJournal(
        store.I()))
  }

  function IALabel(lbl: TransitionLabel) : CrashTolerantJournal.TransitionLabel
  {
    lbl.base
  }

  predicate Decodable(v: Variables)
  {
    && DecodableImage(v.persistent)
    && (v.ephemeral.Known? ==> MarshalledJournalRefinement.Inv(v.ephemeral.v))
    && (v.inFlight.Some? ==> DecodableImage(v.inFlight.value))
  }

  function IMJ(mv: MarshalledJournal.Variables) : AbstractJournal.Variables
    requires mv.WF()
    requires MarshalledJournalRefinement.Inv(mv)
  {
    PagedJournalRefinement.I(LinkedJournalRefinement.I(MarshalledJournalRefinement.I(mv)))
  }

  function I(v: Variables) : CrashTolerantJournal.Variables
    requires Decodable(v)
  {
    CrashTolerantJournal.Variables(
      IImage(v.persistent),
      if v.ephemeral.Unknown?  then CrashTolerantJournal.Unknown else CrashTolerantJournal.Known(IMJ(v.ephemeral.v)),
      if v.inFlight.None? then None else Some(IImage(v.inFlight.value))
    )
  }

  predicate Inv(v: Variables)
  {
    && Decodable(v)
    && (v.ephemeral.Known? ==> v.persistent.I().diskView.IsSubDisk(v.ephemeral.v.journalImage.I().diskView))
    && (v.inFlight.Some? ==>
        && v.ephemeral.Known?
        && LinkedJournalRefinement.InFlightSubDiskProperty(
            MarshalledJournalRefinement.I(v.ephemeral.v), v.inFlight.value.I())
      )
  }

  lemma InitRefines(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures CrashTolerantJournal.Init(I(v))
  {
    assert v.persistent.I().diskView.PointersRespectRank(map[]);  // Decodable requires Acyclic.
  }

  // Maybe this belongs in MarshalledJournal specifically?
  predicate DecodableMJLabel(lbl: MarshalledJournal.TransitionLabel) {
    && lbl.WF()
    && lbl.I().WF()
  }
  function IAMJLabel(lbl: MarshalledJournal.TransitionLabel) : AbstractJournal.TransitionLabel
    requires DecodableMJLabel(lbl)
  {
    PagedJournalRefinement.ILbl(LinkedJournalRefinement.ILbl(lbl.I()))
  }

  lemma LoadEphemeralFromPersistentRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.LoadEphemeralFromPersistentLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    MarshalledJournalRefinement.InvInit(v'.ephemeral.v, v.persistent);
    MarshalledJournalRefinement.RefinementInit(v'.ephemeral.v, v.persistent);
  }

  lemma ReadForRecoveryRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.ReadForRecoveryLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    JournalChainedNext(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.ReadForRecoveryLabel(lbl.base.records));
  }

  lemma JournalChainedNext(j: MarshalledJournal.Variables, j': MarshalledJournal.Variables, lbl: MarshalledJournal.TransitionLabel)
    requires MarshalledJournalRefinement.Inv(j)
    requires MarshalledJournal.Next(j, j', lbl)
    ensures MarshalledJournalRefinement.Inv(j')
    ensures AbstractJournal.Next(IMJ(j), IMJ(j'), IAMJLabel(lbl))
  {
    MarshalledJournalRefinement.RefinementNext(j, j', lbl);
    // TODO(jonh): inconsistent theorem naming: RefinementNext vs NextRefines
    LinkedJournalRefinement.NextRefines(
      MarshalledJournalRefinement.I(j),
      MarshalledJournalRefinement.I(j'),
      lbl.I());
    PagedJournalRefinement.NextRefines(
      LinkedJournalRefinement.I(MarshalledJournalRefinement.I(j)),
      LinkedJournalRefinement.I(MarshalledJournalRefinement.I(j')),
      LinkedJournalRefinement.ILbl(lbl.I()));
  }

//  lemma QueryEndLsnRefines(v: Variables, v': Variables, lbl: TransitionLabel)
//    requires Inv(v) && Next(v, v', lbl) && lbl.base.QueryEndLsnLabel?
//    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
//  {
//  }

  lemma {:timeLimitMultiplier 2} PutRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.PutLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    MarshalledJournalRefinement.RefinementNext(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.PutLabel(lbl.base.records));
  }

//  lemma QueryLsnPersistenceRefines(v: Variables, v': Variables, lbl: TransitionLabel)
//    requires Inv(v) && Next(v, v', lbl) && lbl.base.QueryLsnPersistenceLabel?
//    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
//  {
//  }

  lemma InternalRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.InternalLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    var jlbl := MarshalledJournal.InternalLabel(lbl.allocations);

    JournalChainedNext(v.ephemeral.v, v'.ephemeral.v, jlbl);

    MarshalledJournalRefinement.RefinementNext(v.ephemeral.v, v'.ephemeral.v, jlbl);
      
    if v'.inFlight.Some? {
      var inFlightL := v.inFlight.value.I();
      var ephemeralL := MarshalledJournalRefinement.I(v.ephemeral.v).truncatedJournal;
      var discardedL := ephemeralL.DiscardOld(inFlightL.SeqStart());
      LinkedJournalRefinement.BuildTightBuildsSubDisks(discardedL.diskView, discardedL.freshestRec);  // to pass lstep.addr membership through InFlightSubDiskProperty BuildTight

      LinkedJournalRefinement.InFlightSubDiskPreserved(
        MarshalledJournalRefinement.I(v.ephemeral.v),
        MarshalledJournalRefinement.I(v'.ephemeral.v),
        v.inFlight.value.I(),
        jlbl.I());
    }
    MarshalledJournalRefinement.TypedModelUnique(); // Completes persistent.IsSubDisk(ephemeral) proof.
  }

  lemma CommitStartRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.CommitStartLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    var frozenJournal := v'.inFlight.value;
    JournalChainedNext(v.ephemeral.v, v'.ephemeral.v,
      MarshalledJournal.FreezeForCommitLabel(frozenJournal));

    var mjlbl := MarshalledJournal.FreezeForCommitLabel(frozenJournal);
    MarshalledJournalRefinement.RefinementNext(v.ephemeral.v, v'.ephemeral.v, mjlbl);  // hoist one layer to LinkedJournal. (JournalChainedNext hides this jump)
    LinkedJournalRefinement.InFlightSubDiskCreated(
      MarshalledJournalRefinement.I(v.ephemeral.v),
      MarshalledJournalRefinement.I(v'.ephemeral.v),
      mjlbl.I());
  }

  lemma CommitCompleteRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.CommitCompleteLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    JournalChainedNext(v.ephemeral.v, v'.ephemeral.v,
      MarshalledJournal.DiscardOldLabel(v.inFlight.value.SeqStart(), lbl.base.requireEnd));
    MarshalledJournalRefinement.TypedModelUnique(); // Completes persistent.IsSubDisk(ephemeral) proof.
//    LinkedJournalRefinement.ITruncatedJournal(v.inFlight.value.I()).BuildReceipt().BoundaryLSN();  // MJ label seqStarT is AbstractJournal label SeqStart
  }

  lemma CrashRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.CrashLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
  }


  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    match lbl.base {
      case LoadEphemeralFromPersistentLabel() => { LoadEphemeralFromPersistentRefines(v, v', lbl); }
      case ReadForRecoveryLabel(_) => { ReadForRecoveryRefines(v, v', lbl); }
      case QueryEndLsnLabel(_) => { /*QueryEndLsnRefines(v, v', lbl);*/ }
      case PutLabel(_) => { PutRefines(v, v', lbl); }
      case InternalLabel() => { InternalRefines(v, v', lbl); }
      case QueryLsnPersistenceLabel(_) => { /*QueryLsnPersistenceRefines(v, v', lbl);*/ }
      case CommitStartLabel(_, _) => { CommitStartRefines(v, v', lbl); }
      case CommitCompleteLabel(_) => { CommitCompleteRefines(v, v', lbl); }
      case CrashLabel() => { CrashRefines(v, v', lbl); }
    }
  }

  //////////////////////////////////////////////////////////////////////////
  // Framing obligations

  function ImageRepr(s: StoreImage) : set<Address>
  {
    s.diskView.entries.Keys
  }

  function Repr(v: Variables) : set<Address>
  {
      ImageRepr(v.persistent)
    + (if v.ephemeral.Known? then ImageRepr(v.ephemeral.v.journalImage) else {})
    + (if v.inFlight.Some? then ImageRepr(v.inFlight.value) else {})
  }

  lemma ImageFraming(s1: StoreImage, s2: StoreImage)
    requires DecodableImage(s1)
    requires s1.diskView == s2.diskView // well, duh, I guess. This isn't very interesting.
    requires s1.superblock == s2.superblock
    ensures DecodableImage(s2)
    ensures IImage(s1) == IImage(s2)
  {
  }

/*
  predicate DisksAgree(v1: Variables, v2: Variables)
  {
    && v1.persistent.diskView.AgreesWithDisk(s2.persistent.diskView)
    && 
    && (v.ephemeral.Known? ==> v.ephemeral.v.journalImage.diskView.AgreesWithDisk(v.persistent.diskView))
    && (v.inFlight.Some? ==> v.inFlight.value.diskView.AgreesWithDisk(v.persistent.diskView))
  }

nonsense -- in-memory part needs to be compatible too
  lemma Framing(v1: Variables, v2: Variables)
    requires Decodable(v1)
    requires DisksAgree(v1, v2)
    ensures Decodable(v2)
    ensures I(v1) == I(v2)
  {
  }
*/

  lemma UpdatesInternal(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    requires lbl.base.InternalLabel?
    ensures Repr(v') <= Repr(v) + lbl.allocations
  {
  }

  lemma Updates(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Repr(v') <= Repr(v) + lbl.allocations
    // what good is this <=?
  {
    match lbl.base {
      case LoadEphemeralFromPersistentLabel() => { }
      case ReadForRecoveryLabel(_) => { }
      case QueryEndLsnLabel(_) => { }
      case PutLabel(_) => { }
      case InternalLabel() => { UpdatesInternal(v, v', lbl); }
      case QueryLsnPersistenceLabel(_) => { }
      case CommitStartLabel(_, _) => {
        // introduce inFlight
//        var eph := v'.ephemeral.v.journalImage;
//        var do := v.ephemeral.v.journalImage.truncatedJournal.DiscardOld(v.inFlight.value.SeqStart());
//        var tight := do.BuildTight();
//        assert ImageRepr(v'.inFlight.value) == ImageRepr(tight);
//        assert ImageRepr(tight) <= ImageRepr(do);
//        assert ImageRepr(do) <= ImageRepr(eph);
//        assert ImageRepr(v'.inFlight.value) <= ImageRepr(v'.ephemeral.v.journalImage);
//        assert Repr(v') == Repr(v);
        //assume false;
      }
      case CommitCompleteLabel(_) => {
      }
      case CrashLabel() => {
        // um, in-flight commit modeling is a little weird -- in-flight disk
        // becomes persistent before we hear about it in CommitComplete.
        // Probably going to need to split the step into CommitComplete (which
        // changes the persistent state on the disk) and LearnCommit (which
        // changes the program's model of the persistent state).

        // forgets ephemeral & in-flight
      }
    }
  }
}
