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
    store.I().I().I()
  }

  function IALabel(lbl: TransitionLabel) : CrashTolerantJournal.TransitionLabel
    requires lbl.WF()
  {
    lbl
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
    PagedJournalRefinement.ILbl(lbl.I().I())
  }

  lemma LoadEphemeralFromPersistentRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.LoadEphemeralFromPersistentLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    MarshalledJournalRefinement.InvInit(v'.ephemeral.v, v.persistent);
    MarshalledJournalRefinement.RefinementInit(v'.ephemeral.v, v.persistent);
  }

  lemma ReadForRecoveryRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.ReadForRecoveryLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    JournalChainedNext(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.ReadForRecoveryLabel(lbl.records));
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
      lbl.I().I());
  }

//  lemma QueryEndLsnRefines(v: Variables, v': Variables, lbl: TransitionLabel)
//    requires Inv(v) && Next(v, v', lbl) && lbl.QueryEndLsnLabel?
//    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
//  {
//  }

  lemma PutRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.PutLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    MarshalledJournalRefinement.RefinementNext(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.PutLabel(lbl.records));
  }

//  lemma QueryLsnPersistenceRefines(v: Variables, v': Variables, lbl: TransitionLabel)
//    requires Inv(v) && Next(v, v', lbl) && lbl.QueryLsnPersistenceLabel?
//    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
//  {
//  }

  lemma InternalRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.InternalLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    JournalChainedNext(v.ephemeral.v, v'.ephemeral.v, MarshalledJournal.InternalLabel());

    var lbl := MarshalledJournal.InternalLabel();
    MarshalledJournalRefinement.RefinementNext(v.ephemeral.v, v'.ephemeral.v, lbl);
      
    if v'.inFlight.Some? {
      var inFlightL := v.inFlight.value.I();
      var ephemeralL := MarshalledJournalRefinement.I(v.ephemeral.v).truncatedJournal;
      var discardedL := ephemeralL.DiscardOld(inFlightL.SeqStart());
      LinkedJournalRefinement.BuildTightBuildsSubDisks(discardedL.diskView, discardedL.freshestRec);  // to pass lstep.addr membership through InFlightSubDiskProperty BuildTight

      LinkedJournalRefinement.InFlightSubDiskPreserved(
        MarshalledJournalRefinement.I(v.ephemeral.v),
        MarshalledJournalRefinement.I(v'.ephemeral.v),
        v.inFlight.value.I());
    }
    MarshalledJournalRefinement.TypedModelUnique(); // Completes persistent.IsSubDisk(ephemeral) proof.
  }

  lemma CommitStartRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.CommitStartLabel?
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
    requires Inv(v) && Next(v, v', lbl) && lbl.CommitCompleteLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    JournalChainedNext(v.ephemeral.v, v'.ephemeral.v,
      MarshalledJournal.DiscardOldLabel(v.inFlight.value.SeqStart(), lbl.requireEnd));
    MarshalledJournalRefinement.TypedModelUnique(); // Completes persistent.IsSubDisk(ephemeral) proof.
    v.inFlight.value.I().I().BuildReceipt().BoundaryLSN();  // MJ label seqStarT is AbstractJournal label SeqStart
  }

  lemma CrashRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.CrashLabel?
    ensures Inv(v') && CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
  }


  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Next(v, v', lbl)
    requires Inv(v)
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    match lbl {
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
}
