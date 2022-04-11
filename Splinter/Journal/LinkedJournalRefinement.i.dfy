// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournal.i.dfy"
include "PagedJournalRefinement.i.dfy"

module LinkedJournalRefinement
// TODO refines RefinementObligation(JournalLabels, PagedJournal)
{
  import opened Options
  import opened Maps
  import opened MsgHistoryMod
  import opened LSNMod
  import PagedJournal
  import PagedJournalRefinement
  import opened LinkedJournal

  predicate Inv(v: Variables)
  {
    && v.WF()
    && v.truncatedJournal.Decodable()
  }
  
  function I(v: Variables) : PagedJournal.Variables
    requires v.WF()
    requires v.truncatedJournal.diskView.Acyclic()
  {
    PagedJournal.Variables(v.truncatedJournal.I(), v.unmarshalledTail)
  }

  lemma IPtrFraming(dv1: DiskView, dv2: DiskView, ptr: Pointer)
    requires dv1.WF() && dv1.Acyclic()
    requires dv2.WF() && dv2.Acyclic()
    requires dv1.IsNondanglingPointer(ptr)
    requires dv1.IsSubDisk(dv2)
    requires dv1.boundaryLSN == dv2.boundaryLSN
    ensures dv1.IPtr(ptr) == dv2.IPtr(ptr)
    decreases dv1.TheRankOf(ptr)
  {
    if ptr.Some? {
      IPtrFraming(dv1, dv2, dv1.entries[ptr.value].CroppedPrior(dv1.boundaryLSN));
    }
  }

  lemma BuildTightRanks(dv: DiskView, ptr: Pointer)
    requires dv.Decodable(ptr)
    requires dv.Acyclic()
    requires ptr.Some?
    ensures
      var next := dv.entries[ptr.value].CroppedPrior(dv.boundaryLSN);
      forall addr | addr in dv.BuildTight(next).entries :: addr in dv.TheRanking() && dv.TheRanking()[addr] < dv.TheRanking()[ptr.value]
    decreases dv.TheRankOf(ptr)
  {
    var next := dv.entries[ptr.value].CroppedPrior(dv.boundaryLSN);
    if next.Some? {
      BuildTightRanks(dv, next);
    }
  }

  lemma BuildTightShape(big: DiskView, root: Pointer)
    requires root.Some?
    requires big.Decodable(root)
    requires big.Acyclic()
    ensures
      big.BuildTight(big.entries[root.value].CroppedPrior(big.boundaryLSN)) ==
      DiskView(big.boundaryLSN, MapRemove1(big.BuildTight(root).entries, root.value))
  {
    var next := big.entries[root.value].CroppedPrior(big.boundaryLSN);
    if next.Some? {
      BuildTightRanks(big, root);  // proves root.value !in big.BuildTight(next, ranking).entries;
    }
  }

  lemma IPtrIgnoresExtraBlocks(small: DiskView, ptr: Pointer, big: DiskView)
    requires small.WF()
    requires small.IsNondanglingPointer(ptr)
    requires big.WF()
    requires big.Acyclic()
    requires small.IsSubDisk(big)
    ensures small.Acyclic()
    ensures big.IPtr(ptr) == small.IPtr(ptr)
    decreases big.TheRankOf(ptr)
  {
    assert small.PointersRespectRank(big.TheRanking()); // witness to small.Acyclic
    if ptr.Some? {
      var next := big.entries[ptr.value].CroppedPrior(big.boundaryLSN);
      IPtrIgnoresExtraBlocks(small, next, big);
      assert big.IPtr(ptr) == small.IPtr(ptr);
    }
  }

  lemma TightSubDisk(big: DiskView, root: Pointer, tight: DiskView)
    requires big.Decodable(root)
    requires tight == big.BuildTight(root)
    requires big.Acyclic()
    requires tight.IsSubDisk(big);
    ensures tight.IsTight(root)
    decreases big.TheRankOf(root)
  {
    if root.Some? {
      var next := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      var inner := big.BuildTight(next);
      BuildTightShape(big, root);
      TightSubDisk(big, next, inner);

      forall other:DiskView | && other.Decodable(root) && tight.IPtr(root) == other.IPtr(root) && other.IsSubDisk(tight)
          ensures other == tight {
        // any other tighter disk implies an "otherInner" disk tighter than inner, but inner.IsTight(next).
        var otherInner := DiskView(other.boundaryLSN, MapRemove1(other.entries, root.value));
        assert inner.PointersRespectRank(big.TheRanking());
        IPtrIgnoresExtraBlocks(otherInner, next, inner);
      }
    }
  }

  lemma BuildTightBuildsSubDisks(big: DiskView, root: Pointer)
    requires big.Decodable(root)
    requires big.Acyclic()
    ensures big.BuildTight(root).IsSubDisk(big)
    decreases big.TheRankOf(root)
  {
    if root.Some? {
      var next := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      BuildTightBuildsSubDisks(big, next);
    }
  }

  lemma TightInterp(big: DiskView, root: Pointer, tight: DiskView)
    requires big.Decodable(root)
    requires tight == big.BuildTight(root)
    requires big.Acyclic()
    ensures tight.IsSubDisk(big)
    ensures tight.IsTight(root)
    ensures tight.Decodable(root)
    ensures tight.IPtr(root) == big.IPtr(root)
    ensures tight.Acyclic()
    decreases big.TheRankOf(root)
  {
    if root.None? {
      assert tight.PointersRespectRank(big.TheRanking());
    } else {
      BuildTightBuildsSubDisks(big, root);
      TightSubDisk(big, root, tight);
      assert tight.PointersRespectRank(big.TheRanking());  // witness to Acyclic
      IPtrIgnoresExtraBlocks(tight, root, big);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // non-state-machine function & predicate refinement lemmas

  lemma MkfsRefines()
    ensures Mkfs().diskView.Acyclic()
    ensures Mkfs().I() == PagedJournal.Mkfs()
  {
    assert Mkfs().diskView.PointersRespectRank(map[]);  // witness to exists ranking
  }

  //////////////////////////////////////////////////////////////////////////////
  // State machine refinement

  lemma InvInit(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures Inv(v)
  {
  }

  lemma DiscardInterp(dv: DiskView, lsn: LSN, discarded: DiskView, ptr: Pointer)
    requires dv.WF()
    requires dv.Acyclic()
    requires dv.boundaryLSN <= lsn
    requires discarded == dv.DiscardOld(lsn)
    requires dv.IsNondanglingPointer(ptr)
    ensures discarded.Acyclic()
    ensures discarded.IPtr(ptr) == PagedJournal.DiscardOldJournalRec(dv.IPtr(ptr), lsn)
    decreases if ptr.Some? then dv.TheRanking()[ptr.value] else -1
  {
    assert discarded.PointersRespectRank(dv.TheRanking());
    if ptr.Some? && !(dv.entries[ptr.value].messageSeq.seqStart <= lsn) {
      DiscardInterp(dv, lsn, discarded, discarded.entries[ptr.value].CroppedPrior(discarded.boundaryLSN));
    }
  }

  lemma DiscardHarder(tj: TruncatedJournal, lsn: LSN, discarded: TruncatedJournal)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.I().WF()
    requires tj.I().I().CanDiscardTo(lsn)
    requires tj.SeqStart() <= lsn
    requires discarded == tj.DiscardOld(lsn)
    ensures discarded.diskView.Acyclic();
    ensures tj.I().WF();
    ensures tj.I().DiscardOld(lsn) == discarded.I()
  {
    assert discarded.diskView.PointersRespectRank(tj.diskView.TheRanking());
    DiscardInterp(tj.diskView, lsn, discarded.diskView, tj.freshestRec);
  }
    
  lemma SubDiskInterp(small: DiskView, big: DiskView, ptr: Pointer)
    requires big.WF()
    requires big.Acyclic()
    requires small.WF()
    requires small.IsSubDisk(big)
    requires small.boundaryLSN == big.boundaryLSN
    requires small.IsNondanglingPointer(ptr)
    ensures small.Acyclic()
    ensures small.IPtr(ptr) == big.IPtr(ptr)
    decreases if ptr.Some? then big.TheRanking()[ptr.value] else -1
  {
    assert small.PointersRespectRank(big.TheRanking());
    if ptr.Some? {
      var jr := big.entries[ptr.value];
      SubDiskInterp(small, big, jr.CroppedPrior(big.boundaryLSN));
    }
  }
    
  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    var step: Step :| NextStep(v, v', lbl, step);
    if step.ReadForRecoveryStep? {
      assert Inv(v');
    } else if step.FreezeForCommitStep? {
      assert Inv(v');
    } else if step.ObserveFreshJournalStep? {
      assert Inv(v');
    } else if step.PutStep? {
      assert Inv(v');
    } else if step.DiscardOldStep? {
      var lsn := lbl.startLsn;
      var croppedTJ := v.truncatedJournal.DiscardOld(lsn);
      var tightTJ := croppedTJ.BuildTight();

      assert croppedTJ.diskView.PointersRespectRank(v.truncatedJournal.diskView.TheRanking());  // witness to Acyclic
      TightInterp(croppedTJ.diskView, croppedTJ.freshestRec, tightTJ.diskView);

      if !(v.unmarshalledTail.seqStart <= lsn) {
        assert v.SeqStart() == v.truncatedJournal.I().I().seqStart by { v.truncatedJournal.I().BuildReceipt().TJFacts(); }
        DiscardInterp(croppedTJ.diskView, lsn, croppedTJ.diskView.DiscardOld(lsn), v.truncatedJournal.freshestRec);
        SubDiskInterp(tightTJ.diskView, croppedTJ.diskView, croppedTJ.freshestRec);
        DiscardHarder(v.truncatedJournal, lsn, croppedTJ);
        assert croppedTJ.I() == v.truncatedJournal.I().DiscardOld(lsn); // Trigger for v'.I().WF()
      }
//      assert Inv(v');
    } else if step.InternalJournalMarshalStep? {
      var rank :| v.truncatedJournal.diskView.PointersRespectRank(rank);
      var rank' := rank[step.addr :=
          if v.truncatedJournal.freshestRec.None? then 0
          else rank[v.truncatedJournal.freshestRec.value]+1];
      assert v'.truncatedJournal.diskView.PointersRespectRank(rank'); // new rank witness to Acyclic

      IPtrFraming(v.truncatedJournal.diskView, v'.truncatedJournal.diskView, v.truncatedJournal.freshestRec);
//      assert Inv(v');
    } else {
      assert false;
    }
  }

  lemma InitRefines(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures PagedJournal.Init(I(v), tj.I())
  {
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures PagedJournal.Next(I(v), I(v'), lbl.I())
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    if step.ReadForRecoveryStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl.I(), PagedJournal.ReadForRecoveryStep(step.receiptIndex)); // witness step
    } else if step.FreezeForCommitStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl.I(), PagedJournal.FreezeForCommitStep(step.keepReceiptLines)); // witness step
    } else if step.ObserveFreshJournalStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl.I(), PagedJournal.ObserveFreshJournalStep()); // witness step
    } else if step.PutStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl.I(), PagedJournal.PutStep()); // witness step
    } else if step.DiscardOldStep? {
      var lsn := lbl.startLsn;
      if !(v.unmarshalledTail.seqStart <= lsn) {
        assert v.SeqStart() == I(v).truncatedJournal.I().seqStart by {
          var tj := v.truncatedJournal;
          var dv := v.truncatedJournal.diskView;
          PagedJournal.TruncatedJournal(dv.boundaryLSN, dv.IPtr(tj.freshestRec)).BuildReceipt().TJFacts();
        }
        var croppedTJ := v.truncatedJournal.DiscardOld(lbl.startLsn);
        DiscardInterp(v.truncatedJournal.diskView, lsn, croppedTJ.diskView, v.truncatedJournal.freshestRec);
        TightInterp(croppedTJ.diskView, croppedTJ.freshestRec, v'.truncatedJournal.diskView);
        assert v'.truncatedJournal.diskView.IsSubDisk(croppedTJ.diskView);
        SubDiskInterp(v'.truncatedJournal.diskView, croppedTJ.diskView, croppedTJ.freshestRec);
      }
      assert PagedJournal.NextStep(I(v), I(v'), lbl.I(), PagedJournal.DiscardOldStep()); // witness step
    } else if step.InternalJournalMarshalStep? {
      IPtrFraming(v.truncatedJournal.diskView, v'.truncatedJournal.diskView, v.truncatedJournal.freshestRec);
      assert PagedJournal.NextStep(I(v), I(v'), lbl.I(), PagedJournal.InternalJournalMarshalStep(step.cut)); // witness step
    } else {
      assert false;
    }
  }

  // Exporting a utility for BlockCoordSystem to reason about the TruncatedJournal
  // it takes away for inFlight.
//  //////////////////////////////////////////////////////////////////////////////
//  // Rob strategy
//  predicate InFlightMemberOfEphemeral(eph: Variables, inFlight: TruncatedJournal)
//  {
//    && inFlight.diskView.IsSubDisk(eph.diskView)
//    && eph.diskView.boundaryLSN <= inFlight.diskView.boundaryLSN
//    && inFlight.freshestRec somewhere in eph.receipt
//  }
//
//  lemma RobStyle(eph: Variables, inFlight: TruncatedJournal)
//    requires InFlightMemberOfEphemeral(eph, inFlight)
//    ensures inFlight.diskView.IsSubDisk(eph.DiscardOld(inFlight.SeqStart()).diskView)
//
//  lemma RobAdditionalOverwhelmingBurden(v: Variables, v': Variables, inFlight: TruncatedJournal)
//    requires InFlightMemberOfEphemeral(v, inFlight)
//    requires Next(v, v', anyLabel)
//    ensures InFlightMemberOfEphemeral(v', inFlight)
  //////////////////////////////////////////////////////////////////////////////

  // This is a piece of an invariant that BlockCoordinationSystem maintains,
  // not an invariant of the LinkedJournal.
  predicate InFlightSubDiskProperty(v: Variables, inFlight: TruncatedJournal)
  {
    && v.WF()
    && inFlight.WF()
    && v.truncatedJournal.diskView.boundaryLSN <= inFlight.SeqStart()
    && inFlight.SeqStart() <= v.truncatedJournal.SeqEnd() // Not discarding pages that haven't been appended yet
    && inFlight.diskView.IsSubDisk(v.truncatedJournal.DiscardOld(inFlight.SeqStart()).BuildTight().diskView)
  }
  
  lemma InFlightSubDiskCreated(v: Variables, v': Variables, lbl: TransitionLabel)
    requires lbl.FreezeForCommitLabel?
    requires Next(v, v', lbl)
    ensures InFlightSubDiskProperty(v', lbl.frozenJournal)
  {
    var cropped := v.truncatedJournal.DiscardOld(lbl.frozenJournal.SeqStart());
    var tight := cropped.BuildTight();
    TightInterp(cropped.diskView, cropped.freshestRec, tight.diskView);
  }

  lemma BuildTightPreservesSubDiskUnderInternalMarshall(
      small: DiskView, smallroot: Pointer, smallRanking: Ranking,
      big: DiskView, bigroot: Pointer, bigRanking: Ranking)
    requires small.Decodable(smallroot)
    requires small.PointersRespectRank(smallRanking)
    requires big.Decodable(bigroot)
    requires big.PointersRespectRank(bigRanking)
    requires small.IsSubDisk(big)
    requires big.boundaryLSN == small.boundaryLSN
    requires bigroot.Some?
    requires big.entries[bigroot.value].CroppedPrior(big.boundaryLSN) == smallroot
    ensures small.BuildTight(smallroot).IsSubDisk(big.BuildTight(bigroot))
    decreases if bigroot.Some? then bigRanking[bigroot.value] else -1 // I can't believe this works, Rustan!
  {
    if smallroot.Some? {
      BuildTightBuildsSubDisks(small, smallroot);
      BuildTightBuildsSubDisks(big, bigroot);
      var next := small.entries[smallroot.value].CroppedPrior(small.boundaryLSN);
      BuildTightPreservesSubDiskUnderInternalMarshall(
        small, next, smallRanking, big, smallroot, bigRanking);
    }
  }

  lemma InFlightSubDiskPreserved(v: Variables, v': Variables, inFlight: TruncatedJournal)
    requires Inv(v)
    requires Next(v, v', InternalLabel())
    requires InFlightSubDiskProperty(v, inFlight)
    ensures InFlightSubDiskProperty(v', inFlight)
  {
    var step: Step :| NextStep(v, v', InternalLabel(), step);
    
    var vj := v.truncatedJournal;
    var dj := vj.DiscardOld(inFlight.SeqStart());
    var v'j := v'.truncatedJournal;
    var d'j := v'j.DiscardOld(inFlight.SeqStart());
    InvNext(v, v', InternalLabel());
    assert d'j.diskView.PointersRespectRank(v'j.diskView.TheRanking());  // witness to d'j.Acyclic

    BuildTightPreservesSubDiskUnderInternalMarshall(
      dj.diskView, dj.freshestRec, dj.diskView.TheRanking(),
      d'j.diskView, d'j.freshestRec, d'j.diskView.TheRanking());
  }
  
  //////////////////////////////////////////////////////////////////////////////
}
