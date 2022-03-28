// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournal.i.dfy"
include "PagedJournalRefinement.i.dfy"

module LinkedJournalRefinement
// TODO refines RefinementObligation(JournalLabels, PagedJournal)
{
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened JournalLabels
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

  lemma RankedIPtrFraming(dv1: DiskView, dv2: DiskView, r1: Ranking, r2: Ranking, ptr: Pointer)
    requires dv1.WF() && dv1.Acyclic() && dv1.PointersRespectRank(r1)
    requires dv2.WF() && dv2.Acyclic() && dv2.PointersRespectRank(r2)
    requires dv1.IsNondanglingPointer(ptr)
    requires dv1.IsSubDisk(dv2)
    requires dv1.boundaryLSN == dv2.boundaryLSN
    ensures dv1.RankedIPtr(ptr, r1) == dv2.RankedIPtr(ptr, r2)
    decreases if ptr.Some? then r1[ptr.value] else -1
  {
    if ptr.Some? {
      RankedIPtrFraming(dv1, dv2, r1, r2, dv1.entries[ptr.value].CroppedPrior(dv1.boundaryLSN));
    }
  }

  lemma IPtrFraming(dv1: DiskView, dv2: DiskView, ptr: Pointer)
    requires dv1.WF() && dv1.Acyclic()
    requires dv2.WF() && dv2.Acyclic()
    requires dv1.IsNondanglingPointer(ptr)
    requires dv1.IsSubDisk(dv2)
    requires dv1.boundaryLSN == dv2.boundaryLSN
    ensures dv1.IPtr(ptr) == dv2.IPtr(ptr)
  {
    RankedIPtrFraming(dv1, dv2, dv1.TheRanking(), dv2.TheRanking(), ptr);
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
    ensures discarded.RankedIPtr(ptr, discarded.TheRanking()) == PagedJournal.DiscardOldJournalRec(dv.IPtr(ptr), lsn)
    decreases if ptr.Some? then dv.TheRanking()[ptr.value] else -1
  {
    assert discarded.PointersRespectRank(dv.TheRanking());
    if ptr.Some? && !(dv.entries[ptr.value].messageSeq.seqStart <= lsn) {
      DiscardInterp(dv, lsn, discarded, discarded.entries[ptr.value].CroppedPrior(discarded.boundaryLSN));
    }
  }
    
  lemma SubDiskInterp(small: DiskView, big: DiskView, ptr: Pointer)
    requires big.WF()
    requires big.Acyclic()
    requires small.WF()
    requires small.IsSubDisk(big)
    requires small.boundaryLSN == big.boundaryLSN
    requires small.IsNondanglingPointer(ptr)
    ensures small.Acyclic()
    ensures small.RankedIPtr(ptr, small.TheRanking()) == big.RankedIPtr(ptr, big.TheRanking())
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
      var croppedTJ := v.truncatedJournal.DiscardOld(lbl.startLsn);
      var diskView := v.truncatedJournal.diskView;

      assert v'.truncatedJournal.diskView.PointersRespectRank(diskView.TheRanking());  // ranking witness gets across both DiscardOld and tightening
      if !(v.unmarshalledTail.seqStart <= lsn) {
        assert v.SeqStart() == v.truncatedJournal.I().I().seqStart by { v.truncatedJournal.I().BuildReceipt().TJFacts(); }
        DiscardInterp(diskView, lsn, diskView.DiscardOld(lsn), v.truncatedJournal.freshestRec);
        SubDiskInterp(v'.truncatedJournal.diskView, croppedTJ.diskView, croppedTJ.freshestRec);
        assert croppedTJ.I() == v.truncatedJournal.I().DiscardOld(lsn); // Trigger for v'.I().WF()
      }
      assert Inv(v');
    } else if step.InternalJournalMarshalStep? {
      // Witness new rank
      var rank :| v.truncatedJournal.diskView.PointersRespectRank(rank);
      var rank' := rank[step.addr :=
          if v.truncatedJournal.freshestRec.None? then 0
          else rank[v.truncatedJournal.freshestRec.value]+1];
      assert v'.truncatedJournal.diskView.PointersRespectRank(rank');

      IPtrFraming(v.truncatedJournal.diskView, v'.truncatedJournal.diskView, v.truncatedJournal.freshestRec);
      assert Inv(v');
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
    ensures PagedJournal.Next(I(v), I(v'), lbl)
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    if step.ReadForRecoveryStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl, PagedJournal.ReadForRecoveryStep(step.receiptIndex)); // witness step
    } else if step.FreezeForCommitStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl, PagedJournal.FreezeForCommitStep(step.keepReceiptLines)); // witness step
    } else if step.ObserveFreshJournalStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl, PagedJournal.ObserveFreshJournalStep()); // witness step
    } else if step.PutStep? {
      assert PagedJournal.NextStep(I(v), I(v'), lbl, PagedJournal.PutStep()); // witness step
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
        SubDiskInterp(v'.truncatedJournal.diskView, croppedTJ.diskView, croppedTJ.freshestRec);
      }
      assert PagedJournal.NextStep(I(v), I(v'), lbl, PagedJournal.DiscardOldStep()); // witness step
    } else if step.InternalJournalMarshalStep? {
      IPtrFraming(v.truncatedJournal.diskView, v'.truncatedJournal.diskView, v.truncatedJournal.freshestRec);
      assert PagedJournal.NextStep(I(v), I(v'), lbl, PagedJournal.InternalJournalMarshalStep(step.cut)); // witness step
    } else {
      assert false;
    }
  }
}

