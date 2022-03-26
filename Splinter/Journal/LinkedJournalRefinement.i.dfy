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
    ensures dv1.RankedIPtr(ptr, r1) == dv2.RankedIPtr(ptr, r2)
    decreases if ptr.Some? then r1[ptr.value] else -1
  {
    if ptr != None {
      RankedIPtrFraming(dv1, dv2, r1, r2, dv1.CroppedPointer(dv1.entries[ptr.value].priorRec));
    }
  }

  lemma IPtrFraming(dv1: DiskView, dv2: DiskView, ptr: Pointer)
    requires dv1.WF() && dv1.Acyclic()
    requires dv2.WF() && dv2.Acyclic()
    requires dv1.IsNondanglingPointer(ptr)
    requires dv1.IsSubDisk(dv2)
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

  lemma DiscardOldPreservesAcyclic(big: DiskView, cropped: DiskView)
    requires big.WF()
    requires big.boundaryLSN <= cropped.boundaryLSN
    requires big.Acyclic()
    requires cropped == big.DiscardOld(cropped.boundaryLSN)
    ensures cropped.WF()
    ensures cropped.Acyclic()
  {
    var ranking :| big.PointersRespectRank(ranking);
    assert cropped.PointersRespectRank(ranking);
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
    DiscardOldPreservesAcyclic(dv, discarded);
    if !ptr.None? {
      if dv.entries[ptr.value].messageSeq.seqEnd <= lsn {
        assert discarded.RankedIPtr(ptr, discarded.TheRanking()).None?;
        assert PagedJournal.DiscardOldJournalRec(dv.IPtr(ptr), lsn).None?;
        assert discarded.RankedIPtr(ptr, discarded.TheRanking()) == PagedJournal.DiscardOldJournalRec(dv.IPtr(ptr), lsn);
      } else {
        DiscardInterp(dv, lsn, discarded, dv.CroppedPointer(dv.entries[ptr.value].priorRec));
        if dv.entries[ptr.value].messageSeq.seqStart <= lsn {
          assert discarded.RankedIPtr(ptr, discarded.TheRanking()).value.priorRec.None?;
          assert PagedJournal.DiscardOldJournalRec(dv.IPtr(ptr), lsn).value.priorRec.None?;
          assert discarded.RankedIPtr(ptr, discarded.TheRanking()) == PagedJournal.DiscardOldJournalRec(dv.IPtr(ptr), lsn);
        } else {
          assert discarded.RankedIPtr(ptr, discarded.TheRanking()) == PagedJournal.DiscardOldJournalRec(dv.IPtr(ptr), lsn);
        }
      }
    }
  }
    
//    ensures 

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
      assert DiskView(v.truncatedJournal.diskView.boundaryLSN, map[]).PointersRespectRank(map[]);  // need ranking for case where we make a fresh empty diskview

      var lsn := lbl.startLsn;
      var croppedTJ := v.truncatedJournal.DiscardOld(lbl.startLsn);
      if v.unmarshalledTail.seqStart <= lsn {
        // TODO(jonh): turn on tight before eliminating this proof
        assert croppedTJ.freshestRec == None;
        assert croppedTJ.diskView == v.truncatedJournal.diskView.DiscardOld(lbl.startLsn);
        DiscardOldPreservesAcyclic(v.truncatedJournal.diskView, croppedTJ.diskView);
        assert croppedTJ.diskView.Acyclic();
        assert croppedTJ.I() == PagedJournal.TruncatedJournal(lsn, None);
      } else {
        DiscardOldPreservesAcyclic(v.truncatedJournal.diskView, croppedTJ.diskView);
        assert v.SeqStart() == v.truncatedJournal.I().I().seqStart
          by { v.truncatedJournal.I().BuildReceipt().TJFacts(); }
        if !(v.truncatedJournal.freshestRec.None? 
          || v.truncatedJournal.diskView.entries[v.truncatedJournal.freshestRec.value].messageSeq.seqEnd <= lsn) {
          var diskView := v.truncatedJournal.diskView;
          var discardedDV := diskView.DiscardOld(lsn);
          calc {
            TruncatedJournal(v.truncatedJournal.freshestRec, diskView.DiscardOld(lsn)).I().freshestRec;

            diskView.DiscardOld(lsn).IPtr(v.truncatedJournal.freshestRec);
            discardedDV.RankedIPtr(v.truncatedJournal.freshestRec, discardedDV.TheRanking());
              { DiscardInterp(v.truncatedJournal.diskView, lsn, discardedDV, v.truncatedJournal.freshestRec); }
            
            PagedJournal.DiscardOldJournalRec(v.truncatedJournal.diskView.IPtr(v.truncatedJournal.freshestRec), lsn);
            PagedJournal.DiscardOldJournalRec(v.truncatedJournal.I().freshestRec, lsn);
            v.truncatedJournal.I().DiscardOld(lsn).freshestRec;
          }
          calc {
            croppedTJ.I().freshestRec;
            TruncatedJournal(v.truncatedJournal.freshestRec, v.truncatedJournal.diskView.DiscardOld(lsn)).I().freshestRec;
            v.truncatedJournal.I().DiscardOld(lsn).freshestRec;
          }
        }
        assert croppedTJ.I() == v.truncatedJournal.I().DiscardOld(lsn);
      }

      assert PagedJournal.DiscardOld(I(v), I(v'), lbl); // trigger
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
      assume false;
      if v.unmarshalledTail.seqStart <= lsn {
        assert I(v').truncatedJournal == PagedJournal.TruncatedJournal(lsn, None);
      } else {
        var tj := v.truncatedJournal;
        var tj' := v'.truncatedJournal;
        calc {
          v.SeqStart();
          v.truncatedJournal.SeqStart();
          v.truncatedJournal.diskView.boundaryLSN;
            { assume false; }
          v.truncatedJournal.I().I().seqStart;  // HERE
          I(v).truncatedJournal.I().seqStart;
        }
        assert v.SeqStart() == I(v).truncatedJournal.I().seqStart;
        assert I(v).truncatedJournal.I().seqStart <= lsn;
        assert I(v).truncatedJournal.I().CanDiscardTo(lsn);
        assert I(v').truncatedJournal.boundaryLSN == I(v).truncatedJournal.DiscardOld(lsn).boundaryLSN;
        assert tj'.diskView.IPtr(tj'.freshestRec) == tj.I().DiscardOld(lsn).freshestRec;
        assert v'.truncatedJournal.I().freshestRec == v.truncatedJournal.I().DiscardOld(lsn).freshestRec;
        assert I(v').truncatedJournal.freshestRec == I(v).truncatedJournal.DiscardOld(lsn).freshestRec;
        assert I(v').truncatedJournal == I(v).truncatedJournal.DiscardOld(lsn);
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

