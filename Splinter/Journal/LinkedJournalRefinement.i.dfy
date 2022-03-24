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

  // TODO(robj): move this to maps
  predicate Submap<K,V>(a: map<K,V>, b: map<K,V>)
  {
    forall k | k in a :: k in b && a[k] == b[k]
  }

  lemma RankedIPtrFraming(dv1: DiskView, dv2: DiskView, r1: Ranking, r2: Ranking, ptr: Pointer)
    requires dv1.WF() && dv1.Acyclic() && dv1.PointersRespectRank(r1)
    requires dv2.WF() && dv2.Acyclic() && dv2.PointersRespectRank(r2)
    requires dv1.NondanglingPointer(ptr)
    requires Submap(dv1.entries, dv2.entries)
    ensures dv1.RankedIPtr(ptr, r1) == dv2.RankedIPtr(ptr, r2)
    decreases if ptr.Some? then r1[ptr.value] else -1
  {
    if ptr != None {
      RankedIPtrFraming(dv1, dv2, r1, r2, dv1.entries[ptr.value].priorRec);
    }
  }

  lemma IPtrFraming(dv1: DiskView, dv2: DiskView, ptr: Pointer)
    requires dv1.WF() && dv1.Acyclic()
    requires dv2.WF() && dv2.Acyclic()
    requires dv1.NondanglingPointer(ptr)
    requires Submap(dv1.entries, dv2.entries)
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
    } else if step.ObserveFreshJournalLabel? {
      assert Inv(v');
    } else if step.PutStep? {
      assert Inv(v');
    } else if step.DiscardOldStep? {
      assume false;
      assert PagedJournal.DiscardOld(I(v), I(v'), lbl);
      assert v'.WF();
      assert v'.truncatedJournal.Decodable();
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
    assume false;   // TODO
    var step: Step :| NextStep(v, v', lbl, step);
    if step.ReadForRecoveryStep? {
      assert PagedJournal.Next(I(v), I(v'), lbl);
    } else if step.FreezeForCommitStep? {
      assert PagedJournal.Next(I(v), I(v'), lbl);
    } else if step.ObserveFreshJournalLabel? {
      assert PagedJournal.Next(I(v), I(v'), lbl);
    } else if step.PutStep? {
      assert PagedJournal.Next(I(v), I(v'), lbl);
    } else if step.DiscardOldStep? {
      assert PagedJournal.Next(I(v), I(v'), lbl);
    } else if step.InternalJournalMarshalStep? {
      assert PagedJournal.Next(I(v), I(v'), lbl);
    } else {
      assert false;
    }
  }
}

