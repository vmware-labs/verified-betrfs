include "ReprJournal.i.dfy"
include "LinkedJournalRefinement.i.dfy"

module ReprJournalRefinement {
  import opened Maps
  import opened LSNMod
  import opened ReprJournal
  import LinkedJournal
  import LinkedJournalRefinement

// PROVE INVARIANTS

  predicate Inv(v: Variables)
  {
    var tj :=  v.journal.truncatedJournal;
    && v.WF()
    && tj.diskView.Acyclic()

    && v.reprIndex == BuildReprIndex(tj)

    // todo(tony): Do we need something stronger than this? 
    // I think we also need to say that for each lsn in key, it maps to THE UNIQUE page in the representation that contains it
    // I think this is what we need ultimately, but we may need intermediate invariants to prove this.
    && v.reprIndex.Values == tj.Representation()
  }
  
  lemma InvInit(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures Inv(v)
  {
    BuildReprIndexDomainWF1(tj.diskView, tj.freshestRec, tj.SeqEnd());
    BuildReprIndexDomainWF2(tj.diskView, tj.freshestRec, tj.SeqEnd());
    BuildReprIndexRangeWF(tj);
    BuildReprIndexGivesRepresentation(v.journal.truncatedJournal);
  }

  lemma BuildReprIndexDomainWF1(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd <= tjEnd
    ensures forall lsn :: lsn in BuildReprIndexDefn(dv, root) ==> dv.boundaryLSN <= lsn < tjEnd
    ensures forall lsn | lsn in BuildReprIndexDefn(dv, root) :: BuildReprIndexDefn(dv, root)[lsn] in dv.entries
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      BuildReprIndexDomainWF1(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN), tjEnd);
    }
  }

  lemma BuildReprIndexDomainWF2(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd == tjEnd
    requires root.None? ==> tjEnd <= dv.boundaryLSN
    ensures forall lsn :: dv.boundaryLSN <= lsn < tjEnd ==> lsn in BuildReprIndexDefn(dv, root)
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      var prior := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
      if prior.None? {
        BuildReprIndexDomainWF2(dv, prior, dv.boundaryLSN);
      } else {
        BuildReprIndexDomainWF2(dv, prior, dv.entries[prior.value].messageSeq.seqEnd);
      }
    }
  }

  lemma BuildReprIndexRangeWF(tj: TruncatedJournal)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires forall lsn :: lsn in BuildReprIndex(tj) <==> tj.diskView.boundaryLSN <= lsn < tj.SeqEnd()
    requires forall lsn | lsn in BuildReprIndex(tj) :: BuildReprIndex(tj)[lsn] in tj.diskView.entries
    ensures forall addr | addr in BuildReprIndex(tj).Values ::
        && var msgs := tj.diskView.entries[addr].messageSeq;
        && var boundaryLSN := tj.diskView.boundaryLSN;
        && (forall lsn | Mathematics.max(boundaryLSN, msgs.seqStart) <= lsn < msgs.seqEnd :: 
              && lsn in BuildReprIndex(tj)
              && BuildReprIndex(tj)[lsn] == addr
        )
  {
    assume false;  // TODO
  }


  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    var step: Step :| NextStep(v, v', lbl, step);
    if step.DiscardOldStep? {
      DiscardOldStepPreservesWF(v, v', lbl, step);
      var ranking := v.journal.truncatedJournal.diskView.TheRanking();  // witness to acyclicity
      assert v'.journal.truncatedJournal.diskView.PointersRespectRank(ranking);
      DiscardOldMaintainsReprIndex(v, v', lbl, step);
      BuildReprIndexGivesRepresentation(v'.journal.truncatedJournal);
    } else if step.InternalJournalMarshalStep? {
      assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
      LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
      InvNextInternalJournalMarshalStep(v, v', lbl, step);
      BuildReprIndexGivesRepresentation(v'.journal.truncatedJournal);
    }
    else {
      assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
      LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
    }
  }

  lemma DiscardOldStepPreservesWF(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires step.DiscardOldStep?
    requires NextStep(v, v', lbl, step)
    ensures v'.WF()
  {
    var tj := v.journal.truncatedJournal;
    var tj' := v'.journal.truncatedJournal;
    var oldBdy := tj.diskView.boundaryLSN;
    var newBdy := lbl.startLsn;
    DiscardOldStepPreservesWFDiskView(v, v', lbl, step);
    
    // prove tj'.diskView.IsNondanglingPointer(tj'.freshestRec);
    if tj'.freshestRec.Some? {
      var msgs := tj.diskView.entries[tj.freshestRec.value].messageSeq;
      var lsn := Mathematics.max(newBdy, msgs.seqStart); // witness
      assert lsn in v.reprIndex && v.reprIndex[lsn] == tj.freshestRec.value;
    }
  }

  lemma DiscardOldStepPreservesWFDiskView(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires step.DiscardOldStep?
    requires NextStep(v, v', lbl, step)
    ensures v'.journal.truncatedJournal.diskView.WF();
  {
    var tj := v.journal.truncatedJournal;
    var tj' := v'.journal.truncatedJournal;
    var newBdy := lbl.startLsn;
    forall addr | addr in tj'.diskView.entries
    ensures tj'.diskView.IsNondanglingPointer(tj'.diskView.entries[addr].CroppedPrior(newBdy))
    {
      var currBlock := tj'.diskView.entries[addr];
      if currBlock.CroppedPrior(newBdy).Some? {
        var prevAddr := currBlock.CroppedPrior(newBdy).value;
        assert prevAddr in tj.Representation() by 
        {
          RepresentationSubset(addr, tj.freshestRec.value, tj.diskView);
        }
        // witness
        var x :| x in v.reprIndex && newBdy <= x && v.reprIndex[x] == prevAddr;
      }
    }
  }

  lemma RepresentationSubset(x: Address, y: Address, dv: DiskView)
    requires dv.Decodable(Pointer.Some(x))
    requires dv.Decodable(Pointer.Some(y))
    requires dv.Acyclic()
    requires x in dv.Representation(Pointer.Some(y))
    ensures dv.Representation(Pointer.Some(x)) <= dv.Representation(Pointer.Some(y))
    decreases dv.TheRankOf(Pointer.Some(y))
  {
    if x != y {
      RepresentationSubset(x, dv.entries[y].CroppedPrior(dv.boundaryLSN).value, dv);
    }
  }

  lemma DiscardOldMaintainsReprIndex(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires v'.WF()
    requires step.DiscardOldStep?
    requires NextStep(v, v', lbl, step)
    requires v'.journal.truncatedJournal.diskView.Acyclic()
    ensures v'.reprIndex == BuildReprIndex(v'.journal.truncatedJournal);
  {
    assume false;
    // var index := v.reprIndex;
    // assert index == BuildReprIndex(v.journal.truncatedJournal);
    
    // assert IsSubMap(BuildReprIndex(v'.journal.truncatedJournal), index);

  }

  lemma BuildReprIndexGivesRepresentationHelper(dv: DiskView, root: Pointer) 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    decreases dv.TheRankOf(root)
    ensures forall lsn | lsn in BuildReprIndexDefn(dv, root) 
      :: lsn < dv.entries[root.value].messageSeq.seqEnd
    ensures BuildReprIndexDefn(dv, root).Values == dv.Representation(root)
  {
    if root.Some? {
      BuildReprIndexGivesRepresentationHelper(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
      var currMsgs := dv.entries[root.value].messageSeq;
      var update :=  map x: LSN | Mathematics.max(dv.boundaryLSN, currMsgs.seqStart) <= x < currMsgs.seqEnd :: root.value;
      assert Mathematics.max(dv.boundaryLSN, currMsgs.seqStart) in update;  // witness for 0 < |update|
    }
  }

  lemma BuildReprIndexGivesRepresentation(tj: TruncatedJournal) 
    requires tj.WF()
    requires tj.diskView.Decodable(tj.freshestRec)
    requires tj.diskView.Acyclic()
    ensures BuildReprIndex(tj).Values == tj.Representation()
  {
    BuildReprIndexGivesRepresentationHelper(tj.diskView, tj.freshestRec);
  }

  // Building repr index from the same pointer produces the same result on subdisks
  lemma SubDiskReprIndex(small: DiskView, big: DiskView, ptr: Pointer)
    requires big.WF()
    requires big.Acyclic()
    requires small.WF()
    requires small.IsSubDisk(big)
    requires small.boundaryLSN == big.boundaryLSN
    requires small.IsNondanglingPointer(ptr)
    ensures small.Acyclic()
    requires ptr.Some? ==> small.boundaryLSN < small.entries[ptr.value].messageSeq.seqEnd
    ensures BuildReprIndexDefn(small, ptr) == BuildReprIndexDefn(big, ptr)
    decreases if ptr.Some? then big.TheRanking()[ptr.value] else -1
  {
    assert small.PointersRespectRank(big.TheRanking());
    if ptr.Some? {
      var jr := big.entries[ptr.value];
      SubDiskReprIndex(small, big, jr.CroppedPrior(big.boundaryLSN));
    }
  }

  lemma InvNextInternalJournalMarshalStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires v'.WF()
    requires step.InternalJournalMarshalStep?
    requires NextStep(v, v', lbl, step)
    requires v'.journal.truncatedJournal.diskView.Acyclic()
    ensures v'.reprIndex == BuildReprIndex(v'.journal.truncatedJournal)
  {
    var tj := v.journal.truncatedJournal;
    var tj' := v'.journal.truncatedJournal;
    SubDiskReprIndex(tj.diskView, tj'.diskView, tj.freshestRec);
  }



// PROVE REFINEMENT

  function I(v: Variables) : (out: LinkedJournal.Variables) 
  {
    v.journal
  }

  lemma InitRefines(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures LinkedJournal.Init(I(v), tj)
  {}

  // lemma BuildTightGivesRepresentation(dv: DiskView, root: Pointer)
  //   requires dv.Decodable(root)
  //   requires dv.Acyclic()
  //   ensures dv.BuildTight(root).entries.Keys == dv.Representation(root)
  //   decreases dv.TheRankOf(root)
  // {
  //   if root.Some? {
  //     BuildTightGivesRepresentation(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
  //   }
  // }

  // lemma LsnPageInJournal(tj: TruncatedJournal, lsn: LSN) returns (out: Address)
  //   requires tj.WF()
  //   requires tj.SeqStart() <= lsn < tj.SeqEnd()
  //   ensures out in tj.diskView.entries
  //   ensures tj.diskView.entries[out].messageSeq.seqStart <= lsn < tj.diskView.entries[out].messageSeq.seqEnd
  //   ensures out in tj.diskView.Representation(tj.freshestRec)
  // {
  //   assume false;
  // }

  // lemma BuildTightEquivalentToGarbageCollect(tj: TruncatedJournal, reprIndex: map<LSN, Address>, newBdy: LSN)
  //   requires tj.WF()
  //   requires tj.diskView.Acyclic()
  //   requires tj.diskView.boundaryLSN <= newBdy
  //   requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
  //   requires reprIndex.Values == tj.diskView.Representation(tj.freshestRec);
  //   requires (forall lsn :: tj.SeqStart() <= lsn < tj.SeqEnd() <==> lsn in reprIndex)
  //   requires (forall lsn | lsn in reprIndex ::
  //       && reprIndex[lsn] in tj.diskView.entries
  //       && tj.diskView.entries[reprIndex[lsn]].ContainsLSN(lsn)
  //   )
  //   ensures MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(reprIndex, newBdy).Values)
  //     == tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries
  // {
  //   // to get the fact that DiscardOld maintains acyclicity
  //   LinkedJournalRefinement.DiscardOldCommutes(tj.diskView, tj.freshestRec, newBdy);
  //   assert tj.diskView.entries == tj.diskView.DiscardOld(newBdy).entries;
  //   assert IsSubMap(MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(reprIndex, newBdy).Values), tj.diskView.entries);
    
  //   LinkedJournalRefinement.BuildTightIsAwesome(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
  //   assert IsSubMap(tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries, tj.diskView.entries);
    
  //   BuildTightGivesRepresentation(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
  //   assert tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries.Keys == 
  //     tj.diskView.DiscardOld(newBdy).Representation(tj.freshestRec);

  //   forall addr | addr in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
  //   ensures addr in tj.DiscardOld(newBdy).diskView.Representation(tj.freshestRec)
  //   {
  //     if addr !in tj.DiscardOld(newBdy).diskView.Representation(tj.freshestRec) {
  //       var page := tj.DiscardOld(newBdy).diskView.entries[addr];

  //       // This messageSeq cannot have lsn within the operational range
  //       assert page.messageSeq.seqEnd < newBdy || tj.SeqEnd() <= page.messageSeq.seqStart;

  //       assert false;
  //     }
  //   }

  //   forall addr | addr in tj.diskView.DiscardOld(newBdy).Representation(tj.freshestRec)
  //   ensures addr in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
  //   {
  //     assume false;
  //   }

  //   assert reprIndexDiscardUpTo(reprIndex, newBdy).Values == tj.diskView.DiscardOld(newBdy).Representation(tj.freshestRec);
  // }

  // lemma DiscardOldStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  //   requires Inv(v)
  //   requires Inv(v')
  //   requires NextStep(v, v', lbl, step)
  //   requires step.DiscardOldStep?
  //   ensures LinkedJournal.DiscardOld(I(v), I(v'), lbl)
  // {
  //   var tj := v.journal.truncatedJournal;

  //   var reprIndex' := reprIndexDiscardUpTo(v.reprIndex, lbl.startLsn);
  //   var keepAddrs := reprIndex'.Values;
  //   var newEntries := MapRestrict(tj.diskView.entries, keepAddrs);
  //   var newDiskView := LinkedJournal.DiskView(lbl.startLsn, newEntries);

  //   if v.journal.truncatedJournal.SeqEnd() == lbl.startLsn {
  //     assume false;
  //   } else {
  //     calc{
  //       LinkedJournal.DiskView(lbl.startLsn, newEntries);
  //       LinkedJournal.DiskView(lbl.startLsn, MapRestrict(tj.diskView.entries, keepAddrs));
  //       LinkedJournal.DiskView(lbl.startLsn, MapRestrict(tj.diskView.entries, reprIndex'.Values));
  //       {
  //         calc {
  //           MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(v.reprIndex, lbl.startLsn).Values);
  //             { BuildTightEquivalentToGarbageCollect(tj, v.reprIndex, lbl.startLsn); }
  //           tj.diskView.DiscardOld(lbl.startLsn).BuildTight(tj.freshestRec).entries;
  //         }
  //       }
  //       tj.diskView.DiscardOld(lbl.startLsn).BuildTight(tj.freshestRec);
  //     }
  //     calc{    
  //       DiscardOldAndGarbageCollect(tj, lbl.startLsn, keepAddrs);
  //       LinkedJournal.TruncatedJournal(tj.freshestRec, newDiskView);
  //       LinkedJournal.TruncatedJournal(tj.freshestRec, LinkedJournal.DiskView(lbl.startLsn, newEntries));
  //       // via above calc
  //       LinkedJournal.TruncatedJournal(tj.freshestRec, tj.diskView.DiscardOld(lbl.startLsn).BuildTight(tj.freshestRec));
  //       LinkedJournal.TruncatedJournal(tj.freshestRec, tj.diskView.DiscardOld(lbl.startLsn)).BuildTight();
  //       tj.DiscardOld(lbl.startLsn).BuildTight();
  //     }
  //   }
  //   assert LinkedJournal.DiscardOld(I(v), I(v'), lbl);
  // }

  // lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
  //   requires Inv(v)
  //   requires Next(v, v', lbl)
  //   ensures v'.WF()
  //   ensures Inv(v')
  //   ensures LinkedJournal.Next(I(v), I(v'), lbl)
  // {
  //   InvNext(v, v', lbl);
  //   var step: Step :| NextStep(v, v', lbl, step);
  //   match step {
  //     case ReadForRecoveryStep(depth) => {
  //       assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
  //     }
  //     case FreezeForCommitStep(depth) => {
  //       assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
  //     } 
  //     case ObserveFreshJournalStep() => {
  //       assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
  //     } 
  //     case PutStep() => {
  //       assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
  //     }
  //     case DiscardOldStep() => {
  //       DiscardOldStepRefines(v, v', lbl, step);
  //       assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
  //     }
  //     case InternalJournalMarshalStep(cut) => {
  //       assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
  //     }
  //   }
  // }
}