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
    if tj.freshestRec.Some? {
      BuildReprIndexDomainWF(tj.diskView, tj.freshestRec);
    }
    BuildReprIndexRangeWF(tj.diskView, tj.freshestRec, tj.SeqEnd());
    BuildReprIndexGivesRepresentation(v.journal.truncatedJournal);
  }

  // BuildReprIndex has domain that is a subset of [dv.boundaryLsn, tjEnd)
  // and every value is an entry in the disk
  lemma BuildReprIndexDomainWFHelper1(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd <= tjEnd
    ensures forall lsn :: lsn in BuildReprIndexDefn(dv, root) ==> dv.boundaryLSN <= lsn < tjEnd
    ensures forall lsn | lsn in BuildReprIndexDefn(dv, root) :: BuildReprIndexDefn(dv, root)[lsn] in dv.entries
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      BuildReprIndexDomainWFHelper1(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN), tjEnd);
    }
  }

  lemma BuildReprIndexDomainWFHelper2(dv: DiskView, root: Pointer, tjEnd: LSN)
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
        BuildReprIndexDomainWFHelper2(dv, prior, dv.boundaryLSN);
      } else {
        BuildReprIndexDomainWFHelper2(dv, prior, dv.entries[prior.value].messageSeq.seqEnd);
      }
    }
  }

  // Wrapper for domain properties of BuildReprIndex
  lemma BuildReprIndexDomainWF(dv: DiskView, root: Pointer)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some?  // otherwise BuildReprIndex is trivially empty
    requires dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    ensures forall lsn :: lsn in BuildReprIndexDefn(dv, root) <==> dv.boundaryLSN <= lsn < dv.entries[root.value].messageSeq.seqEnd
    ensures forall lsn | lsn in BuildReprIndexDefn(dv, root) :: BuildReprIndexDefn(dv, root)[lsn] in dv.entries
  {
    BuildReprIndexDomainWFHelper1(dv, root, dv.entries[root.value].messageSeq.seqEnd);
    BuildReprIndexDomainWFHelper2(dv, root, dv.entries[root.value].messageSeq.seqEnd);
  }

  lemma BuildReprIndexRangeWF(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd == tjEnd
    requires root.None? ==> tjEnd <= dv.boundaryLSN
    requires forall lsn :: lsn in BuildReprIndexDefn(dv, root) <==> dv.boundaryLSN <= lsn < tjEnd
    requires forall lsn | lsn in BuildReprIndexDefn(dv, root) :: BuildReprIndexDefn(dv, root)[lsn] in dv.entries
    ensures forall addr | addr in BuildReprIndexDefn(dv, root).Values ::
        && var msgs := dv.entries[addr].messageSeq;
        && (forall lsn | Mathematics.max(dv.boundaryLSN, msgs.seqStart) <= lsn < msgs.seqEnd :: 
              && lsn in BuildReprIndexDefn(dv, root)
              && BuildReprIndexDefn(dv, root)[lsn] == addr
        )
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      var priorPtr := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
      BuildReprIndexOneStepSubmap(dv, root);
      if priorPtr.None? {
        BuildReprIndexRangeWF(dv, priorPtr, dv.boundaryLSN);
      } else {
        BuildReprIndexDomainWF(dv, priorPtr);
        BuildReprIndexRangeWF(dv, priorPtr, dv.entries[priorPtr.value].messageSeq.seqEnd);
      }
    }
  }

  // Building from the prior rec gives a submap
  lemma BuildReprIndexOneStepSubmap(dv: DiskView, root: Pointer)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some?
    requires dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    ensures IsSubMap(BuildReprIndexDefn(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN)), BuildReprIndexDefn(dv, root))
  {
    var priorPtr := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
    if priorPtr.Some? {
      BuildReprIndexDomainWF(dv, priorPtr);
    }
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
      DiscardOldMaintainsReprIndex(v, v', lbl);
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

  lemma BuildReprIndexWithSubDiskProducesSubMap(small: DiskView, big: DiskView, root: Pointer)
    requires small.Decodable(root)
    requires small.Acyclic()
    requires big.Decodable(root)
    requires big.Acyclic()
    requires root.Some? ==> small.boundaryLSN < small.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> big.boundaryLSN < big.entries[root.value].messageSeq.seqEnd
    requires small.IsSubDiskWithNewerLSN(big)
    ensures IsSubMap(BuildReprIndexDefn(small, root), BuildReprIndexDefn(big, root))
    decreases small.TheRankOf(root)
  {
    if root.Some? {
      BuildReprIndexWithSubDiskProducesSubMap(small, big, small.entries[root.value].CroppedPrior(small.boundaryLSN));
      var smallPrior := small.entries[root.value].CroppedPrior(small.boundaryLSN);
      if smallPrior.Some? {
        BuildReprIndexDomainWF(small, smallPrior);
      }
      var bigPrior := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      if bigPrior.Some? {
        BuildReprIndexDomainWF(big, bigPrior);
      }
    }
  }
 
  lemma DiscardOldMaintainsReprIndex(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires v'.WF()
    requires DiscardOld(v, v', lbl)
    requires v'.journal.truncatedJournal.diskView.Acyclic()
    ensures v'.reprIndex == BuildReprIndex(v'.journal.truncatedJournal);
  {
    var newBdy := lbl.startLsn;
    var tj := v.journal.truncatedJournal;
    var keepAddrs := reprIndexDiscardUpTo(v.reprIndex, newBdy).Values;
    var newEntries := MapRestrict(tj.diskView.entries, keepAddrs); 
    var newDiskView := LinkedJournal.DiskView(newBdy, newEntries);

    if newBdy < tj.SeqEnd() {
      assert IsSubMap(reprIndexDiscardUpTo(v.reprIndex, newBdy), BuildReprIndexDefn(newDiskView, tj.freshestRec)) 
      by {
        BuildReprIndexDomainWF(newDiskView, tj.freshestRec);
        BuildReprIndexWithSubDiskProducesSubMap(newDiskView, tj.diskView, tj.freshestRec);
      }
      assert IsSubMap(BuildReprIndexDefn(newDiskView, tj.freshestRec), reprIndexDiscardUpTo(v.reprIndex, newBdy)) 
      by {
        BuildReprIndexDomainWF(newDiskView, tj.freshestRec);
      }
    }
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