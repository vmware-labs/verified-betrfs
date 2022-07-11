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

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case ReadForRecoveryStep(depth) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        assert Inv(v');
      }
      case FreezeForCommitStep(depth) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        assert Inv(v');
      } 
      case ObserveFreshJournalStep() => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        assert Inv(v');
      } 
      case PutStep() => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        assert Inv(v');
      }
      case DiscardOldStep() => {
        // TODO
        assume false;
        // assume LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        // LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        assert Inv(v');
      }
      case InternalJournalMarshalStep(cut) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        InvNextInternalJournalMarshalStep(v, v', lbl, step);
        BuildReprIndexGivesRepresentation(v'.journal.truncatedJournal);
        assert Inv(v');
      }
    }
  }

  lemma BuildReprIndexGivesRepresentationHelper(dv: DiskView, root: Pointer) 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    decreases dv.TheRankOf(root)
    ensures forall lsn | lsn in BuildReprIndexDefn(dv, root) 
      :: lsn < dv.entries[root.value].messageSeq.seqEnd
    ensures BuildReprIndexDefn(dv, root).Values == dv.Representation(root)
  {
    if root.None? {
      assert BuildReprIndexDefn(dv, root).Values == dv.Representation(root);
    } else {
      BuildReprIndexGivesRepresentationHelper(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
      var currMsgs := dv.entries[root.value].messageSeq;
      var update :=  map x: LSN | currMsgs.seqStart <= x < currMsgs.seqEnd :: root.value;
      assert currMsgs.seqStart in update;  // witness for 0 < |update|
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

  lemma InvNextInternalJournalMarshalStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires v'.WF()
    requires step.InternalJournalMarshalStep?
    requires NextStep(v, v', lbl, step)
    requires v'.journal.truncatedJournal.diskView.Acyclic()
    ensures v'.reprIndex == BuildReprIndex(v'.journal.truncatedJournal)
  {
    var msgs := v.journal.unmarshalledTail.DiscardRecent(step.cut);
    assert forall x | msgs.seqStart <= x < msgs.seqEnd :: x !in v.reprIndex;
    assert lbl.addr !in v.reprIndex.Values;
    assert v'.reprIndex.Values == v.reprIndex.Values + {lbl.addr};

    // todo
    // assert v'.journal.truncatedJournal.Representation() == v.journal.truncatedJournal.Representation() + {lbl.addr};
    assert v'.reprIndex == BuildReprIndex(v'.journal.truncatedJournal);
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