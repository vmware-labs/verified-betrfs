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
    && tj.RepresentationIsTight(v.reprIndex.Values)
    && v.reprIndex == BuildReprIndex(tj.diskView, tj.freshestRec)
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
        assume LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        assert Inv(v');
      }
      case InternalJournalMarshalStep(cut) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl, step);
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl);
        assert Inv(v');
      }
    }
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

  lemma BuildTightGivesRepresentation(dv: DiskView, root: Pointer)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    ensures dv.BuildTight(root).entries.Keys == dv.Representation(root)
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      BuildTightGivesRepresentation(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
    }
  }

  lemma BuildTightEquivalentToGarbageCollect(tj: TruncatedJournal, reprIndex: map<LSN, Address>, newBdy: LSN)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.diskView.boundaryLSN <= newBdy
    requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
    requires reprIndex.Values == tj.diskView.Representation(tj.freshestRec);
    requires (forall lsn :: tj.SeqStart() <= lsn < tj.SeqEnd() <==> lsn in reprIndex)
    requires (forall lsn | lsn in reprIndex ::
        && reprIndex[lsn] in tj.diskView.entries
        && tj.diskView.entries[reprIndex[lsn]].ContainsLSN(lsn)
    )
    // requires reprIndexDiscardUpTo(reprIndex, newBdy).Values == LinkedJournal.DiskView(newBdy, MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(reprIndex, newBdy).Values)).Representation(tj.freshestRec)
    ensures MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(reprIndex, newBdy).Values)
      == tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries
  {
    // to get the fact that DiscardOld maintains acyclicity
    LinkedJournalRefinement.DiscardOldCommutes(tj.diskView, tj.freshestRec, newBdy);
    assert tj.diskView.entries == tj.diskView.DiscardOld(newBdy).entries;
    assert IsSubMap(MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(reprIndex, newBdy).Values), tj.diskView.entries);
    
    LinkedJournalRefinement.BuildTightIsAwesome(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
    assert IsSubMap(tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries, tj.diskView.entries);
    
    BuildTightGivesRepresentation(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
    assert tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries.Keys == 
      tj.diskView.DiscardOld(newBdy).Representation(tj.freshestRec);

    forall addr | addr in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
    ensures addr in tj.diskView.DiscardOld(newBdy).Representation(tj.freshestRec)
    {
      var newIndex := reprIndexDiscardUpTo(reprIndex, newBdy);
      var lsn :| MapsTo(newIndex, lsn, addr);
      
      

    }

    forall addr | addr in tj.diskView.DiscardOld(newBdy).Representation(tj.freshestRec)
    ensures addr in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
    {
      assume false;
    }

    assert reprIndexDiscardUpTo(reprIndex, newBdy).Values == tj.diskView.DiscardOld(newBdy).Representation(tj.freshestRec);
  }

  lemma DiscardOldStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires Inv(v')
    requires NextStep(v, v', lbl, step)
    requires step.DiscardOldStep?
    ensures LinkedJournal.DiscardOld(I(v), I(v'), lbl)
  {
    var tj := v.journal.truncatedJournal;

    var reprIndex' := reprIndexDiscardUpTo(v.reprIndex, lbl.startLsn);
    var keepAddrs := reprIndex'.Values;
    var newEntries := MapRestrict(tj.diskView.entries, keepAddrs);
    var newDiskView := LinkedJournal.DiskView(lbl.startLsn, newEntries);

    if v.journal.truncatedJournal.SeqEnd() == lbl.startLsn {
      assume false;
    } else {
      calc{
        LinkedJournal.DiskView(lbl.startLsn, newEntries);
        LinkedJournal.DiskView(lbl.startLsn, MapRestrict(tj.diskView.entries, keepAddrs));
        LinkedJournal.DiskView(lbl.startLsn, MapRestrict(tj.diskView.entries, reprIndex'.Values));
        {
          calc {
            MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(v.reprIndex, lbl.startLsn).Values);
              { BuildTightEquivalentToGarbageCollect(tj, v.reprIndex, lbl.startLsn); }
            tj.diskView.DiscardOld(lbl.startLsn).BuildTight(tj.freshestRec).entries;
          }
        }
        tj.diskView.DiscardOld(lbl.startLsn).BuildTight(tj.freshestRec);
      }
      // calc{    
      //   DiscardOldAndGarbageCollect(tj, lbl.startLsn, keepAddrs);
      //   LinkedJournal.TruncatedJournal(tj.freshestRec, newDiskView);
      //   LinkedJournal.TruncatedJournal(tj.freshestRec, LinkedJournal.DiskView(lbl.startLsn, newEntries));
      //   // via above calc
      //   LinkedJournal.TruncatedJournal(tj.freshestRec, tj.diskView.DiscardOld(lbl.startLsn).BuildTight(tj.freshestRec));
      //   LinkedJournal.TruncatedJournal(tj.freshestRec, tj.diskView.DiscardOld(lbl.startLsn)).BuildTight();
      //   tj.DiscardOld(lbl.startLsn).BuildTight();
      // }
    }
    assert LinkedJournal.DiscardOld(I(v), I(v'), lbl);
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures LinkedJournal.Next(I(v), I(v'), lbl)
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case ReadForRecoveryStep(depth) => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
      }
      case FreezeForCommitStep(depth) => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
      } 
      case ObserveFreshJournalStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
      } 
      case PutStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
      }
      case DiscardOldStep() => {
        DiscardOldStepRefines(v, v', lbl, step);
        assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
      }
      case InternalJournalMarshalStep(cut) => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl, step);
      }
    }
  }
}