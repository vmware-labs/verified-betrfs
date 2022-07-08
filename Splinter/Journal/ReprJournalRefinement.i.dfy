include "ReprJournal.i.dfy"
include "LinkedJournalRefinement.i.dfy"

module ReprJournalRefinement {
  import opened ReprJournal
  import LinkedJournal
  import LinkedJournalRefinement

// PROVE INVARIANTS

  predicate Inv(v: Variables)
  {
    && v.WF()
    && v.journal.truncatedJournal.diskView.Acyclic()
    // && v.journal.truncatedJournal.RepresentationIsTight(v.reprIndex.Values)
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

  lemma DiscardOldStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires Inv(v')
    requires NextStep(v, v', lbl, step)
    requires step.DiscardOldStep?
    ensures LinkedJournal.DiscardOld(I(v), I(v'), lbl)
  {

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