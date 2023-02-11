include "LikesJournal.i.dfy"
// include "LinkedJournalRefinement.i.dfy"

module LikesJournalRefinement {
  import opened Maps
  import opened LSNMod
  import opened LikesJournal
  import LinkedJournal
//   import LinkedJournalRefinement


  function IStep(step: Step) : LinkedJournal.Step {
    match step {
      case ReadForRecoveryStep(depth) => LinkedJournal.ReadForRecoveryStep(depth)
      case FreezeForCommitStep(depth) => LinkedJournal.FreezeForCommitStep(depth)
      case ObserveFreshJournalStep() => LinkedJournal.ObserveFreshJournalStep()
      case PutStep() => LinkedJournal.PutStep()
      case DiscardOldStep() => LinkedJournal.DiscardOldStep()
      case InternalJournalMarshalStep(cut, addr) => LinkedJournal.InternalJournalMarshalStep(cut, addr)
      case InternalNoOpStep() => LinkedJournal.InternalNoOpStep()
    }
  }


// PROVE INVARIANTS

  predicate Inv(v: Variables)
  {
    // TODO
    true
  }
  
  lemma InvInit(v: Variables, journal: TruncatedJournal)
    requires Init(v, journal)
    ensures Inv(v)
  {
    // TODO
    assume false;
  }


  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    // TODO
    assume false;
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case ReadForRecoveryStep(depth) => {
        assert Inv(v');
      }
      case FreezeForCommitStep(depth) => {
        assert Inv(v');
      }
      case ObserveFreshJournalStep() => {
        assert Inv(v');
      }
      case PutStep() => {
        assert Inv(v');
      }
      case DiscardOldStep() => {
        assert Inv(v');
      }
      case InternalJournalMarshalStep(cut, addr) => {
        assert Inv(v');
      }
      case InternalNoOpStep() => assert Inv(v');
    }
  }


// PROVE REFINEMENT

  function I(v: Variables) : (out: LinkedJournal.Variables) 
  {
    v.journal
  }

  lemma InitRefines(v: Variables, journal: TruncatedJournal)
    requires Init(v, journal)
    ensures LinkedJournal.Init(I(v), journal)
  {
    // TODO
    assume false;
  }



  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures LinkedJournal.Next(I(v), I(v'), lbl.I())
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case ReadForRecoveryStep(depth) => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
      case FreezeForCommitStep(depth) => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      } 
      case ObserveFreshJournalStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      } 
      case PutStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
      case DiscardOldStep() => {
        // TODO
        assume false;
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
      case InternalJournalMarshalStep(cut, addr) => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
      case InternalNoOpStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
    }
  }
}
