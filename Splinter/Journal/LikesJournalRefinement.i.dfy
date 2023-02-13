include "LikesJournal.i.dfy"
include "LinkedJournalRefinement.i.dfy"

module LikesJournalRefinement {
  import opened Maps
  import opened LSNMod
  import opened LikesJournal
  import LinkedJournal
  import LinkedJournalRefinement


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

  predicate IndexKeysMapToValidEntries(lsnAddrIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
  {
    forall lsn | lsn in lsnAddrIndex ::
      && lsnAddrIndex[lsn] in tj.diskView.entries
      && tj.diskView.entries[lsnAddrIndex[lsn]].ContainsLSN(lsn)
  }

  predicate IndexDomainValid(lsnAddrIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
  {
    // lsnAddrIndex's domain is exactly the set of LSN between journal.SeqStart() and journal.SeqEnd()
    && (forall lsn :: lsn in lsnAddrIndex <==> tj.SeqStart() <= lsn < tj.SeqEnd())
  }

  predicate IndexRangeValid(lsnAddrIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
    requires IndexDomainValid(lsnAddrIndex, tj)
    requires IndexKeysMapToValidEntries(lsnAddrIndex, tj)
  {
    forall addr | addr in lsnAddrIndex.Values ::
      && var msgs := tj.diskView.entries[addr].messageSeq;
      && var boundaryLSN := tj.diskView.boundaryLSN;
      && (forall lsn | Mathematics.max(boundaryLSN, msgs.seqStart) <= lsn < msgs.seqEnd :: 
            && lsn in lsnAddrIndex
            && lsnAddrIndex[lsn] == addr
        )
  }

  // It's not clear we need all these definitions.
  TransitiveLikes  // functional construction over LinkedJournal
  FunctionalIndex
  Index (also imper)
  ImperativeLikes (imper)
  
  // TODO invariant; move to proof
  predicate ImperativeAgreement(v: Variables) 
    requires v.WF()
  {
    && v.journal.truncatedJournal.diskView.Acyclic()
    // && v.branchedVars.branched.Valid()
    && TransitiveLikes(v.journal.truncatedJournal) == ImperativeLikes(v)
  }

  predicate ImperativeLikesMatchIndex(v: Variables)
  {
    ImperativeLikes(v) == multiset(v.lsnAddrIndex.Values)
  }

  predicate Inv(v: Variables)
  {
    var tj :=  v.journal.truncatedJournal;
    && v.WF()
    && tj.diskView.Acyclic()
    && v.lsnAddrIndex == BuildLsnAddrIndex(tj)
    && v.lsnAddrIndex.Values == tj.Representation() // Our index correctly tracks Linked representation
    && IndexDomainValid(v.lsnAddrIndex, tj)
    && IndexKeysMapToValidEntries(v.lsnAddrIndex, tj)
    && IndexRangeValid(v.lsnAddrIndex, tj)
    && tj.DiskIsTightWrtRepresentation()
    && ImperativeLikesMatchIndex(v)
  }
  
  lemma BuildLsnAddrIndexIgnoresBuildTight(dv: DiskView, btRoot: Pointer, root: Pointer)
    requires dv.Decodable(btRoot)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires dv.BuildTight(btRoot).Decodable(root)
    ensures dv.BuildTight(btRoot).WF()
    ensures dv.BuildTight(btRoot).Acyclic()
    ensures root.Some? ==> dv.boundaryLSN < dv.BuildTight(btRoot).entries[root.value].messageSeq.seqEnd
    ensures BuildLsnAddrIndexDefn(dv, root) == BuildLsnAddrIndexDefn(dv.BuildTight(btRoot), root)
    decreases dv.TheRankOf(root)
  {
    LinkedJournalRefinement.BuildTightIsAwesome(dv, btRoot);
    if root.Some? {
      BuildLsnAddrIndexIgnoresBuildTight(dv, btRoot, dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
    }
  }

  lemma RepresentationIgnoresBuildTight(dv: DiskView, btRoot: Pointer, root: Pointer)
    requires dv.Decodable(btRoot)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires dv.BuildTight(btRoot).Decodable(root)
    ensures dv.BuildTight(btRoot).WF()
    ensures dv.BuildTight(btRoot).Acyclic()
    ensures dv.BuildTight(btRoot).Representation(root) == dv.Representation(root)
    decreases dv.TheRankOf(root)
  {
    LinkedJournalRefinement.BuildTightIsAwesome(dv, btRoot);
    if root.Some? {
      RepresentationIgnoresBuildTight(dv, btRoot, dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
    }
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
