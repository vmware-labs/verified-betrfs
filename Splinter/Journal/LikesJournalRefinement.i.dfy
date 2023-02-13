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

  predicate {:opaque} IndexKeysMapToValidEntries(lsnAddrIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
  {
    forall lsn | lsn in lsnAddrIndex ::
      && lsnAddrIndex[lsn] in tj.diskView.entries
      && tj.diskView.entries[lsnAddrIndex[lsn]].ContainsLSN(lsn)
  }

  predicate {:opaque} IndexDomainValid(lsnAddrIndex: map<LSN, Address>, tj: TruncatedJournal)
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

  // The thrilling climax, the actual proof goal we want to use in lower
  // refinement layers.
  predicate ImperativeMatchesTransitive(v: Variables)
  {
    TransitiveLikes(v) == ImperativeLikes(v)
  }

  predicate Inv(v: Variables)
  {
    var tj :=  v.journal.truncatedJournal;
    && v.WF()
    && tj.diskView.Acyclic()
    && v.lsnAddrIndex == BuildLsnAddrIndex(tj)
    && v.lsnAddrIndex.Values == tj.Representation()
    && IndexDomainValid(v.lsnAddrIndex, tj)
    && IndexKeysMapToValidEntries(v.lsnAddrIndex, tj)
    && IndexRangeValid(v.lsnAddrIndex, tj)
    && tj.DiskIsTightWrtRepresentation()
    && ImperativeMatchesTransitive(v)
  }

  lemma BuildLsnAddrIndexIgnoresBuildTight(dv: DiskView, btRoot: Pointer, reprRoot: Pointer)
    requires dv.Decodable(btRoot)
    requires dv.Decodable(reprRoot)
    requires dv.Acyclic()
    requires reprRoot.Some? ==> dv.boundaryLSN < dv.entries[reprRoot.value].messageSeq.seqEnd
    requires dv.BuildTight(btRoot).Decodable(reprRoot)
    ensures dv.BuildTight(btRoot).WF()
    ensures dv.BuildTight(btRoot).Acyclic()
    ensures reprRoot.Some? ==> dv.boundaryLSN < dv.BuildTight(btRoot).entries[reprRoot.value].messageSeq.seqEnd
    ensures BuildLsnAddrIndexDefn(dv, reprRoot) == BuildLsnAddrIndexDefn(dv.BuildTight(btRoot), reprRoot)
    decreases dv.TheRankOf(reprRoot)
  {
    LinkedJournalRefinement.BuildTightIsAwesome(dv, btRoot);
    if reprRoot.Some? {
      BuildLsnAddrIndexIgnoresBuildTight(dv, btRoot, dv.entries[reprRoot.value].CroppedPrior(dv.boundaryLSN));
    }
  }

  lemma RepresentationIgnoresBuildTight(dv: DiskView, btRoot: Pointer, reprRoot: Pointer)
    requires dv.Decodable(btRoot)
    requires dv.Decodable(reprRoot)
    requires dv.Acyclic()
    requires dv.BuildTight(btRoot).Decodable(reprRoot)
    ensures dv.BuildTight(btRoot).WF()
    ensures dv.BuildTight(btRoot).Acyclic()
    ensures dv.BuildTight(btRoot).Representation(reprRoot) == dv.Representation(reprRoot)
    decreases dv.TheRankOf(reprRoot)
  {
    LinkedJournalRefinement.BuildTightIsAwesome(dv, btRoot);
    if reprRoot.Some? {
      RepresentationIgnoresBuildTight(dv, btRoot, dv.entries[reprRoot.value].CroppedPrior(dv.boundaryLSN));
    }
  }
  
  lemma InvInit(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures Inv(v)
  {
    LinkedJournalRefinement.BuildTightIsAwesome(tj.diskView, tj.freshestRec);
    var tightTj := tj.BuildTight();
    if tightTj.freshestRec.Some? {
      BuildLsnAddrIndexDomainValid(tightTj.diskView, tightTj.freshestRec);
    }
    BuildLsnAddrIndexRangeValid(tightTj.diskView, tightTj.freshestRec,tightTj.SeqEnd());
    BuildLsnAddrIndexGivesRepresentation(tightTj);
    BuildTightGivesRepresentation(tj.diskView, tj.freshestRec);
    RepresentationIgnoresBuildTight(tj.diskView, tj.freshestRec, tj.freshestRec);
    BuildLsnAddrIndexIgnoresBuildTight(tj.diskView, tj.freshestRec, tj.freshestRec);
  }

  // BuildLsnAddrIndex has domain that is a subset of [dv.boundaryLsn, tjEnd)
  // and every value is an entry in the disk
  lemma BuildLsnAddrIndexDomainValidHelper1(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd <= tjEnd
    ensures forall lsn :: lsn in BuildLsnAddrIndexDefn(dv, root) ==> dv.boundaryLSN <= lsn < tjEnd
    ensures forall lsn | lsn in BuildLsnAddrIndexDefn(dv, root) :: 
      && BuildLsnAddrIndexDefn(dv, root)[lsn] in dv.entries
      && dv.entries[BuildLsnAddrIndexDefn(dv, root)[lsn]].ContainsLSN(lsn)
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      BuildLsnAddrIndexDomainValidHelper1(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN), tjEnd);
    }
  }

  lemma BuildLsnAddrIndexDomainValidHelper2(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd == tjEnd
    requires root.None? ==> tjEnd <= dv.boundaryLSN
    ensures forall lsn :: dv.boundaryLSN <= lsn < tjEnd ==> lsn in BuildLsnAddrIndexDefn(dv, root)
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      var prior := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
      if prior.None? {
        BuildLsnAddrIndexDomainValidHelper2(dv, prior, dv.boundaryLSN);
      } else {
        BuildLsnAddrIndexDomainValidHelper2(dv, prior, dv.entries[prior.value].messageSeq.seqEnd);
      }
    }
  }

  // Wrapper for domain properties of BuildLsnAddrIndex
  lemma BuildLsnAddrIndexDomainValid(dv: DiskView, root: Pointer)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some?  // otherwise BuildLsnAddrIndex is trivially empty
    requires dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    ensures IndexDomainValid(BuildLsnAddrIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    ensures IndexKeysMapToValidEntries(BuildLsnAddrIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
  {
    BuildLsnAddrIndexDomainValidHelper1(dv, root, dv.entries[root.value].messageSeq.seqEnd);
    BuildLsnAddrIndexDomainValidHelper2(dv, root, dv.entries[root.value].messageSeq.seqEnd);
  }

  lemma BuildLsnAddrIndexRangeValid(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd == tjEnd
    requires root.None? ==> tjEnd <= dv.boundaryLSN
    requires IndexDomainValid(BuildLsnAddrIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    requires IndexKeysMapToValidEntries(BuildLsnAddrIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    ensures IndexRangeValid(BuildLsnAddrIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      var priorPtr := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
      BuildLsnAddrIndexOneStepSubmap(dv, root);
      if priorPtr.None? {
        BuildLsnAddrIndexRangeValid(dv, priorPtr, dv.boundaryLSN);
      } else {
        BuildLsnAddrIndexDomainValid(dv, priorPtr);
        BuildLsnAddrIndexRangeValid(dv, priorPtr, dv.entries[priorPtr.value].messageSeq.seqEnd);
      }
    }
  }

  // Building from the prior rec gives a submap
  lemma BuildLsnAddrIndexOneStepSubmap(dv: DiskView, root: Pointer)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some?
    requires dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    ensures IsSubMap(BuildLsnAddrIndexDefn(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN)), BuildLsnAddrIndexDefn(dv, root))
  {
    var priorPtr := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
    if priorPtr.Some? {
      BuildLsnAddrIndexDomainValid(dv, priorPtr);
    }
  }

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case ReadForRecoveryStep(depth) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        assert IndexRangeValid(v'.lsnAddrIndex, v'.journal.truncatedJournal);
      }
      case FreezeForCommitStep(depth) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        assert IndexRangeValid(v'.lsnAddrIndex, v'.journal.truncatedJournal);
      }
      case ObserveFreshJournalStep() => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        assert IndexRangeValid(v'.lsnAddrIndex, v'.journal.truncatedJournal);
      }
      case PutStep() => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        assert IndexRangeValid(v'.lsnAddrIndex, v'.journal.truncatedJournal);
      }
      case DiscardOldStep() => {
        DiscardOldStepPreservesWFAndIndex(v, v', lbl);
        var ranking := v.journal.truncatedJournal.diskView.TheRanking();  // witness to acyclicity
        assert v'.journal.truncatedJournal.diskView.ValidRanking(ranking);
        DiscardOldMaintainsReprIndex(v, v', lbl);
        BuildLsnAddrIndexGivesRepresentation(v'.journal.truncatedJournal);
        assert IndexRangeValid(v'.lsnAddrIndex, v'.journal.truncatedJournal);
        assert Inv(v');
      }
      case InternalJournalMarshalStep(cut, addr) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        InvNextInternalJournalMarshalStep(v, v', lbl, step);
        BuildLsnAddrIndexGivesRepresentation(v'.journal.truncatedJournal);
        assert IndexRangeValid(v'.lsnAddrIndex, v'.journal.truncatedJournal);
        assert Inv(v');
      }
      case InternalNoOpStep() => assert Inv(v');
    }
  }

  lemma {:timeLimitMultiplier 2} DiscardOldStepPreservesWFAndIndex(v: Variables, v': Variables, lbl: TransitionLabel)
    requires v.WF()
    requires IndexDomainValid(v.lsnAddrIndex, v.journal.truncatedJournal)
    requires IndexKeysMapToValidEntries(v.lsnAddrIndex, v.journal.truncatedJournal)
    requires IndexRangeValid(v.lsnAddrIndex, v.journal.truncatedJournal)
    requires v.journal.truncatedJournal.diskView.Acyclic()
    requires v.lsnAddrIndex == BuildLsnAddrIndex(v.journal.truncatedJournal)
    requires v.lsnAddrIndex.Values == v.journal.truncatedJournal.Representation()
    requires DiscardOld(v, v', lbl)
    ensures v'.WF()
    ensures IndexDomainValid(v'.lsnAddrIndex, v'.journal.truncatedJournal)
    ensures IndexKeysMapToValidEntries(v'.lsnAddrIndex, v'.journal.truncatedJournal)
    ensures IndexRangeValid(v'.lsnAddrIndex, v'.journal.truncatedJournal)
  {
    var tj := v.journal.truncatedJournal;
    var tj' := v'.journal.truncatedJournal;
    var oldBdy := tj.diskView.boundaryLSN;
    var newBdy := lbl.startLsn;
    DiscardOldStepPreservesWFDiskView(v, v', lbl);
    
    // prove tj'.diskView.IsNondanglingPointer(tj'.freshestRec);
    if tj'.freshestRec.Some? {
      var msgs := tj.diskView.entries[tj.freshestRec.value].messageSeq;
      var lsn := Mathematics.max(newBdy, msgs.seqStart); // witness
      assert lsn in v.lsnAddrIndex && v.lsnAddrIndex[lsn] == tj.freshestRec.value;
    }
  }

  lemma DiscardOldStepPreservesWFDiskView(v: Variables, v': Variables, lbl: TransitionLabel)
    requires v.WF()
    requires IndexDomainValid(v.lsnAddrIndex, v.journal.truncatedJournal)
    requires IndexKeysMapToValidEntries(v.lsnAddrIndex, v.journal.truncatedJournal)
    requires IndexRangeValid(v.lsnAddrIndex, v.journal.truncatedJournal)
    requires v.journal.truncatedJournal.diskView.Acyclic()
    requires v.lsnAddrIndex == BuildLsnAddrIndex(v.journal.truncatedJournal)
    requires v.lsnAddrIndex.Values == v.journal.truncatedJournal.Representation()
    requires DiscardOld(v, v', lbl)
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
          RepresentationContainment(addr, tj.freshestRec.value, tj.diskView);
        }
        // witness
        var x :| x in v.lsnAddrIndex && newBdy <= x && v.lsnAddrIndex[x] == prevAddr;
      }
    }
  }

  lemma RepresentationContainment(x: Address, y: Address, dv: DiskView)
    requires dv.Decodable(Pointer.Some(x))
    requires dv.Decodable(Pointer.Some(y))
    requires dv.Acyclic()
    requires x in dv.Representation(Pointer.Some(y))
    ensures dv.Representation(Pointer.Some(x)) <= dv.Representation(Pointer.Some(y))
    decreases dv.TheRankOf(Pointer.Some(y))
  {
    if x != y {
      RepresentationContainment(x, dv.entries[y].CroppedPrior(dv.boundaryLSN).value, dv);
    }
  }

  lemma BuildLsnAddrIndexWithSubDiskProducesSubMap(small: DiskView, big: DiskView, root: Pointer)
    requires small.Decodable(root)
    requires small.Acyclic()
    requires big.Decodable(root)
    requires big.Acyclic()
    requires root.Some? ==> small.boundaryLSN < small.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> big.boundaryLSN < big.entries[root.value].messageSeq.seqEnd
    requires small.IsSubDiskWithNewerLSN(big)
    ensures IsSubMap(BuildLsnAddrIndexDefn(small, root), BuildLsnAddrIndexDefn(big, root))
    decreases small.TheRankOf(root)
  {
    if root.Some? {
      BuildLsnAddrIndexWithSubDiskProducesSubMap(small, big, small.entries[root.value].CroppedPrior(small.boundaryLSN));
      var smallPrior := small.entries[root.value].CroppedPrior(small.boundaryLSN);
      if smallPrior.Some? {
        BuildLsnAddrIndexDomainValid(small, smallPrior);
      }
      var bigPrior := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      if bigPrior.Some? {
        BuildLsnAddrIndexDomainValid(big, bigPrior);
      }
    }
  }
 
  lemma DiscardOldMaintainsReprIndex(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires v'.WF()
    requires DiscardOld(v, v', lbl)
    requires v'.journal.truncatedJournal.diskView.Acyclic()
    ensures v'.lsnAddrIndex == BuildLsnAddrIndex(v'.journal.truncatedJournal);
  {
    var newBdy := lbl.startLsn;
    var tj := v.journal.truncatedJournal;
    var keepAddrs := lsnAddrIndexDiscardUpTo(v.lsnAddrIndex, newBdy).Values;
    var newEntries := MapRestrict(tj.diskView.entries, keepAddrs); 
    var newDiskView := LinkedJournal.DiskView(newBdy, newEntries);

    if newBdy < tj.SeqEnd() {
      assert IsSubMap(lsnAddrIndexDiscardUpTo(v.lsnAddrIndex, newBdy), BuildLsnAddrIndexDefn(newDiskView, tj.freshestRec)) 
      by {
        BuildLsnAddrIndexDomainValid(newDiskView, tj.freshestRec);
        BuildLsnAddrIndexWithSubDiskProducesSubMap(newDiskView, tj.diskView, tj.freshestRec);
      }
      assert IsSubMap(BuildLsnAddrIndexDefn(newDiskView, tj.freshestRec), lsnAddrIndexDiscardUpTo(v.lsnAddrIndex, newBdy)) 
      by {
        BuildLsnAddrIndexDomainValid(newDiskView, tj.freshestRec);
      }
    }
  }

  lemma BuildLsnAddrIndexGivesRepresentationHelper(dv: DiskView, root: Pointer) 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    decreases dv.TheRankOf(root)
// Gonna need to put this back -- commented out for timeout.
//    ensures forall lsn | lsn in BuildLsnAddrIndexDefn(dv, root) 
//      :: lsn < dv.entries[root.value].messageSeq.seqEnd
    ensures BuildLsnAddrIndexDefn(dv, root).Values == dv.Representation(root)
  {
    if root.Some? {
      BuildLsnAddrIndexGivesRepresentationHelper(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
      var currMsgs := dv.entries[root.value].messageSeq;
      var update :=  map x: LSN | Mathematics.max(dv.boundaryLSN, currMsgs.seqStart) <= x < currMsgs.seqEnd :: root.value;
      assert Mathematics.max(dv.boundaryLSN, currMsgs.seqStart) in update;  // witness for 0 < |update|
    }
  }

  lemma BuildLsnAddrIndexGivesRepresentation(tj: TruncatedJournal) 
    requires tj.WF()
    requires tj.diskView.Decodable(tj.freshestRec)
    requires tj.diskView.Acyclic()
    ensures BuildLsnAddrIndex(tj).Values == tj.Representation()
  {
    BuildLsnAddrIndexGivesRepresentationHelper(tj.diskView, tj.freshestRec);
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
    ensures BuildLsnAddrIndexDefn(small, ptr) == BuildLsnAddrIndexDefn(big, ptr)
    decreases if ptr.Some? then big.TheRanking()[ptr.value] else -1
  {
    assert small.ValidRanking(big.TheRanking());
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
    ensures v'.lsnAddrIndex == BuildLsnAddrIndex(v'.journal.truncatedJournal)
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


  lemma RepresentationLSNBound(tj: TruncatedJournal)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    ensures forall addr | addr in tj.Representation() ::
      && var block := tj.diskView.entries[addr];
      && tj.diskView.boundaryLSN < block.messageSeq.seqEnd
    decreases tj.diskView.TheRankOf(tj.freshestRec)
  {
    if tj.freshestRec.Some? {
      var subTj := TruncatedJournal.TruncatedJournal(
        tj.diskView.entries[tj.freshestRec.value].CroppedPrior(tj.diskView.boundaryLSN),
        tj.diskView
      );
      RepresentationLSNBound(subTj);
    }
  }

  lemma RepresentationWithSubDiskProducesSubset(small:DiskView, big: DiskView, root: Pointer)
    requires small.WF() && big.WF()
    requires small.Decodable(root)
    requires big.Decodable(root)
    requires small.Acyclic()
    requires big.Acyclic()
    requires small.IsSubDiskWithNewerLSN(big)
    ensures small.Representation(root) <= big.Representation(root)
    decreases small.TheRankOf(root)
  {
    if root.Some? {
      RepresentationWithSubDiskProducesSubset(small, big, small.entries[root.value].CroppedPrior(small.boundaryLSN));
      var smallPrior := small.entries[root.value].CroppedPrior(small.boundaryLSN);
      if smallPrior.Some? {
        BuildLsnAddrIndexDomainValid(small, smallPrior);
      }
      var bigPrior := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      if bigPrior.Some? {
        BuildLsnAddrIndexDomainValid(big, bigPrior);
      }
    }
  }

  lemma RepresentationWithSubDiskCompleteness(small:DiskView, big: DiskView, root: Pointer)
    requires small.WF() && big.WF()
    requires small.Decodable(root)
    requires big.Decodable(root)
    requires small.Acyclic()
    requires big.Acyclic()
    requires small.entries == big.entries
    requires big.boundaryLSN <= small.boundaryLSN
    ensures forall addr | addr in big.Representation(root) && small.boundaryLSN < big.entries[addr].messageSeq.seqEnd
              :: addr in small.Representation(root)
    decreases big.TheRankOf(root)
  {
    RepresentationWithSubDiskProducesSubset(small, big, root);
    if root.Some? {
      var bigPrior := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      RepresentationWithSubDiskCompleteness(small, big, bigPrior);
    }   
  }

  lemma RepresentationAcrossDiscardOld(tj: TruncatedJournal, newBdy: LSN) 
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.CanDiscardTo(newBdy)
    requires tj.DiscardOld(newBdy).diskView.Acyclic()
    ensures tj.DiscardOld(newBdy).Representation() <= tj.Representation()
    ensures forall addr | addr in tj.Representation() && addr !in tj.DiscardOld(newBdy).Representation()
      :: tj.diskView.entries[addr].messageSeq.seqEnd <= newBdy
  {
    RepresentationWithSubDiskProducesSubset(tj.DiscardOld(newBdy).diskView, tj.diskView, tj.freshestRec);
    RepresentationWithSubDiskCompleteness(tj.DiscardOld(newBdy).diskView, tj.diskView, tj.freshestRec);
  } 

  lemma DiscardedIndexContainsDiscardedRepresentation(tj: TruncatedJournal, lsnAddrIndex: map<LSN, Address>, newBdy: LSN)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.CanDiscardTo(newBdy)
    requires tj.DiskIsTightWrtRepresentation()
    requires tj.DiscardOld(newBdy).diskView.Acyclic()
    requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
    requires lsnAddrIndex == BuildLsnAddrIndex(tj)
    ensures forall x | x in lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy).Values 
      :: x in tj.DiscardOld(newBdy).Representation()
  {
    forall addr | addr in lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy).Values 
    ensures addr in tj.DiscardOld(newBdy).Representation()
    {
      if addr !in tj.DiscardOld(newBdy).Representation() {
        RepresentationAcrossDiscardOld(tj, newBdy);
        BuildLsnAddrIndexDomainValid(tj.diskView, tj.freshestRec);
        assert false;
      }
    }
  }

  lemma DiscardedRepresentationContainsDiscardedIndex(tj: TruncatedJournal, lsnAddrIndex: map<LSN, Address>, newBdy: LSN)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.CanDiscardTo(newBdy)
    requires tj.DiskIsTightWrtRepresentation()
    requires tj.DiscardOld(newBdy).diskView.Acyclic()
    requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
    requires lsnAddrIndex == BuildLsnAddrIndex(tj)
    requires IndexDomainValid(lsnAddrIndex, tj)
    requires IndexKeysMapToValidEntries(lsnAddrIndex, tj)
    requires IndexRangeValid(lsnAddrIndex, tj)
    ensures forall x | x in tj.DiscardOld(newBdy).Representation()
        :: x in lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy).Values 
  {
    forall addr | addr in tj.DiscardOld(newBdy).Representation()
    ensures addr in lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy).Values 
    {
      if addr !in lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy).Values {
        if addr in lsnAddrIndex.Values {
          forall lsn | lsn in lsnAddrIndex && lsnAddrIndex[lsn] == addr 
          ensures lsn < newBdy {
            if newBdy <= lsn {
              assert lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy)[lsn] == addr;
            }
          }
          var block := tj.diskView.entries[addr];
          assert block.messageSeq.seqEnd <= newBdy by {
            if newBdy < block.messageSeq.seqEnd {
              var x := Mathematics.max(newBdy, block.messageSeq.seqStart);
              assert IndexRangeValid(lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy), tj.DiscardOld(newBdy));
              assert x in lsnAddrIndex && lsnAddrIndex[x] == addr && newBdy <= x;
              assert false;
            }
          }
          RepresentationLSNBound(tj.DiscardOld(newBdy));
          assert false;
        } else {
          BuildLsnAddrIndexGivesRepresentation(tj);
          assert false;
        }
      }
    }
  }

  lemma BuildTightEquivalentToGarbageCollect(tj: TruncatedJournal, lsnAddrIndex: map<LSN, Address>, newBdy: LSN)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.CanDiscardTo(newBdy)
    requires tj.DiskIsTightWrtRepresentation()
    requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
    requires lsnAddrIndex == BuildLsnAddrIndex(tj)
    requires IndexDomainValid(lsnAddrIndex, tj)
    requires IndexKeysMapToValidEntries(lsnAddrIndex, tj)
    requires IndexRangeValid(lsnAddrIndex, tj)
    ensures MapRestrict(tj.diskView.entries, lsnAddrIndexDiscardUpTo(lsnAddrIndex, newBdy).Values)
      == tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries
  {
    // to get the fact that DiscardOld maintains acyclicity
    assert tj.diskView.DiscardOld(newBdy).ValidRanking(tj.diskView.TheRanking());
    
    LinkedJournalRefinement.BuildTightIsAwesome(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
    BuildTightGivesRepresentation(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
    assert tj.DiscardOld(newBdy).diskView.Representation(tj.freshestRec) == tj.DiscardOld(newBdy).Representation();  // trigger
    DiscardedIndexContainsDiscardedRepresentation(tj, lsnAddrIndex, newBdy);
    DiscardedRepresentationContainsDiscardedIndex(tj, lsnAddrIndex, newBdy);
  }

  lemma DiscardOldStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires Inv(v')
    requires NextStep(v, v', lbl, step)
    requires step.DiscardOldStep?
    ensures LinkedJournal.DiscardOld(I(v), I(v'), lbl.I())
  {
    var tj := v.journal.truncatedJournal;

    var lsnAddrIndex' := lsnAddrIndexDiscardUpTo(v.lsnAddrIndex, lbl.startLsn);
    var keepAddrs := lsnAddrIndex'.Values;
    var newEntries := MapRestrict(tj.diskView.entries, keepAddrs);
    var newDiskView := LinkedJournal.DiskView(lbl.startLsn, newEntries);

    if v.journal.truncatedJournal.SeqEnd() == lbl.startLsn {
      assert tj.diskView.DiscardOld(lbl.startLsn).ValidRanking(tj.diskView.TheRanking());
    } else {
      BuildTightEquivalentToGarbageCollect(tj, v.lsnAddrIndex, lbl.startLsn);
    }
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
        DiscardOldStepRefines(v, v', lbl, step);
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
