include "ReprJournal.i.dfy"
include "LinkedJournalRefinement.i.dfy"

module ReprJournalRefinement {
  import opened Maps
  import opened LSNMod
  import opened ReprJournal
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
      case InternalJournalReserveStep() => LinkedJournal.InternalNoOpStep()
      case InternalJournalFreeStep() => LinkedJournal.InternalNoOpStep()
      case InternalNoOpStep() => LinkedJournal.InternalNoOpStep()
    }
  }


// PROVE INVARIANTS

  predicate IndexKeysMapToValidEntries(reprIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
  {
    forall lsn | lsn in reprIndex ::
      && reprIndex[lsn] in tj.diskView.entries
      && tj.diskView.entries[reprIndex[lsn]].ContainsLSN(lsn)
  }

  predicate IndexDomainValid(reprIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
  {
    // reprIndex's domain is exactly the set of LSN between journal.SeqStart() and journal.SeqEnd()
    && (forall lsn :: lsn in reprIndex <==> tj.SeqStart() <= lsn < tj.SeqEnd())
  }

  predicate IndexRangeValid(reprIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
    requires IndexDomainValid(reprIndex, tj)
    requires IndexKeysMapToValidEntries(reprIndex, tj)
  {
    forall addr | addr in reprIndex.Values ::
      && var msgs := tj.diskView.entries[addr].messageSeq;
      && var boundaryLSN := tj.diskView.boundaryLSN;
      && (forall lsn | Mathematics.max(boundaryLSN, msgs.seqStart) <= lsn < msgs.seqEnd :: 
            && lsn in reprIndex
            && reprIndex[lsn] == addr
        )
  }

  predicate Inv(v: Variables)
  {
    var tj :=  v.journal.truncatedJournal;
    && v.WF()
    && tj.diskView.Acyclic()
    && v.reprIndex == BuildReprIndex(tj)
    && v.reprIndex.Values == tj.Representation()
    && IndexDomainValid(v.reprIndex, tj)
    && IndexKeysMapToValidEntries(v.reprIndex, tj)
    && IndexRangeValid(v.reprIndex, tj)
    && tj.DiskIsTightWrtRepresentation()
  }

  lemma BuildReprIndexIgnoresBuildTight(dv: DiskView, btRoot: Pointer, reprRoot: Pointer)
    requires dv.Decodable(btRoot)
    requires dv.Decodable(reprRoot)
    requires dv.Acyclic()
    requires reprRoot.Some? ==> dv.boundaryLSN < dv.entries[reprRoot.value].messageSeq.seqEnd
    requires dv.BuildTight(btRoot).Decodable(reprRoot)
    ensures dv.BuildTight(btRoot).WF()
    ensures dv.BuildTight(btRoot).Acyclic()
    ensures reprRoot.Some? ==> dv.boundaryLSN < dv.BuildTight(btRoot).entries[reprRoot.value].messageSeq.seqEnd
    ensures BuildReprIndexDefn(dv, reprRoot) == BuildReprIndexDefn(dv.BuildTight(btRoot), reprRoot)
    decreases dv.TheRankOf(reprRoot)
  {
    LinkedJournalRefinement.BuildTightIsAwesome(dv, btRoot);
    if reprRoot.Some? {
      BuildReprIndexIgnoresBuildTight(dv, btRoot, dv.entries[reprRoot.value].CroppedPrior(dv.boundaryLSN));
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
  
  lemma InvInit(v: Variables, gctj: GCTruncatedJournal)
    requires Init(v, gctj)
    ensures Inv(v)
  {
    var tj := gctj.journal;
    LinkedJournalRefinement.BuildTightIsAwesome(tj.diskView, tj.freshestRec);
    var tightTj := tj.BuildTight();
    if tightTj.freshestRec.Some? {
      BuildReprIndexDomainValid(tightTj.diskView, tightTj.freshestRec);
    }
    BuildReprIndexRangeValid(tightTj.diskView, tightTj.freshestRec,tightTj.SeqEnd());
    BuildReprIndexGivesRepresentation(tightTj);
    BuildTightGivesRepresentation(tj.diskView, tj.freshestRec);
    RepresentationIgnoresBuildTight(tj.diskView, tj.freshestRec, tj.freshestRec);
    BuildReprIndexIgnoresBuildTight(tj.diskView, tj.freshestRec, tj.freshestRec);
  }

  // BuildReprIndex has domain that is a subset of [dv.boundaryLsn, tjEnd)
  // and every value is an entry in the disk
  lemma BuildReprIndexDomainValidHelper1(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd <= tjEnd
    ensures forall lsn :: lsn in BuildReprIndexDefn(dv, root) ==> dv.boundaryLSN <= lsn < tjEnd
    ensures forall lsn | lsn in BuildReprIndexDefn(dv, root) :: 
      && BuildReprIndexDefn(dv, root)[lsn] in dv.entries
      && dv.entries[BuildReprIndexDefn(dv, root)[lsn]].ContainsLSN(lsn)
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      BuildReprIndexDomainValidHelper1(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN), tjEnd);
    }
  }

  lemma BuildReprIndexDomainValidHelper2(dv: DiskView, root: Pointer, tjEnd: LSN)
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
        BuildReprIndexDomainValidHelper2(dv, prior, dv.boundaryLSN);
      } else {
        BuildReprIndexDomainValidHelper2(dv, prior, dv.entries[prior.value].messageSeq.seqEnd);
      }
    }
  }

  // Wrapper for domain properties of BuildReprIndex
  lemma BuildReprIndexDomainValid(dv: DiskView, root: Pointer)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some?  // otherwise BuildReprIndex is trivially empty
    requires dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    ensures IndexDomainValid(BuildReprIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    ensures IndexKeysMapToValidEntries(BuildReprIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
  {
    BuildReprIndexDomainValidHelper1(dv, root, dv.entries[root.value].messageSeq.seqEnd);
    BuildReprIndexDomainValidHelper2(dv, root, dv.entries[root.value].messageSeq.seqEnd);
  }

  lemma BuildReprIndexRangeValid(dv: DiskView, root: Pointer, tjEnd: LSN)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    requires root.Some? ==> dv.entries[root.value].messageSeq.seqEnd == tjEnd
    requires root.None? ==> tjEnd <= dv.boundaryLSN
    requires IndexDomainValid(BuildReprIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    requires IndexKeysMapToValidEntries(BuildReprIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    ensures IndexRangeValid(BuildReprIndexDefn(dv, root), TruncatedJournal.TruncatedJournal(root, dv))
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      var priorPtr := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
      BuildReprIndexOneStepSubmap(dv, root);
      if priorPtr.None? {
        BuildReprIndexRangeValid(dv, priorPtr, dv.boundaryLSN);
      } else {
        BuildReprIndexDomainValid(dv, priorPtr);
        BuildReprIndexRangeValid(dv, priorPtr, dv.entries[priorPtr.value].messageSeq.seqEnd);
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
      BuildReprIndexDomainValid(dv, priorPtr);
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
        assert IndexRangeValid(v'.reprIndex, v'.journal.truncatedJournal);
      }
      case FreezeForCommitStep(depth) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        assert IndexRangeValid(v'.reprIndex, v'.journal.truncatedJournal);
      }
      case ObserveFreshJournalStep() => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        assert IndexRangeValid(v'.reprIndex, v'.journal.truncatedJournal);
      }
      case PutStep() => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        assert IndexRangeValid(v'.reprIndex, v'.journal.truncatedJournal);
      }
      case DiscardOldStep() => {
        DiscardOldStepPreservesWFAndIndex(v, v', lbl);
        var ranking := v.journal.truncatedJournal.diskView.TheRanking();  // witness to acyclicity
        assert v'.journal.truncatedJournal.diskView.ValidRanking(ranking);
        DiscardOldMaintainsReprIndex(v, v', lbl);
        BuildReprIndexGivesRepresentation(v'.journal.truncatedJournal);
        assert IndexRangeValid(v'.reprIndex, v'.journal.truncatedJournal);
        assert Inv(v');
      }
      case InternalJournalMarshalStep(cut, addr) => {
        assert LinkedJournal.NextStep(v.journal, v'.journal, lbl.I(), IStep(step));
        LinkedJournalRefinement.InvNext(v.journal, v'.journal, lbl.I());
        InvNextInternalJournalMarshalStep(v, v', lbl, step);
        BuildReprIndexGivesRepresentation(v'.journal.truncatedJournal);
        assert IndexRangeValid(v'.reprIndex, v'.journal.truncatedJournal);
        assert Inv(v');
      }
      case InternalJournalReserveStep() => assert Inv(v');
      case InternalJournalFreeStep() => assert Inv(v');
      case InternalNoOpStep() => assert Inv(v');
    }
  }

  lemma {:timeLimitMultiplier 2} DiscardOldStepPreservesWFAndIndex(v: Variables, v': Variables, lbl: TransitionLabel)
    requires v.WF()
    requires IndexDomainValid(v.reprIndex, v.journal.truncatedJournal)
    requires IndexKeysMapToValidEntries(v.reprIndex, v.journal.truncatedJournal)
    requires IndexRangeValid(v.reprIndex, v.journal.truncatedJournal)
    requires v.journal.truncatedJournal.diskView.Acyclic()
    requires v.reprIndex == BuildReprIndex(v.journal.truncatedJournal)
    requires v.reprIndex.Values == v.journal.truncatedJournal.Representation()
    requires DiscardOld(v, v', lbl)
    ensures v'.WF()
    ensures IndexDomainValid(v'.reprIndex, v'.journal.truncatedJournal)
    ensures IndexKeysMapToValidEntries(v'.reprIndex, v'.journal.truncatedJournal)
    ensures IndexRangeValid(v'.reprIndex, v'.journal.truncatedJournal)
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
      assert lsn in v.reprIndex && v.reprIndex[lsn] == tj.freshestRec.value;
    }
  }

  lemma DiscardOldStepPreservesWFDiskView(v: Variables, v': Variables, lbl: TransitionLabel)
    requires v.WF()
    requires IndexDomainValid(v.reprIndex, v.journal.truncatedJournal)
    requires IndexKeysMapToValidEntries(v.reprIndex, v.journal.truncatedJournal)
    requires IndexRangeValid(v.reprIndex, v.journal.truncatedJournal)
    requires v.journal.truncatedJournal.diskView.Acyclic()
    requires v.reprIndex == BuildReprIndex(v.journal.truncatedJournal)
    requires v.reprIndex.Values == v.journal.truncatedJournal.Representation()
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
        var x :| x in v.reprIndex && newBdy <= x && v.reprIndex[x] == prevAddr;
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
        BuildReprIndexDomainValid(small, smallPrior);
      }
      var bigPrior := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      if bigPrior.Some? {
        BuildReprIndexDomainValid(big, bigPrior);
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
        BuildReprIndexDomainValid(newDiskView, tj.freshestRec);
        BuildReprIndexWithSubDiskProducesSubMap(newDiskView, tj.diskView, tj.freshestRec);
      }
      assert IsSubMap(BuildReprIndexDefn(newDiskView, tj.freshestRec), reprIndexDiscardUpTo(v.reprIndex, newBdy)) 
      by {
        BuildReprIndexDomainValid(newDiskView, tj.freshestRec);
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

  lemma InitRefines(v: Variables, gctj: GCTruncatedJournal)
    requires Init(v, gctj)
    ensures LinkedJournal.Init(I(v), gctj.journal)
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
        BuildReprIndexDomainValid(small, smallPrior);
      }
      var bigPrior := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      if bigPrior.Some? {
        BuildReprIndexDomainValid(big, bigPrior);
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

  lemma DiscardedIndexContainsDiscardedRepresentation(tj: TruncatedJournal, reprIndex: map<LSN, Address>, newBdy: LSN)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.CanDiscardTo(newBdy)
    requires tj.DiskIsTightWrtRepresentation()
    requires tj.DiscardOld(newBdy).diskView.Acyclic()
    requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
    requires reprIndex == BuildReprIndex(tj)
    ensures forall x | x in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
      :: x in tj.DiscardOld(newBdy).Representation()
  {
    forall addr | addr in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
    ensures addr in tj.DiscardOld(newBdy).Representation()
    {
      if addr !in tj.DiscardOld(newBdy).Representation() {
        RepresentationAcrossDiscardOld(tj, newBdy);
        BuildReprIndexDomainValid(tj.diskView, tj.freshestRec);
        assert false;
      }
    }
  }

  lemma DiscardedRepresentationContainsDiscardedIndex(tj: TruncatedJournal, reprIndex: map<LSN, Address>, newBdy: LSN)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.CanDiscardTo(newBdy)
    requires tj.DiskIsTightWrtRepresentation()
    requires tj.DiscardOld(newBdy).diskView.Acyclic()
    requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
    requires reprIndex == BuildReprIndex(tj)
    requires IndexDomainValid(reprIndex, tj)
    requires IndexKeysMapToValidEntries(reprIndex, tj)
    requires IndexRangeValid(reprIndex, tj)
    ensures forall x | x in tj.DiscardOld(newBdy).Representation()
        :: x in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
  {
    forall addr | addr in tj.DiscardOld(newBdy).Representation()
    ensures addr in reprIndexDiscardUpTo(reprIndex, newBdy).Values 
    {
      if addr !in reprIndexDiscardUpTo(reprIndex, newBdy).Values {
        if addr in reprIndex.Values {
          forall lsn | lsn in reprIndex && reprIndex[lsn] == addr 
          ensures lsn < newBdy {
            if newBdy <= lsn {
              assert reprIndexDiscardUpTo(reprIndex, newBdy)[lsn] == addr;
            }
          }
          var block := tj.diskView.entries[addr];
          assert block.messageSeq.seqEnd <= newBdy by {
            if newBdy < block.messageSeq.seqEnd {
              var x := Mathematics.max(newBdy, block.messageSeq.seqStart);
              assert IndexRangeValid(reprIndexDiscardUpTo(reprIndex, newBdy), tj.DiscardOld(newBdy));
              assert x in reprIndex && reprIndex[x] == addr && newBdy <= x;
              assert false;
            }
          }
          RepresentationLSNBound(tj.DiscardOld(newBdy));
          assert false;
        } else {
          BuildReprIndexGivesRepresentation(tj);
          assert false;
        }
      }
    }
  }

  lemma BuildTightEquivalentToGarbageCollect(tj: TruncatedJournal, reprIndex: map<LSN, Address>, newBdy: LSN)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    requires tj.CanDiscardTo(newBdy)
    requires tj.DiskIsTightWrtRepresentation()
    requires tj.freshestRec.Some? ==> newBdy < tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd
    requires reprIndex == BuildReprIndex(tj)
    requires IndexDomainValid(reprIndex, tj)
    requires IndexKeysMapToValidEntries(reprIndex, tj)
    requires IndexRangeValid(reprIndex, tj)
    ensures MapRestrict(tj.diskView.entries, reprIndexDiscardUpTo(reprIndex, newBdy).Values)
      == tj.diskView.DiscardOld(newBdy).BuildTight(tj.freshestRec).entries
  {
    // to get the fact that DiscardOld maintains acyclicity
    assert tj.diskView.DiscardOld(newBdy).ValidRanking(tj.diskView.TheRanking());
    
    LinkedJournalRefinement.BuildTightIsAwesome(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
    BuildTightGivesRepresentation(tj.diskView.DiscardOld(newBdy), tj.freshestRec);
    assert tj.DiscardOld(newBdy).diskView.Representation(tj.freshestRec) == tj.DiscardOld(newBdy).Representation();  // trigger
    DiscardedIndexContainsDiscardedRepresentation(tj, reprIndex, newBdy);
    DiscardedRepresentationContainsDiscardedIndex(tj, reprIndex, newBdy);
  }

  lemma DiscardOldStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires Inv(v')
    requires NextStep(v, v', lbl, step)
    requires step.DiscardOldStep?
    ensures LinkedJournal.DiscardOld(I(v), I(v'), lbl.I())
  {
    var tj := v.journal.truncatedJournal;

    var reprIndex' := reprIndexDiscardUpTo(v.reprIndex, lbl.startLsn);
    var keepAddrs := reprIndex'.Values;
    var newEntries := MapRestrict(tj.diskView.entries, keepAddrs);
    var newDiskView := LinkedJournal.DiskView(lbl.startLsn, newEntries);

    if v.journal.truncatedJournal.SeqEnd() == lbl.startLsn {
      assert tj.diskView.DiscardOld(lbl.startLsn).ValidRanking(tj.diskView.TheRanking());
    } else {
      BuildTightEquivalentToGarbageCollect(tj, v.reprIndex, lbl.startLsn);
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
      case InternalJournalReserveStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
      case InternalJournalFreeStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
      case InternalNoOpStep() => {
        assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      }
    }
  }
}
