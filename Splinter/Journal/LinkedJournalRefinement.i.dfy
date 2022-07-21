// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournal.i.dfy"
include "PagedJournalRefinement.i.dfy"

module LinkedJournalRefinement
// TODO refines RefinementObligation(JournalLabels, PagedJournal)
{
  import opened Options
  import opened Maps
  import opened MsgHistoryMod
  import opened LSNMod
  import PagedJournal
  import PagedJournalRefinement
  import opened LinkedJournal


  function ILbl(lbl: TransitionLabel) : PagedJournal.TransitionLabel
    requires lbl.WF()
  {
    match lbl
      case ReadForRecoveryLabel(messages) => PagedJournal.ReadForRecoveryLabel(messages)
      case FreezeForCommitLabel(frozenJournal) => PagedJournal.FreezeForCommitLabel(ITruncatedJournal(frozenJournal))
      case QueryEndLsnLabel(endLsn) => PagedJournal.QueryEndLsnLabel(endLsn)
      case PutLabel(messages) => PagedJournal.PutLabel(messages)
      case DiscardOldLabel(startLsn, requireEnd) => PagedJournal.DiscardOldLabel(startLsn, requireEnd)
      case InternalJournalMarshalLabel(addrs) => PagedJournal.InternalLabel()
      case InternalLabel() => PagedJournal.InternalLabel()
  }

  predicate Inv(v: Variables)
  {
    && v.WF()
    && v.truncatedJournal.Decodable()
    && v.truncatedJournal.diskView.Acyclic()
  }

  function IPtr(dv: DiskView, ptr: Pointer) : (out: Option<PagedJournal.JournalRecord>)
      requires dv.Decodable(ptr)
      requires dv.Acyclic()
      ensures dv.BlockInBounds(ptr) && out.Some? ==> out.value.Valid(dv.boundaryLSN)
      decreases dv.TheRankOf(ptr)
  {
    if ptr.None?
    then None
    else
      var jr := dv.entries[ptr.value];
      Some(PagedJournal.JournalRecord(jr.messageSeq, IPtr(dv, jr.CroppedPrior(dv.boundaryLSN))))
  }

  function ITruncatedJournal(tj: TruncatedJournal) : (out: PagedJournal.TruncatedJournal)
    requires tj.Decodable()
    ensures out.WF()
  {
    PagedJournal.TruncatedJournal(tj.diskView.boundaryLSN, IPtr(tj.diskView, tj.freshestRec))   
  }

  function I(v: Variables) : PagedJournal.Variables
    requires v.WF()
    requires v.truncatedJournal.diskView.Acyclic()
  {
    PagedJournal.Variables(ITruncatedJournal(v.truncatedJournal), v.unmarshalledTail)
  }

  predicate IsTight(dv: DiskView, root: Pointer)
  {
    && dv.Decodable(root)
    && dv.Acyclic()
    && (forall other:DiskView |
        && other.Decodable(root)
        && other.Acyclic()
        && IPtr(dv, root) == IPtr(other, root)
        && other.IsSubDisk(dv)
        :: other == dv
      )
  }

  lemma IPtrFraming(dv1: DiskView, dv2: DiskView, ptr: Pointer)
    requires dv1.WF() && dv1.Acyclic()
    requires dv2.WF() && dv2.Acyclic()
    requires dv1.IsNondanglingPointer(ptr)
    requires dv1.IsSubDisk(dv2)
    requires dv1.boundaryLSN == dv2.boundaryLSN
    ensures IPtr(dv1, ptr) == IPtr(dv2, ptr)
    decreases dv1.TheRankOf(ptr)
  {
    if ptr.Some? {
      IPtrFraming(dv1, dv2, dv1.entries[ptr.value].CroppedPrior(dv1.boundaryLSN));
    }
  }

  lemma BuildTightRanks(dv: DiskView, ptr: Pointer)
    requires dv.Decodable(ptr)
    requires dv.Acyclic()
    requires ptr.Some?
    ensures
      var next := dv.entries[ptr.value].CroppedPrior(dv.boundaryLSN);
      forall addr | addr in dv.BuildTight(next).entries :: addr in dv.TheRanking() && dv.TheRanking()[addr] < dv.TheRanking()[ptr.value]
    decreases dv.TheRankOf(ptr)
  {
    var next := dv.entries[ptr.value].CroppedPrior(dv.boundaryLSN);
    if next.Some? {
      BuildTightRanks(dv, next);
    }
  }

  lemma BuildTightShape(big: DiskView, root: Pointer)
    requires root.Some?
    requires big.Decodable(root)
    requires big.Acyclic()
    ensures
      big.BuildTight(big.entries[root.value].CroppedPrior(big.boundaryLSN)) ==
      DiskView(big.boundaryLSN, MapRemove1(big.BuildTight(root).entries, root.value))
  {
    var next := big.entries[root.value].CroppedPrior(big.boundaryLSN);
    if next.Some? {
      BuildTightRanks(big, root);  // proves root.value !in big.BuildTight(next, ranking).entries;
    }
  }

  // TODO(jonh): how is this not IPtrFraming?
  lemma IPtrIgnoresExtraBlocks(small: DiskView, ptr: Pointer, big: DiskView)
    requires small.WF()
    requires small.IsNondanglingPointer(ptr)
    requires big.WF()
    requires big.Acyclic()
    requires small.IsSubDisk(big)
    ensures small.Acyclic()
    ensures IPtr(big, ptr) == IPtr(small, ptr)
    decreases big.TheRankOf(ptr)
  {
    assert small.PointersRespectRank(big.TheRanking()); // witness to small.Acyclic
    if ptr.Some? {
      var next := big.entries[ptr.value].CroppedPrior(big.boundaryLSN);
      IPtrIgnoresExtraBlocks(small, next, big);
      assert IPtr(big, ptr) == IPtr(small, ptr);
    }
  }

  lemma TightSubDisk(big: DiskView, root: Pointer, tight: DiskView)
    requires big.Decodable(root)
    requires tight == big.BuildTight(root)
    requires big.Acyclic()
    requires tight.IsSubDisk(big);
    ensures IsTight(tight, root)
    decreases big.TheRankOf(root)
  {
    if root.Some? {
      var next := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      var inner := big.BuildTight(next);
      BuildTightShape(big, root);
      TightSubDisk(big, next, inner);
      assert tight.PointersRespectRank(big.TheRanking());  // witness
      forall other:DiskView | other.Decodable(root) && other.Acyclic() && IPtr(tight, root) == IPtr(other, root) && other.IsSubDisk(tight)
          ensures other == tight {
        // any other tighter disk implies an "otherInner" disk tighter than inner, but inner.IsTight(next).
        var otherInner := DiskView(other.boundaryLSN, MapRemove1(other.entries, root.value));
        assert inner.PointersRespectRank(big.TheRanking());
        IPtrIgnoresExtraBlocks(otherInner, next, inner);
      }
    }
    assert tight.PointersRespectRank(big.TheRanking());  // witness
  }

  lemma BuildTightBuildsSubDisks(big: DiskView, root: Pointer)
    requires big.Decodable(root)
    requires big.Acyclic()
    ensures big.BuildTight(root).IsSubDisk(big)
    decreases big.TheRankOf(root)
  {
    if root.Some? {
      var next := big.entries[root.value].CroppedPrior(big.boundaryLSN);
      BuildTightBuildsSubDisks(big, next);
    }
  }

  lemma TightInterp(big: DiskView, root: Pointer, tight: DiskView)
    requires big.Decodable(root)
    requires tight == big.BuildTight(root)
    requires big.Acyclic()
    ensures tight.IsSubDisk(big)
    ensures IsTight(tight, root)
    ensures tight.Decodable(root)
    ensures IPtr(tight, root) == IPtr(big, root)
    ensures tight.Acyclic()
    decreases big.TheRankOf(root)
  {
    if root.None? {
      assert tight.PointersRespectRank(big.TheRanking());
    } else {
      BuildTightBuildsSubDisks(big, root);
      TightSubDisk(big, root, tight);
      assert tight.PointersRespectRank(big.TheRanking());  // witness to Acyclic
      IPtrIgnoresExtraBlocks(tight, root, big);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // non-state-machine function & predicate refinement lemmas

  lemma MkfsRefines()
    ensures Mkfs().diskView.Acyclic()
    ensures ITruncatedJournal(Mkfs()) == PagedJournal.Mkfs()
  {
    assert Mkfs().diskView.PointersRespectRank(map[]);  // witness to exists ranking
  }

  //////////////////////////////////////////////////////////////////////////////
  // State machine refinement

  lemma InvInit(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures Inv(v)
  {}

  lemma IPtrOutputValid(dv: DiskView, ptr: Pointer) 
    requires dv.Decodable(ptr)
    requires dv.Acyclic()
    requires dv.BlockInBounds(ptr)
    ensures IPtr(dv, ptr).Some? ==> IPtr(dv, ptr).value.Valid(dv.boundaryLSN)
    decreases dv.TheRankOf(ptr)
  {
    if ptr.Some? {
      IPtrOutputValid(dv, dv.entries[ptr.value].CroppedPrior(dv.boundaryLSN));  
    }
  }

  lemma DiscardInterp(bef: DiskView, lsn: LSN, aft: DiskView, ptr: Pointer)
    requires bef.WF()
    requires bef.Acyclic()
    requires bef.boundaryLSN <= lsn
    requires aft == bef.DiscardOld(lsn)
    requires bef.BlockInBounds(ptr)
    requires aft.BlockInBounds(ptr)
    ensures aft.Acyclic()
    ensures IPtr(bef, ptr).Some? ==> IPtr(bef, ptr).value.Valid(lsn)
    ensures IPtr(aft, ptr) == PagedJournal.DiscardOldJournalRec(IPtr(bef, ptr), lsn)
    decreases if ptr.Some? then bef.TheRanking()[ptr.value] else -1
  {
    IPtrOutputValid(bef, ptr);
    assert aft.PointersRespectRank(bef.TheRanking());
    if ptr.Some? && lsn < bef.entries[ptr.value].messageSeq.seqStart {
      DiscardInterp(bef, lsn, aft, aft.entries[ptr.value].CroppedPrior(aft.boundaryLSN));
    }
  }

  lemma TJDiscardInterp(tj: TruncatedJournal, lsn: LSN, discarded: TruncatedJournal)
    requires tj.WF()
    requires tj.diskView.Acyclic()
    // requires ITruncatedJournal(tj).WF()
    requires tj.SeqStart() <= lsn <= tj.SeqEnd()
    requires discarded == tj.DiscardOld(lsn)
    ensures discarded.diskView.Acyclic();
    // ensures ITruncatedJournal(tj).WF();
    ensures ITruncatedJournal(tj).DiscardOldDefn(lsn) == ITruncatedJournal(discarded)
  {
    assert discarded.diskView.PointersRespectRank(tj.diskView.TheRanking());
    DiscardInterp(tj.diskView, lsn, discarded.diskView, discarded.freshestRec);
  }
    
    // TODO(jonh): how does this relate to IPtrFraming!?
  lemma SubDiskInterp(small: DiskView, big: DiskView, ptr: Pointer)
    requires big.WF()
    requires big.Acyclic()
    requires small.WF()
    requires small.IsSubDisk(big)
    requires small.boundaryLSN == big.boundaryLSN
    requires small.IsNondanglingPointer(ptr)
    ensures small.Acyclic()
    ensures IPtr(small, ptr) == IPtr(big, ptr)
    decreases if ptr.Some? then big.TheRanking()[ptr.value] else -1
  {
    assert small.PointersRespectRank(big.TheRanking());
    if ptr.Some? {
      var jr := big.entries[ptr.value];
      SubDiskInterp(small, big, jr.CroppedPrior(big.boundaryLSN));
    }
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
    } else if step.ObserveFreshJournalStep? {
      assert Inv(v');
    } else if step.PutStep? {
      assert Inv(v');
    } else if step.DiscardOldStep? {
      var lsn := lbl.startLsn;
      var croppedTJ := v.truncatedJournal.DiscardOld(lsn);
      var tightTJ := croppedTJ.BuildTight();

      assert croppedTJ.diskView.PointersRespectRank(v.truncatedJournal.diskView.TheRanking());  // witness to Acyclic
      TightInterp(croppedTJ.diskView, croppedTJ.freshestRec, tightTJ.diskView);

      if !(v.unmarshalledTail.seqStart <= lsn) {
        DiscardInterp(croppedTJ.diskView, lsn, croppedTJ.diskView.DiscardOld(lsn), v.truncatedJournal.freshestRec);
        SubDiskInterp(tightTJ.diskView, croppedTJ.diskView, croppedTJ.freshestRec);
        TJDiscardInterp(v.truncatedJournal, lsn, croppedTJ);
        assert ITruncatedJournal(croppedTJ) == ITruncatedJournal(v.truncatedJournal).DiscardOldDefn(lsn); // Trigger for v'.I().WF()
      }
    } else if step.InternalJournalMarshalStep? {
      var rank :| v.truncatedJournal.diskView.PointersRespectRank(rank);
      var rank' := rank[lbl.addr :=
          if v.truncatedJournal.freshestRec.None? then 0
          else rank[v.truncatedJournal.freshestRec.value]+1];
      assert v'.truncatedJournal.diskView.PointersRespectRank(rank'); // new rank witness to Acyclic

      IPtrFraming(v.truncatedJournal.diskView, v'.truncatedJournal.diskView, v.truncatedJournal.freshestRec);
    } else if step.InternalNoOpStep? {
      assert Inv(v');
    } else {
      assert false;
    }
  }

  lemma InitRefines(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures PagedJournal.Init(I(v), ITruncatedJournal(tj))
  {
  }
  

  lemma PointerAfterCropCommutesWithInterpretation(dv: DiskView, ptr: Pointer, bdy: LSN, depth: nat) 
    requires dv.Decodable(ptr)
    requires dv.Acyclic()
    requires dv.BlockInBounds(ptr)
    requires bdy == dv.boundaryLSN
    requires dv.CanCrop(ptr, depth)
    requires dv.PointerAfterCrop(ptr, depth).Some?
    ensures PagedJournal.OptRecCanCropHeadRecords(IPtr(dv, ptr), bdy, depth)
    ensures PagedJournal.OptRecCanCropHeadRecords(IPtr(dv, ptr), bdy, depth+1)
    ensures IPtr(dv, dv.PointerAfterCrop(ptr, depth)) == PagedJournal.OptRecCropHeadRecords(IPtr(dv, ptr), bdy, depth)
    decreases depth
  {
    if 0 < depth {
      PointerAfterCropCommutesWithInterpretation(dv, dv.entries[ptr.value].CroppedPrior(bdy), bdy, depth-1);
      assert IPtr(dv, dv.PointerAfterCrop(ptr, depth)) 
        == PagedJournal.OptRecCropHeadRecords(IPtr(dv, ptr), bdy, depth); // trigger
    }
  }

  lemma PointerAfterCropCommutesWithInterpretation_NoSome(dv: DiskView, ptr: Pointer, depth: nat) 
    requires dv.Decodable(ptr)
    requires dv.Acyclic()
    requires dv.BlockInBounds(ptr)
    requires dv.CanCrop(ptr, depth)
    ensures PagedJournal.OptRecCanCropHeadRecords(IPtr(dv, ptr), dv.boundaryLSN, depth)
    ensures IPtr(dv, dv.PointerAfterCrop(ptr, depth)) == PagedJournal.OptRecCropHeadRecords(IPtr(dv, ptr), dv.boundaryLSN, depth)
    decreases depth
  {
    var bdy := dv.boundaryLSN;
    if 0 < depth {
      PointerAfterCropCommutesWithInterpretation_NoSome(dv, dv.entries[ptr.value].CroppedPrior(bdy), depth-1);
      assert IPtr(dv, dv.PointerAfterCrop(ptr, depth)) 
        == PagedJournal.OptRecCropHeadRecords(IPtr(dv, ptr), bdy, depth); // trigger
    }
  }

  lemma DiscardOldCommutes(dv: DiskView, ptr: Pointer, newBdy: LSN) 
    requires dv.Decodable(ptr)
    requires dv.Acyclic()
    requires dv.boundaryLSN <= newBdy
    requires ptr.Some? ==> newBdy < dv.entries[ptr.value].messageSeq.seqEnd
    requires dv.BlockInBounds(ptr)
    ensures dv.DiscardOld(newBdy).Acyclic()
    ensures IPtr(dv, ptr).Some? ==> IPtr(dv, ptr).value.Valid(newBdy)  // satifies DiscardOldJournalRec prereq
    ensures PagedJournal.DiscardOldJournalRec(IPtr(dv, ptr), newBdy) == IPtr(dv.DiscardOld(newBdy), ptr)
    decreases dv.TheRankOf(ptr)
  {
    assert dv.DiscardOld(newBdy).PointersRespectRank(dv.TheRanking());  // witness to Acyclic
    if ptr.Some? {
      var nextPtr := dv.entries[ptr.value].CroppedPrior(newBdy);
      PagedJournalRefinement.DiscardValid(IPtr(dv, ptr).value, dv.boundaryLSN, newBdy);
      DiscardOldCommutes(dv, nextPtr, newBdy);
    }
  }

  lemma TjDiscardOldCommutes(tj: TruncatedJournal, newBdy: LSN)
    requires tj.Decodable()
    requires tj.CanDiscardTo(newBdy)
    ensures tj.DiscardOld(newBdy).Decodable()   // prereq for ITruncatedJournal
    ensures ITruncatedJournal(tj).CanDiscardTo(newBdy)  // prereq for DiscardOld
    ensures ITruncatedJournal(tj.DiscardOld(newBdy)) == ITruncatedJournal(tj).DiscardOldDefn(newBdy)
  {
    assert tj.diskView.DiscardOld(newBdy).PointersRespectRank(tj.diskView.TheRanking());  // witness to Acyclic
    if newBdy < tj.SeqEnd() {
      DiscardOldCommutes(tj.diskView, tj.freshestRec, newBdy);
    }
  }

  // This is a wrapper around the ugly expression
  predicate PagedTJCanCrop(itj: PagedJournal.TruncatedJournal, depth: nat)
  {
    PagedJournal.OptRecCanCropHeadRecords(itj.freshestRec, itj.boundaryLSN, depth)
  }

  // todo: this is duplicated in Betree/PivotBetreeRefinement
  lemma CommuteTransitivity<L,H>(I: L->H, f: L->L, F: H->H, g: L->L, G: H->H)
    requires forall x :: I(f(x))==F(I(x))
    requires forall x :: I(g(x))==G(I(x))
    ensures forall x :: I(g(f(x)))==G(F(I(x)))
  {
    // See Tony's phone cam picture of the proof that we wrote on the whiteboard
    // but which dafny doesn't need; eyeroll
  }

  lemma CanCropMonotonic(tj: TruncatedJournal, depth: nat, more:nat) 
    requires depth < more
    requires tj.CanCrop(more)
    ensures tj.CanCrop(depth)
    decreases depth
  {
    if 0 < depth {
      var tjNext := TruncatedJournal(tj.diskView.entries[tj.freshestRec.value].CroppedPrior(tj.diskView.boundaryLSN), tj.diskView);
      CanCropMonotonic(tjNext, depth-1, more-1);
    }
  }

  lemma CropDecreasesSeqEnd(tj: TruncatedJournal, depth: nat) 
    requires tj.CanCrop(depth)
    ensures depth == 0 ==> tj.Crop(depth).SeqEnd() == tj.SeqEnd()
    ensures 0 < depth ==> tj.Crop(depth).SeqEnd() < tj.SeqEnd()
    decreases depth
  {
    if 0 < depth {
      var tjNext := TruncatedJournal(tj.diskView.entries[tj.freshestRec.value].CroppedPrior(tj.diskView.boundaryLSN), tj.diskView);
      CanCropMonotonic(tj, depth-1, depth); 
      CropDecreasesSeqEnd(tjNext, depth-1);
    }
  }

  lemma CanCropIncrement(tj: TruncatedJournal, depth: nat) 
    requires 0 < depth
    requires tj.WF()
    requires tj.freshestRec.Some?
    requires tj.CanCrop(1)
    requires tj.Crop(1).CanCrop(depth-1)
    ensures tj.CanCrop(depth)
    decreases depth
  {
    if 1 < depth {
      var tjSuffix := tj.Crop(1);
      CanCropIncrement(tjSuffix, depth-1);
    }
  }

  lemma PagedTjCanCropImpliesLinkedTjCanCrop(tj: TruncatedJournal, itj: PagedJournal.TruncatedJournal, depth: nat) 
    requires tj.Decodable()
    requires itj == ITruncatedJournal(tj)
    requires PagedJournal.OptRecCanCropHeadRecords(itj.freshestRec, itj.boundaryLSN, depth)
    ensures tj.CanCrop(depth)
    decreases depth
  {
    if 0 < depth {
      var tjNext := TruncatedJournal(tj.diskView.entries[tj.freshestRec.value].CroppedPrior(tj.diskView.boundaryLSN), tj.diskView);
      var itjNext := PagedJournal.TruncatedJournal(itj.boundaryLSN, itj.freshestRec.value.priorRec);
      PagedTjCanCropImpliesLinkedTjCanCrop(tjNext, itjNext, depth-1);
      CanCropIncrement(tj, depth);
    } 
  }

  lemma LinkedTjCanCropImpliesPagedTjCanCrop(tj: TruncatedJournal, itj: PagedJournal.TruncatedJournal, depth: nat) 
    requires tj.Decodable()
    requires itj == ITruncatedJournal(tj)
    requires tj.CanCrop(depth)
    ensures PagedTJCanCrop(itj, depth)
    decreases depth
  {
    if 0 < depth {
      var tjNext := TruncatedJournal(tj.diskView.entries[tj.freshestRec.value].CroppedPrior(tj.diskView.boundaryLSN), tj.diskView);
      var itjNext := PagedJournal.TruncatedJournal(itj.boundaryLSN, itj.freshestRec.value.priorRec);
      LinkedTjCanCropImpliesPagedTjCanCrop(tjNext, itjNext, depth-1);
      CanCropIncrement(tj, depth);
    }
  }

  lemma CropHeadComposedWithDiscardOldCommutes(tj: TruncatedJournal, newBdy: LSN, depth: nat)
    requires tj.Decodable()
    requires tj.CanCrop(depth)
    ensures PagedTJCanCrop(ITruncatedJournal(tj), depth)  // prereq
    requires tj.Crop(depth).CanDiscardTo(newBdy)
    ensures tj.CanDiscardTo(newBdy)   // prereq
    ensures ITruncatedJournal(tj).CropHeadRecords(depth).CanDiscardTo(newBdy)  // prereq
    ensures tj.Crop(depth).DiscardOld(newBdy).Decodable()  // prereq
    ensures ITruncatedJournal(tj).CropHeadRecords(depth).DiscardOldDefn(newBdy)
      == ITruncatedJournal(tj.Crop(depth).DiscardOld(newBdy))
  {
    var dummy := Mkfs();
    var idummy := ITruncatedJournal(dummy);
    var i := (tj:TruncatedJournal) => if tj.Decodable() then ITruncatedJournal(tj) else idummy;
    var f := (tj:TruncatedJournal) => if tj.Decodable() && tj.CanCrop(depth) then tj.Crop(depth) else dummy;
    var g := (tj:TruncatedJournal) => if tj.Decodable() && tj.CanDiscardTo(newBdy) then tj.DiscardOld(newBdy) else dummy;
    var F := (itj:PagedJournal.TruncatedJournal) => if PagedJournal.OptRecCanCropHeadRecords(itj.freshestRec, itj.boundaryLSN, depth) then itj.CropHeadRecords(depth) else idummy;
    var G := (itj:PagedJournal.TruncatedJournal) => if itj.WF() && itj.CanDiscardTo(newBdy) then itj.DiscardOldDefn(newBdy) else idummy;

    forall tjx ensures i(f(tjx))==F(i(tjx)) {
      if tjx.Decodable() && tjx.CanCrop(depth) { 
        PointerAfterCropCommutesWithInterpretation_NoSome(tjx.diskView, tjx.freshestRec, depth);
      } else {
        if tjx.Decodable() {
          if PagedJournal.OptRecCanCropHeadRecords(i(tjx).freshestRec, i(tjx).boundaryLSN, depth) {
            PagedTjCanCropImpliesLinkedTjCanCrop(tjx, i(tjx), depth);
            // Contradiction
          }
        }
      }
    }
    assert ITruncatedJournal(f(tj))==F(ITruncatedJournal(tj));  // trigger

    forall tjx ensures i(g(tjx))==G(i(tjx)) {
      if tjx.Decodable() && tjx.CanDiscardTo(newBdy) {
        TjDiscardOldCommutes(tjx, newBdy);
      } 
    }
    CommuteTransitivity(i, f, F, g, G);
    assert G(F(ITruncatedJournal(tj))) == ITruncatedJournal(tj.Crop(depth).DiscardOld(newBdy));  // trigger
    LinkedTjCanCropImpliesPagedTjCanCrop(tj, ITruncatedJournal(tj), depth);
    CropDecreasesSeqEnd(tj, depth);
  }

  lemma BuildTightIsAwesome(dv: DiskView, root: Pointer) 
    requires dv.Decodable(root)
    requires dv.Decodable(root)
    requires dv.Acyclic()
    ensures dv.BuildTight(root).IsSubDisk(dv)
    ensures dv.BuildTight(root).WF()
    ensures dv.BuildTight(root).Acyclic()
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      var nextPtr := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
      BuildTightIsAwesome(dv, nextPtr);
    }
    assert dv.BuildTight(root).PointersRespectRank(dv.TheRanking());  // witness
  }

  function BuildTightAwesome(dv: DiskView, root: Pointer) : (out: DiskView) 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    ensures dv.BuildTight(root).IsSubDisk(dv)
    ensures out.Decodable(root)
    ensures out.Acyclic()
  {
    BuildTightIsAwesome(dv, root);
    dv.BuildTight(root)
  }

  lemma BuildTightMaintainsInterpretation(dv: DiskView, root: Pointer) 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    ensures IPtr(dv, root) == IPtr(BuildTightAwesome(dv, root), root)
    decreases dv.TheRankOf(root)
  {
    if root.Some? {
      var next := dv.entries[root.value].CroppedPrior(dv.boundaryLSN);
      BuildTightMaintainsInterpretation(dv, next);
      IPtrFraming(BuildTightAwesome(dv, root), dv,  dv.entries[root.value].CroppedPrior(dv.boundaryLSN));
    }
  }

  lemma FreezeForCommitRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires Next(v, v', lbl)
    requires NextStep(v, v', lbl, step)
    requires step.FreezeForCommitStep?
    ensures PagedJournal.FreezeForCommit(I(v), I(v'), ILbl(lbl), step.depth)
  {
    var newBdy := ILbl(lbl).frozenJournal.boundaryLSN;
    var depth := step.depth;
    var dv := v.truncatedJournal.diskView;
    PointerAfterCropCommutesWithInterpretation_NoSome(dv, v.truncatedJournal.freshestRec, depth);
    CropHeadComposedWithDiscardOldCommutes(v.truncatedJournal, newBdy, depth);
    var croppedPtr := dv.PointerAfterCrop(v.truncatedJournal.freshestRec, depth);
    var croppedTj := TruncatedJournal(croppedPtr, v.truncatedJournal.diskView);
    BuildTightMaintainsInterpretation(croppedTj.DiscardOld(newBdy).diskView, croppedTj.DiscardOld(newBdy).freshestRec);
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures PagedJournal.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    if step.ReadForRecoveryStep? {
      PointerAfterCropCommutesWithInterpretation(v.truncatedJournal.diskView, v.truncatedJournal.freshestRec, v.truncatedJournal.diskView.boundaryLSN, step.depth);
      assert PagedJournal.NextStep(I(v), I(v'), ILbl(lbl), PagedJournal.ReadForRecoveryStep(step.depth)); // witness step
    } else if step.FreezeForCommitStep? {
      FreezeForCommitRefines(v, v', lbl, step);
      assert PagedJournal.NextStep(I(v), I(v'), ILbl(lbl), PagedJournal.FreezeForCommitStep(step.depth)); // witness step
    } else if step.ObserveFreshJournalStep? {
      assert PagedJournal.NextStep(I(v), I(v'), ILbl(lbl), PagedJournal.ObserveFreshJournalStep()); // witness step
    } else if step.PutStep? {
      assert PagedJournal.NextStep(I(v), I(v'), ILbl(lbl), PagedJournal.PutStep()); // witness step
    } else if step.DiscardOldStep? {
      var lsn := lbl.startLsn;
      if !(v.unmarshalledTail.seqStart <= lsn) {
        var croppedTJ := v.truncatedJournal.DiscardOld(lbl.startLsn);
        DiscardInterp(v.truncatedJournal.diskView, lsn, croppedTJ.diskView, v.truncatedJournal.freshestRec);
        TightInterp(croppedTJ.diskView, croppedTJ.freshestRec, v'.truncatedJournal.diskView);
        SubDiskInterp(v'.truncatedJournal.diskView, croppedTJ.diskView, croppedTJ.freshestRec);
      }
      assert PagedJournal.NextStep(I(v), I(v'), ILbl(lbl), PagedJournal.DiscardOldStep()); // witness step
    } else if step.InternalJournalMarshalStep? {
      IPtrFraming(v.truncatedJournal.diskView, v'.truncatedJournal.diskView, v.truncatedJournal.freshestRec);
      assert PagedJournal.NextStep(I(v), I(v'), ILbl(lbl), PagedJournal.InternalJournalMarshalStep(step.cut)); // witness step
    } else if step.InternalNoOpStep? {
      assert PagedJournal.NextStep(I(v), I(v'), ILbl(lbl), PagedJournal.InternalNoOpStep()); // witness step
    } else {
      assert false;
    }
  }

  // Exporting a utility for BlockCoordSystem to reason about the TruncatedJournal
  // it takes away for inFlight.
//  //////////////////////////////////////////////////////////////////////////////
//  // Rob strategy
//  predicate InFlightMemberOfEphemeral(eph: Variables, inFlight: TruncatedJournal)
//  {
//    && inFlight.diskView.IsSubDisk(eph.diskView)
//    && eph.diskView.boundaryLSN <= inFlight.diskView.boundaryLSN
//    && inFlight.freshestRec somewhere in eph.receipt
//  }
//
//  lemma RobStyle(eph: Variables, inFlight: TruncatedJournal)
//    requires InFlightMemberOfEphemeral(eph, inFlight)
//    ensures inFlight.diskView.IsSubDisk(eph.DiscardOld(inFlight.SeqStart()).diskView)
//
//  lemma RobAdditionalOverwhelmingBurden(v: Variables, v': Variables, inFlight: TruncatedJournal)
//    requires InFlightMemberOfEphemeral(v, inFlight)
//    requires Next(v, v', anyLabel)
//    ensures InFlightMemberOfEphemeral(v', inFlight)
  //////////////////////////////////////////////////////////////////////////////

  // This is a piece of an invariant that BlockCoordinationSystem maintains,
  // not an invariant of the LinkedJournal.
  predicate InFlightSubDiskProperty(v: Variables, inFlight: TruncatedJournal)
  {
    && v.WF()
    && inFlight.WF()
    && v.truncatedJournal.diskView.boundaryLSN <= inFlight.SeqStart()
    && inFlight.SeqStart() <= v.truncatedJournal.SeqEnd() // Not discarding pages that haven't been appended yet
    && inFlight.diskView.IsSubDisk(v.truncatedJournal.DiscardOld(inFlight.SeqStart()).BuildTight().diskView)
  }

  lemma LemmaBuildTightPreservesSubDiskCommonRoot(small: TruncatedJournal, big: TruncatedJournal) 
    requires small.Decodable()
    requires big.Decodable()
    requires small.freshestRec == big.freshestRec
    requires small.diskView.IsSubDisk(big.diskView)
    ensures small.BuildTight().diskView.IsSubDisk(big.BuildTight().diskView)
    decreases small.diskView.TheRankOf(small.freshestRec)
  {
    if small.freshestRec.None? {
      assert small.BuildTight().diskView.IsSubDisk(big.BuildTight().diskView);
    } else {
      var smallSuffix := TruncatedJournal(small.diskView.entries[big.freshestRec.value].CroppedPrior(small.diskView.boundaryLSN), small.diskView);
      var bigSuffix := TruncatedJournal(big.diskView.entries[big.freshestRec.value].CroppedPrior(big.diskView.boundaryLSN), big.diskView);
      LemmaBuildTightPreservesSubDiskCommonRoot(smallSuffix, bigSuffix);
    }
  }

  lemma LemmaBuildTightPreservesSubDisk(small: TruncatedJournal, big: TruncatedJournal, depth: nat) 
    requires small.Decodable()
    requires big.Decodable()
    requires big.CanCrop(depth)
    requires small.freshestRec == big.Crop(depth).freshestRec
    requires small.diskView.IsSubDisk(big.diskView)
    ensures small.BuildTight().diskView.IsSubDisk(big.BuildTight().diskView)
    decreases depth
  {
    if depth == 0 {
      LemmaBuildTightPreservesSubDiskCommonRoot(small, big);
    } else {
      var bigSuffix := TruncatedJournal(big.diskView.entries[big.freshestRec.value].CroppedPrior(big.diskView.boundaryLSN), big.diskView);
      LemmaBuildTightPreservesSubDisk(small, bigSuffix, depth-1);
      // invoke awesomeness
      assert big.BuildTight().diskView == BuildTightAwesome(big.diskView, big.freshestRec);
      assert bigSuffix.BuildTight().diskView == BuildTightAwesome(bigSuffix.diskView, bigSuffix.freshestRec);
    }
  }

  lemma DiscardOldCanCropIncrement(tj: TruncatedJournal, depth: nat, newBdy: LSN) 
    requires 0 < depth
    requires tj.WF()
    requires tj.CanCrop(1) && tj.Crop(1).CanDiscardTo(newBdy) ==> tj.Crop(1).DiscardOld(newBdy).CanCrop(depth-1)
    ensures tj.CanCrop(1) && tj.Crop(1).CanDiscardTo(newBdy) ==> tj.DiscardOld(newBdy).CanCrop(depth)
    decreases depth
  {
    if tj.CanCrop(1) && tj.Crop(1).CanDiscardTo(newBdy) {
      if 1 < depth {
        var tjSuffix := tj.Crop(1);
        DiscardOldCanCropIncrement(tjSuffix, depth-1, newBdy);
      } 
    }
  }

  lemma CropAndDiscardCommutes(tj: TruncatedJournal, depth: nat, newBdy: LSN) 
    requires tj.Decodable()
    requires tj.CanCrop(depth) 
    requires tj.Crop(depth).CanDiscardTo(newBdy)
    ensures tj.CanDiscardTo(newBdy)
    ensures tj.Crop(depth).CanDiscardTo(newBdy)
    ensures tj.DiscardOld(newBdy).Decodable() 
    ensures tj.DiscardOld(newBdy).CanCrop(depth)
    ensures tj.Crop(depth).DiscardOld(newBdy) == tj.DiscardOld(newBdy).Crop(depth)
    decreases depth
  {
    CropDecreasesSeqEnd(tj, depth); // to get tj.CanDiscardTo(newBdy) from tj.Crop(depth).CanDiscardTo(newBdy)
    TjDiscardOldCommutes(tj, newBdy);  // to get CanDiscardTo(newBdy)
    TjDiscardOldCommutes(tj.Crop(depth), newBdy);  // to get CanDiscardTo(newBdy)
    if 0 < depth {
      var tjNext := TruncatedJournal(tj.diskView.entries[tj.freshestRec.value].CroppedPrior(tj.diskView.boundaryLSN), tj.diskView);
      CropAndDiscardCommutes(tjNext, depth-1, newBdy); 
      DiscardOldCanCropIncrement(tj, depth, newBdy);
    }
  }
  
  
  lemma InFlightSubDiskCreated(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires lbl.FreezeForCommitLabel?
    requires NextStep(v, v', lbl, step)
    ensures InFlightSubDiskProperty(v', lbl.frozenJournal)
  {
    CropDecreasesSeqEnd(v.truncatedJournal, step.depth);
    var ephemeral := v.truncatedJournal;
    var croppedPtr := ephemeral.diskView.PointerAfterCrop(ephemeral.freshestRec, step.depth);
    var croppedTj := TruncatedJournal(croppedPtr, ephemeral.diskView);
    var newBdy := lbl.frozenJournal.SeqStart();
    var discardedTj := croppedTj.DiscardOld(newBdy);
    var tightTj := discardedTj.BuildTight();
    assert tightTj.diskView == BuildTightAwesome(discardedTj.diskView, discardedTj.freshestRec);  // invoke awesomeness
    CropAndDiscardCommutes(v.truncatedJournal, step.depth, newBdy);
    LemmaBuildTightPreservesSubDisk(discardedTj, v.truncatedJournal.DiscardOld(newBdy), step.depth);
  }

  lemma BuildTightPreservesSubDiskUnderInternalMarshall(
      small: DiskView, smallroot: Pointer, smallRanking: GenericDisk.Ranking,
      big: DiskView, bigroot: Pointer, bigRanking: GenericDisk.Ranking)
    requires small.Decodable(smallroot)
    requires small.PointersRespectRank(smallRanking)
    requires big.Decodable(bigroot)
    requires big.PointersRespectRank(bigRanking)
    requires small.IsSubDisk(big)
    requires big.boundaryLSN == small.boundaryLSN
    requires bigroot.Some?
    requires big.entries[bigroot.value].CroppedPrior(big.boundaryLSN) == smallroot
    ensures small.BuildTight(smallroot).IsSubDisk(big.BuildTight(bigroot))
    decreases if bigroot.Some? then bigRanking[bigroot.value] else -1 // I can't believe this works, Rustan!
  {
    if smallroot.Some? {
      BuildTightBuildsSubDisks(small, smallroot);
      BuildTightBuildsSubDisks(big, bigroot);
      var next := small.entries[smallroot.value].CroppedPrior(small.boundaryLSN);
      BuildTightPreservesSubDiskUnderInternalMarshall(
        small, next, smallRanking, big, smallroot, bigRanking);
    }
  }

  lemma InFlightSubDiskPreserved(v: Variables, v': Variables, inFlight: TruncatedJournal, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    requires lbl.InternalJournalMarshalLabel?
    requires InFlightSubDiskProperty(v, inFlight)
    ensures InFlightSubDiskProperty(v', inFlight)
  {
    var step: Step :| NextStep(v, v', lbl, step);
    
    var vj := v.truncatedJournal;
    var dj := vj.DiscardOld(inFlight.SeqStart());
    var v'j := v'.truncatedJournal;
    var d'j := v'j.DiscardOld(inFlight.SeqStart());
    InvNext(v, v', lbl);
    assert d'j.diskView.PointersRespectRank(v'j.diskView.TheRanking());  // witness to d'j.Acyclic

    BuildTightPreservesSubDiskUnderInternalMarshall(
      dj.diskView, dj.freshestRec, dj.diskView.TheRanking(),
      d'j.diskView, d'j.freshestRec, d'j.diskView.TheRanking());
  }
  
  //////////////////////////////////////////////////////////////////////////////
}
