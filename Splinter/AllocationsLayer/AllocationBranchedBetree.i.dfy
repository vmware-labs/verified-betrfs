// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LikesAU.i.dfy"
include "Compactor.i.dfy"
include "../Betree/LikesBranchedBetree.i.dfy"
include "../Betree/AllocationBranchRefinement.i.dfy"

module AllocationBranchedBetreeMod
{
  import opened Sets
  import opened Maps
  import opened Sequences
  import opened LSNMod
  import opened MsgHistoryMod
  import opened StampedMod
  import opened KeyType
  import opened ValueMessage
  import opened SplitRequestMod
  import opened LikesAUMod
  import opened MiniAllocatorMod
  import opened CompactorMod
  import opened AllocationBranchMod

  import M = Mathematics
  import G = GenericDisk
  import BB = BranchedBetreeMod
  import LB = LikesBranchedBetreeMod
  import ABR = AllocationBranchRefinement

  type Address = GenericDisk.Address
  type AU = GenericDisk.AU
  type Compactor = CompactorMod.Variables
  type BranchDiskView = AllocationBranchMod.DiskView
  type StampedBetree = Stamped<BB.BranchedBetree>

  function FirstPage(au: AU) : Address
  {
    G.Address(au, 0)
  }

  // function PathAddrsToPathAUs(addrs: BB.PathAddrs) : PathAUs
  // {
  //   Apply((x: Address) => x.au, addrs)
  // }

  // TODO: miniallocator labels for compactor steps
  // growing should just be AU
  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(branched: StampedBetree)
    | InternalAllocationsLabel(allocs: set<AU>, deallocs: set<AU>)
    | InternalLabel()   // Local No-op label
  {
    function I() : LB.TransitionLabel
    {
      match this {
        case QueryLabel(endLsn, key, value) => LB.QueryLabel(endLsn, key, value)
        case PutLabel(puts) => LB.PutLabel(puts)
        case QueryEndLsnLabel(endLsn) => LB.QueryEndLsnLabel(endLsn)
        case FreezeAsLabel(branched) => LB.FreezeAsLabel(branched)
        case _ => LB.InternalLabel
      }
    }
  }

  datatype Variables = Variables(
    likesVars: LB.Variables,
    // memtable: AllocationMemtable, // TODO: a mini alloocator & allocation branch
    // imperative states maintained to compute which AUs may be freed in a step
    betreeAULikes: LikesAU, // references of betreee node
    branchAULikes: LikesAU, // root au of each branch
    branchReadRefs: LikesAU, // updated when compact starts and ends
    // ghosty
    allocBranchDiskView: BranchDiskView, // diskview containing allocation branches
    // part ghosty (DiskView) & part imperative
    compactor: Compactor
    // Need to union the buildTight disk and all the threadseq disk.
    // sequence of "thread" information for compacting branches, each with its own mini-allocator, and its own read-refs(?)
  )
  {
    predicate WF() {
      && likesVars.WF()
      && allocBranchDiskView.WF()
    }
  
    // Maintained via Inv (all ghosty?)
    // move to proof land, condition for refinement
    // predicate IsFresh(aus: set<AU>) {
    //   && M.Set(betreeAULikes) !! aus
    //   // && M.Set(branchAULikes) !! aus
    //   && UnionSetOfSets(branchToSummary.Values) !! aus
    //   && M.Set(compactor.Likes()) !! aus
    //   // && G.ToAUs(allocBranchDiskView.Representation()) !! aus 
    //    && aus !! memtable.Likes()
    // }
    
    // one layer: lbl would inherit allocation and free arguments
    // conditional refinement lemma
    // AU == lbl.allocated things 
    // freeset from cooirdination system implies this
  }

  // group a couple definitions together
  predicate OnlyAdvanceLikesVars(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && LB.NextStep(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && v' == v.(
      likesVars := v'.likesVars // admit relational update above
    )
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && LB.InternalGrowTree(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      betreeAULikes := v.betreeAULikes + multiset({step.newRootAddr.au})
    )
  }

  // TODO: blocked on integrating linkedbranch for memtable 
  // Any b+tree that is "observed" is not in the mini-allocator
  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && LB.InternalFlushMemtableTree(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && var oldRootAU := if v.likesVars.branchedVars.branched.HasRoot() 
      then multiset{v.likesVars.branchedVars.branched.root.value.au} else multiset{};
    // TODO: change memtable steps

    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      // memtableVars := v'.memtableVars, 
      // allocBranchDiskView: BranchDiskView, // diskview containing allocation branches
      betreeAULikes := v.betreeAULikes - oldRootAU + multiset{step.newRootAddr.au},
      branchAULikes := v.branchAULikes + multiset{step.branch.root.au}
    )
  }

  predicate AddrsWithDisjointAUs(addrs: set<Address>) 
  {
    forall addr1, addr2 | addr1 in addrs && addr2 in addrs && addr1 != addr2 :: addr1.au != addr2.au
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && LB.InternalSplitTree(v.likesVars, v'.likesVars, lbl.I(), step.I())

    && var newBetreeAddrs := Set(step.pathAddrs) + step.newAddrs.Repr();
    && AddrsWithDisjointAUs(newBetreeAddrs) // maintain as an invariant for all nodes of the tree
    && var newBetreeAULikes := multiset(G.ToAUs(newBetreeAddrs));
    && var derefBetreeAULikes := multiset(G.ToAUs(Set(step.path.AddrsOnPath())) 
      + {step.path.Target().ChildAtIdx(step.request.childIdx).root.value.au});

    && lbl.allocs == G.ToAUs(newBetreeAddrs)
    && lbl.deallocs == M.Set(v.betreeAULikes) - M.Set(v'.betreeAULikes)
    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      betreeAULikes := v.betreeAULikes - derefBetreeAULikes + newBetreeAULikes
      // no change to the branchAULikes bc the newly splitted nodes will split the replaced node's branchseq
    )
  }

  function SummaryFromBranchRoot(root: Address, dv: BranchDiskView) : set<AU>
  {
    var branch := AllocationBranch(root, dv);
    if branch.WF() // true by Inv
    then branch.GetSummary()
    else {}
  }

  function FullAddrsFromBranchRoot(root: Address, dv: BranchDiskView) : set<Address>
  {
    var branch := AllocationBranch(root, dv);
    if branch.Acyclic() // true by Inv
    then branch.Representation()
    else {}
  }

  function SubdiskForBranches(roots: set<Address>, dv: BranchDiskView) : BranchDiskView
  {
    var fullAddrs := UnionSetOfSets(set addr | addr in roots :: FullAddrsFromBranchRoot(addr, dv));
    var subdisk := DiskView(MapRestrict(dv.entries, fullAddrs));
    subdisk
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && LB.InternalFlushTree(v.likesVars, v'.likesVars, lbl.I(), step.I())

    && var newBetreeAddrs := {step.targetAddr} + {step.targetChildAddr} + Set(step.pathAddrs);
    && AddrsWithDisjointAUs(newBetreeAddrs)
    && var root := step.path.Target().Root();
    && var newflushedOffsets := root.flushedOffsets.AdvanceIndex(step.childIdx, root.branches.Length());
    && assert step.branchGCCount <= root.branches.Length() by {
      var i:nat :| i < newflushedOffsets.Size();
      assert newflushedOffsets.Get(i) <= root.branches.Length();
    }

    && var newBetreeAULikes := multiset(G.ToAUs(newBetreeAddrs));
    && var derefBetreeAULikes := multiset(G.ToAUs(Set(step.path.AddrsOnPath())) 
      + {step.path.Target().ChildAtIdx(step.childIdx).root.value.au});

    && var newBranchAULikes := multiset(G.ToAUs(root.branches.Slice(root.flushedOffsets.Get(step.childIdx), 
      root.branches.Length()).Representation())); // account for added branch root references as a result of flush
    && var derefBranchRootAddrs := root.branches.Slice(0, step.branchGCCount).Representation(); // deref roots from parent as a result of GC
    && var derefBranchAULikes := multiset(G.ToAUs(derefBranchRootAddrs)); // just the root AUs

    && var discardBranchAULikes := M.Set(v.branchAULikes) - M.Set(v'.branchAULikes);
    && var discardBranchRootAddrs := set addr | addr in derefBranchRootAddrs && addr.au in discardBranchAULikes && addr.au !in v.branchReadRefs; // branch that are actually discarded as a result of deref (GC)
    && var discardBranchAUSummary := UnionSetOfSets(set addr | addr in discardBranchRootAddrs :: SummaryFromBranchRoot(addr, v.allocBranchDiskView)); // computed
    && var newAllocBranchDiskView := v.allocBranchDiskView.RemoveDisk(SubdiskForBranches(discardBranchRootAddrs, v.allocBranchDiskView));

    // what can be discarded, things that are in 
    // nodes that temporarily exist, we don't need their full node, so their nodes are reclaimable, we just want their branches

    && lbl.allocs == G.ToAUs(newBetreeAddrs)
    && lbl.deallocs == M.Set(v.betreeAULikes) - M.Set(v'.betreeAULikes) + discardBranchAUSummary

    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      betreeAULikes := v.betreeAULikes - derefBetreeAULikes + newBetreeAULikes,
      branchAULikes := v.branchAULikes - derefBranchAULikes + newBranchAULikes,
      allocBranchDiskView := newAllocBranchDiskView
    )
  }

  function GetCompactInput(path: BB.Path, start: nat, end: nat, dv: BranchDiskView) : CompactInput
    requires path.Valid()
    requires start < end <= path.Target().Root().branches.Length()
  {
    var node := path.Target().Root(); 
    var offsetMap := node.MakeOffsetMap().Decrement(start);
    var branchSeq := node.branches.Slice(start, end); // branches to be compacted
    var subdisk := SubdiskForBranches(branchSeq.Representation(), dv);

    CompactInput(branchSeq, offsetMap, subdisk)
  }

  predicate InternalCompactBegin(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalCompactBeginStep?
    && step.path.Valid()
    && step.start < step.end <= step.path.Target().Root().branches.Length()

    && var compactInput := GetCompactInput(step.path, step.start, step.end, v.allocBranchDiskView);
    && CompactorMod.Next(v.compactor, v'.compactor, Begin(compactInput, lbl.allocs))
    && lbl.deallocs == {}

    && v' == v.(
      compactor := v'.compactor, // admit relational update above
      branchReadRefs := v.branchReadRefs + multiset(G.ToAUs(compactInput.branchSeq.Representation()))
    )
  }

  predicate InternalCompactBuild(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?  
    && CompactorMod.Next(v.compactor, v'.compactor, Internal(lbl.allocs))
    && lbl.deallocs == {}

    && v' == v.(
      compactor := v'.compactor // admit relational update above
    )
  }

  // This corresponds to Compactor commit
  predicate InternalCompactCommit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && LB.InternalCompactTree(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && step.path.Valid()
    && step.start < step.end <= step.path.Target().Root().branches.Length()
    && !step.newBranch.NotSealed() // new branch must be sealed

    && var compactInput := GetCompactInput(step.path, step.start, step.end, v.allocBranchDiskView);
    && CompactorMod.Next(v.compactor, v'.compactor, Commit(compactInput, AllocBranch.Variables(step.newBranch)))

    && var newBetreeAddrs := Set(step.pathAddrs) + {step.targetAddr};
    && AddrsWithDisjointAUs(newBetreeAddrs)
    && var newBetreeAULikes := multiset(G.ToAUs(newBetreeAddrs));
    && var derefBetreeAULikes := multiset(G.ToAUs(Set(step.path.AddrsOnPath())));

    && var newBranchAULikes := multiset{step.newBranch.root.au};
    && var derefBranchRootAddrs := compactInput.branchSeq.Representation();
    && var derefBranchAULikes := multiset(G.ToAUs(derefBranchRootAddrs));
    && var discardBranchAULikes := M.Set(v.branchAULikes) - M.Set(v'.branchAULikes);
    && var discardBranchRootAddrs := set addr | addr in derefBranchRootAddrs && addr.au in discardBranchAULikes && addr.au !in v.branchReadRefs; // branch that are actually discarded as a result of deref (GC)
    && var discardBranchAUSummary := UnionSetOfSets(set addr | addr in discardBranchRootAddrs :: SummaryFromBranchRoot(addr, v.allocBranchDiskView)); // computed
    && var newAllocBranchDiskView := v.allocBranchDiskView.RemoveDisk(SubdiskForBranches(discardBranchRootAddrs, v.allocBranchDiskView)).MergeDisk(step.newBranch.diskView);

    && lbl.allocs == G.ToAUs(newBetreeAddrs)
    && lbl.deallocs == M.Set(v.betreeAULikes) - M.Set(v'.betreeAULikes) + discardBranchAUSummary

    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      compactor := v'.compactor,  // admit relational update above
      allocBranchDiskView := newAllocBranchDiskView,
      branchReadRefs := v.branchReadRefs - multiset(G.ToAUs(derefBranchRootAddrs)),
      betreeAULikes := v.betreeAULikes - derefBetreeAULikes + newBetreeAULikes,
      branchAULikes := v.branchAULikes - derefBranchAULikes + newBranchAULikes
    )
  }

  predicate NoOp(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && LB.NextStep(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && v' == v
  }

  predicate Init(v: Variables)
  {
    && true
  }

  datatype Step =
      QueryStep(receipt: BB.QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep(newRootAddr: Address) // this could potentially be the AU and we make sure that it's written to the first AU?
    | InternalSplitStep(path: BB.Path, request: SplitRequest, newAddrs: BB.L.SplitAddrs, pathAddrs: BB.PathAddrs)
    | InternalFlushMemtableStep(newRootAddr: Address, branch: AllocationBranch)
    | InternalFlushStep(path: BB.Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: BB.PathAddrs, branchGCCount: nat)
    | InternalCompactBeginStep(path: BB.Path, start: nat, end: nat)
    | InternalCompactBuildStep()
    | InternalCompactCommitStep(path: BB.Path, start: nat, end: nat, newBranch: AllocationBranch, targetAddr: Address, pathAddrs: BB.PathAddrs)
    | InternalNoOpStep()   // Local No-op label
  {
    function I() : LB.Step
    {
      match this {
        case QueryStep(receipt) => LB.QueryStep(receipt)
        case PutStep() => LB.PutStep()
        case QueryEndLsnStep() => LB.QueryEndLsnStep
        case FreezeAsStep() => LB.FreezeAsStep()
        case InternalGrowStep(newRootAddr) => LB.InternalGrowStep(newRootAddr)
        case InternalSplitStep(path, request, newAddrs, pathAddrs)
          => LB.InternalSplitStep(path, request, newAddrs, pathAddrs)
        case InternalFlushMemtableStep(newRootAddr, branch) => LB.InternalFlushMemtableStep(newRootAddr, ABR.I(branch))
        case InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount) 
          => LB.InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount)
        case InternalCompactCommitStep(path, start, end, newBranch, targetAddr, pathAddrs) 
          => LB.InternalCompactStep(path, start, end, ABR.I(newBranch), targetAddr, pathAddrs) 
        case InternalCompactBeginStep(_, _, _) => LB.InternalNoOpStep
        case InternalCompactBuildStep() => LB.InternalNoOpStep
        case InternalNoOpStep() => LB.InternalNoOpStep
      }
    }
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep(_) => OnlyAdvanceLikesVars(v, v', lbl, step)
      // case PutStep() => OnlyAdvanceLikesVars(v, v', lbl, step) // put inserts into the memtable and effect state
      case QueryEndLsnStep() => OnlyAdvanceLikesVars(v, v', lbl, step)
      case FreezeAsStep() => OnlyAdvanceLikesVars(v, v', lbl, step)
      case InternalGrowStep(_) => InternalGrow(v, v', lbl, step)
      case InternalSplitStep(_, _, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushMemtableStep(_,_) => InternalFlushMemtable(v, v', lbl, step)
      case InternalFlushStep(_, _, _, _, _, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactBeginStep(_, _, _) => InternalCompactBegin(v, v', lbl, step)
      case InternalCompactBuildStep() => InternalCompactBuild(v, v', lbl)
      case InternalCompactCommitStep(_, _, _, _, _, _) => InternalCompactCommit(v, v', lbl, step)
      case InternalNoOpStep() => NoOp(v, v', lbl, step)
      case _ => NoOp(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }  

} // end AllocationBranchedBetreeMod