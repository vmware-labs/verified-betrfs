// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LikesAU.i.dfy"
include "Compactor.i.dfy"
include "../Betree/LikesBetree.i.dfy"
include "../Betree/AllocationBranchRefinement.i.dfy"

module AllocationBetreeMod
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
  import CompactorMod
  import opened AllocationBranchMod

  import M = Mathematics
  import G = GenericDisk
  import BB = BranchedBetreeMod
  import LB = LikesBetreeMod
  import ABR = AllocationBranchRefinement

  type Address = GenericDisk.Address
  type AU = GenericDisk.AU
  type Compactor = CompactorMod.Variables
  type BranchDiskView = AllocationBranchMod.DiskView

  datatype BetreeImage = BetreeImage(
    branched: BB.BranchedBetree,
    dv: BranchDiskView
  )

  type StampedBetree = Stamped<BetreeImage>

  function EmptyBetreeImage() : (out: BetreeImage)
  {
    BetreeImage(BB.EmptyBranchedBetree(), EmptyDisk())
  }

  function EmptyImage() : StampedBetree
  {
    Stamped(EmptyBetreeImage(), 0)
  }

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(stamped: StampedBetree, unobserved: set<AU>)
    | InternalAllocationsLabel(allocs: set<AU>, deallocs: set<AU>)
  {
    function I() : LB.TransitionLabel
    {
      match this {
        case QueryLabel(endLsn, key, value) => LB.QueryLabel(endLsn, key, value)
        case PutLabel(puts) => LB.PutLabel(puts)
        case QueryEndLsnLabel(endLsn) => LB.QueryEndLsnLabel(endLsn)
        case FreezeAsLabel(stamped, _) => LB.FreezeAsLabel(Stamped(stamped.value.branched, stamped.seqEnd))
        case InternalAllocationsLabel(_, _) => LB.InternalLabel
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

    // gather allocated but unobserved AUs here to return back
    function UnobservedAUs() : set<AU>
    {
      compactor.AUs() // TODO: add memtable too
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
    && (lbl.QueryLabel? || lbl.PutLabel? || lbl.QueryEndLsnLabel?)
    && LB.NextStep(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && v' == v.(
      likesVars := v'.likesVars // admit relational update above
    )
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.FreezeAsLabel?
    && LB.Next(v.likesVars, v'.likesVars, lbl.I())
    && lbl.stamped.value == BetreeImage(v.likesVars.branchedVars.branched, v.allocBranchDiskView)
    && lbl.unobserved == v.UnobservedAUs()

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

  predicate AddrsWithDisjointAUs(addrs: set<Address>) 
  {
    forall addr1, addr2 | addr1 in addrs && addr2 in addrs && addr1 != addr2 :: addr1.au != addr2.au
  }

  // data structure for tracking betree allocation status
  datatype BetreeInfo = BetreeInfo(newAddrs: set<Address>, derefAddrs: set<Address>) 
  {
    predicate WF() {
      AddrsWithDisjointAUs(newAddrs)
    }

    function NewLikes() : (out: LikesAU)
    {
      multiset(AllocAUs())
    }

    function DerefLikes(): LikesAU
    {
      multiset(G.ToAUs(derefAddrs))
    }

    function AllocAUs() : set<AU>
    {
      G.ToAUs(newAddrs)
    }

    function DeallocAUs(likes: LikesAU) : set<AU>
    {
      var pre := M.Set(likes);
      var post := M.Set(likes - DerefLikes());
      pre - post
    }

    function UpdateLikes(likes: LikesAU) : LikesAU
    {
      likes - DerefLikes() + NewLikes()
    }
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

  // data structure for tracking branch/b+tree allocation status
  datatype BranchInfo = BranchInfo(newRoots: set<Address>, derefRoots: set<Address>)
  {
    function NewLikes() : LikesAU
    {
      multiset(G.ToAUs(newRoots))
    }

    function DerefLikes() : LikesAU
    {
      multiset(G.ToAUs(derefRoots))
    }

    // NOTE(Jialin): this is not needed bc we incrementally build each branch via mini allocator
    // so allocation for the branch is already captured by the mini allocator
    // the newRoots are new references to the branches from the betree node
    // function AllocAUs(dv: BranchDiskView) : set<AU>
    // {
    //   UnionSetOfSets(set root | root in newRoots :: SummaryFromBranchRoot(root, dv))
    // }

    // root AUs no longer reachable from betree nodes
    function DeallocRootAUs(likes: LikesAU) : set<AU>
    {
      var pre := M.Set(likes);
      var post := M.Set(likes - DerefLikes());
      pre - post
    }

    function DeallocRootAddrs(likes: LikesAU, readRefs: LikesAU, readRefs': LikesAU) : set<Address>
    {
      var discardAUs := DeallocRootAUs(likes);
      var discardReadRefs := M.Set(readRefs - readRefs');
      var discardAddrs := set addr | 
        && addr in derefRoots 
        && addr.au in discardAUs
        && (addr.au in discardReadRefs || addr.au !in readRefs);

      discardAddrs
    }

    function DeallocAUs(rootAddrs: set<Address>, dv: BranchDiskView) : set<AU>
    {
      UnionSetOfSets(set root | root in rootAddrs :: SummaryFromBranchRoot(root, dv))
    }

    function UpdateLikes(likes: LikesAU) : LikesAU
    {
      likes - DerefLikes() + NewLikes()
    }
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

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && LB.InternalSplitTree(v.likesVars, v'.likesVars, lbl.I(), step.I())

    // set up betree info
    && var betreeNewAddrs := Set(step.pathAddrs) + step.newAddrs.Repr();
    && var betreeDerefAddrs := Set(step.path.AddrsOnPath()) + {step.path.Target().ChildAtIdx(step.request.childIdx).root.value};
    && var betreeInfo := BetreeInfo(betreeNewAddrs, betreeDerefAddrs);
    && betreeInfo.WF()

    && lbl.allocs == betreeInfo.AllocAUs()
    && lbl.deallocs == betreeInfo.DeallocAUs(v.betreeAULikes)

    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      betreeAULikes := betreeInfo.UpdateLikes(v.betreeAULikes)
    )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && LB.InternalFlushTree(v.likesVars, v'.likesVars, lbl.I(), step.I())

    // set up betree info
    && var betreeNewAddrs := {step.targetAddr} + {step.targetChildAddr} + Set(step.pathAddrs);
    && var betreeDerefAddrs := Set(step.path.AddrsOnPath()) + {step.path.Target().ChildAtIdx(step.childIdx).root.value};
    && var betreeInfo := BetreeInfo(betreeNewAddrs, betreeDerefAddrs);
    && betreeInfo.WF()

    // show precondition for branchDerefAddrs
    && var root := step.path.Target().Root();
    && var activeOffset := root.flushedOffsets.Get(step.childIdx);
    && assert step.branchGCCount <= root.branches.Length() by {
      var newflushedOffsets := root.flushedOffsets.AdvanceIndex(step.childIdx, root.branches.Length());
      var i:nat :| i < newflushedOffsets.Size();
      assert newflushedOffsets.Get(i) <= root.branches.Length();
    }

    // set up branch info
    && var branchNewAddrs := root.branches.Slice(activeOffset, root.branches.Length()).Representation(); // branches flushed to child
    && var branchDerefAddrs := root.branches.Slice(0, step.branchGCCount).Representation();  // result of GC
    && var branchInfo := BranchInfo(branchNewAddrs, branchDerefAddrs);
    && var discardRoots := branchInfo.DeallocRootAddrs(v.branchAULikes, v.branchReadRefs, v'.branchReadRefs);

    && lbl.allocs == betreeInfo.AllocAUs()
    && lbl.deallocs == betreeInfo.DeallocAUs(v.betreeAULikes) + branchInfo.DeallocAUs(discardRoots, v.allocBranchDiskView)

    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      betreeAULikes := betreeInfo.UpdateLikes(v.betreeAULikes),
      branchAULikes := branchInfo.UpdateLikes(v.branchAULikes),
      allocBranchDiskView := v.allocBranchDiskView.RemoveAddrs(discardRoots)
    )
  }

  function GetCompactInput(path: BB.Path, start: nat, end: nat, dv: BranchDiskView) : CompactorMod.CompactInput
    requires path.Valid()
    requires start < end <= path.Target().Root().branches.Length()
  {
    var node := path.Target().Root(); 
    var offsetMap := node.MakeOffsetMap().Decrement(start);
    var branchSeq := node.branches.Slice(start, end); // branches to be compacted
    var subdisk := SubdiskForBranches(branchSeq.Representation(), dv);

    CompactorMod.CompactInput(branchSeq, offsetMap, subdisk)
  }

  predicate InternalCompactBegin(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalCompactBeginStep?
    && step.path.Valid()
    && step.start < step.end <= step.path.Target().Root().branches.Length()

    && var compactInput := GetCompactInput(step.path, step.start, step.end, v.allocBranchDiskView);
    && var inputReadRefs := multiset(G.ToAUs(compactInput.branchSeq.Representation()));
    && CompactorMod.Next(v.compactor, v'.compactor, CompactorMod.BeginLabel(compactInput, lbl.allocs)) 
    && lbl.deallocs == {}  // lbl.allocs specified by compactor transitions

    && v' == v.(
      compactor := v'.compactor, // admit relational update above
      branchReadRefs := v.branchReadRefs + inputReadRefs // track ongoing compact inputs so we don't dealloc them during compaction
    )
  }

  predicate InternalCompactBuild(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?  
    && CompactorMod.Next(v.compactor, v'.compactor, CompactorMod.InternalLabel(lbl.allocs))
    && lbl.deallocs == {} // lbl.allocs specified by compactor transitions

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
    && var compactInput := GetCompactInput(step.path, step.start, step.end, v.allocBranchDiskView);
    && var output := AllocationBranchMod.Variables(step.newBranch);
    && CompactorMod.Next(v.compactor, v'.compactor, CompactorMod.CommitLabel(compactInput, output))

    // set up betree info
    && var betreeNewAddrs := Set(step.pathAddrs) + {step.targetAddr};
    && var betreeDerefAddrs := Set(step.path.AddrsOnPath());
    && var betreeInfo := BetreeInfo(betreeNewAddrs, betreeDerefAddrs);
    && betreeInfo.WF()

    // set up branch info
    && var branchNewAddrs := {step.newBranch.root}; // new compacted branch
    && var branchDerefAddrs := compactInput.branchSeq.Representation();
    && var branchInfo := BranchInfo(branchNewAddrs, branchDerefAddrs);
    && var discardRoots := branchInfo.DeallocRootAddrs(v.branchAULikes, v.branchReadRefs, v'.branchReadRefs);
    && var newAllocBranchDiskView := v.allocBranchDiskView.RemoveAddrs(discardRoots).MergeDisk(step.newBranch.diskView);

    && lbl.allocs == betreeInfo.AllocAUs()
    && lbl.deallocs == betreeInfo.DeallocAUs(v.betreeAULikes) + branchInfo.DeallocAUs(discardRoots, v.allocBranchDiskView)

    && v' == v.(
      likesVars := v'.likesVars, // admit relational update above
      compactor := v'.compactor,  // admit relational update above
      allocBranchDiskView := newAllocBranchDiskView,
      branchReadRefs := v.branchReadRefs - branchInfo.DerefLikes(),
      betreeAULikes := betreeInfo.UpdateLikes(v.betreeAULikes),
      branchAULikes := branchInfo.UpdateLikes(v.branchAULikes)
    )
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl == InternalAllocationsLabel({}, {})
    && LB.InternalNoOp(v.likesVars, v'.likesVars, lbl.I())
    && v' == v
  }

  predicate Init(v: Variables, stamped: StampedBetree)
  {
    && LB.Init(v.likesVars, Stamped(stamped.value.branched, stamped.seqEnd))
    // v.betreeAULikes == v.likesVars.betreeLikes.ToAUs()
    // v.branchAULikes == v.likesVars.branchLikes.ToAUs() 
    && v.branchReadRefs == multiset{}
    && stamped.value.branched.branchDiskView == ABR.IDiskView(stamped.value.dv)
    && CompactorMod.Init(v.compactor)
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
      case InternalNoOpStep() => InternalNoOp(v, v', lbl)
      case _ => InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }  

} // end AllocationBetreeMod