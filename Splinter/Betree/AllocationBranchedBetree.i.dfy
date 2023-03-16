// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../LikesAU.i.dfy"
include "../Journal/MiniAllocator.i.dfy"   // tony: borrowing from Journal for now
include "LikesBranchedBetree.i.dfy"

module AllocationBranchedBetreeMod
{
  import GenericDisk
  import opened Sequences
  import opened LSNMod
  import opened MsgHistoryMod
  import opened StampedMod
  import opened KeyType
  import opened ValueMessage
  import opened SplitRequestMod
  import opened LikesAUMod
  import opened MiniAllocatorMod
  import LikesBranchedBetreeMod

  import M = Mathematics
  import BB = BranchedBetreeMod
  import LkB = LinkedBranchMod 
  import LB = LikesBranchedBetreeMod

//   type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type AU = GenericDisk.AU

  type PathAUs = seq<AU>

//   type Ranking = GenericDisk.Ranking
  type StampedBetree = Stamped<BB.BranchedBetree>
//   type BranchDiskView = LB.DiskView

  function FirstPage(au: AU) : Address
  {
    GenericDisk.Address(au, 0)
  }

  // function FirstPageOfPathAUs(aus: PathAUs) : seq<Address>
  // {
  //   Apply(FirstPage, aus)
  // }

  function PathAddrsToPathAUs(addrs: BB.PathAddrs) : PathAUs
  {
    Apply((x: Address) => x.au, addrs)
  }

  // TODO: Forest should be a state machine at this layer 

  datatype Variables = Variables(
    likesVars: LB.Variables,
    betreeAULikes: LikesAU, 
    branchAULikes: LikesAU,
    branchMiniAllocator: MiniAllocator  // this is not involved in trunk stuff
  )
  {
    predicate WF() {
      && likesVars.WF()
    }

    predicate IsFresh(aus: set<AU>) {
      && betreeAULikes !! multiset(aus)
      && branchAULikes !! multiset(aus)
      //TODO: This is not sufficient, since branchAULikes only contain b+tree root. Need
      // to get the branch summary
    }
  }

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(branched: StampedBetree)
    | InternalAllocationsLabel(addrs: set<Address>)
    | InternalLabel()   // Local No-op label
  {
    function I() : LB.TransitionLabel
    {
      match this {
        case QueryLabel(endLsn, key, value) => LB.QueryLabel(endLsn, key, value)
        case PutLabel(puts) => LB.PutLabel(puts)
        case QueryEndLsnLabel(endLsn) => LB.QueryEndLsnLabel(endLsn)
        case FreezeAsLabel(branched) => LB.FreezeAsLabel(branched)
        case InternalAllocationsLabel(addrs) => LB.InternalAllocationsLabel(addrs)
        case _ => LB.InternalLabel
      }
    }
  }

  // group a couple definitions together
  predicate OnlyAdvanceBranchedVars(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && LB.NextStep(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && v' == v.(
      likesVars := v'.likesVars // admit relational update above
    )
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && LB.InternalGrowTree(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && v.IsFresh({step.newRootAddr.au})
    && v' == v.(
      betreeAULikes := v.betreeAULikes + multiset({step.newRootAddr.au})
    )
  }

  // Any b+tree that is "observed" is not in the mini-allocator

  // TODO
  // predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  // {
  //   && LB.InternalFlushMemtableTree(v.likesVars, v'.likesVars, lbl.I(), step.I())
  //   && var oldRootAU := if v.likesVars.branchedVars.branched.HasRoot() then multiset{v.branchedVars.branched.root.value.au} else multiset{};
  //   && v' == v.(
  //     likesVars := v'.likesVars, // admit relational update above

  //     // TODO: mini allocator needs to be updated here. Can forget linked pages.
  //     betreeAULikes := v.betreeLikes - oldRootAU + multiset{step.newRootAU},
  //     branchAULikes := v.branchLikes + multiset{step.branch.root}
  //   )
  // }

//   predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//   && lbl.InternalAllocationsLabel?
//   && step.InternalSplitStep?
//   && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
//   && var newBetreeLikes := multiset(Set(step.pathAddrs) + step.newAddrs.Repr());
//   && var discardBetreeLikes := 
//     multiset(step.path.AddrsOnPath() + {step.path.Target().ChildAtIdx(step.request.childIdx).root.value});
//   && v' == v.(
//     branchedVars := v'.branchedVars, // admit relational update above
//     betreeLikes := v.betreeLikes - discardBetreeLikes + newBetreeLikes
//     // branchLikes do not change
//   )
//   }

//   predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//   && lbl.InternalAllocationsLabel?
//   && step.InternalFlushStep?
//   && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
//   && var target := step.path.Target();
//   && var root := target.Root();
//   && var newflushedOffsets := root.flushedOffsets.AdvanceIndex(step.childIdx, root.branches.Length());
//   && assert step.branchGCCount <= root.branches.Length() by {
//     var i:nat :| i < newflushedOffsets.Size();
//     assert newflushedOffsets.Get(i) <= root.branches.Length();
//   }
//   && var newBetreeLikes := multiset(Set(step.pathAddrs) + {step.targetAddr, step.targetChildAddr});
//   && var discardBetreeLikes := multiset(step.path.AddrsOnPath() + {target.ChildAtIdx(step.childIdx).root.value});
//   && var newBranchLikes := root.branches.Slice(root.flushedOffsets.Get(step.childIdx), root.branches.Length()).ToMultiset();
//   && var discardBranchLikes := root.branches.Slice(0, step.branchGCCount).ToMultiset();
//   && v' == v.(
//     branchedVars := v'.branchedVars, // admit relational update above
//     betreeLikes := v.betreeLikes - discardBetreeLikes + newBetreeLikes,
//     branchLikes := v.branchLikes - discardBranchLikes + newBranchLikes
//   )
//   }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && LB.InternalCompactTree(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && var newBetreeAULikes := multiset(Set(PathAddrsToPathAUs(step.pathAddrs)) + {step.targetAddr.au});
    && var discardBetreeLikes := multiset(PathAddrsToPathAUs(step.path.AddrsOnPath()));
    && var newBranchLikes := multiset{step.newBranch.root.au};
    && var discardBranchLikes := multiset(Set(PathAddrsToPathAUs(step.path.Target().Root().branches.Slice(step.start, step.end).roots)));
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      branchMiniAllocator := 
      // Func: Take a set of page addrs, remove them from reserved of respective Page Allocators,
      // add them to observed of respective Page Allocators. 
      /*
        1. Remove new builded branch tree:
          1a. drop the stack ref to its root
          1b. return the root addr
          1c. un-reserve the set of addrs in its repr from the miniallocater
          1d. learn that root.i() has the value we need
          1e. return set of addrs in the repr
        2. Insert the newly-built branch into the BranchedBetree
          2a. add the set of addrs in its repr as *observed* in the miniallocator
          2b. record a reference to the root page from the betree's branchseq
      */ 
      betreeLikes := v.betreeLikes - discardBetreeLikes + newBetreeLikes,
      branchLikes := v.branchLikes - discardBranchLikes + newBranchLikes
    )
  }

//   predicate NoOp(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//   && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
//   && v' == v
//   }


  predicate NoOp(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && LB.NextStep(v.likesVars, v'.likesVars, lbl.I(), step.I())
    && v' == v
  }

  datatype Step =
      QueryStep(receipt: BB.QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep(newRootAddr: Address)
    | InternalSplitStep(path: BB.Path, request: SplitRequest, newAddrs: BB.L.SplitAddrs, pathAddrs: BB.PathAddrs)
    | InternalFlushMemtableStep(newRootAddr: Address, branch: LkB.LinkedBranch)
    | InternalFlushStep(path: BB.Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: BB.PathAddrs, branchGCCount: nat)
    | InternalCompactStep(path: BB.Path, start: nat, end: nat, newBranch: LkB.LinkedBranch, targetAddr: Address, pathAddrs: BB.PathAddrs)
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
        case InternalFlushMemtableStep(newRootAddr, branch) => LB.InternalFlushMemtableStep(newRootAddr, branch)
        case InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount) 
          => LB.InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount)
        case InternalCompactStep(path, start, end, newBranch, targetAddr, pathAddrs) 
          => LB.InternalCompactStep(path, start, end, newBranch, targetAddr, pathAddrs) 
        case InternalNoOpStep() => LB.InternalNoOpStep
      }
    }
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep(_) => OnlyAdvanceBranchedVars(v, v', lbl, step)
      case PutStep() => OnlyAdvanceBranchedVars(v, v', lbl, step)
      case QueryEndLsnStep() => OnlyAdvanceBranchedVars(v, v', lbl, step)
      case FreezeAsStep() => OnlyAdvanceBranchedVars(v, v', lbl, step)
      case InternalGrowStep(_) => InternalGrow(v, v', lbl, step)
      // case InternalSplitStep(_, _, _, _) => InternalSplit(v, v', lbl, step)
      // case InternalFlushMemtableStep(_,_) => InternalFlushMemtable(v, v', lbl, step)
      // case InternalFlushStep(_, _, _, _, _, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactStep(_, _, _, _, _, _) => InternalCompact(v, v', lbl, step)
      case InternalNoOpStep() => NoOp(v, v', lbl, step)
      case _ => NoOp(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }  

} // end AllocationBranchedBetreeMod