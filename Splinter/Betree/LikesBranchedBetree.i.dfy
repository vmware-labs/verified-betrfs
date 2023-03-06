// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "../Likes.i.dfy"
include "Domain.i.dfy"
include "../../lib/Base/mathematics.i.dfy"
include "../../lib/Base/Multisets.i.dfy"
// include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "BranchedBetree.i.dfy"

module LikesBranchedBetreeMod
{
  // import opened BoundedPivotsLib
  // import opened DomainMod
  import GenericDisk
  // import opened LSNMod
  // import opened MemtableMod
  // import opened MsgHistoryMod
  // import opened Options
  import opened Sequences
  import opened StampedMod
  // import opened Upperbounded_Lexicographic_Byte_Order_Impl
  // import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  // import opened KeyType
  // import opened ValueMessage
  import opened Maps
  // import TotalKMMapMod
  import opened SplitRequestMod
  import opened BranchSeqMod
  import opened Multisets
  import opened LikesMod

  import M = Mathematics
  import BB = BranchedBetreeMod
  import LB = LinkedBranchMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type Ranking = GenericDisk.Ranking
  type StampedBetree = Stamped<BB.BranchedBetree>
  type BranchDiskView = LB.DiskView

  function BranchLikes(root: Address, branchDiskView: BranchDiskView) : Likes
  {
    var branch := LB.LinkedBranch(root, branchDiskView);
    if branch.Acyclic() then multiset(branch.Representation()) else NoLikes()
  }

  function TransitiveLikes(bbtree: BB.BranchedBetree) : Likes
    requires bbtree.Acyclic()
  {
    TransitiveLikesDefn(bbtree, bbtree.TheRanking())
  }

  // Account for every page reachable from bbtree.Root(), including
  // a ref the root. The caller of this, from some other data structure,
  // will multiply all my likes by the number of references into it from
  // that outer structure, so we can't leave any reachable stuff with zero.
  function TransitiveLikesDefn(bbtree: BB.BranchedBetree, r: Ranking) : Likes
    requires bbtree.WF()
    requires bbtree.ValidRanking(r)
    decreases bbtree.GetRank(r)
  {
    if !bbtree.HasRoot()
    then
      NoLikes()
    else (
      var root := bbtree.Root();
      var rootLikes := multiset{bbtree.root.value};
      var branchLikes := mapsum(map addr | addr in root.branches.Representation() :: BranchLikes(addr, bbtree.branchDiskView)); 
      var childrenLikes := mapsum(map i | 0 <= i < |root.children| :: TransitiveLikesDefn(bbtree.ChildAtIdx(i), r));
      rootLikes + branchLikes + childrenLikes
    )
  }

  function ImperativeLikes(v: Variables) : Likes
  {
    var branchLikes := mapsum(map addr | addr in v.branchLikes :: 
      Multiply(BranchLikes(addr, v.branchedVars.branched.branchDiskView), v.branchLikes[addr]));
    branchLikes + v.betreeLikes
  }

  // TODO invariant; move to proof
  predicate ImperativeAgreement(v: Variables) 
  {
    && v.branchedVars.branched.Acyclic()
    && TransitiveLikes(v.branchedVars.branched) == ImperativeLikes(v)
  }

  datatype Variables = Variables(
    // Inheritedstuff
    branchedVars: BB.Variables,
  
    // plus imperatively-maintained view of the functional TransitiveLikes:
    // internal refs, track # of times each betree node is referenced by another node
    // should be 1 for tree, can be more after clone makes it a DAG
    betreeLikes: Likes, 
    // outgoing refs, track # of times each b+tree root is referenced by a betree node
    branchLikes: Likes
  )
  {
    predicate WF() {
      && branchedVars.WF()
    }
  }

  datatype TransitionLabel =
    | InternalAllocationsLabel(addrs: set<Address>)
    | InternalLabel()   // Local No-op label
  {
    function I() : BB.TransitionLabel
    {
      match this {
        case InternalAllocationsLabel(addrs) => BB.InternalAllocationsLabel(addrs)
        case _ => BB.InternalLabel
      }
    }
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && step.InternalGrowStep?
    && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := v.betreeLikes + multiset{step.newRootAddr}
    )
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && step.InternalFlushMemtableStep?
    && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && var oldRoot := if v.branchedVars.branched.HasRoot() then multiset{v.branchedVars.branched.root.value} else multiset{};
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := v.betreeLikes - oldRoot + multiset{step.newRootAddr},
      branchLikes := v.branchLikes + multiset{step.branch.root}
    )
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && step.InternalSplitStep?
    && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())

    && var node := v.branchedVars.branched.Root();
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := 
        v.betreeLikes - multiset{node.children[step.request.childIdx].value} - multiset{ v.branchedVars.branched.root.value}
        + multiset{step.newAddrs.parent} + multiset{step.newAddrs.left} + multiset{step.newAddrs.right}
      // branchLikes do not change as a result
    )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && step.InternalFlushStep?
    && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())

    && var node := v.branchedVars.branched.Root();
    && v' == v.(
      branchedVars := v'.branchedVars // admit relational update above
    )
  }

//   predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//     && lbl.InternalAllocationsLabel?
//     && BB.Next(v.branchedVars, v'.branchedVars, lbl.I())
// //     && LinkedBetreeMod.InternalCompact(v.betree, v'.betree, lbl.I(), step.I())

//     // should be in step
//     // && var root := v.branchedVars.branched.Root() 
//     // && var unlikedBranchRoots := multiset{Set(root.buffers[compactStart..compactEnd])};
//     // && var unlikedBetreeNodes := step.path.AddrsOnPath();

//     // && v' == v.(
//     //   branchedVars := v'.branchedVars,  // admit relational update above
//     //   betreeLikes := v.betreeLikes + step.treeAddrs - unlikedBetreeNodes,
//     //   branchLikes := v.branchLikes + multiset{step.compactedBranch.root} - unlikedBranchRoots,
//     // )
//   }

  predicate NoOp(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && v' == v
  }

  datatype Step =
      QueryStep(receipt: BB.QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep(newRootAddr: Address)
    | InternalSplitStep(path: BB.Path, request: SplitRequest, newAddrs: BB.L.SplitAddrs, pathAddrs: BB.PathAddrs)
    | InternalFlushMemtableStep(newRootAddr: Address, branch: LB.LinkedBranch)
    | InternalFlushStep(path: BB.Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: BB.PathAddrs, branchGCCount: nat)
    | InternalCompactStep(path: BB.Path, start: nat, end: nat, newBranch: LB.LinkedBranch, targetAddr: Address, pathAddrs: BB.PathAddrs)
    | InternalNoOpStep()   // Local No-op label
  {
    function I() : BB.Step
    {
      match this {
        case QueryStep(receipt) => BB.QueryStep(receipt)
        case PutStep() => BB.PutStep()
        case QueryEndLsnStep() => BB.QueryEndLsnStep
        case FreezeAsStep() => BB.FreezeAsStep()
        case InternalGrowStep(newRootAddr) => BB.InternalGrowStep(newRootAddr)
        case InternalFlushMemtableStep(newRootAddr, branch) => BB.InternalFlushMemtableStep(newRootAddr, branch)
        case InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount) 
          => BB.InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount)
        case InternalCompactStep(path, start, end, newBranch, targetAddr, pathAddrs) 
          => BB.InternalCompactStep(path, start, end, newBranch, targetAddr, pathAddrs) 
        case _ => BB.InternalNoOpStep
      }
    }
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case InternalGrowStep(_) => InternalGrow(v, v', lbl, step)
      case InternalSplitStep(_, _, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushMemtableStep(_,_) => InternalFlushMemtable(v, v', lbl, step)
      case InternalFlushStep(_, _, _, _, _, _) => InternalFlush(v, v', lbl, step)
      // case InternalCompactStep(_, _, _, _, _, _) => InternalCompact(v, v', lbl, step)
      case _ => NoOp(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }  

} // moduleif v.betreeLikes[step] 