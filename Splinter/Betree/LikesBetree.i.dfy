// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "../Likes.i.dfy"
include "Domain.i.dfy"
include "../../lib/Base/mathematics.i.dfy"
include "../../lib/Base/Multisets.i.dfy"
// include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "BranchedBetree.i.dfy"

module LikesBetreeMod
{
  import GenericDisk
  import opened LSNMod
  import opened MsgHistoryMod
  import opened Sequences
  import opened StampedMod
  import opened KeyType
  import opened ValueMessage
  import opened Maps
  import opened SplitRequestMod
  import opened BranchSeqMod
  import opened Multisets
  import opened LikesMod
  import opened Sets

  import M = Mathematics
  import BB = BranchedBetreeMod
  import LB = LinkedBranchMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type Ranking = GenericDisk.Ranking
  type StampedBetree = Stamped<BB.BranchedBetree>
  type BranchDiskView = LB.DiskView

  // Likes for a single B+Tree branch
  function BranchLikes(root: Address, branchDiskView: BranchDiskView) : Likes
  {
    var branch := LB.LinkedBranch(root, branchDiskView);
    if branch.Acyclic() then multiset(branch.Representation()) else NoLikes()
  }

  // Likes for the entire BranchedBetree
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

  function FullBranchAddrs(branchLikes: Likes, dv: BranchDiskView) : set<Address>
  {
    UnionSetOfSets(set addr | addr in branchLikes :: M.Set(BranchLikes(addr, dv)))
  }

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(branched: StampedBetree)
    | InternalLabel()   // Local No-op label
  {
    function I() : BB.TransitionLabel
    {
      match this {
        case QueryLabel(endLsn, key, value) => BB.QueryLabel(endLsn, key, value)
        case PutLabel(puts) => BB.PutLabel(puts)
        case QueryEndLsnLabel(endLsn) => BB.QueryEndLsnLabel(endLsn)
        case FreezeAsLabel(branched) => BB.FreezeAsLabel(branched)
        case _ => BB.InternalLabel
      }
    }
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

    predicate IsFresh(addrs: set<Address>) {
      && addrs !! M.Set(betreeLikes)
      // && addrs !! M.Set(branchLikes)
      // && addrs !! branchedVars.branched.branchDiskView.Representation()
      && addrs !! FullBranchAddrs(branchLikes, branchedVars.branched.branchDiskView)
    }
  }

  // group a couple definitions together
  predicate OnlyAdvanceBranchedVars(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && (lbl.QueryLabel? || lbl.PutLabel? || lbl.QueryEndLsnLabel?)
    && BB.NextStep(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && v' == v.(
      branchedVars := v'.branchedVars // admit relational update above
    )
  }

  predicate InternalGrowTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && BB.InternalGrowTree(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := v.betreeLikes + multiset{step.newRootAddr}
    )
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalGrowTree(v, v', lbl, step)
    && v.IsFresh({step.newRootAddr})  // Subway Eat Fresh!
  }

  predicate InternalFlushMemtableTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && BB.InternalFlushMemtableTree(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && var oldRoot := if v.branchedVars.branched.HasRoot() then multiset{v.branchedVars.branched.root.value} else multiset{};
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := v.betreeLikes - oldRoot + multiset{step.newRootAddr},
      branchLikes := v.branchLikes + multiset{step.branch.root}
    )
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalFlushMemtableTree(v, v', lbl, step)
    && v.IsFresh({step.newRootAddr})
    && v.IsFresh(step.branch.Representation())
  }

  predicate InternalSplitTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && BB.InternalSplitTree(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && var newBetreeLikes := multiset(Set(step.pathAddrs) + step.newAddrs.Repr());
    && var derefBetreeLikes := 
        multiset(step.path.AddrsOnPath() + [step.path.Target().ChildAtIdx(step.request.childIdx).root.value]);
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := v.betreeLikes - derefBetreeLikes + newBetreeLikes
      // branchLikes do not change
    )
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalSplitTree(v, v', lbl, step)
    && v.IsFresh(step.newAddrs.Repr() + Set(step.pathAddrs))
  }

  predicate InternalFlushTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && BB.InternalFlushTree(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && var target := step.path.Target();
    && var root := target.Root();
    && var newflushedOffsets := root.flushedOffsets.AdvanceIndex(step.childIdx, root.branches.Length());
    && assert step.branchGCCount <= root.branches.Length() by {
      var i:nat :| i < newflushedOffsets.Size();
      assert newflushedOffsets.Get(i) <= root.branches.Length();
    }
    && var newBetreeLikes := multiset(Set(step.pathAddrs) + {step.targetAddr, step.targetChildAddr});
    && var derefBetreeLikes := multiset(step.path.AddrsOnPath() + [target.ChildAtIdx(step.childIdx).root.value]);
    && var newBranchLikes := root.branches.Slice(root.flushedOffsets.Get(step.childIdx), root.branches.Length()).ToMultiset();
    && var derefBranchLikes := root.branches.Slice(0, step.branchGCCount).ToMultiset();
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := v.betreeLikes - derefBetreeLikes + newBetreeLikes,
      branchLikes := v.branchLikes - derefBranchLikes + newBranchLikes
    )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalFlushTree(v, v', lbl, step)
    && v.IsFresh({step.targetAddr, step.targetChildAddr} + Set(step.pathAddrs))
  }

  predicate InternalCompactTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && BB.InternalCompactTree(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && var newBetreeLikes := multiset(Set(step.pathAddrs) + {step.targetAddr});
    && var derefBetreeLikes := multiset(step.path.AddrsOnPath());
    && var newBranchLikes := multiset{step.newBranch.root};
    && var derefBranchLikes := step.path.Target().Root().branches.Slice(step.start, step.end).ToMultiset();
    && v' == v.(
      branchedVars := v'.branchedVars, // admit relational update above
      betreeLikes := v.betreeLikes - derefBetreeLikes + newBetreeLikes,
      branchLikes := v.branchLikes - derefBranchLikes + newBranchLikes
    )
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalCompactTree(v, v', lbl, step)
    && v.IsFresh(Set(step.pathAddrs) + {step.targetAddr} + step.newBranch.Representation())
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && BB.InternalNoOp(v.branchedVars, v'.branchedVars, lbl.I())
    && v' == v
  }

  predicate Init(v: Variables, stamped: StampedBetree)
  {
    && BB.Init(v.branchedVars, stamped)
    && ImperativeAgreement(v)
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
        case InternalSplitStep(path, request, newAddrs, pathAddrs)
          => BB.InternalSplitStep(path, request, newAddrs, pathAddrs)
        case InternalFlushMemtableStep(newRootAddr, branch) => BB.InternalFlushMemtableStep(newRootAddr, branch)
        case InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount) 
          => BB.InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, branchGCCount)
        case InternalCompactStep(path, start, end, newBranch, targetAddr, pathAddrs) 
          => BB.InternalCompactStep(path, start, end, newBranch, targetAddr, pathAddrs) 
        case InternalNoOpStep() => BB.InternalNoOpStep
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
      case InternalSplitStep(_, _, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushMemtableStep(_,_) => InternalFlushMemtable(v, v', lbl, step)
      case InternalFlushStep(_, _, _, _, _, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactStep(_, _, _, _, _, _) => InternalCompact(v, v', lbl, step)
      case InternalNoOpStep() => InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }  

} // moduleif v.betreeLikes[step] 