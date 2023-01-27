// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Branches.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "Domain.i.dfy"
include "../../lib/Base/mathematics.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "LinkedBetree.i.dfy"
include "SplitRequest.i.dfy"

module LikesBranchedBetreeMod
{
  import opened BoundedPivotsLib
  import opened DomainMod
  import opened GenericDisk
  import opened LSNMod
  import opened MemtableMod
  import opened MsgHistoryMod
  import opened Options
  import opened Sequences
  import opened StampedMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened KeyType
  import opened ValueMessage
  import opened Maps
  import TotalKMMapMod
  import opened SplitRequestMod

  import M = Mathematics
  import BB = BranchedBetreeMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type StampedBetree = Stamped<BranchedBetree>

  function TransitiveLikes(dv: DiskView, ptr: Pointer, r: Ranking) : Likes
  {
    if ptr.None
    then
      NoLikes()
    else (
      var node := dv.get(ptr);
      var branchLikes = sum(fcnlmap(node.buffers,
        bufferRoot => BranchMod.TransitiveLikes(branches, bufferRoot)));
      var childrenLikes = sum(set(chlidren),
        childPtr => TransitiveLikes(dv, childPtr, r));
      branchLikes + childrenLikes
    )
  }

  function ImperativeLikes(v: Variables) : Likes
  {
    var branchLikes := sum(fcnlmap(v.branchLikes,
        branchRoot => BranchMod.TransitiveLikes(branches, branchRoot)) * v.branchLikes.multiplicity(branchRoot))
    branchLikes + v.betreeLikes
  }

  predicate ImperativeAgreement(v: Variables) {
    TransitiveLikes(blah, v.branchedVars.root, blah) == ImperativeLikes(v)
  }

  datatype Variables = Variables(
    // Inheritedstuff
    branchedVars: BB.Variables,
  
    // plus imperatively-maintained view of the functional TransitiveLikes:
    betreeLikes: Likes, // internal refs
    branchLikes: Likes, // outgoing refs
  )
  {
    predicate WF() {
      && bbtree.WF()
    }
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    // NB step.newRootAddr, allocation, and lbl are all tied together up in
    // LinkedBetree.InternalGrow.
    && BB.InternalGrow(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && v' == v.(
      branchedVars := v'.branchedVars,  // admit relational update above
      betreeLikes := v.betreeLikes,
    )
  }
  
  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && LinkedBetreeMod.InternalCompact(v.betree, v'.betree, lbl.I(), step.I())
    && var unlikedBranchRoots = multiset{Set(root.buffers[compactStart..compactEnd])};
    && var unlikedBetreeNodes := step.path.AddrsOnPath();
    && v' == v.(
      branchedVars := v'.branchedVars,  // admit relational update above
      betreeLikes := v.betreeLikes + lbl.treeAddrs - unlikedBetreeNodes,
      branchLikes := v.branchLikes + multiset{step.compactedBranch.root} - unlikedBranchRoots,
    )
  }

  

} // module
