// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Branches.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "Domain.i.dfy"
include "../../lib/Base/mathematics.i.dfy"
include "../../lib/Base/Multisets.i.dfy"
// include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "BranchedBetree.i.dfy"
include "SplitRequest.i.dfy"

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
  // import opened SplitRequestMod
  import opened BranchesMod
  import opened Multisets

  import M = Mathematics
  import BB = BranchedBetreeMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type Ranking = GenericDisk.Ranking
  type StampedBetree = Stamped<BB.BranchedBetree>

  type Likes = multiset<Address>

  function NoLikes() : Likes
  {
    multiset{}
  }

  function mapsum<T>(s: map<T, Likes>) : Likes
  {
    if s.Keys == {} then NoLikes()
    else (
      var k :| k in s.Keys;
      s[k] + mapsum(MapRemove1(s, k))
    )
  }

  function toSeq<T>(s: set<T>) : seq<T> 
  {
    if s == {} then []
    else (
      var e :| e in s;
      [e] + toSeq(s - {e})
    )
  }

  // TODO: add to branch module
  function BranchLikes(root: Address, branches: Branches) : Likes
  {
    NoLikes() 
  }

  function TransitiveLikes(bbtree: BB.BranchedBetree, r: Ranking) : Likes
    requires bbtree.WF()
    requires bbtree.ValidRanking(r)
    decreases bbtree.GetRank(r)
  {
    if !bbtree.HasRoot()
    then
      NoLikes()
    else (
      var root := bbtree.Root();
      var branchLikes := mapsum(map addr | addr in root.buffers :: BranchLikes(addr, bbtree.branches)); 
      var childrenLikes := mapsum(map i | 0 <= i < |root.children| :: TransitiveLikes(bbtree.ChildAtIdx(i), r));
      branchLikes + childrenLikes
    )
  }

  function ImperativeLikes(v: Variables) : Likes
  {
    var branchLikes := mapsum(map addr | addr in v.branchLikes :: 
      Multiply(BranchLikes(addr, v.branchedVars.branched.branches), v.branchLikes[addr]));
    branchLikes + v.betreeLikes
  }

  predicate ImperativeAgreement(v: Variables) 
  {
    && v.branchedVars.branched.Acyclic()
    // && v.branchedVars.branched.Valid()
    && TransitiveLikes(v.branchedVars.branched, v.branchedVars.branched.TheRanking()) == ImperativeLikes(v)
  }

  datatype Variables = Variables(
    // Inheritedstuff
    branchedVars: BB.Variables,
  
    // plus imperatively-maintained view of the functional TransitiveLikes:
    betreeLikes: Likes, // internal refs
    branchLikes: Likes // outgoing refs
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
        case InternalAllocationsLabel(addrs) => BB.InternalAllocationsLabel(toSeq(addrs), [])
        case _ => BB.InternalLabel
      }
    }
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && BB.Next(v.branchedVars, v'.branchedVars, lbl.I())
    // && BB.InternalGrow(v.branchedVars, v'.branchedVars, lbl.I(), step.I())
    && v' == v.(
      branchedVars := v'.branchedVars,  // admit relational update above
      betreeLikes := v.betreeLikes
    )
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && BB.Next(v.branchedVars, v'.branchedVars, lbl.I())
//     && LinkedBetreeMod.InternalCompact(v.betree, v'.betree, lbl.I(), step.I())

    // should be in step
    // && var root := v.branchedVars.branched.Root() 
    // && var unlikedBranchRoots := multiset{Set(root.buffers[compactStart..compactEnd])};
    // && var unlikedBetreeNodes := step.path.AddrsOnPath();

    // && v' == v.(
    //   branchedVars := v'.branchedVars,  // admit relational update above
    //   betreeLikes := v.betreeLikes + step.treeAddrs - unlikedBetreeNodes,
    //   branchLikes := v.branchLikes + multiset{step.compactedBranch.root} - unlikedBranchRoots,
    // )
  }

  datatype Step =
    | InternalGrow(newRootAddr: Address)
    | InternalCompact()
    | InternalLabel()   // Local No-op label
  {
  //   function I() : BB.TransitionLabel
  //   {
  //     match this {
  //       case InternalAllocationsLabel(addrs) => BB.InternalAllocationsLabel(toSeq(addrs), [])
  //       case _ => BB.InternalLabel
  //     }
  //   }
  }

} // module
