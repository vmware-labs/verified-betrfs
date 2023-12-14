// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "LinkedBranch.i.dfy"

module BranchSeqMod {
  import opened KeyType
  import opened ValueMessage
  import opened Maps
  import opened Sequences
  import opened OffsetMapMod
  import opened LinkedBranchMod
  import D = GenericDisk

  // track a sequence of roots
  datatype BranchSeq = BranchSeq(roots: seq<Address>)
  {
    // predicate Valid(dv: DiskView)
    // {
    //   && (forall i:nat | i < |roots| :: roots[i] in dv.Representation())
    //   && (forall i:nat | i < |roots| :: LinkedBranch(roots[i], dv).Acyclic())
    // }

    function Length() : nat 
    {
      |roots|
    }

    function Representation() : set<Address>
    {
      set addr | addr in roots
    }

    function ToMultiset() : multiset<Address>
    {
      multiset(Representation())
    }

    function Slice(start: nat, end: nat) : BranchSeq
      requires start <= end <= |roots|
    {
      BranchSeq(roots[start..end])
    }

    function Extend(newBranchSeq: BranchSeq) : BranchSeq
    {
      BranchSeq(roots + newBranchSeq.roots)
    }

    function QueryFrom(dv: DiskView, key: Key, start: nat) : Message
      requires start <= |roots|
      decreases |roots| - start
    {
      if start == |roots| then Update(NopDelta())
      else (
        var branch := LinkedBranch(roots[start], dv);
        var msg := if branch.Acyclic() then branch.Query(key) else Update(NopDelta());
        Merge(QueryFrom(dv, key, start+1), msg)
      )
    }

    function DropFirst() : BranchSeq
      requires 0 < |roots|
    {
      Slice(1, |roots|)
    }

    function QueryFiltered(dv: DiskView, offsetMap: OffsetMap, key: Key) : Message
      requires offsetMap.WF()
      decreases Length()
    {
      if |roots| == 0 then Update(NopDelta())
      else (
        var branch := LinkedBranch(roots[0], dv);
        var msg := 
          if branch.Acyclic() && key in offsetMap.FilterForBottom() 
          then branch.Query(key) else Update(NopDelta());
        Merge(DropFirst().QueryFiltered(dv, offsetMap.Decrement(1), key), msg)
      )
    }

    predicate QueryFilteredEquiv(dv: DiskView, offsetMap: OffsetMap, newBranch: LinkedBranch)
      requires offsetMap.WF()
      requires newBranch.Acyclic()
    {
      && (forall key :: QueryFiltered(dv, offsetMap, key) == newBranch.Query(key))    
    }
  }  // end type BranchSeq
}
