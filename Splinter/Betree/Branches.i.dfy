// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "LinkedBranch.i.dfy"

module BranchesMod {
	import opened KeyType
	import opened ValueMessage
  import opened Maps
	import opened Sequences
  import opened OffsetMapMod
	import opened LinkedBranchMod
  import D = GenericDisk

  function EmptyBranches() : Branches
  {
    Branches({}, DiskView.DiskView(map[]))
  }

  // track a sequence of roots
  datatype BranchSeq = BranchSeq(roots: seq<Address>)
  {
    predicate Valid(dv: DiskView)
    {
      && (forall i:nat | i < |roots| :: roots[i] in dv.Representation())
      && (forall i:nat | i < |roots| :: LinkedBranch(roots[i], dv).Acyclic())
    }

    function Length() : nat 
    {
      |roots|
    }

    function Representation() : set<Address> {
      set addr | addr in roots :: addr
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
      requires Valid(dv)
      decreases |roots| - start
    {
      if start == |roots| then Update(NopDelta())
      else (
        var branch := LinkedBranch(roots[start], dv);
        Merge(QueryFrom(dv, key, start+1), branch.Query(key))
      )
    }

    function DropFirst() : BranchSeq
      requires 0 < |roots|
    {
      Slice(1, |roots|)
    }

    function QueryFiltered(dv: DiskView, offsetMap: OffsetMap, key: Key) : Message
      requires Valid(dv)
      requires offsetMap.WF()
      decreases Length()
    {
      if |roots| == 0 then Update(NopDelta())
      else (
        var branch := LinkedBranch(roots[0], dv);
        var msg := if key in offsetMap.FilterForBottom() then branch.Query(key) else Update(NopDelta());
        Merge(DropFirst().QueryFiltered(dv, key, offsetMap.Decrement(1)), msg)
      )
    }

    predicate QueryFilteredEquiv(dv: DiskView, offsetMap: OffsetMap, newBranch: LinkedBranch)
      requires Valid(dv)
      requires offsetMap.WF()
      requires newBranch.Acyclic()
    {
      && (forall key :: QueryFiltered(dv, key, offsetMap) == newBranch.Query(key))    
    }
  }  // end type BranchSeq

	// Track the branches as branchroot and a single diskView
	// We can construct LinkedBranch from each tree and the diskView
	datatype Branches = Branches(roots: set<Address>, diskView: DiskView) 
	{
		predicate WF() {
			&& diskView.WF() // ensures all nodes are connected
			&& (forall root | root in roots :: diskView.ValidAddress(root))
      && (forall root | root in roots :: GetBranch(root).Acyclic())
      // && (forall root | root in roots :: GetBranch(root).AllKeysInRange())
      && BranchesDisjoint()
		}

    predicate BranchesDisjoint()
      requires (forall root | root in roots :: GetBranch(root).Acyclic())
    {
      && (forall r1, r2 | r1 in roots && r2 in roots && r1 != r2 :: 
        GetBranch(r1).ReachableAddrs() !! GetBranch(r2).ReachableAddrs())
    }

		predicate ValidBranch(addr: Address)
		{
			addr in roots
		}

		function GetBranch(addr: Address) : (branch: LinkedBranch)
      requires ValidBranch(addr)
		{
      LinkedBranch(addr, diskView)
		}

		function Query(key: Key, roots: seq<Address>) : Message
      requires WF()
      requires (forall addr | addr in roots :: ValidBranch(addr))
		{
			if roots == [] then Update(NopDelta())
      else (
				var branch := GetBranch(Last(roots));
        Merge(Query(key, DropLast(roots)), branch.Query(key))
			)
		}

    function AddBranch(branch: LinkedBranch) : (out: Branches)
      requires WF()
      requires branch.Acyclic()
   //   requires branch.AllKeysInRange()
      requires branch.TightDiskView()
      requires diskView.IsFresh(branch.ReachableAddrs())
    {
      Branches(roots + {branch.root}, diskView.MergeDisk(branch.diskView))
    }
    
    function RemoveBranch(root: Address) : (out: Branches)
      requires WF()
      requires ValidBranch(root)
    {
      var branchDisk := DiskView(MapRestrict(diskView.entries, GetBranch(root).ReachableAddrs()));
      Branches(roots - {root}, diskView.RemoveDisk(branchDisk))
    }
	}
}
