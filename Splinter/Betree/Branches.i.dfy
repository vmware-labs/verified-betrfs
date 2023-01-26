// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "LinkedBranch.i.dfy"

module BranchesMod {
	import opened KeyType
	import opened ValueMessage
  import opened Maps
	import opened Sequences
	import opened LinkedBranchMod
  import D = GenericDisk

  function EmptyBranches() : Branches
  {
    Branches({}, DiskView.DiskView(map[]))
  }

	// Track the branches as branchroot and a single diskView
	// We can construct LinkedBranch from each tree and the diskView
	datatype Branches = Branches(roots: set<Address>, diskView: DiskView) 
	{
		predicate WF() {
			&& diskView.WF() // ensures all nodes are connected
			&& (forall root | root in roots :: diskView.ValidAddress(root))
      && (forall root | root in roots :: GetBranch(root).Acyclic())
      && (forall root | root in roots :: GetBranch(root).AllKeysInRange())
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

		function Query(key: Key, buffers: seq<Address>) : Message
      requires WF()
      requires (forall addr | addr in buffers :: ValidBranch(addr))
		{
			if buffers == [] then Update(NopDelta())
      else (
				var branch := GetBranch(Last(buffers));
        var msg := if branch.Query(key).Some? then branch.Query(key).value else Update(NopDelta());
				Merge(Query(key, DropLast(buffers)), msg)
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
