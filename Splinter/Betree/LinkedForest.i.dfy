// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Journal/GenericDisk.i.dfy"
include "LinkedBranch.i.dfy"

// Forest at linked layer 
module LinkedForestMod {
	import opened KeyType
	import opened ValueMessage
	import opened Sequences
	import opened LinkedBranchMod
  import D = GenericDisk

	// Track the forest as trees and a single diskView
	// We can construct LinkedBranch from each tree and the diskView
	datatype LinkedForest = LinkedForest(trees: set<Address>, diskView: DiskView) 
	{
    // TODO: disjoint reachable addrs from each root as part of Inv
		predicate WF() {
			&& diskView.WF() // ensures all nodes are connected
			&& (forall root | root in trees :: diskView.ValidAddress(root))
		}

		predicate ValidTree(addr: Address)
		{
			addr in trees
		}

		function GetTree(addr: Address) : (branch: LinkedBranch)
      requires WF()
      requires ValidTree(addr)
      ensures branch.WF()
		{
			LinkedBranch(addr, diskView)
		}

		function Query(key: Key, buffers: seq<Address>) : Message
      requires WF()
      requires (forall addr | addr in buffers :: ValidTree(addr))
		{
			if buffers == [] then Update(NopDelta())
      else (
				var tree := GetTree(Last(buffers));
				Merge(Query(key, DropLast(buffers)), tree.Query(key))
			)
		}
	}

	datatype Step = AddTreeStep | RemoveTreeStep(branch: LinkedBranch)

	datatype TransitionLabel =
    AddTreeLabel(tree: LinkedBranch)
  | RemoveTreeLabel(root: Address)

	datatype Variables = Variables(forest: LinkedForest) {
		predicate WF() {
			&& forest.WF()
		}

    function AllAddresses() : set<Address>
		{
      forest.diskView.AllAddresses()
		}
	}

  predicate AddTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) {
    && v.WF()
    && lbl.AddTreeLabel?
    && step.AddTreeStep?
    // new tree must be acyclic with fresh addresses
    && lbl.tree.WF()
    && lbl.tree.Acyclic()
    && lbl.tree.TightDiskView()
    && v.forest.diskView.IsFresh(lbl.tree.ReachableAddrs())
    // updated forest
    && v'.forest.trees == v.forest.trees + { lbl.tree.root }
    && v'.forest.diskView == v.forest.diskView.MergeDisk(lbl.tree.diskView)
  }

  predicate RemoveTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) {
    && v.WF()
    && lbl.RemoveTreeLabel?
    && step.RemoveTreeStep?
    && lbl.root in v.forest.trees
    && step.branch.root == lbl.root
    && step.branch.WF()
    && step.branch.Acyclic()
    && step.branch.TightDiskView()
    && v'.forest.trees == v.forest.trees - {lbl.root}
    && v'.forest.diskView == v.forest.diskView.RemoveDisk(step.branch.diskView)
  }

	// public:

  predicate Init(v: Variables, forest: LinkedForest) {
    && v.forest == forest
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case AddTreeStep() => AddTree(v, v', lbl, step)
      case RemoveTreeStep(_) => RemoveTree(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(v, v', lbl, step)
  }
}

