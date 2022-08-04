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
    // we currently do not require each b+tree to be disjoint from another 
    // TODO: should we require each tree to be disjoint from another?
    //       we could enforce that in addtree if we don't plan to init from a new one 
		predicate WF() {
			&& diskView.WF()
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

    predicate ValidRanking(ranking: D.Ranking) 
      requires WF()
    {
      && diskView.ValidRanking(ranking)
      && (forall root | root in trees :: root in ranking)
    }

    function TheRanking() : D.Ranking
      requires Acyclic()
    {
      var out :| ValidRanking(out);
      out
    }

    predicate Acyclic()
    {
      && WF()
      && (exists ranking :: ValidRanking(ranking))
    }
	}
  

	datatype Step = AddTreeStep | RemoveTreeStep(branch: LinkedBranch)

	datatype TransitionLabel =
    AddTreeLabel(tree: LinkedBranch)
  | RemoveTreeLabel(root: Address) // new diskview in step

	datatype Variables = Variables(forest: LinkedForest) {
		predicate WF() {
			&& forest.WF()
		}

    function Addresses() : set<Address>
		{
			set addr | addr in forest.diskView.entries
		}
	}

  // TODO: each tree is disjoint from another should be kept as an Inv
  predicate AddTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) {
    && lbl.AddTreeLabel?
    && step.AddTreeStep?
    && v.WF()
    // new tree must be acyclic with fresh addresses
    && lbl.tree.WF()
    && lbl.tree.Acyclic()
    && v.forest.diskView.IsFresh(lbl.tree.diskView.Addresses())
    // updated forest
    && v'.forest.trees == v.forest.trees + { lbl.tree.root }
    && v'.forest.diskView == v.forest.diskView.MergeDisk(lbl.tree.diskView)
  }

  predicate RemoveTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) {
    && lbl.RemoveTreeLabel?
    && step.RemoveTreeStep?
    && v.WF()

    && lbl.root in v.forest.trees
    && step.branch.root == lbl.root
    && step.branch.WF()
    && step.branch.Acyclic()

    // well somehow remove a tight disk tree
    // TODO!
    // makes sure everything is found elsewhere 
  }

	// public:

  // TODO: might need to update to StampedLinkedForest
  predicate Init(v: Variables) {
    && v.WF()
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case AddTreeStep() => AddTree(v, v', lbl)
      case RemoveTreeStep(branch) => RemoveTree()
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(v, v', lbl, step)
  }
}

