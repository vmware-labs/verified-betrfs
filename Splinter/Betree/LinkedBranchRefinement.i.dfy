// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "LinkedBranch.i.dfy"

// LinkedBranch module stores each node in the b+tree on a different disk address

module LinkedBranchRefinement {
  import opened Maps
  import opened Options
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import opened DomainMod
  import opened GenericDisk
  import opened Sets
  import opened LinkedBranchMod
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord
  import P = PivotBranchMod


  // Interpretation functions
  function I(branch: LinkedBranch) : (out: P.Node)
    requires branch.Acyclic()
    ensures branch.Root().Index? <==> out.Index?
    ensures branch.AllKeysInRange() ==> out.WF()
  {
    var ranking := branch.TheRanking();
    var out := ILinkedBranchNode(branch, ranking);
    assert branch.AllKeysInRange() ==> out.WF() by {
      if branch.AllKeysInRangeInternal(ranking) {
        ILinkedBranchNodeWF(branch, ranking);
      }
    }
    out
  }

  function ILinkedBranchNode(branch: LinkedBranch, ranking: Ranking) : (out: P.Node)
    requires branch.WF()
    requires branch.ValidRanking(ranking)
    ensures branch.Root().Index? <==> out.Index?
    ensures branch.Root().Index? ==> branch.Root().pivots == out.pivots
    ensures branch.Root().Index? ==> |branch.Root().children| == |out.children|      
    decreases branch.GetRank(ranking), 1
  {
    var node := branch.Root();
    if node.Leaf? 
    then P.Leaf(node.keys, node.msgs)
    else P.Index(node.pivots, IChildren(branch, ranking))
  }

  function IChildren(branch: LinkedBranch, ranking: Ranking) : (out: seq<P.Node>)
    requires branch.WF()
    requires branch.Root().Index?
    requires branch.ValidRanking(ranking)
    decreases branch.GetRank(ranking), 0
  {
    var numChildren := |branch.Root().children|;
    seq(numChildren, i requires 0 <= i < numChildren => 
      ILinkedBranchNode(branch.ChildAtIdx(i), ranking))
  }

  lemma AllKeysIsConsistentWithI(branch: LinkedBranch, ranking: Ranking)
    requires branch.WF()
    requires branch.ValidRanking(ranking)
    ensures branch.AllKeys(ranking) == ILinkedBranchNode(branch, ranking).AllKeys()
    decreases branch.GetRank(ranking)
  {
    var node := branch.Root();
    if node.Leaf? {
    } else {
      var node' := ILinkedBranchNode(branch, ranking);
      assert IChildren(branch, ranking) == node'.children; // trigger

      forall k 
        ensures k in node'.AllKeys() <==> k in branch.AllKeys(ranking)
      {
        if k in node'.AllKeys() {
          if k !in node'.pivots {
            var i :| 0 <= i < |node'.children| && k in node'.children[i].AllKeys();
            AllKeysIsConsistentWithI(branch.ChildAtIdx(i), ranking);
            assert k in branch.AllKeys(ranking);
          }
        } else if k in branch.AllKeys(ranking) {
          if k !in node.pivots {
            var i :| 0 <= i < |node.children| && k in branch.ChildAtIdx(i).AllKeys(ranking);
            var linked_child := branch.ChildAtIdx(i);
            assert ILinkedBranchNode(linked_child, ranking) == node'.children[i];
            AllKeysIsConsistentWithI(linked_child, ranking);
            assert k in node'.AllKeys();
            assert false;
          }
        }
      }
    }
  }

  lemma ILinkedBranchNodeWF(branch: LinkedBranch, ranking: Ranking)
    requires ILinkedBranchNode.requires(branch, ranking)
    requires branch.AllKeysInRangeInternal(ranking)
    ensures ILinkedBranchNode(branch, ranking).WF()
    decreases branch.GetRank(ranking)
  {
    var node := branch.Root();
    var out := ILinkedBranchNode(branch, ranking);
      
    if node.Index? {
      assert |out.pivots| == |out.children| - 1;
      assert Keys.IsStrictlySorted(out.pivots);

      forall i | 0 <= i < |IChildren(branch, ranking)|
        ensures IChildren(branch, ranking)[i].WF()
      {
        ILinkedBranchNodeWF(branch.ChildAtIdx(i), ranking);
      }

      assert IChildren(branch, ranking) == out.children; // trigger
      assert (forall i :: 0 <= i < |out.children| ==> out.children[i].WF());

      forall i | 0 <= i < |out.children|
        ensures i < |out.children|-1  ==> out.AllKeysBelowBound(i)
        ensures 0 < i ==> out.AllKeysAboveBound(i)
      {
        var child := out.children[i];
        var linked_child := branch.ChildAtIdx(i);
          
        if 0 <= i < |out.children|-1 {
          assert branch.AllKeysBelowBound(i, ranking);
        }

        if 0 < i < |out.children| {
          assert branch.AllKeysAboveBound(i, ranking);
        }

        AllKeysIsConsistentWithI(linked_child, ranking);
      }
    }
  }

  // query refines
  // I().WF() ==> msg == I().Query(key)
  // ILinkedBranchNode(ranking).WF() ==> msg == ILinkedBranchNode(ranking).Query(key)


}
