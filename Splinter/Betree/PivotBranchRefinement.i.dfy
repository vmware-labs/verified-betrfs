// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBranch.i.dfy"

module PivotBranchRefinement {
  import opened Maps
  import opened Options
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import opened DomainMod
  import opened BufferMod
  import opened PivotBranchMod
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord

  // a data structure refinement: pivot branch => buffer

  lemma GrowPreservesWF(node: Node)
    requires node.WF()
    requires node.AllKeys() != {}
    ensures node.Grow().WF()
  {
    assert Keys.IsStrictlySorted([]) by {
      Keys.reveal_IsStrictlySorted();
    }
  }

  lemma GrowPreservesAllKeys(node: Node)
    requires node.WF()
    ensures node.Grow().AllKeys() == node.AllKeys()
  {
    assert forall key :: key in node.AllKeys() ==> key in node.Grow().children[0].AllKeys();
  }

  lemma InterpretationDelegation(node: Node, key: Key)
    requires node.WF()
    requires node.Index?
    requires key in node.children[Keys.LargestLte(node.pivots, key)+1].I().mapp
    ensures MapsTo(node.I().mapp, key, node.children[Keys.LargestLte(node.pivots, key)+1].I().mapp[key])
  {
    var interp := node.I().mapp;
    assert key in node.children[Keys.LargestLte(node.pivots, key)+1].AllKeys();
    assert key in node.AllKeys();
    assert key in interp;
  }

  // lemma AllKeysIsConsistentWithInterpretation(node: Node, key: Key)
  //   requires node.WF()
  //   requires key in node.I().mapp
  //   ensures key in node.AllKeys()
  //   ensures node.Index? ==> 
  //     node.WF() && key in node.AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
  // {
  //   if node.Index? {
  //     assert key in (node.children[Keys.LargestLte(node.pivots, key) + 1]);
  //   }
  // }

  lemma GrowPreservesI(node: Node)
    requires node.WF()
    requires node.AllKeys() != {}
    ensures node.Grow().WF()
    ensures node.Grow().I() == node.I()
  {
    var interp := node.I().mapp;
    GrowPreservesWF(node);
    var ginterp := node.Grow().I().mapp;
      
    forall key | key in interp
      ensures key in ginterp && ginterp[key] == interp[key]
    {
      InterpretationDelegation(node.Grow(), key);
    }
  }

  lemma {:timeLimitMultiplier 2} InsertLeafIsCorrect(node: Node, key: Key, msg: Message)
    requires node.Leaf?
    requires node.WF()
    ensures node.InsertLeaf(key, msg).I() == Buffer(node.I().mapp[key := msg])
    // ensures node.InsertLeaf(key, msg).AllKeys() == node.AllKeys() + {key}
  {
    var result := node.InsertLeaf(key, msg);
    var llte := Keys.LargestLte(node.keys, key);
    if 0 <= llte && node.keys[llte] == key {
      assert result.I() == Buffer(node.I().mapp[key := msg]);
    } else {
      Keys.reveal_IsStrictlySorted();
      forall k | k in result.I().mapp.Keys
        ensures k in node.I().mapp.Keys + {key}
      {
        var kpos := IndexOf(result.keys, k);
        if llte + 1 < kpos {
          assert k == node.keys[kpos-1];
        }
      }
      // forall k | k in result.AllKeys()
      //   ensures k in node.AllKeys() + {key}
      // {
      //   var i :| 0 <= i < |result.keys| && result.keys[i] == k;
      //   if i < llte+1 {
      //   } else if i == llte+1 {
      //   } else {
      //     assert k == node.keys[i-1];
      //   }
      // }
    }
  }

  lemma SplitLeafPreservesWF(node: Node, leftleaf: Node, rightleaf: Node, pivot: Key)
    requires node.WF()
    requires node.SplitLeaf(leftleaf, rightleaf, pivot)
    ensures leftleaf.WF()
    ensures rightleaf.WF()
  {
    Keys.StrictlySortedSubsequence(node.keys, 0, |leftleaf.keys|);
    Keys.StrictlySortedSubsequence(node.keys, |leftleaf.keys|, |node.keys|);
    assert Keys.IsStrictlySorted(node.keys[|leftleaf.keys|..|node.keys|]);
    assert rightleaf.keys == node.keys[|leftleaf.keys|..|node.keys|];
  }

  lemma SubIndexPreservesWF(node: Node, from: int, to: int)
    requires node.WF()
    requires node.Index?
    requires 0 <= from < to <= |node.children|
    ensures node.SubIndex(from, to).WF()
  {
    Keys.StrictlySortedSubsequence(node.pivots, from, to-1);
    var subindex := node.SubIndex(from, to);
    forall i | 0 <= i < to - from - 1
      ensures subindex.AllKeysBelowBound(i)
    {
      assert node.AllKeysBelowBound(from + i);
    }
    forall i | 0 < i < to - from
      ensures subindex.AllKeysAboveBound(i)
    {
      assert node.AllKeysAboveBound(from + i);
    }
    assert |subindex.pivots| == |subindex.children| - 1;
    assert subindex.WF();
  }

  lemma SplitIndexPreservesWF(node: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires node.WF()
    requires node.SplitIndex(leftindex, rightindex, pivot)
    ensures leftindex.WF()
    ensures rightindex.WF()
  {
    SubIndexPreservesWF(node, 0, |leftindex.children|);
    SubIndexPreservesWF(node, |leftindex.children|, |node.children|);
  }

  lemma SplitNodePreservesWF(node: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires node.SplitNode(leftnode, rightnode, pivot)
    requires node.WF()
    ensures leftnode.WF()
    ensures rightnode.WF()
  {
    if node.SplitLeaf(leftnode, rightnode, pivot) {
      SplitLeafPreservesWF(node, leftnode, rightnode, pivot);
    } else {
      SplitIndexPreservesWF(node, leftnode, rightnode, pivot);
    }
  }

  lemma {:timeLimitMultiplier 4} SplitLeafInterpretation(oldleaf: Node, leftleaf: Node, rightleaf: Node, pivot: Key)
    requires oldleaf.SplitLeaf(leftleaf, rightleaf, pivot)
    requires oldleaf.WF()
    requires leftleaf.WF()
    requires rightleaf.WF()
    ensures oldleaf.I().mapp == Keys.MapPivotedUnion(leftleaf.I().mapp, pivot, rightleaf.I().mapp)
  {
    var oldint := oldleaf.I().mapp;
    var leftint := leftleaf.I().mapp;
    var rightint := rightleaf.I().mapp;
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    forall key | key in oldint
      ensures key in newint && newint[key] == oldint[key]
    {
      var llte := Keys.LargestLte(oldleaf.keys, key);
      Keys.lteTransitiveForall();

      if llte < |leftleaf.keys| {
        Keys.PosEqLargestLte(leftleaf.keys, key, llte);
        Keys.IsStrictlySortedImpliesLt(oldleaf.keys, llte, |leftleaf.keys|);
        assert Keys.lt(oldleaf.keys[llte], pivot);
      } else {
        var rightllte := llte - |leftleaf.keys|;
        Keys.PosEqLargestLte(rightleaf.keys, key, rightllte);
        if |leftleaf.keys| < llte {
          Keys.IsStrictlySortedImpliesLt(oldleaf.keys, |leftleaf.keys|, llte);
        }
      }
    }

    forall key | key in newint
      ensures key in oldint && oldint[key] == newint[key]
    {
      if Keys.lt(key, pivot) {
        var llte := Keys.LargestLte(leftleaf.keys, key);
        Keys.PosEqLargestLte(oldleaf.keys, key, llte);
      } else {
        var llte := Keys.LargestLte(rightleaf.keys, key);
        Keys.PosEqLargestLte(oldleaf.keys, key, |leftleaf.keys| + llte);
      }
    }
  }

  lemma SplitIndexInterpretation1(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires oldindex.WF()
    requires leftindex.WF()
    requires rightindex.WF()
    requires oldindex.SplitIndex(leftindex, rightindex, pivot)
    ensures forall key :: key in oldindex.I().mapp ==>
      MapsTo(Keys.MapPivotedUnion(leftindex.I().mapp, pivot, rightindex.I().mapp), 
        key, oldindex.I().mapp[key])
  {
    var oldint := oldindex.I().mapp;
    var leftint := leftindex.I().mapp;
    var rightint := rightindex.I().mapp;
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    forall key | key in oldint
      ensures MapsTo(newint, key, oldint[key])
    {
      var llte := Keys.LargestLte(oldindex.pivots, key);

      if Keys.lt(key, pivot) { 
        Keys.LargestLteSubsequence(oldindex.pivots, key, 0, |leftindex.pivots|);
        assert leftindex.children[llte+1] == oldindex.children[llte+1];
        InterpretationDelegation(leftindex, key);
      } else {
        Keys.LargestLteSubsequence(oldindex.pivots, key, |leftindex.pivots|+1, |oldindex.pivots|);
        assert rightindex.children[llte - |leftindex.children| + 1] == oldindex.children[llte + 1];
        InterpretationDelegation(rightindex, key);
      }
    }
  }
  
  lemma SplitIndexInterpretation2(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires oldindex.WF()
    requires leftindex.WF()
    requires rightindex.WF()
    requires oldindex.SplitIndex(leftindex, rightindex, pivot)
    ensures oldindex.I().mapp.Keys >=
            Keys.MapPivotedUnion(leftindex.I().mapp, pivot, rightindex.I().mapp).Keys
  {
    var oldint := oldindex.I().mapp;
    var leftint := leftindex.I().mapp;
    var rightint := rightindex.I().mapp;
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    forall key | key in newint
      ensures key in oldint
    {
      if Keys.lt(key, pivot) {
        Keys.LargestLteSubsequence(oldindex.pivots, key, 0, |leftindex.pivots|);
      } else {
        Keys.LargestLteSubsequence(oldindex.pivots, key, |leftindex.pivots|+1, |oldindex.pivots|);
      }
      InterpretationDelegation(oldindex, key);
    }
  }

  lemma SplitIndexInterpretation(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires oldindex.WF()
    requires leftindex.WF()
    requires rightindex.WF()
    requires oldindex.SplitIndex(leftindex, rightindex, pivot)
    ensures oldindex.I().mapp ==
            Keys.MapPivotedUnion(leftindex.I().mapp, pivot, rightindex.I().mapp)
  {
    SplitIndexInterpretation1(oldindex, leftindex, rightindex, pivot);
    SplitIndexInterpretation2(oldindex, leftindex, rightindex, pivot);
  }

  lemma SplitNodeInterpretation(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires oldnode.WF()
    requires leftnode.WF()
    requires rightnode.WF()
    requires oldnode.SplitNode(leftnode, rightnode, pivot)
    ensures oldnode.I().mapp == Keys.MapPivotedUnion(leftnode.I().mapp, pivot, rightnode.I().mapp) 
  {
    if oldnode.SplitLeaf(leftnode, rightnode, pivot) {
      SplitLeafInterpretation(oldnode, leftnode, rightnode, pivot);
    } else {
      SplitIndexInterpretation(oldnode, leftnode, rightnode, pivot);
    }
  }

   lemma SplitLeafAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires oldnode.WF()
    requires leftnode.WF()
    requires rightnode.WF()
    requires oldnode.SplitLeaf(leftnode, rightnode, pivot)
    ensures oldnode.AllKeys() == leftnode.AllKeys() + rightnode.AllKeys()
    ensures forall key :: key in leftnode.AllKeys() <==> (Keys.lt(key, pivot) && key in oldnode.AllKeys())
    ensures forall key :: key in rightnode.AllKeys() <==> (Keys.lte(pivot, key) && key in oldnode.AllKeys())
  {
    Keys.transitivity_forall();

    forall key | key in leftnode.AllKeys()
      ensures Keys.lt(key, pivot)
    {
      var i :| 0 <= i < |leftnode.keys| && key == leftnode.keys[i];
      Keys.IsStrictlySortedImpliesLte(oldnode.keys, i, |leftnode.keys|-1);
    }
    forall key | key in rightnode.AllKeys()
      ensures Keys.lte(pivot, key)
    {
      var i :| 0 <= i < |rightnode.keys| && key == rightnode.keys[i];
      Keys.IsSortedImpliesLte(oldnode.keys, |leftnode.keys|, |leftnode.keys| + i);
    }
  }

  lemma SplitIndexAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires oldnode.WF()
    requires leftnode.WF()
    requires rightnode.WF()
    requires oldnode.SplitIndex(leftnode, rightnode, pivot)
    ensures oldnode.AllKeys() == leftnode.AllKeys() + rightnode.AllKeys() + {pivot}
    ensures forall key :: key in leftnode.AllKeys() <==> (Keys.lt(key, pivot) && key in oldnode.AllKeys())
    ensures forall key :: key in (rightnode.AllKeys() + {pivot}) <==> (Keys.lte(pivot, key) && key in oldnode.AllKeys())
  {
    Keys.transitivity_forall();

    forall key | key in leftnode.AllKeys()
      ensures Keys.lt(key, pivot)
    {
      if i :| 0 <= i < |leftnode.pivots| && key == leftnode.pivots[i] {
        Keys.IsStrictlySortedImpliesLt(oldnode.pivots, i, |leftnode.pivots|);
      } else {
        var i :| 0 <= i < |leftnode.children| && key in leftnode.children[i].AllKeys();
        assert oldnode.AllKeysBelowBound(i);
        if i < |leftnode.pivots| {
          Keys.IsStrictlySortedImpliesLt(oldnode.pivots, i, |leftnode.pivots|);
        }
      }
    }

    forall key | key in rightnode.AllKeys()
      ensures Keys.lte(pivot, key)
    {
      if i :| 0 <= i < |rightnode.pivots| && key == rightnode.pivots[i] {
        Keys.IsSortedImpliesLte(oldnode.pivots, |leftnode.pivots|, |leftnode.children| + i);
      } else {
        var i :| 0 <= i < |rightnode.children| && key in rightnode.children[i].AllKeys();
        assert oldnode.AllKeysAboveBound(|leftnode.children| + i);
        Keys.IsSortedImpliesLte(oldnode.pivots, |leftnode.pivots|, |leftnode.children| + i - 1);
      }
    }
    assert Last(rightnode.children) == Last(oldnode.children);
  }

  lemma SplitNodeAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires oldnode.WF()
    requires leftnode.WF()
    requires rightnode.WF()
    requires oldnode.SplitNode(leftnode, rightnode, pivot)
    ensures oldnode.AllKeys() <= leftnode.AllKeys() + rightnode.AllKeys() + {pivot}
    ensures leftnode.AllKeys() + rightnode.AllKeys() <= oldnode.AllKeys()
    ensures forall key :: key in leftnode.AllKeys() <==> (Keys.lt(key, pivot) && key in oldnode.AllKeys())
    ensures forall key :: key in (rightnode.AllKeys()) ==> (Keys.lte(pivot, key) && key in oldnode.AllKeys())
    ensures forall key :: key in (rightnode.AllKeys() + {pivot}) <== (Keys.lte(pivot, key) && key in oldnode.AllKeys())
  {
    if oldnode.SplitLeaf(leftnode, rightnode, pivot) {
      SplitLeafAllKeys(oldnode, leftnode, rightnode, pivot);
    } else {
      SplitIndexAllKeys(oldnode, leftnode, rightnode, pivot);
    }
  }

}
