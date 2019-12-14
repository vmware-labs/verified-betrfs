include "MutableBtree.i.dfy"

abstract module MutableBtreeBulkOperations {
  import opened NativeTypes
  import opened NativeArrays
  import opened Sequences
  import opened MB : MutableBtree`All

  method NumElements(node: Node) returns (count: uint64)
    requires WFShape(node)
    requires Spec.WF(I(node))
    requires Spec.NumElements(I(node)) < Uint64UpperBound()
    ensures count as nat == Spec.NumElements(I(node))
    decreases node.height
  {
    reveal_I();
    if node.contents.Leaf? {
      count := node.contents.nkeys;
    } else {
      ghost var inode := I(node);
      count := 0;
      ghost var icount: int := 0;
      
      var i: uint64 := 0;
      while i < node.contents.nchildren
        invariant i <= node.contents.nchildren
        invariant icount == Spec.NumElementsOfChildren(inode.children[..i])
        invariant icount < Uint64UpperBound()
        invariant count == icount as uint64
      {
        ghost var ichildcount := Spec.NumElements(inode.children[i]);
        assert inode.children[..i+1][..i] == inode.children[..i];
        Spec.NumElementsOfChildrenNotZero(inode);
        Spec.NumElementsOfChildrenDecreases(inode.children, (i+1) as int);
        icount := icount + ichildcount;
        
        var childcount: uint64 := NumElements(node.contents.children[i]);
        count := count + childcount;
        i := i + 1;
      }
      assert inode.children[..node.contents.nchildren] == inode.children;
    }
  }

  method ToSeqSubtree(node: Node, keys: array<Key>, values: array<Value>, start: uint64) returns (nextstart: uint64)
    requires WF(node)
    requires !Arrays.Aliases(keys, values)
    requires keys.Length == values.Length
    requires keys !in node.repr
    requires values !in node.repr
    requires start as nat + Spec.NumElements(I(node)) <= keys.Length
    requires start as nat + Spec.NumElements(I(node)) < Uint64UpperBound()
    ensures nextstart as nat == start as nat + Spec.NumElements(I(node))
    ensures keys[..start] == old(keys[..start])
    ensures keys[start..nextstart] == Spec.ToSeq(I(node)).0
    ensures keys[nextstart..] == old(keys[nextstart..]);
    ensures values[..start] == old(values[..start]);
    ensures values[start..nextstart] == Spec.ToSeq(I(node)).1
    ensures values[nextstart..] == old(values[nextstart..])
    modifies keys, values
    decreases node.height
  {
    if node.contents.Leaf? {
      Arrays.Memcpy(keys, start, node.contents.keys[..node.contents.nkeys]); // FIXME: remove conversion to seq
      Arrays.Memcpy(values, start, node.contents.values[..node.contents.nkeys]); // FIXME: remove conversion to seq
      nextstart := start + node.contents.nkeys;
      forall
        ensures keys[start..nextstart] == Spec.ToSeq(I(node)).0
        ensures values[start..nextstart] == Spec.ToSeq(I(node)).1
      {
        reveal_I();
      }
    } else {
      nextstart := start;
      var i: uint64 := 0;
      while i < node.contents.nchildren
        invariant 0 <= i <= node.contents.nchildren
        invariant nextstart as nat == start as nat + Spec.NumElementsOfChildren(I(node).children[..i])
        invariant nextstart as nat <= keys.Length
        invariant keys[..start] == old(keys[..start])
        invariant keys[start..nextstart] == Spec.Seq.Flatten(Spec.ToSeqChildren(I(node).children[..i]).0)
        invariant keys[nextstart..] == old(keys[nextstart..]);
        invariant values[..start] == old(values[..start]);
        invariant values[start..nextstart] == Spec.Seq.Flatten(Spec.ToSeqChildren(I(node).children[..i]).1)
        invariant values[nextstart..] == old(values[nextstart..])
      {
        assert I(node).children[..i+1][..i] == I(node).children[..i];
        Spec.NumElementsOfChildrenDecreases(I(node).children, (i + 1) as int);
        Spec.ToSeqChildrenDecomposition(I(node).children[..i+1]);
        IOfChild(node, i as int);

        nextstart := ToSeqSubtree(node.contents.children[i], keys, values, nextstart);
        i := i + 1;
      }
      assert I(node).children[..node.contents.nchildren] == I(node).children;
    }
  }

  method ToSeq(node: Node) returns (kvlists: (array<Key>, array<Value>))
    requires WFShape(node)
    requires Spec.WF(I(node))
    requires Spec.NumElements(I(node)) < Uint64UpperBound()
    ensures (kvlists.0[..], kvlists.1[..]) == Spec.ToSeq(I(node))
    ensures fresh(kvlists.0)
    ensures fresh(kvlists.1)
  {
    var count := NumElements(node);
    var keys := newArrayFill(count, DefaultKey());
    var values := newArrayFill(count, DefaultValue());
    var end := ToSeqSubtree(node, keys, values, 0);
    assert keys[..] == keys[0..end];
    assert values[..] == values[0..end];
    return (keys, values);
  }

  method IndexFromChildren(children: seq<Node>, pivots: seq<Key>) returns (node: Node)
    requires 0 < |children| <= MB.MaxChildren() as int
    requires |pivots| == |children|-1
    requires forall i :: 0 <= i < |children| ==> WF(children[i])
    requires forall i :: 0 <= i < |pivots| ==> forall k :: k in Spec.AllKeys(I(children[i])) ==> Spec.Keys.lt(k, pivots[i])
    requires forall i :: 1 <= i < |children| ==> forall k :: k in Spec.AllKeys(I(children[i])) ==> Spec.Keys.lte(pivots[i-1], k)
    

  method FromSeqLeaves(keys: seq<Key>, values: seq<Value>) returns (pivots: array<Key>, leaves: array<Node?>, ghost ileaves: seq<Spec.Node>)
    requires Spec.Keys.IsStrictlySorted(keys)
    requires 0 < |keys| == |values| < Uint64UpperBound() / 2
    ensures fresh(pivots)
    ensures fresh(leaves)
    ensures forall i :: 0 <= i < leaves.Length ==> leaves[i] != null
    ensures forall i :: 0 <= i < leaves.Length ==> MB.WF(leaves[i])
    ensures forall i :: 0 <= i < leaves.Length ==> leaves[i].contents.Leaf?
    ensures forall i :: 0 <= i < leaves.Length ==> fresh(leaves[i].repr)
    ensures forall i :: 0 <= i < leaves.Length ==> leaves !in leaves[i].repr
    ensures forall i :: 0 <= i < leaves.Length ==> pivots !in leaves[i].repr
    ensures forall i, j :: 0 <= i < j < leaves.Length ==> leaves[i].repr !! leaves[j].repr
    ensures |ileaves| == leaves.Length
    ensures forall i :: 0 <= i < |ileaves| ==> ileaves[i] == I(leaves[i])
    ensures Spec.WF(Spec.Index(pivots[..], ileaves))
    ensures Spec.ToSeq(Spec.Index(pivots[..], ileaves)) == (keys, values)
  {
    var keysperleaf: uint64 := 3 * MB.MaxKeysPerLeaf() / 4;
    var numleaves: uint64 := (|keys| as uint64 + keysperleaf - 1) / keysperleaf;
    assert (numleaves as int - 1) * keysperleaf as int < |keys| <= (numleaves * keysperleaf) as int;

    pivots := newArrayFill(numleaves-1, MB.DefaultKey());
    leaves := newArrayFill(numleaves, null);
    ileaves := [];

    forall i: int | i < numleaves as int - 1
      ensures i * keysperleaf as int + keysperleaf as int < |keys|
    {
      calc <= {
        i                      * keysperleaf as int + keysperleaf as int;
        (numleaves as int - 2) * keysperleaf as int + keysperleaf as int;
        |keys|;
      }
    }
    
    var leafidx: uint64 := 0;
    var keyidx: uint64 := 0;
    while leafidx < numleaves-1
      invariant leafidx <= numleaves-1
      invariant keyidx == leafidx * keysperleaf
      invariant fresh(leaves)
      invariant fresh(pivots)
      invariant !Arrays.Aliases(pivots, leaves)
      invariant forall i :: 0 <= i < leafidx ==> leaves[i] != null
      invariant forall i :: leafidx <= i < numleaves ==> leaves[i] == null
      invariant forall i :: 0 <= i < leafidx ==> MB.WF(leaves[i])
      invariant forall i :: 0 <= i < leafidx ==> leaves[i].contents.Leaf?
      invariant forall i :: 0 <= i < leafidx ==> fresh(leaves[i].repr)
      invariant forall i :: 0 <= i < leafidx ==> leaves !in leaves[i].repr
      invariant forall i :: 0 <= i < leafidx ==> pivots !in leaves[i].repr
      invariant forall i, j :: 0 <= i < j < leafidx ==> leaves[i].repr !! leaves[j].repr
      invariant |ileaves| == leafidx as int
      invariant forall i :: 0 <= i < leafidx ==> ileaves[i] == I(leaves[i])
      invariant forall i :: 0 <= i < leafidx ==> ileaves[i].keys == keys[i * keysperleaf..i * keysperleaf + keysperleaf]
      invariant forall i :: 0 <= i < leafidx ==> ileaves[i].values == values[i * keysperleaf..i * keysperleaf + keysperleaf]
      invariant forall i :: 0 <= i < leafidx as int - 1 ==> pivots[i] == keys[(i+1) * keysperleaf as int]
    {
      var nextkeyidx := keyidx + keysperleaf;
      Spec.Keys.StrictlySortedSubsequence(keys, keyidx as int, nextkeyidx as int);
      leaves[leafidx] := LeafFromSeqs(keys[keyidx..nextkeyidx], values[keyidx..nextkeyidx]);
      ileaves := ileaves + [I(leaves[leafidx])];

      if 0 < leafidx {
        pivots[leafidx-1] := keys[keyidx];
      }
      
      leafidx := leafidx + 1;
      keyidx := nextkeyidx;
    }
    Spec.Keys.StrictlySortedSubsequence(keys, keyidx as int, |keys|);
    calc <= {
      |keys| - keyidx as int;
      |keys| - (numleaves-1) as int * keysperleaf as int;
      |keys| - numleaves as int * keysperleaf as int + keysperleaf as int;
      |keys| - |keys| + keysperleaf as int;
      keysperleaf as int;
    }
    leaves[leafidx] := LeafFromSeqs(keys[keyidx..|keys|], values[keyidx..|keys|]);
    if 0 < leafidx {
      pivots[leafidx-1] := keys[keyidx];
    }
    ileaves := ileaves + [I(leaves[leafidx])];

    ghost var boundaries := seq(numleaves, i => i * keysperleaf as int) + [|keys|];
    Spec.RegularBoundaryIsValid(|keys|, keysperleaf as int);
    Spec.ToSeqChildrenOfChildrenFromSeq(keys, values, boundaries, ileaves);

    assert forall i :: 0 <= i < pivots.Length ==> pivots[i] == keys[boundaries[i+1]];
    forall i | 0 <= i < |ileaves|
      ensures Spec.AllKeys(ileaves[i]) <= Set(keys[boundaries[i]..boundaries[i+1]])
    {
    }
    Spec.FromSeqWF(keys, boundaries, pivots[..], ileaves);

    assert Spec.ToSeq(Spec.Index(pivots[..], ileaves)) == (keys, values);
  }
  
  // method SplitLeafOfIndexAtKey(node: Node, childidx: uint64, pivot: Key, nleft: uint64)  returns (ghost wit: Key)
  //   requires WFShape(node)
  //   requires Spec.WF(I(node))
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   requires 0 <= childidx < node.contents.nchildren
  //   requires node.contents.children[childidx].contents.Leaf?
  //   requires WFShape(node.contents.children[childidx])
  //   requires Spec.Keys.lt(node.contents.children[childidx].contents.keys[0], pivot)
  //   requires Spec.Keys.lte(pivot, node.contents.children[childidx].contents.keys[node.contents.children[childidx].contents.nkeys-1])
  //   requires Spec.Keys.IsSorted(node.contents.children[childidx].contents.keys[..node.contents.children[childidx].contents.nkeys])
  //   requires nleft as int == Spec.Keys.LargestLt(node.contents.children[childidx].contents.keys[..node.contents.children[childidx].contents.nkeys], pivot) + 1
  //   ensures WFShape(node)
  //   ensures node.contents.Index?
  //   ensures fresh(node.repr - old(node.repr))
  //   ensures node.height == old(node.height)
  //   ensures Spec.SplitChildOfIndex(old(I(node)), I(node), childidx as int, wit)
  //   ensures !Full(node.contents.children[childidx])
  //   ensures !Full(node.contents.children[childidx+1])
  //   ensures node.contents.pivots[childidx] == pivot
  //   modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  // {
  //   ChildrenAreDistinct(node);
    
  //   ghost var ioldnode := I(node);
  //   var child := node.contents.children[childidx];
  //   //assert 0 < nleft;
  //   var right, wit' := SplitLeaf(node.contents.children[childidx], nleft, pivot);
  //   ghost var ileft := I(node.contents.children[childidx]);
  //   ghost var iright := I(right);

  //   Arrays.Insert(node.contents.pivots, node.contents.nchildren-1, pivot, childidx);
  //   Arrays.Insert(node.contents.children, node.contents.nchildren, right, childidx + 1);
  //   node.contents := node.contents.(nchildren := node.contents.nchildren + 1);
  //   node.repr := node.repr + right.repr;
  //   wit := wit';

  //   forall i | 0 <= i < node.contents.nchildren
  //     ensures node.contents.children[i] != null
  //     ensures node.contents.children[i] in node.repr
  //     ensures node.contents.children[i].repr < node.repr
  //     ensures node !in node.contents.children[i].repr
  //     ensures node.contents.pivots !in node.contents.children[i].repr
  //     ensures node.contents.children !in node.contents.children[i].repr
  //     ensures node.contents.children[i].height < node.height
  //     ensures WFShape(node.contents.children[i])
  //   {
  //     if i < childidx {
  //       assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
  //     } else if i == childidx {
  //     } else if i == childidx + 1 {
  //     } else {
  //       assert node.contents.children[i] == old(node.contents.children[i-1]);
  //       assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));
  //     }
  //   }

  //   forall i: uint64, j: uint64 | 0 <= i < j < node.contents.nchildren
  //     ensures DisjointSubtrees(node.contents, i as int, j as int)
  //   {
  //     if                           j <  childidx       {
  //       assert old(DisjointSubtrees(node.contents, i as int, j as int));
  //     } else if                    j == childidx       {
  //       assert old(DisjointSubtrees(node.contents, i as int, j as int));
  //     } else if i < childidx     && j == childidx+1     {
  //       assert old(DisjointSubtrees(node.contents, i as int, j as int - 1));
  //     } else if i == childidx    && j == childidx+1     {
  //       assert node.contents.children[childidx+1] == right;
  //       //assert node.contents.children[childidx].repr !! right.repr;
  //       assert DisjointSubtrees(node.contents, childidx as int, (childidx + 1) as int);
  //     } else if i < childidx     &&      childidx+1 < j {
  //       assert node.contents.children[j] == old(node.contents.children[j-1]);
  //       assert old(DisjointSubtrees(node.contents, i as int, (j-1) as int));
  //     } else if i == childidx    &&      childidx+1 < j {
  //       assert node.contents.children[j] == old(node.contents.children[j-1]);
  //       assert old(DisjointSubtrees(node.contents, i as int, (j-1) as int));
  //     } else if i == childidx+1  &&      childidx+1 < j {
  //       assert node.contents.children[j] == old(node.contents.children[j-1]);
  //       assert old(DisjointSubtrees(node.contents, (i-1) as int, (j-1) as int));
  //     } else {
  //       assert node.contents.children[i] == old(node.contents.children[i-1]);
  //       assert node.contents.children[j] == old(node.contents.children[j-1]);
  //       assert old(DisjointSubtrees(node.contents, (i-1) as int, (j-1) as int));
  //     }
  //   }
      
  //   ghost var inode := I(node);

  //   ghost var target := Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
  //   forall i | 0 <= i < |inode.children|
  //     ensures inode.children[i] == target[i]
  //   {
  //     if i < childidx as int {
  //       assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
  //       assert inode.children[i] == ioldnode.children[i] == target[i];
  //     } else if i == childidx as int {
  //       assert inode.children[i] == ileft == target[i];
  //     } else if i == (childidx + 1) as int {
  //       assert inode.children[i] == iright == target[i];
  //     } else {
  //       assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));      
  //       assert inode.children[i] == ioldnode.children[i-1] == target[i];
  //     }
  //   }
  //   assert inode.children == Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
  // }


  // method EnsurePivotNotFullParentOfLeaf(node: Node, pivot: Key, childidx: uint64) returns (pos: int64)
  //   requires WFShape(node)
  //   requires Spec.WF(I(node))
  //   requires Spec.NumElements(I(node)) < Uint64UpperBound()
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   requires childidx as int == Spec.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], pivot) + 1
  //   requires node.contents.children[childidx].contents.Leaf?
  //   ensures WFShape(node)
  //   ensures Spec.WF(I(node))
  //   ensures node.contents.Index?
  //   ensures node.height == old(node.height)
  //   ensures fresh(node.repr - old(node.repr))
  //   ensures -1 <= pos as int < node.contents.nchildren as int
  //   ensures 0 <= pos as int < node.contents.nchildren as int - 1 ==> node.contents.pivots[pos] == pivot
  //   ensures Spec.Interpretation(I(node)) == Spec.Interpretation(old(I(node)))
  //   ensures Spec.AllKeys(I(node)) <= Spec.AllKeys(old(I(node))) + {pivot}
  //   modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  // {
  //   var child := node.contents.children[childidx];
  //   assert child.contents.keys[0..child.contents.nkeys] == child.contents.keys[..child.contents.nkeys];
  //   var nleft := Spec.Keys.ArrayLargestLtPlus1(child.contents.keys, 0, child.contents.nkeys, pivot);

  //   if 0 == nleft {
  //     if 0 < childidx {
  //       node.contents.pivots[childidx-1] := pivot;
  //       assert I(node) == Spec.ReplacePivot(old(I(node)), childidx as int - 1, pivot);
  //       Spec.IncreasePivotIsCorrect(old(I(node)), childidx as int - 1, pivot);
  //       pos := childidx as int64 - 1;
  //     } else {
  //       pos := -1;
  //     }
  //   } else if nleft == child.contents.nkeys {
  //     if childidx < node.contents.nchildren-1 {
  //       node.contents.pivots[childidx] := pivot;
  //       assert I(node) == Spec.ReplacePivot(old(I(node)), childidx as int, pivot);
  //       Spec.DecreasePivotIsCorrect(old(I(node)), childidx as int, pivot);
  //       pos := childidx as int64;
  //     } else {
  //       pos := node.contents.nchildren as int64 - 1;
  //     }
  //   } else {
  //     ghost var wit := SplitLeafOfIndexAtKey(node, childidx, pivot, nleft);
  //     pos := childidx as int64;
  //     Spec.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int, wit);
  //     Spec.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int, wit);
  //     Spec.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int, wit);
  //   }
  // }

  // method EnsurePivotNotFull(node: Node, pivot: Key) returns (pos: int64)
  //   requires WFShape(node)
  //   requires Spec.WF(I(node))
  //   requires Spec.NumElements(I(node)) < Uint64UpperBound()
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   ensures WFShape(node)
  //   ensures Spec.WF(I(node))
  //   ensures -1 <= pos as int < node.contents.nchildren as int
  //   ensures 0 <= pos as int < node.contents.nchildren as int - 1 ==> node.contents.pivots[pos] == pivot
  // {
  //   var childidx := Spec.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, pivot);
  //   if 0 < childidx && node.contents.pivots[childidx-1] == pivot {
  //     pos := childidx as int64 - 1;
  //   } else {
  //     var childpos := EnsurePivot(node.contents.children[pos], pivot);
  //   }
  // }

  // method EnsurePivot(node: Node, pivot: Key) returns (pos: int64)
  //   requires WFShape(node)
  //   requires Spec.WF(I(node))
  //   requires Spec.NumElements(I(node)) < Uint64UpperBound()
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   ensures WFShape(node)
  //   ensures Spec.WF(I(node))
  //   ensures -1 <= pos as int < node.contents.nchildren as int
  //   ensures 0 <= pos as int < node.contents.nchildren as int - 1 ==> node.contents.pivots[pos] == pivot

}
