include "MutableBtree.i.dfy"

abstract module MutableBtreeBulkOperations {
  import opened NativeTypes
  import opened Sequences
  import opened MB : MutableBtree`All

  method NumElements(node: Node) returns (count: uint64)
    requires WFShape(node)
    requires Spec.WF(I(node))
    requires Spec.NumElements(I(node)) < Uint64UpperBound()
    ensures count as nat == Spec.NumElements(I(node))
    decreases node.height
  {
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
    ensures forall i :: 0 <= i < start ==> keys[i] == old(keys[i]);
    ensures forall i :: 0 <= i < start ==> values[i] == old(values[i]);
    ensures keys[start..nextstart] == Spec.ToSeq(I(node)).0
    ensures values[start..nextstart] == Spec.ToSeq(I(node)).1
    ensures forall i :: nextstart as nat <= i < keys.Length ==> keys[i] == old(keys[i]);
    ensures forall i :: nextstart as nat <= i < values.Length ==> values[i] == old(values[i]);
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
      ghost var inextstart := start as nat;
      var i: uint64 := 0;
      Spec.NumElementsOfChildrenNotZero(I(node));
      while i < node.contents.nchildren
        invariant I(node) == old(I(node))
        invariant 0 <= i <= node.contents.nchildren
        invariant inextstart == start as nat + Spec.NumElementsOfChildren(I(node).children[..i])
        invariant inextstart <= keys.Length
        invariant i < node.contents.nchildren ==> inextstart < keys.Length
        invariant nextstart as nat == inextstart
        invariant forall i :: 0 <= i < start ==> keys[i] == old(keys[i])
        invariant forall i :: 0 <= i < start ==> values[i] == old(values[i])
        invariant keys[start..nextstart] == Spec.Seq.Flatten(Spec.ToSeqChildren(I(node).children[..i]).0)
        invariant values[start..inextstart] == Spec.Seq.Flatten(Spec.ToSeqChildren(I(node).children[..i]).1)
        invariant forall i :: inextstart <= i < keys.Length ==> keys[i] == old(keys[i])
        invariant forall i :: inextstart <= i < values.Length ==> values[i] == old(values[i])
      {
        assert I(node).children[..i+1][..i] == I(node).children[..i];
        ghost var oldinextstart := inextstart;
        inextstart := inextstart + Spec.NumElements(I(node).children[i]);
        Spec.NumElementsOfChildrenNotZero(I(node));
        Spec.NumElementsOfChildrenDecreases(I(node).children, (i + 1) as int);

        IOfChild(node, i as int);
        nextstart := ToSeqSubtree(node.contents.children[i], keys, values, nextstart);
        i := i + 1;

        Spec.ToSeqChildrenDecomposition(I(node).children[..i]);
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
    var keys := new Key[count](_ => DefaultKey());
    var values := new Value[count](_ => DefaultValue());
    var end := ToSeqSubtree(node, keys, values, 0);
    assert keys[..] == keys[0..end];
    assert values[..] == values[0..end];
    return (keys, values);
  }

  method SplitLeafOfIndexAtKey(node: Node, childidx: uint64, pivot: Key, nleft: uint64)  returns (ghost wit: Key)
    requires WFShape(node)
    requires Spec.WF(I(node))
    requires node.contents.Index?
    requires !Full(node)
    requires 0 <= childidx < node.contents.nchildren
    requires node.contents.children[childidx].contents.Leaf?
    requires WFShape(node.contents.children[childidx])
    requires Spec.Keys.lt(node.contents.children[childidx].contents.keys[0], pivot)
    requires Spec.Keys.lte(pivot, node.contents.children[childidx].contents.keys[node.contents.children[childidx].contents.nkeys-1])
    requires Spec.Keys.IsSorted(node.contents.children[childidx].contents.keys[..node.contents.children[childidx].contents.nkeys])
    requires nleft as int == Spec.Keys.LargestLt(node.contents.children[childidx].contents.keys[..node.contents.children[childidx].contents.nkeys], pivot) + 1
    ensures WFShape(node)
    ensures node.contents.Index?
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures Spec.SplitChildOfIndex(old(I(node)), I(node), childidx as int, wit)
    ensures !Full(node.contents.children[childidx])
    ensures !Full(node.contents.children[childidx+1])
    ensures node.contents.pivots[childidx] == pivot
    modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  {
    ChildrenAreDistinct(node);
    
    ghost var ioldnode := I(node);
    var child := node.contents.children[childidx];
    //assert 0 < nleft;
    var right, wit' := SplitLeaf(node.contents.children[childidx], nleft, pivot);
    ghost var ileft := I(node.contents.children[childidx]);
    ghost var iright := I(right);

    Arrays.Insert(node.contents.pivots, node.contents.nchildren-1, pivot, childidx);
    Arrays.Insert(node.contents.children, node.contents.nchildren, right, childidx + 1);
    node.contents := node.contents.(nchildren := node.contents.nchildren + 1);
    node.repr := node.repr + right.repr;
    wit := wit';

    forall i | 0 <= i < node.contents.nchildren
      ensures node.contents.children[i] != null
      ensures node.contents.children[i] in node.repr
      ensures node.contents.children[i].repr < node.repr
      ensures node !in node.contents.children[i].repr
      ensures node.contents.pivots !in node.contents.children[i].repr
      ensures node.contents.children !in node.contents.children[i].repr
      ensures node.contents.children[i].height < node.height
      ensures WFShape(node.contents.children[i])
    {
      if i < childidx {
        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
      } else if i == childidx {
      } else if i == childidx + 1 {
      } else {
        assert node.contents.children[i] == old(node.contents.children[i-1]);
        assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));
      }
    }

    forall i: uint64, j: uint64 | 0 <= i < j < node.contents.nchildren
      ensures DisjointSubtrees(node.contents, i as int, j as int)
    {
      if                           j <  childidx       {
        assert old(DisjointSubtrees(node.contents, i as int, j as int));
      } else if                    j == childidx       {
        assert old(DisjointSubtrees(node.contents, i as int, j as int));
      } else if i < childidx     && j == childidx+1     {
        assert old(DisjointSubtrees(node.contents, i as int, j as int - 1));
      } else if i == childidx    && j == childidx+1     {
        assert node.contents.children[childidx+1] == right;
        //assert node.contents.children[childidx].repr !! right.repr;
        assert DisjointSubtrees(node.contents, childidx as int, (childidx + 1) as int);
      } else if i < childidx     &&      childidx+1 < j {
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, i as int, (j-1) as int));
      } else if i == childidx    &&      childidx+1 < j {
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, i as int, (j-1) as int));
      } else if i == childidx+1  &&      childidx+1 < j {
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, (i-1) as int, (j-1) as int));
      } else {
        assert node.contents.children[i] == old(node.contents.children[i-1]);
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, (i-1) as int, (j-1) as int));
      }
    }
      
    ghost var inode := I(node);

    ghost var target := Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
    forall i | 0 <= i < |inode.children|
      ensures inode.children[i] == target[i]
    {
      if i < childidx as int {
        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
        assert inode.children[i] == ioldnode.children[i] == target[i];
      } else if i == childidx as int {
        assert inode.children[i] == ileft == target[i];
      } else if i == (childidx + 1) as int {
        assert inode.children[i] == iright == target[i];
      } else {
        assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));      
        assert inode.children[i] == ioldnode.children[i-1] == target[i];
      }
    }
    assert inode.children == Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
  }


  method EnsurePivotNotFullParentOfLeaf(node: Node, pivot: Key, childidx: uint64) returns (pos: int64)
    requires WFShape(node)
    requires Spec.WF(I(node))
    requires Spec.NumElements(I(node)) < Uint64UpperBound()
    requires node.contents.Index?
    requires !Full(node)
    requires childidx as int == Spec.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], pivot) + 1
    requires node.contents.children[childidx].contents.Leaf?
    ensures WFShape(node)
    ensures Spec.WF(I(node))
    ensures node.contents.Index?
    ensures node.height == old(node.height)
    ensures fresh(node.repr - old(node.repr))
    ensures -1 <= pos as int < node.contents.nchildren as int
    ensures 0 <= pos as int < node.contents.nchildren as int - 1 ==> node.contents.pivots[pos] == pivot
    ensures Spec.Interpretation(I(node)) == Spec.Interpretation(old(I(node)))
    ensures Spec.AllKeys(I(node)) <= Spec.AllKeys(old(I(node))) + {pivot}
    modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  {
    var child := node.contents.children[childidx];
    assert child.contents.keys[0..child.contents.nkeys] == child.contents.keys[..child.contents.nkeys];
    var nleft := Spec.Keys.ArrayLargestLtPlus1(child.contents.keys, 0, child.contents.nkeys, pivot);

    if 0 == nleft {
      if 0 < childidx {
        node.contents.pivots[childidx-1] := pivot;
        assert I(node) == Spec.ReplacePivot(old(I(node)), childidx as int - 1, pivot);
        Spec.IncreasePivotIsCorrect(old(I(node)), childidx as int - 1, pivot);
        pos := childidx as int64 - 1;
      } else {
        pos := -1;
      }
    } else if nleft == child.contents.nkeys {
      if childidx < node.contents.nchildren-1 {
        node.contents.pivots[childidx] := pivot;
        assert I(node) == Spec.ReplacePivot(old(I(node)), childidx as int, pivot);
        Spec.DecreasePivotIsCorrect(old(I(node)), childidx as int, pivot);
        pos := childidx as int64;
      } else {
        pos := node.contents.nchildren as int64 - 1;
      }
    } else {
      ghost var wit := SplitLeafOfIndexAtKey(node, childidx, pivot, nleft);
      pos := childidx as int64;
      Spec.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int, wit);
      Spec.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int, wit);
      Spec.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int, wit);
    }
  }

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
