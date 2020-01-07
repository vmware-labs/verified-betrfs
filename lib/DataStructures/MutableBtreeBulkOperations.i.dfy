include "MutableBtree.i.dfy"
include "../Base/mathematics.i.dfy"
  
abstract module MutableBtreeBulkOperations {
  import opened NativeTypes
  import opened NativeArrays
  import opened Sequences
  import opened MB : MutableBtree`All
  import Mathematics
  import Integer_Order
  import Uint64_Order
  
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

        IOfChild(node, i as int);
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
        Spec.reveal_ToSeq();
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
        assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
        assert I(node).children[..i+1][..i] == I(node).children[..i];
        Spec.NumElementsOfChildrenDecreases(I(node).children, (i + 1) as int);
        Spec.ToSeqChildrenDecomposition(I(node).children[..i+1]);
        IOfChild(node, i as int);

        nextstart := ToSeqSubtree(node.contents.children[i], keys, values, nextstart);
        i := i + 1;
        Spec.reveal_ToSeq();
      }
      assert I(node).children[..node.contents.nchildren] == I(node).children;
      Spec.reveal_ToSeq();
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

  function method DivCeilUint64(x: uint64, d: uint64) : (y: uint64)
    requires 0 < d
    requires x as int + d as int < Uint64UpperBound()
    ensures d as int *(y as int - 1) < x as int <= d as int * y as int
  {
    (x + d - 1) / d
  }

  function NatBoundaries(boundaries: seq<uint64>) : (natboundaries: seq<nat>)
    ensures |natboundaries| == |boundaries|
    ensures forall i :: 0 <= i < |boundaries| ==> natboundaries[i] == boundaries[i] as nat
  {
    if |boundaries| == 0 then []
    else NatBoundaries(DropLast(boundaries)) + [Last(boundaries) as nat]
  }

  predicate ValidBoundariesForSeqInner(len: uint64, boundaries: seq<uint64>)
  {
    Spec.ValidBoundariesForSeq(len as nat, NatBoundaries(boundaries))
  }
  
  lemma ValidBoundariesForSeqProperties(len: uint64, boundaries: seq<uint64>)
    ensures ValidBoundariesForSeqInner(len, boundaries) ==> Uint64_Order.IsStrictlySorted(boundaries)
  {
    if ValidBoundariesForSeqInner(len, boundaries) {
      forall i, j | 0 < i < j < |boundaries|
        ensures boundaries[i] < boundaries[j]
        {
          Integer_Order.IsStrictlySortedImpliesLt(NatBoundaries(boundaries), i, j);
        }
      Uint64_Order.reveal_IsStrictlySorted();
    }
  }

  predicate ValidBoundariesForSeq(len: uint64, boundaries: seq<uint64>)
    ensures ValidBoundariesForSeq(len, boundaries) ==> Uint64_Order.IsStrictlySorted(boundaries)
  {
    ValidBoundariesForSeqProperties(len, boundaries);
    ValidBoundariesForSeqInner(len, boundaries)
  }
  
  predicate BoundariesFit(boundaries: seq<uint64>, groupSize: uint64)
  {
    Spec.BoundariesFit(NatBoundaries(boundaries), groupSize as nat)
  }
  
  // FIXME: This proof is bizarre and fragile.
  method BuildBoundaries(numthings: uint64, groupSize: uint64) returns (boundaries: seq<uint64>)
    requires 0 < numthings
    requires 0 < groupSize
    requires numthings as int + groupSize as int < Uint64UpperBound()
    ensures NatBoundaries(boundaries) == Spec.BuildBoundaries(numthings as nat, groupSize as nat)
  {
    var numgroups: uint64 := (numthings + groupSize - 1) / groupSize;
    var aboundaries := newArrayFill(numgroups + 1, numthings);

    ghost var nnumthings := numthings as nat;
    ghost var ngroupSize := groupSize as nat;
    ghost var targetA: seq<nat> := Apply((i: nat) => i * ngroupSize, Range((nnumthings + ngroupSize - 1) / ngroupSize));
    ghost var target := Spec.BuildBoundaries(nnumthings, ngroupSize);

    assert target == targetA || target == targetA + [nnumthings] by {Spec.reveal_BuildBoundariesInner();}
    assert target ==
      if Last(targetA) == nnumthings then targetA
      else targetA + [nnumthings]
    by { Spec.reveal_BuildBoundariesInner(); }

    var i: uint64 := 0;
    while i < numgroups
      invariant i <= numgroups
      invariant forall j :: 0 <= j < i ==> aboundaries[j] as nat == targetA[j]
      invariant forall j :: i <= j <= numgroups ==> aboundaries[j] == numthings;
    {
      //assert target[i] == i as nat * groupSize as nat;
      aboundaries[i] := i * groupSize;
      i := i + 1;
    }
    
    if aboundaries[numgroups-1] == numthings {
      boundaries := aboundaries[..numgroups];
    } else {
      boundaries := aboundaries[..numgroups+1];
    }
  }

  method ExtractPivotsForBoundaries(pivots: seq<Key>, boundaries: seq<uint64>) returns (subpivots: seq<Key>)
    requires |pivots| + 1 < Uint64UpperBound()
    requires ValidBoundariesForSeq(|pivots| as uint64 + 1, boundaries)
    requires |boundaries| < Uint64UpperBound()
    ensures subpivots == Spec.ExtractPivotsForBoundaries(pivots, NatBoundaries(boundaries))
  {
    ghost var target := Spec.ExtractPivotsForBoundaries(pivots, NatBoundaries(boundaries));
    Spec.reveal_ExtractPivotsForBoundaries();

    var asubpivots := newArrayFill(|boundaries| as uint64 - 2, DefaultKey());

    var i: uint64 := 0;
    while i < asubpivots.Length as uint64
      invariant i <= asubpivots.Length as uint64
      invariant forall j :: 0 <= j < i ==> asubpivots[j] == target[j]
    {
      asubpivots[i] := pivots[boundaries[i+1]-1];
      i := i + 1;
    }

    subpivots := asubpivots[..];
  }

  method BuildLeafForSequence(kvlist: Spec.KVList, boundaries: seq<uint64>, i: uint64) returns (node: Node)
    requires |kvlist.keys| < Uint64UpperBound()
    requires Spec.WFKVList(kvlist)
    requires ValidBoundariesForSeq(|kvlist.keys| as uint64, boundaries)
    requires i as int < |boundaries| - 1
    requires BoundariesFit(boundaries, MB.MaxKeysPerLeaf())
    ensures WFShape(node)
    ensures I(node) == Spec.BuildLeafForSequence(kvlist, NatBoundaries(boundaries), i as nat)
    ensures fresh(node.repr)
  {
    Spec.ValidBoundaryLength(|kvlist.keys|, NatBoundaries(boundaries));
    Uint64_Order.IsStrictlySortedImpliesLte(boundaries, i as int, i as int + 1);
    assert boundaries[i+1] - boundaries[i] <= MB.MaxKeysPerLeaf() by { Spec.reveal_BoundariesFit(); }
    
    var mykeys := kvlist.keys[boundaries[i]..boundaries[i+1]];
    var myvals := kvlist.values[boundaries[i]..boundaries[i+1]];
    node := MB.LeafFromSeqs(mykeys, myvals);

    Spec.reveal_ExtractBoundedSubsequence();
  }

  method BuildLeavesForSequence(kvlist: Spec.KVList, boundaries: seq<uint64>) returns (nodes: seq<Node>)
    requires Spec.WFKVList(kvlist)
    requires |kvlist.keys| < Uint64UpperBound() - 1
    requires ValidBoundariesForSeq(|kvlist.keys| as uint64, boundaries)
    requires BoundariesFit(boundaries, MB.MaxKeysPerLeaf())
    ensures WFShapeSiblings(nodes)
    ensures fresh(SeqRepr(nodes))
    ensures forall i :: 0 <= i < |nodes| ==> nodes[i].height  == 0
    ensures Ichildren(nodes, 1) == Spec.BuildLeavesForSequence(kvlist, NatBoundaries(boundaries))
  {
    Spec.ValidBoundaryLength(|kvlist.keys|, NatBoundaries(boundaries));
    var anodes: array<Node?> := newArrayFill(|boundaries| as uint64 - 1, null);

    var i: uint64 := 0;
    while i < anodes.Length as uint64
      invariant i <= anodes.Length as uint64
    {
      anodes[i] := BuildLeafForSequence(kvlist, boundaries, i);
      i := i + 1;
    }

    nodes := anodes[..];
  }
    
  // method FromSeqLeaves(keys: seq<Key>, values: seq<Value>, boundaries: seq<uint64>) returns (leaves: seq<Node>)
  //   requires 0 < |keys| == |values| < Uint64UpperBound() / 2
  //   requires |boundaries| < Uint64UpperBound()
  //   requires Spec.ValidBoundariesForSeq(|keys|, NatBoundaries(boundaries))
  //   requires BoundariesFit(boundaries, MB.MaxKeysPerLeaf() as nat)
  //   ensures forall i :: 0 <= i < |leaves| ==> fresh(leaves[i].repr)
  //   ensures WFShapeChildren(leaves, MB.SeqRepr(leaves), 1)
  //   ensures forall i :: 0 <= i < |leaves| ==> leaves[i].contents.Leaf?
  //   ensures |boundaries| == |leaves| + 1
  //   ensures forall i :: 0 <= i < |leaves| ==> Spec.LeafMatchesBoundary(keys, values, NatBoundaries(boundaries), I(leaves[i]), i)
  // {
  //   var aleaves: array<Node?> := newArrayFill(|boundaries| as uint64 - 1, null);

  //   ghost var nboundaries := NatBoundaries(boundaries);

  //   var leafidx: uint64 := 0;
  //   while leafidx < |boundaries| as uint64 - 1
  //     invariant leafidx as nat <= |boundaries|-1
  //     invariant fresh(aleaves)
  //     invariant forall i :: 0 <= i < leafidx ==> aleaves[i] != null
  //     invariant forall i :: 0 <= i < leafidx ==> aleaves !in aleaves[i].repr
  //     invariant forall i :: 0 <= i < leafidx ==> fresh(aleaves[i].repr)
  //     invariant forall i :: 0 <= i < leafidx ==> aleaves[i].contents.Leaf?
  //     invariant WFShapeChildren(aleaves[..leafidx], SeqRepr(aleaves[..leafidx]), 1)
  //     invariant forall i :: 0 <= i < leafidx ==> Spec.LeafMatchesBoundary(keys, values, nboundaries, I(aleaves[i]), i as nat)
  //   {
  //     Integer_Order.IsStrictlySortedImpliesLte(NatBoundaries(boundaries), leafidx as int, leafidx as int + 1);
  //     assert BoundaryFits(boundaries, MB.MaxKeysPerLeaf() as nat, leafidx as nat);
      
  //     var tkeys := keys[boundaries[leafidx]..boundaries[leafidx+1]];
  //     var tvalues := values[boundaries[leafidx]..boundaries[leafidx+1]];
  //     aleaves[leafidx] := LeafFromSeqs(tkeys, tvalues);
  //     leafidx := leafidx + 1;
  //   }
  //   leaves := aleaves[..];
  // }

  // method FromSeqPivots(keys: seq<Key>, boundaries: seq<uint64>) returns (pivots: seq<Key>)
  //   requires 1 < |keys|
  //   requires |boundaries| < Uint64UpperBound()
  //   requires Spec.ValidBoundariesForSeq(|keys|, NatBoundaries(boundaries))
  //   ensures |pivots| == |boundaries| - 2
  //   ensures forall i :: 0 <= i < |pivots| ==> pivots[i] == keys[boundaries[i+1]]
  // {
  //   var apivots := newArrayFill(|boundaries| as uint64 - 2, MB.DefaultKey());

  //   forall i | 0 <= i < |boundaries|-1
  //     ensures boundaries[i] as int < |keys|
  //   {
  //     Integer_Order.IsStrictlySortedImpliesLt(NatBoundaries(boundaries), i, |boundaries|-1);
  //   }
    
  //   var pidx: uint64 := 0;
  //   while pidx < apivots.Length as uint64
  //     invariant pidx <= apivots.Length as uint64
  //     invariant forall i :: 0 <= i < pidx ==> apivots[i] == keys[boundaries[i+1]]
  //   {
  //     apivots[pidx] := keys[boundaries[pidx+1]];
  //     pidx := pidx + 1;
  //   }
  //   pivots := apivots[..];
  // }

  // lemma WFShapeChildrenAugment(nodes: seq<Node>, height: nat, node: Node)
  //   requires WFShapeChildren(nodes, SeqRepr(nodes), height)
  //   requires WFShape(node)
  //   requires node.height < height
  //   requires forall i :: 0 <= i < |nodes| ==> node.repr !! nodes[i].repr
  //   ensures WFShapeChildren(nodes + [node], SeqRepr(nodes + [node]), height)
  // {
  //   assume false;
  // }
  
  // method ParentsFromChildren(pivots: seq<Key>, children: seq<Node>, boundaries: seq<uint64>, ghost repr: set<object>, ghost height: nat) returns (parents: seq<Node>)
  //   requires |children| < Uint64UpperBound() / 2
  //   requires WFShapeChildren(children, repr, height)
  //   requires |children| == |pivots| + 1
  //   requires Spec.ValidBoundariesForSeq(|children|, NatBoundaries(boundaries))
  //   requires BoundariesFit(boundaries, MB.MaxChildren() as nat)
  // {
  //   Spec.ValidBoundaryLength(|children|, NatBoundaries(boundaries));
  //   var aparents: array<Node?> := newArrayFill(|boundaries| as uint64 - 1, null);

  //   var pidx: uint64 := 0;
  //   while pidx < aparents.Length as uint64
  //     invariant pidx <= aparents.Length as uint64
  //     invariant fresh(aparents)
  //     invariant forall i :: 0 <= i < pidx ==> aparents[i] != null
  //     invariant forall i :: 0 <= i < pidx ==> aparents[i].contents.Index?
  //     invariant forall i :: 0 <= i < pidx ==> aparents !in aparents[i].repr
  //     invariant forall i :: 0 <= i < pidx ==> fresh(aparents[i].repr - repr)
  //     invariant WFShapeChildren(aparents[..pidx], SeqRepr(aparents[..pidx]), height + 1)
  //     //invariant forall i :: 0 <= i < pidx ==> Spec.LeafMatchesBoundary(keys, values, nboundaries, I(aparents[i]), i as nat)
  //   {
  //     Integer_Order.IsStrictlySortedImpliesLt(NatBoundaries(boundaries), pidx as int, pidx as int + 1);
  //     assert BoundaryFits(boundaries, MB.MaxChildren() as nat, pidx as nat);
      
  //     var tchildren := children[boundaries[pidx]..boundaries[pidx+1]];
  //     var tpivots := pivots[boundaries[pidx]..boundaries[pidx+1]-1];
  //     aparents[pidx] := IndexFromChildren(tpivots, tchildren, height);

  //     MB.SeqReprSubsequence(children, boundaries[pidx] as int, boundaries[pidx+1] as int);
  //     MB.WFShapeChildrenSeqRepr(children, repr, height);

  //     assume forall i :: 0 <= i < pidx ==> aparents[i].repr !! aparents[pidx].repr;
  //     WFShapeChildrenAugment(aparents[..pidx], height + 1, aparents[pidx]);
  //     assert aparents[..pidx+1] == aparents[..pidx] + [aparents[pidx]];
      
  //     pidx := pidx + 1;

  //   }
  //   parents := aparents[..];
  // }

  // method FromSeq(keys: seq<Key>, values: seq<Value>) returns (node: Node)
  //   requires 0 < |keys| == |values| < Uint64UpperBound() / 2
  // {
  //   var nodes: array<Node?>, boundaries, inodes := FromSeqLeaves(keys, values);
  //   while 1 < nodes.Length
  //     invariant nodes.Length < Uint64UpperBound() / 2
  //     invariant forall i :: 0 <= i < nodes.Length ==> nodes[i] != null
  //     invariant nodes.Length == pivots.Length + 1
  //   {
  //     pivots, nodes := FromSeqIndexLayer(pivots[..], nodes[..]);
  //   }
  //   node := nodes[0];
  // }
  
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
