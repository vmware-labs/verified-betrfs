include "MutableBtree.i.dfy"
include "../Base/mathematics.i.dfy"
// TODO(robj): dead code; delete? 

abstract module MutableBtreeBulkOperations {
  import opened NativeTypes
  import opened NativeArrays
  import opened Sequences
  import opened MB : MutableBtree`All
  import Mathematics
  import Integer_Order
  import Uint64_Order

  function NumElements(node: Node) : nat
    reads node, node.repr
    requires WF(node)
  {
    Model.NumElements(I(node))
  }
  
  method CountElements(node: Node) returns (count: uint64)
    requires WFShape(node)
    requires Model.WF(I(node))
    requires NumElements(node) < Uint64UpperBound()
    ensures count as nat == Model.NumElements(I(node))
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
        invariant icount == Model.NumElementsOfChildren(inode.children[..i])
        invariant icount < Uint64UpperBound()
        invariant count == icount as uint64
      {
        ghost var ichildcount := Model.NumElements(inode.children[i]);
        assert inode.children[..i+1][..i] == inode.children[..i];
        Model.NumElementsOfChildrenNotZero(inode);
        Model.NumElementsOfChildrenDecreases(inode.children, (i+1) as int);
        icount := icount + ichildcount;

        IOfChild(node, i as int);
        var childcount: uint64 := CountElements(node.contents.children[i]);
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
    requires start as nat + NumElements(node) <= keys.Length
    requires start as nat + NumElements(node) < Uint64UpperBound()
    ensures nextstart as nat == start as nat + NumElements(node)
    ensures keys[..start] == old(keys[..start])
    ensures keys[start..nextstart] == Model.ToSeq(I(node)).0
    ensures keys[nextstart..] == old(keys[nextstart..]);
    ensures values[..start] == old(values[..start]);
    ensures values[start..nextstart] == Model.ToSeq(I(node)).1
    ensures values[nextstart..] == old(values[nextstart..])
    modifies keys, values
    decreases node.height
  {
    if node.contents.Leaf? {
      CopyArrayIntoDifferentArray(node.contents.keys, 0, keys, start, node.contents.nkeys);
      CopyArrayIntoDifferentArray(node.contents.values, 0, values, start, node.contents.nkeys);
      //CopySeqIntoArray(node.contents.keys[..node.contents.nkeys], 0, keys, start, node.contents.nkeys);
      //CopySeqIntoArray(node.contents.values[..node.contents.nkeys], 0, values, start, node.contents.nkeys);
      nextstart := start + node.contents.nkeys;
      forall
        ensures keys[start..nextstart] == Model.ToSeq(I(node)).0
        ensures values[start..nextstart] == Model.ToSeq(I(node)).1
      {
        reveal_I();
        Model.reveal_ToSeq();
      }
    } else {
      nextstart := start;
      var i: uint64 := 0;
      while i < node.contents.nchildren
        invariant 0 <= i <= node.contents.nchildren
        invariant nextstart as nat == start as nat + Model.NumElementsOfChildren(I(node).children[..i])
        invariant nextstart as nat <= keys.Length
        invariant keys[..start] == old(keys[..start])
        invariant keys[start..nextstart] == Model.Seq.Flatten(Model.ToSeqChildren(I(node).children[..i]).0)
        invariant keys[nextstart..] == old(keys[nextstart..]);
        invariant values[..start] == old(values[..start]);
        invariant values[start..nextstart] == Model.Seq.Flatten(Model.ToSeqChildren(I(node).children[..i]).1)
        invariant values[nextstart..] == old(values[nextstart..])
      {
        assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
        assert I(node).children[..i+1][..i] == I(node).children[..i];
        Model.NumElementsOfChildrenDecreases(I(node).children, (i + 1) as int);
        Model.ToSeqChildrenDecomposition(I(node).children[..i+1]);
        IOfChild(node, i as int);

        nextstart := ToSeqSubtree(node.contents.children[i], keys, values, nextstart);
        i := i + 1;
        Model.reveal_ToSeq();
      }
      assert I(node).children[..node.contents.nchildren] == I(node).children;
      Model.reveal_ToSeq();
    }
  }

  method ToSeq(node: Node) returns (kvlists: (array<Key>, array<Value>))
    requires WF(node)
    requires NumElements(node) < Uint64UpperBound()
    ensures (kvlists.0[..], kvlists.1[..]) == Model.ToSeq(I(node))
    ensures fresh(kvlists.0)
    ensures fresh(kvlists.1)
  {
    var count := CountElements(node);
    var keys := newArrayFill(count, DefaultKey());
    var values := newArrayFill(count, DefaultValue());
    var end := ToSeqSubtree(node, keys, values, 0);
    assert keys[..] == keys[0..end];
    assert values[..] == values[0..end];
    return (keys, values);
  }

  // function method DivCeilUint64(x: uint64, d: uint64) : (y: uint64)
  //   requires 0 < d
  //   requires x as int + d as int < Uint64UpperBound()
  //   ensures d as int *(y as int - 1) < x as int <= d as int * y as int
  // {
  //   (x + d - 1) / d
  // }

  // function NatBoundaries(boundaries: seq<uint64>) : (natboundaries: seq<nat>)
  //   ensures |natboundaries| == |boundaries|
  //   ensures forall i :: 0 <= i < |boundaries| ==> natboundaries[i] == boundaries[i] as nat
  // {
  //   if |boundaries| == 0 then []
  //   else NatBoundaries(DropLast(boundaries)) + [Last(boundaries) as nat]
  // }

  // predicate ValidBoundariesForSeqInner(len: uint64, boundaries: seq<uint64>)
  // {
  //   Model.ValidBoundariesForSeq(len as nat, NatBoundaries(boundaries))
  // }
  
  // lemma ValidBoundariesForSeqProperties(len: uint64, boundaries: seq<uint64>)
  //   ensures ValidBoundariesForSeqInner(len, boundaries) ==> Uint64_Order.IsStrictlySorted(boundaries)
  // {
  //   if ValidBoundariesForSeqInner(len, boundaries) {
  //     forall i, j | 0 < i < j < |boundaries|
  //       ensures boundaries[i] < boundaries[j]
  //       {
  //         Integer_Order.IsStrictlySortedImpliesLt(NatBoundaries(boundaries), i, j);
  //       }
  //     Uint64_Order.reveal_IsStrictlySorted();
  //   }
  // }

  // predicate ValidBoundariesForSeq(len: uint64, boundaries: seq<uint64>)
  //   ensures ValidBoundariesForSeq(len, boundaries) ==> Uint64_Order.IsStrictlySorted(boundaries)
  // {
  //   ValidBoundariesForSeqProperties(len, boundaries);
  //   ValidBoundariesForSeqInner(len, boundaries)
  // }
  
  // predicate BoundariesFit(boundaries: seq<uint64>, groupSize: uint64)
  // {
  //   Model.BoundariesFit(NatBoundaries(boundaries), groupSize as nat)
  // }
  
  // // FIXME: This proof is bizarre and fragile.
  // method BuildBoundaries(numthings: uint64, groupSize: uint64) returns (boundaries: seq<uint64>)
  //   requires 0 < numthings
  //   requires 0 < groupSize
  //   requires numthings as int + groupSize as int < Uint64UpperBound()
  //   ensures NatBoundaries(boundaries) == Model.BuildBoundaries(numthings as nat, groupSize as nat)
  // {
  //   var numgroups: uint64 := (numthings + groupSize - 1) / groupSize;
  //   var aboundaries := newArrayFill(numgroups + 1, numthings);

  //   ghost var nnumthings := numthings as nat;
  //   ghost var ngroupSize := groupSize as nat;
  //   ghost var targetA: seq<nat> := Apply((i: nat) => i * ngroupSize, Range((nnumthings + ngroupSize - 1) / ngroupSize));
  //   ghost var target := Model.BuildBoundaries(nnumthings, ngroupSize);

  //   assert target == targetA || target == targetA + [nnumthings] by {Model.reveal_BuildBoundariesInner();}
  //   assert target ==
  //     if Last(targetA) == nnumthings then targetA
  //     else targetA + [nnumthings]
  //   by { Model.reveal_BuildBoundariesInner(); }

  //   var i: uint64 := 0;
  //   while i < numgroups
  //     invariant i <= numgroups
  //     invariant forall j :: 0 <= j < i ==> aboundaries[j] as nat == targetA[j]
  //     invariant forall j :: i <= j <= numgroups ==> aboundaries[j] == numthings;
  //   {
  //     //assert target[i] == i as nat * groupSize as nat;
  //     aboundaries[i] := i * groupSize;
  //     i := i + 1;
  //   }
    
  //   if aboundaries[numgroups-1] == numthings {
  //     boundaries := aboundaries[..numgroups];
  //   } else {
  //     boundaries := aboundaries[..numgroups+1];
  //   }
  // }

  // method ExtractPivotsForBoundaries(pivots: seq<Key>, boundaries: seq<uint64>) returns (subpivots: seq<Key>)
  //   requires |pivots| + 1 < Uint64UpperBound()
  //   requires ValidBoundariesForSeq(|pivots| as uint64 + 1, boundaries)
  //   requires |boundaries| < Uint64UpperBound()
  //   ensures subpivots == Model.ExtractPivotsForBoundaries(pivots, NatBoundaries(boundaries))
  // {
  //   ghost var target := Model.ExtractPivotsForBoundaries(pivots, NatBoundaries(boundaries));
  //   Model.reveal_ExtractPivotsForBoundaries();

  //   var asubpivots := newArrayFill(|boundaries| as uint64 - 2, DefaultKey());

  //   var i: uint64 := 0;
  //   while i < asubpivots.Length as uint64
  //     invariant i <= asubpivots.Length as uint64
  //     invariant forall j :: 0 <= j < i ==> asubpivots[j] == target[j]
  //   {
  //     asubpivots[i] := pivots[boundaries[i+1]-1];
  //     i := i + 1;
  //   }

  //   subpivots := asubpivots[..];
  // }

  // method BuildLeafForSequence(kvlist: Model.KVList, boundaries: seq<uint64>, i: uint64) returns (node: Node)
  //   requires |kvlist.keys| < Uint64UpperBound()
  //   requires Model.WFKVList(kvlist)
  //   requires ValidBoundariesForSeq(|kvlist.keys| as uint64, boundaries)
  //   requires i as int < |boundaries| - 1
  //   requires BoundariesFit(boundaries, MaxKeysPerLeaf())
  //   ensures WFShape(node)
  //   ensures I(node) == Model.BuildLeafForSequence(kvlist, NatBoundaries(boundaries), i as nat)
  //   ensures fresh(node.repr)
  // {
  //   Model.ValidBoundaryLength(|kvlist.keys|, NatBoundaries(boundaries));
  //   Uint64_Order.IsStrictlySortedImpliesLte(boundaries, i as int, i as int + 1);
  //   assert boundaries[i+1] - boundaries[i] <= MaxKeysPerLeaf() by { Model.reveal_BoundariesFit(); }
    
  //   var mykeys := kvlist.keys[boundaries[i]..boundaries[i+1]];
  //   var myvals := kvlist.values[boundaries[i]..boundaries[i+1]];
  //   node := LeafFromSeqs(mykeys, myvals);

  //   Model.reveal_ExtractBoundedSubsequence();
  // }

  // method BuildLeavesForSequence(kvlist: Model.KVList, boundaries: seq<uint64>) returns (nodes: seq<Node>)
  //   requires Model.WFKVList(kvlist)
  //   requires |kvlist.keys| < Uint64UpperBound() - 1
  //   requires ValidBoundariesForSeq(|kvlist.keys| as uint64, boundaries)
  //   requires BoundariesFit(boundaries, MaxKeysPerLeaf())
  //   ensures WFShapeSiblings(nodes)
  //   ensures fresh(SeqRepr(nodes))
  //   ensures forall i :: 0 <= i < |nodes| ==> nodes[i].height  == 0
  //   ensures ISiblings(nodes) == Model.BuildLeavesForSequence(kvlist, NatBoundaries(boundaries))
  // {
  //   Model.ValidBoundaryLength(|kvlist.keys|, NatBoundaries(boundaries));
  //   var anodes: array<Node?> := newArrayFill(|boundaries| as uint64 - 1, null);
  //   ghost var target := Model.BuildLeavesForSequence(kvlist, NatBoundaries(boundaries));
    
  //   var i: uint64 := 0;
  //   while i < anodes.Length as uint64
  //     invariant i <= anodes.Length as uint64
  //     invariant forall j :: 0 <= j < i ==> anodes[j] != null
  //     invariant forall j :: 0 <= j < i ==> anodes !in anodes[j].repr
  //     invariant WFShapeSiblings(anodes[..i])
  //     invariant fresh(SeqRepr(anodes[..i]))
  //     invariant forall j :: 0 <= j < i ==> anodes[j].height == 0
  //     invariant ISiblings(anodes[..i]) == Model.BuildLeavesForSequenceInner(kvlist, NatBoundaries(boundaries), i as int);
  //   {
  //     anodes[i] := BuildLeafForSequence(kvlist, boundaries, i);
  //     i := i + 1;
      
  //     forall j, k | 0 <= j < k < i as int
  //       ensures DisjointReprs(anodes[..i], j, k)
  //     {
  //       if k < i as int - 1 {
  //         assert DisjointReprs(anodes[..i-1], j, k);
  //       } else {
  //       }
  //     }

  //     ghost var seqrepr := SeqRepr(anodes[..i]);
  //     forall o | o in seqrepr
  //       ensures fresh(o)
  //     {
  //       var j: int := SeqReprDelegation(anodes[..i], o);
  //       if j < i as int - 1 {
  //         assert o in SeqRepr(anodes[..i-1]);
  //       } else {
  //       }
  //     }
  //     assert fresh(seqrepr);
  //   }

  //   assert anodes[..] == anodes[..anodes.Length as uint64];
  //   nodes := anodes[..];
  // }

  // function ExtractBoundedSubsequence<T>(things: seq<T>, boundaries: seq<uint64>, i: uint64) :  seq<T>
  //   requires |things| < Uint64UpperBound()
  //   requires ValidBoundariesForSeq(|things| as uint64, boundaries)
  //   requires 0 <= i as int < |boundaries|-1
  // {
  //   Model.ExtractBoundedSubsequence(things, NatBoundaries(boundaries), i as int)
  // }

  // lemma ExtractBoundedSubsequenceFacts<T>(things: seq<T>, boundaries: seq<uint64>, i: uint64)
  //   requires |things| < Uint64UpperBound() - 1
  //   requires ValidBoundariesForSeq(|things| as uint64, boundaries)
  //   requires 0 <= i as int < |boundaries|-1
  //   ensures |boundaries| <= |things| + 1
  //   ensures boundaries[i] < boundaries[i+1]
  //   ensures ExtractBoundedSubsequence(things, boundaries, i) == things[boundaries[i]..boundaries[i+1]]
  // {
  //   Model.ValidBoundaryLength(|things|, NatBoundaries(boundaries));
  //   Uint64_Order.IsStrictlySortedImpliesLt(boundaries, i as int, i as int + 1);
  //   Model.reveal_ExtractBoundedSubsequence();
  // }
    
  // lemma ExtractBoundedSubsequenceRepr(nodes: seq<Node>, boundaries: seq<uint64>, i: uint64)
  //   requires |nodes| < Uint64UpperBound() - 1
  //   requires ValidBoundariesForSeq(|nodes| as uint64, boundaries)
  //   requires 0 <= i as int < |boundaries|-1
  //   ensures SeqRepr(ExtractBoundedSubsequence(nodes, boundaries, i)) <= SeqRepr(nodes)
  // {
  //   ExtractBoundedSubsequenceFacts(nodes, boundaries, i);
  //   SubSeqRepr(nodes, boundaries[i] as nat, boundaries[i+1] as nat);
  // }
  
  // datatype BuildParentsArgs = BuildParentsArgs(children: seq<Node>,
  //                                              pivots: seq<Key>, 
  //                                              boundaries: seq<uint64>,
  //                                              ghost height: nat)

                                               
                                               
  // predicate ValidBuildParentsArgs(bpa: BuildParentsArgs)
  //   ensures ValidBuildParentsArgs(bpa) ==> |bpa.boundaries| <= |bpa.children| + 1
  //   reads Set(bpa.children), SeqRepr(bpa.children)
  // {
  //   && |bpa.children| < Uint64UpperBound() - 1
  //   && WFShapeSiblings(bpa.children)
  //   && (forall j :: 0 <= j < |bpa.children| ==> bpa.children[j].height < bpa.height)
  //   && Model.WF(Model.Index(bpa.pivots, ISiblings(bpa.children)))
  //   && ValidBoundariesForSeq(|bpa.children| as uint64, bpa.boundaries)
  //   && (Model.ValidBoundaryLength(|bpa.children|, NatBoundaries(bpa.boundaries));
  //      && BoundariesFit(bpa.boundaries, MaxChildren()))
  // }

  // predicate BuildParentRequires(bpa: BuildParentsArgs, i: uint64)
  //   reads Set(bpa.children), SeqRepr(bpa.children)
  // {
  //   && ValidBuildParentsArgs(bpa)
  //   && 0 <= i < |bpa.boundaries| as uint64 - 1
  // }
  
  // twostate predicate BuildParentShapeProperties(bpa: BuildParentsArgs, i: uint64, new parent: Node)
  //   requires BuildParentRequires(bpa, i)
  //   reads Set(bpa.children), SeqRepr(bpa.children), parent, parent.repr
  // {
  //   var mychildren := ExtractBoundedSubsequence(bpa.children, bpa.boundaries, i);
  //   ExtractBoundedSubsequenceFacts(bpa.children, bpa.boundaries, i);
  //   ExtractBoundedSubsequenceRepr(bpa.children, bpa.boundaries, i);
  //   && WFShape(parent)
  //   && fresh(parent.repr - SeqRepr(mychildren))
  // }

  // predicate MatchesModelBuildParent(bpa: BuildParentsArgs, i: uint64, parent: Node)
  //   requires BuildParentRequires(bpa, i)
  //   requires WFShape(parent)
  //   reads Set(bpa.children), SeqRepr(bpa.children), parent, parent.repr
  // {
  //   I(parent) == Model.BuildParent(ISiblings(bpa.children), bpa.pivots, NatBoundaries(bpa.boundaries), i as nat)
  // }
  
  // method BuildParent(bpa: BuildParentsArgs, i: uint64) returns (parent: Node)
  //   requires BuildParentRequires(bpa, i)
  //   ensures BuildParentShapeProperties(bpa, i, parent)
  //   ensures MatchesModelBuildParent(bpa, i, parent)
  // {
  //   ExtractBoundedSubsequenceFacts(bpa.children, bpa.boundaries, i);
  //   var mychildren := bpa.children[bpa.boundaries[i]..bpa.boundaries[i+1]];
  //   var mypivots   := bpa.pivots[bpa.boundaries[i]..bpa.boundaries[i+1]-1];
  //   assert |mychildren| <= MaxChildren() as int by { Model.reveal_BoundariesFit(); }
  //   parent := IndexFromChildren(mypivots, mychildren, bpa.height);
  //   forall j, k | 0 <= j < k < |mychildren|
  //     ensures DisjointReprs(mychildren, j, k)
  //   {
  //     assert DisjointReprs(bpa.children, bpa.boundaries[i] as int + j, bpa.boundaries[i] as int + k);
  //   }
  //   assert SeqRepr(mychildren) <= SeqRepr(bpa.children) by { reveal_SeqRepr(); }
  //   SeqReprSet(mychildren);

  //   assert WFShape(parent);
  //   reveal_I();
  //   ghost var iparent := I(parent);
  //   ghost var target := Model.BuildParent(ISiblings(bpa.children), bpa.pivots, NatBoundaries(bpa.boundaries), i as nat);
  //   assert iparent.pivots == target.pivots;
  // }

  
  
  // predicate BuildParentsLoopStateRequirements(boundaries: seq<uint64>,
  //   sparents: seq<Node?>, i: nat, allReprs: set<object>)
  //   requires i as int <= |sparents|
  //   reads Set(sparents[..i])
  // {
  //   && |sparents| == |boundaries| -1
  //   && (forall j :: 0 <= j < i ==> sparents[j] != null)
  //   && SeqRepr(sparents[..i]) <= allReprs
  // }

  // twostate lemma BuildParentsLoopPreservesStateRequirements(children: seq<Node>, pivots: seq<Key>,
  //   boundaries: seq<uint64>, height: nat, new sparents: seq<Node?>, i: uint64, new allReprs: set<object>)
  //   requires BuildParentsArgRequirements(children, pivots, boundaries, height)
  //   requires i as int <= |sparents|
  //   requires BuildParentsLoopStateRequirements(boundaries, sparents, i as nat, allReprs)
  //   requires i as int < |sparents|
  //   requires sparents[i] != null
  //   ensures BuildParentsLoopStateRequirements(boundaries, sparents, i as nat + 1, allReprs + sparents[i].repr)
  // {
  //   reveal_SeqRepr();
  // }
    
  // twostate predicate {:opaque} BuildParentsLoopShapeInvariant(children: seq<Node>, pivots: seq<Key>,
  //   boundaries: seq<uint64>, height: nat, new sparents: seq<Node?>, i: uint64, new allReprs: set<object>)
  //   requires BuildParentsArgRequirements(children, pivots, boundaries, height)
  //   requires i as int <= |sparents|
  //   requires BuildParentsLoopStateRequirements(boundaries, sparents, i as nat, allReprs)
  //   ensures i == 0 && allReprs == {} ==>
  //      BuildParentsLoopShapeInvariant(children, pivots, boundaries, height, sparents, i, allReprs)
  //   reads Set(children), SeqRepr(children), Set(sparents[..i]), SeqRepr(sparents[..i])
  // {
  //   // && (forall j :: 0 <= j < i ==> aparents[j].contents.Index?)
  //   // && (forall j :: 0 <= j < i ==>
  //   //   var subchildren := Model.ExtractBoundedSubsequence(children, NatBoundaries(boundaries), j as int);
  //   //   assume Set(subchildren) <= Set(children);
  //   //   fresh(aparents[j].repr - SeqRepr(subchildren)))
  //   && fresh(allReprs - SeqRepr(children))
  //   && WFShapeSiblings(sparents[..i])
  // }

  // twostate lemma BuildParentsLoopPreservesShapeInvariant(children: seq<Node>, pivots: seq<Key>,
  //   boundaries: seq<uint64>, height: nat, new sparents: seq<Node?>, i: uint64, new allReprs: set<object>)
  //   requires BuildParentsArgRequirements(children, pivots, boundaries, height)
  //   requires i as int <= |sparents|
  //   requires BuildParentsLoopStateRequirements(boundaries, sparents, i as nat, allReprs)
  //   requires BuildParentsLoopShapeInvariant(children, pivots, boundaries, height, sparents, i, allReprs)
  //   requires i as int < |sparents|
  //   requires sparents[i] != null
  //   requires sparents[i].repr !! allReprs
  //   requires BuildParentShapeProperties(children, pivots, boundaries, i, height, sparents[i])
  //   requires BuildParentsLoopStateRequirements(boundaries, sparents, i as nat + 1, allReprs + sparents[i].repr)
  //   ensures  BuildParentsLoopShapeInvariant(children, pivots, boundaries,
  //                                           height, sparents, i + 1, allReprs + sparents[i].repr)
  // {
  //   var nodes := sparents[..i+1];
  //   assert forall j :: 0 <= j < |nodes| ==> WFShape(nodes[j]) by {
  //     reveal_BuildParentsLoopShapeInvariant();
  //   }
  //   forall k, j | 0 <= k < j < |nodes| as int
  //     ensures DisjointReprs(nodes, k, j)
  //   {
  //     if j < i as int {
  //       reveal_BuildParentsLoopShapeInvariant();
  //       assert DisjointReprs(sparents[..i], k, j);
  //     } else {
  //     }
  //   }
  //   Uint64_Order.IsStrictlySortedImpliesLt(boundaries, i as int, i as int + 1);
  //   SubSeqRepr(children, boundaries[i] as nat, boundaries[i+1] as nat);
  //   forall o | o in (allReprs + sparents[i].repr) - SeqRepr(children)
  //     ensures fresh(o)
  //     {
  //       if o in allReprs - SeqRepr(children) {
  //         reveal_BuildParentsLoopShapeInvariant();
  //       } else {
  //         assert o in sparents[i].repr - SeqRepr(children);
  //         SubSeqRepr(children, boundaries[i] as nat, boundaries[i+1] as nat);
  //         assert Model.ExtractBoundedSubsequence(children, NatBoundaries(boundaries), i as int) ==
  //           children[boundaries[i]..boundaries[i+1]] by {
  //             Model.reveal_ExtractBoundedSubsequence();
  //         }
  //         assert o in sparents[i].repr -
  //           SeqRepr(Model.ExtractBoundedSubsequence(children, NatBoundaries(boundaries), i as int));
  //         assert o == sparents[i] || o == sparents[i].contents.pivots || o == sparents[i].contents.children;
  //       }
  //   }
  //   reveal_BuildParentsLoopShapeInvariant();
  //   assert BuildParentsLoopShapeInvariant(children, pivots, boundaries,
  //                                           height, sparents, i + 1, allReprs + sparents[i].repr);
  // }

  //twostate lemma BuildParentsLoopInvariant(bpa: BuildParentsArgs, new aparents: array<Node?>, i: uint64)

  // twostate lemma BuildParentsLoopInvariant1(bpa: BuildParentsArgs, new aparents: array<Node?>, i: uint64)
  //   requires ValidBuildParentsArgs(bpa)
  //   requires aparents.Length == |bpa.boundaries|-1
  //   requires i as int < aparents.Length
  //   requires forall j :: 0 <= j <= i ==> aparents[j] != null
  //   requires aparents !in SeqRepr(aparents[..i])
  //   requires aparents !in aparents[i].repr;
  //   requires fresh(aparents[i].repr - SeqRepr(ExtractBoundedSubsequence(bpa.children, bpa.boundaries, i)))
  //   ensures aparents !in SeqRepr(aparents[..i+1])
  // {
  //   assert SeqRepr(aparents[..i+1]) == SeqRepr(aparents[..i]) + aparents[i].repr by {
  //     reveal_SeqRepr();
  //   }
  //   assert aparents !in SeqRepr(aparents[..i]);
  // }

  // twostate predicate Stale(new a: set<object>)
  // {
  //   forall o :: o in a ==> !fresh(o)
  // }
  
  // twostate lemma BuildParentsLoopInvariant2(bpa: BuildParentsArgs, new aparents: array<Node?>, i: uint64)
  //   requires ValidBuildParentsArgs(bpa)
  //   requires aparents.Length == |bpa.boundaries|-1
  //   requires i as int < aparents.Length
  //   requires forall j :: 0 <= j <= i ==> aparents[j] != null
  //   requires Stale(SeqRepr(bpa.children))
  //   requires SeqRepr(aparents[..i]) !! SeqRepr(bpa.children[bpa.boundaries[i]..])
  //   requires fresh(aparents[i].repr - SeqRepr(ExtractBoundedSubsequence(bpa.children, bpa.boundaries, i)))
  //   ensures SeqRepr(aparents[..i+1]) !! SeqRepr(bpa.children[bpa.boundaries[i+1]..])
  // {
  //   var srpi  := SeqRepr(aparents[..i]);
  //   var srpii := SeqRepr(aparents[..i+1]);
  //   var src   := SeqRepr(ExtractBoundedSubsequence(bpa.children, bpa.boundaries, i));
  //   var srci  := SeqRepr(bpa.children[bpa.boundaries[i]..]);
  //   var srcii := SeqRepr(bpa.children[bpa.boundaries[i+1]..]);

  //   assert srpi !! srci;
    
  //   assert srpii == srpi + aparents[i].repr by {
  //     reveal_SeqRepr();
  //   }
    
  //   assert srci == src + srcii by {
  //     ExtractBoundedSubsequenceFacts(bpa.children, bpa.boundaries, i);
  //     ExtractBoundedSubsequenceRepr(bpa.children, bpa.boundaries, i);
  //     SeqReprUnion(bpa.children[bpa.boundaries[i]..bpa.boundaries[i+1]], bpa.children[bpa.boundaries[i+1]..]);
  //     assert bpa.children[bpa.boundaries[i]..] ==
  //       bpa.children[bpa.boundaries[i]..bpa.boundaries[i+1]] + bpa.children[bpa.boundaries[i+1]..];
  //   }
  //   assert src !! srcii by {
  //     ExtractBoundedSubsequenceFacts(bpa.children, bpa.boundaries, i);
  //     DisjointSubSeqReprsAreDisjoint(bpa.children,
  //       bpa.boundaries[i] as int, bpa.boundaries[i+1] as int,
  //       bpa.boundaries[i+1] as int, |bpa.children|);
  //     assert bpa.children[bpa.boundaries[i]..] == bpa.children[bpa.boundaries[i]..|bpa.children|];
  //     assert bpa.children[bpa.boundaries[i+1]..] == bpa.children[bpa.boundaries[i+1]..|bpa.children|];
  //   }
  //   assert srcii == srci - src;

  //   assert fresh(aparents[i].repr - src);
  //   assert Stale(srci) by {
  //     SubSeqRepr(bpa.children, bpa.boundaries[i] as nat, |bpa.children|);
  //     assert bpa.children[bpa.boundaries[i]..|bpa.children|] == bpa.children[bpa.boundaries[i]..];
  //     assert srci <= SeqRepr(bpa.children);
  //   }
  //   assert (aparents[i].repr - src) !! (srci - src);
  // }

  // twostate lemma BuildParentsLoopInvariant3(bpa: BuildParentsArgs, new aparents: array<Node?>, i: uint64)
  //   requires ValidBuildParentsArgs(bpa)
  //   requires aparents.Length == |bpa.boundaries|-1
  //   requires i as int < aparents.Length
  //   requires forall j :: 0 <= j <= i ==> aparents[j] != null
  //   requires fresh(SeqRepr(aparents[..i]) - SeqRepr(bpa.children))
  //   requires BuildParentShapeProperties(bpa, i, aparents[i])
  //   ensures fresh(SeqRepr(aparents[..i+1]) - SeqRepr(bpa.children))
  // {
  //   assert SeqRepr(aparents[..i+1]) == SeqRepr(aparents[..i]) + aparents[i].repr by {
  //     reveal_SeqRepr();
  //   }
  //   assert fresh(aparents[i].repr - SeqRepr(ExtractBoundedSubsequence(bpa.children, bpa.boundaries, i)));
  //   ExtractBoundedSubsequenceRepr(bpa.children, bpa.boundaries, i);
  // }
  
  // twostate lemma BuildParentsLoopInvariant4(bpa: BuildParentsArgs, new aparents: array<Node?>, i: uint64)
  //   requires ValidBuildParentsArgs(bpa)
  //   requires aparents.Length == |bpa.boundaries|-1
  //   requires i as int < aparents.Length
  //   requires forall j :: 0 <= j <= i ==> aparents[j] != null
  //   requires SeqRepr(aparents[..i]) !! SeqRepr(bpa.children[bpa.boundaries[i]..])
  //   requires WFShapeSiblings(aparents[..i])
  //   requires BuildParentShapeProperties(bpa, i, aparents[i])
  //   requires aparents[i].repr * SeqRepr(aparents[..i]) <=
  //            SeqRepr(ExtractBoundedSubsequence(bpa.children, bpa.boundaries, i))
  //   ensures WFShapeSiblings(aparents[..i+1])
  // {
  //   forall j, k | 0 <= j < k < i+1
  //     ensures DisjointReprs(aparents[..i+1], j as int, k as int)
  //   {
  //     if k < i {
  //       assert DisjointReprs(aparents[..i], j as int, k as int);
  //     } else {
  //       assume false;
  //     }
  //   }
    
  //   assert WFShapeSiblings(aparents[..i+1]);
  // }
  
  // method BuildParents(bpa: BuildParentsArgs) returns (parents: seq<Node>)
  //   requires ValidBuildParentsArgs(bpa)
  //   ensures WFShapeSiblings(parents)
  //   ensures fresh(SeqRepr(parents) - SeqRepr(bpa.children))
  //   ensures ISiblings(parents) == Model.BuildParents(ISiblings(bpa.children), bpa.pivots, NatBoundaries(bpa.boundaries))
  //   ensures |parents| < |bpa.children|
  // {
  //   // assert Stale(SeqRepr(bpa.children)) by {
  //   //   reveal_SeqRepr();
  //   // }
    
  //   var aparents: array<Node?> := newArrayFill(|bpa.boundaries| as uint64 - 1, null);
  //   //assert aparents !in SeqRepr(bpa.children) by { reveal_SeqRepr(); }

  //   var i: uint64 := 0;
  //   while i < aparents.Length as uint64
  //     invariant i as int <= aparents.Length
  //     invariant forall j :: 0 <= j < i ==> aparents[j] != null
  //     // invariant aparents !in SeqRepr(aparents[..i])
  //     // invariant Stale(SeqRepr(bpa.children))
  //     // invariant SeqRepr(aparents[..i]) !! SeqRepr(bpa.children[bpa.boundaries[i]..])
  //     // invariant fresh(SeqRepr(aparents[..i]) - SeqRepr(bpa.children))
  //     // invariant forall j :: 0 <= j < i ==> WF(aparents[j])
  //     modifies aparents
  //   {
  //     //ghost var oldrepr := SeqRepr(aparents[..i]);
  //     aparents[i] := BuildParent(bpa, i);

  //     // assert aparents !in aparents[i].repr by {
  //     //   ExtractBoundedSubsequenceRepr(bpa.children, bpa.boundaries, i);
  //     // }
  //     // BuildParentsLoopInvariant1(bpa, aparents, i);
  //     // BuildParentsLoopInvariant2(bpa, aparents, i);
  //     // BuildParentsLoopInvariant3(bpa, aparents, i);

      
  //     i := i + 1;
  //   }

  //   parents := aparents[..aparents.Length as uint64];
  //   assume false;
  // }

  // method BuildLayers(children: seq<Node>, pivots: seq<Key>, ghost height: nat) returns (newnode: Node)
  //   requires 0 < |children|
  //   requires |children| < Uint64UpperBound() - 1
  //   requires |children| == |pivots| + 1
  //   requires WFShapeSiblings(children)
  //   requires Model.WF(Model.Index(pivots, ISiblings(children)))
  //   ensures WF(newnode)
  //   ensures Interpretation(newnode) == Model.Interpretation(Model.Index(pivots, ISiblings(children)))
  // {
  //   var currChildren := children;
  //   var currPivots := pivots;
  //   ghost var currHeight := height;
    
  //   while 1 < |currChildren| as uint64
  //     invariant 0 < |currChildren|
  //     //invariant |currChildren| < Uint64UpperBound() - 1
  //     //invariant |currChildren| == |currPivots| + 1
  //     //invariant WFShapeSiblings(currChildren)
  //     //invariant Model.WF(Model.Index(currPivots, ISiblings(currChildren)))
  //     decreases |currChildren|
  //   {
  //     assume false;
  //     var boundaries := BuildBoundaries(|currChildren| as uint64, 3 * MaxChildren() / 4);
  //     var newPivots := ExtractPivotsForBoundaries(currPivots, boundaries);
  //     var bpa := BuildParentsArgs(currChildren, currPivots, boundaries, currHeight);
  //     var parents := BuildParents(bpa);

  //     currChildren := parents;
  //     currPivots := newPivots;
  //     currHeight := currHeight + 1;
  //   }

  //   newnode := currChildren[0];
  //   assume false;
  // }

  // method BuildTreeForSequence(kvlist: Model.KVList) returns (node: Node)
  //   requires |kvlist.keys| < Uint64UpperBound() - 1
  //   requires Model.WFKVList(kvlist)
  //   ensures WF(node)
  //   ensures Interpretation(node) == Model.KVListInterpretation(kvlist)
  //   ensures fresh(node.repr)
  // {
  //   if |kvlist.keys| == 0 {
  //     node := EmptyTree();
  //   } else {
  //     assume false;
  //     var boundaries := BuildBoundaries(|kvlist.keys| as uint64, MaxKeysPerLeaf());
  //     var leaves := BuildLeavesForSequence(kvlist, boundaries);
  //     var pivots := ExtractPivotsForBoundaries(kvlist.keys[1..], boundaries);
  //     node := BuildLayers(leaves, pivots, 1);
  //   }
  // }

    
  // method SplitLeafOfIndexAtKey(node: Node, childidx: uint64, pivot: Key, nleft: uint64)  returns (ghost wit: Key)
  //   requires WFShape(node)
  //   requires Model.WF(I(node))
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   requires 0 <= childidx < node.contents.nchildren
  //   requires node.contents.children[childidx].contents.Leaf?
  //   requires WFShape(node.contents.children[childidx])
  //   requires Model.Keys.lt(node.contents.children[childidx].contents.keys[0], pivot)
  //   requires Model.Keys.lte(pivot, node.contents.children[childidx].contents.keys[node.contents.children[childidx].contents.nkeys-1])
  //   requires Model.Keys.IsSorted(node.contents.children[childidx].contents.keys[..node.contents.children[childidx].contents.nkeys])
  //   requires nleft as int == Model.Keys.LargestLt(node.contents.children[childidx].contents.keys[..node.contents.children[childidx].contents.nkeys], pivot) + 1
  //   ensures WFShape(node)
  //   ensures node.contents.Index?
  //   ensures fresh(node.repr - old(node.repr))
  //   ensures node.height == old(node.height)
  //   ensures Model.SplitChildOfIndex(old(I(node)), I(node), childidx as int, wit)
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
  //   requires Model.WF(I(node))
  //   requires Model.NumElements(I(node)) < Uint64UpperBound()
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   requires childidx as int == Model.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], pivot) + 1
  //   requires node.contents.children[childidx].contents.Leaf?
  //   ensures WFShape(node)
  //   ensures Model.WF(I(node))
  //   ensures node.contents.Index?
  //   ensures node.height == old(node.height)
  //   ensures fresh(node.repr - old(node.repr))
  //   ensures -1 <= pos as int < node.contents.nchildren as int
  //   ensures 0 <= pos as int < node.contents.nchildren as int - 1 ==> node.contents.pivots[pos] == pivot
  //   ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))
  //   ensures Model.AllKeys(I(node)) <= Model.AllKeys(old(I(node))) + {pivot}
  //   modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  // {
  //   var child := node.contents.children[childidx];
  //   assert child.contents.keys[0..child.contents.nkeys] == child.contents.keys[..child.contents.nkeys];
  //   var nleft := Model.Keys.ArrayLargestLtPlus1(child.contents.keys, 0, child.contents.nkeys, pivot);

  //   if 0 == nleft {
  //     if 0 < childidx {
  //       node.contents.pivots[childidx-1] := pivot;
  //       assert I(node) == Model.ReplacePivot(old(I(node)), childidx as int - 1, pivot);
  //       Model.IncreasePivotIsCorrect(old(I(node)), childidx as int - 1, pivot);
  //       pos := childidx as int64 - 1;
  //     } else {
  //       pos := -1;
  //     }
  //   } else if nleft == child.contents.nkeys {
  //     if childidx < node.contents.nchildren-1 {
  //       node.contents.pivots[childidx] := pivot;
  //       assert I(node) == Model.ReplacePivot(old(I(node)), childidx as int, pivot);
  //       Model.DecreasePivotIsCorrect(old(I(node)), childidx as int, pivot);
  //       pos := childidx as int64;
  //     } else {
  //       pos := node.contents.nchildren as int64 - 1;
  //     }
  //   } else {
  //     ghost var wit := SplitLeafOfIndexAtKey(node, childidx, pivot, nleft);
  //     pos := childidx as int64;
  //     Model.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int, wit);
  //     Model.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int, wit);
  //     Model.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int, wit);
  //   }
  // }

  // method EnsurePivotNotFull(node: Node, pivot: Key) returns (pos: int64)
  //   requires WFShape(node)
  //   requires Model.WF(I(node))
  //   requires Model.NumElements(I(node)) < Uint64UpperBound()
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   ensures WFShape(node)
  //   ensures Model.WF(I(node))
  //   ensures -1 <= pos as int < node.contents.nchildren as int
  //   ensures 0 <= pos as int < node.contents.nchildren as int - 1 ==> node.contents.pivots[pos] == pivot
  // {
  //   var childidx := Model.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, pivot);
  //   if 0 < childidx && node.contents.pivots[childidx-1] == pivot {
  //     pos := childidx as int64 - 1;
  //   } else {
  //     var childpos := EnsurePivot(node.contents.children[pos], pivot);
  //   }
  // }

  // method EnsurePivot(node: Node, pivot: Key) returns (pos: int64)
  //   requires WFShape(node)
  //   requires Model.WF(I(node))
  //   requires Model.NumElements(I(node)) < Uint64UpperBound()
  //   requires node.contents.Index?
  //   requires !Full(node)
  //   ensures WFShape(node)
  //   ensures Model.WF(I(node))
  //   ensures -1 <= pos as int < node.contents.nchildren as int
  //   ensures 0 <= pos as int < node.contents.nchildren as int - 1 ==> node.contents.pivots[pos] == pivot

}
