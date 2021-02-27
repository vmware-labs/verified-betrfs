// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

module BucketImplModule {
  type Key(==)
  type Message(==)
  type Bucket = map<Key, Message>
  datatype Option<V> = None | Some(value:V)

  // This is some opaque operation on a Bucket, doesn't matter what.
  function {:opaque} SplitLeft(bucket: Bucket, pivot: Key) : Bucket
  {
    map[]
  }

  // BucketImpl class has an intepretation as a Bucket.

  // (This is a stub with only the interface included,
  // implementation omitted.)

  class BucketImpl {
    // Set of objects on which the interpretation of this
    // object depends.
    ghost var Repr: set<object>;

    // Interpretation of the BucketImpl.
    ghost var Bucket: map<Key, Message>;

    // Invariant
    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    {
      this in Repr
    }

    // Interpretation
    function I() : Bucket
    reads this
    {
      this.Bucket
    }

    // Utilities for talking about sequences of ImplBuckets.

    static function ReprSeq(s: seq<BucketImpl>) : set<object>
    reads s
    {
      set i, o | 0 <= i < |s| && o in s[i].Repr :: o
    }

    static predicate ReprSeqDisjoint(buckets: seq<BucketImpl>)
    reads set i | 0 <= i < |buckets| :: buckets[i]
    {
      forall i, j | 0 <= i < |buckets| && 0 <= j < |buckets| && i != j ::
          buckets[i].Repr !! buckets[j].Repr
    }

    // Given a sequence of BucketImpls, take the interpreation
    // of each one and return a sequence of Buckets
    // Basically `map I`

    static protected function ISeq(s: seq<BucketImpl>) : (bs : seq<Bucket>)
    reads s
    reads ReprSeq(s)
    ensures |bs| == |s|
    ensures forall i | 0 <= i < |s| :: bs[i] == s[i].Bucket
    decreases |s|
    {
      //reveal_ReprSeq();
      if |s| == 0 then [] else ISeq(s[..|s|-1]) + [s[|s|-1].I()]
    }

    // Says that Inv holds for each BucketImpl in a sequence.
    static predicate {:opaque} InvSeq(s: seq<BucketImpl>)
    reads s
    reads ReprSeq(s)
    ensures InvSeq(s) == (forall i | 0 <= i < |s| :: s[i].Inv())
    {
      //reveal_ReprSeq();
      forall i | 0 <= i < |s| :: s[i].Inv()
    }

    // Implementation that corresponds to the opaque SplitLeft
    // function declared above.
    method ImplSplitLeft(pivot: Key)
    returns (left: BucketImpl)
    requires Inv()
    ensures left.Inv()
    ensures left.Bucket == SplitLeft(Bucket, pivot)
    ensures fresh(left.Repr)

    // Clone the sequence of BucketImpls.
    // The new sequence should consist entirely of freshly allocated
    // objects and not modify the existing sequence.
    static method CloneSeq(buckets: seq<BucketImpl>) returns (buckets': seq<BucketImpl>)
    requires InvSeq(buckets)
    requires |buckets| < 0x1_0000_0000_0000_0000;
    ensures InvSeq(buckets')
    ensures fresh(ReprSeq(buckets'))
    ensures |buckets'| == |buckets|
    ensures ISeq(buckets) == ISeq(buckets')
    ensures ReprSeqDisjoint(buckets')
  }
}

module NodeImplModule {
  import opened BucketImplModule

  // The NodeImpl class has an interpretation as a Node.
  // A Node contains a sequence of Buckets;
  // therefore, the NodeImpl has a sequence of BucketImpls.

  datatype Node = Node(
      pivotTable: seq<Key>,
      children: Option<seq<int>>,
      buckets: seq<Bucket>)

  // Declare some operations about pivot sequences.

  predicate WFPivots(pivots: seq<Key>)

  predicate WFNode(node: Node) {
    && (node.children.Some? ==> |node.children.value| == |node.pivotTable| + 1)
    && (|node.buckets| == |node.pivotTable| + 1)
    && WFPivots(node.pivotTable)
  }

  function {:opaque} PivotsCutoffForLeft(pivots: seq<Key>, pivot: Key) : int
  requires WFPivots(pivots)
  ensures 0 <= PivotsCutoffForLeft(pivots, pivot) <= |pivots|

  function {:opaque} CutoffNodeAndKeepLeft(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  ensures |node'.buckets| == |node'.pivotTable| + 1
  ensures node'.children.Some? ==> |node'.buckets| == |node'.children.value|
  {
    var cLeft := PivotsCutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var splitBucket := SplitLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Node(leftPivots, leftChildren, leftBuckets)
  }

  method ImplPivotsCutoffForLeft(pivots: seq<Key>, pivot: Key) returns (i: int)
  requires |pivots| < 0x4000_0000_0000_0000
  requires WFPivots(pivots)
  ensures i as int == PivotsCutoffForLeft(pivots, pivot)

  // NodeImpl class

  class NodeImpl
  {
    var pivotTable: seq<Key>;
    var children: Option<seq<int>>;
    var buckets: seq<BucketImplModule.BucketImpl>;
    ghost var Repr: set<object>;

    constructor(
      pivotTable: seq<Key>,
      children: Option<seq<int>>,
      buckets: seq<BucketImplModule.BucketImpl>)
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    requires BucketImpl.ReprSeqDisjoint(buckets)
    ensures this.pivotTable == pivotTable;
    ensures this.children == children;
    ensures this.buckets == buckets;
    ensures Inv();
    ensures forall o | o in Repr :: fresh(o) || o in old(BucketImpl.ReprSeq(buckets))

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    ensures Inv() ==>
      forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    {
      && (forall i | 0 <= i < |buckets| :: buckets[i] in Repr)
      && Repr == {this} + BucketImpl.ReprSeq(buckets)
      && BucketImpl.ReprSeqDisjoint(buckets)

      && (
        //BucketImpl.reveal_ReprSeq();
        && (forall i | 0 <= i < |buckets| :: buckets[i].Inv())
        && (forall i | 0 <= i < |buckets| :: this !in buckets[i].Repr)
      )
    }

    function I() : Node
    reads this, Repr
    requires Inv()
    {
      Node(pivotTable, children,
        BucketImplModule.BucketImpl.ISeq(buckets))
    }

    lemma ReprSeqDisjointAppend(s: seq<BucketImpl>, t: BucketImpl)
    requires BucketImpl.ReprSeqDisjoint(s)
    requires BucketImpl.ReprSeq(s) !! t.Repr
    ensures BucketImpl.ReprSeqDisjoint(s + [t])
    {
      //BucketImpl.reveal_ReprSeqDisjoint();
      //BucketImpl.reveal_ReprSeq();
    }

    lemma ReprSeqAppend(s: seq<BucketImpl>, t: BucketImpl)
    ensures BucketImpl.ReprSeq(s + [t]) == BucketImpl.ReprSeq(s) + t.Repr
    {
      //BucketImpl.reveal_ReprSeq();
      var a := BucketImpl.ReprSeq(s + [t]);
      var b := BucketImpl.ReprSeq(s) + t.Repr;
      forall o | o in a ensures o in b { }
      forall o | o in b ensures o in a {
        if o in BucketImpl.ReprSeq(s) {
          var i :| 0 <= i < |s| && o in s[i].Repr;
          assert o in (s + [t])[i].Repr;
          assert o in a;
        } else {
          assert o in (s + [t])[|s|].Repr;
          assert o in a;
        }
      }
    }

    // This method is slow to verify.

    method ImplCutoffNodeAndKeepLeft(pivot: Key) returns (node': NodeImpl)
    requires Inv()
    requires WFNode(I())
    requires |this.pivotTable| < 0x4000_0000_0000_0000
    ensures node'.Inv()
    //ensures fresh(node'.Repr)
    ensures node'.I() == CutoffNodeAndKeepLeft(old(I()), pivot);
    {
      reveal_CutoffNodeAndKeepLeft();

      // First method call
      var cLeft := ImplPivotsCutoffForLeft(this.pivotTable, pivot);

      // Some functional computation
      var leftPivots := this.pivotTable[.. cLeft];
      var leftChildren := if this.children.Some? then Some(this.children.value[.. cLeft + 1]) else None;
      //WeightBucketLeBucketList(BucketImpl.ISeq(this.buckets), cLeft as int);

      // Grab a BucketImpl from the sequence
      // And split it.
      var splitBucket := this.buckets[cLeft].ImplSplitLeft(pivot);

      // Grab every bucket from the list *before* that buck.
      var slice := BucketImpl.CloneSeq(this.buckets[.. cLeft]);

      // Put them together.
      var leftBuckets := slice + [splitBucket];

      // Lemmas
      ReprSeqDisjointAppend(slice, splitBucket);
      ReprSeqAppend(slice, splitBucket);

      // Create a new node.
      node' := new NodeImpl(leftPivots, leftChildren, leftBuckets);
    }
  }
}
