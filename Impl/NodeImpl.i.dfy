include "StateModel.i.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"
include "NodeModel.i.dfy"
//
// Implements PivotBetree/PivotBetreeSpec.Node. (There's no Model file
// because Node is already a precise functional model of this code.)
//

module NodeImpl {
  import DebugAccumulator
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import opened KeyType
  import opened ValueMessage

  import IM = StateModel
  import BT = PivotBetreeSpec`Internal
  import Pivots = PivotsLib
  import opened Bounds
  import opened BucketImpl
  import opened BucketsLib
  import opened BucketWeights
  import NodeModel

  import MM = MutableMap
  import ReferenceType`Internal

  class Node
  {
    var pivotTable: Pivots.PivotTable;
    var children: Option<seq<BT.G.Reference>>;
    var buckets: seq<BucketImpl.MutBucket>;
    ghost var Repr: set<object>;

    method DebugCountBytes(acc:DebugAccumulator.DebugCounter) {
      var i:uint64 := 0;
      //print("pivots-one-node ", |pivotTable| as uint64, " buckets ", |buckets| as uint64, "\n");
      while i < |pivotTable| as uint64 {
        acc.pivotCount := acc.pivotCount + 1;
        acc.pivotWeight := acc.pivotWeight + |pivotTable[i]| as uint64;
        i := i + 1;
      }
      var hasTreeBucket := false;
      i:=0;
      while i < |buckets| as uint64 {
        var bucket := buckets[i];
        if bucket.format.BFKvl?
        {
          acc.kvlBuckets := acc.kvlBuckets + 1;
          var kvl := bucket.kvl;
          var j:uint64 := 0;
          while j < |kvl.keys| as uint64 {
            acc.keyCount := acc.keyCount + 1;
            acc.keyWeight := acc.keyWeight + |kvl.keys[j]| as uint64;
            j := j + 1;
          }
          j:=0;
          while j < |kvl.messages| as uint64 {
            acc.messageCount := acc.messageCount + 1;
            acc.messageWeight := acc.messageWeight + |kvl.messages[j].value| as uint64;
            j := j + 1;
          }
        }
        else if bucket.format.BFTree? {
          acc.treeBuckets := acc.treeBuckets + 1;
          hasTreeBucket := true;
        }
        else if bucket.format.BFPkv? {
          acc.pkvBuckets := acc.pkvBuckets + 1;
        } else {
          acc.weirdBuckets := acc.weirdBuckets + 1;
        }
        i := i + 1;
      }  // while buckets
      if hasTreeBucket {
        acc.treeNodes := acc.treeNodes + 1;
      }
    }

    constructor(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<BT.G.Reference>>,
      buckets: seq<BucketImpl.MutBucket>)
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    requires MutBucket.ReprSeqDisjoint(buckets)
    ensures this.pivotTable == pivotTable;
    ensures this.children == children;
    ensures this.buckets == buckets;
    ensures Inv();
    ensures forall o | o in Repr :: fresh(o) || o in old(MutBucket.ReprSeq(buckets))
    {
      this.pivotTable := pivotTable;
      this.children := children;
      this.buckets := buckets;

      new;

      this.Repr := {this} + MutBucket.ReprSeq(buckets);
      MutBucket.reveal_ReprSeq();
    }

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    ensures Inv() ==>
      forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    {
      && (forall i | 0 <= i < |buckets| :: buckets[i] in Repr)
      && Repr == {this} + MutBucket.ReprSeq(buckets)
      && MutBucket.ReprSeqDisjoint(buckets)

      && (
        MutBucket.reveal_ReprSeq();
        && (forall i | 0 <= i < |buckets| :: buckets[i].Inv())
        && (forall i | 0 <= i < |buckets| :: this !in buckets[i].Repr)
      )
    }

    // There's another copy of this method over in LeafImpl. It's a mess
    // because I'm just trying to prove that we CAN manage memory successfully.
    // TODO Clean this mess up.
    method CopyKey(k: KeyType.Key) returns (k2: KeyType.Key)
      ensures k == k2
    {
      k2 := [] + k;
    }

    method RecopyPivots()
    requires Inv()
    modifies Repr
    ensures Inv()
    ensures I() == old(I())
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o);
    {
      assume 0 <= |pivotTable| < Uint64UpperBound();
      var newPivotTable := [];
      var i:uint64 := 0;
      while i < (|pivotTable| as uint64)
        invariant pivotTable == old(pivotTable)
        invariant i as int <= |pivotTable|
        invariant i as int == |newPivotTable|
        invariant forall j :: 0<=j<i ==> newPivotTable[j] == pivotTable[j]
      {
        var newKey := CopyKey(pivotTable[i]);
        newPivotTable := newPivotTable + [newKey];
        i := i + 1;
      }
      pivotTable := newPivotTable;
      assume false; // all the Repr crap
    }

    method AmassBuckets()
    requires Inv()
    modifies Repr
    ensures Inv()
    ensures I() == old(I())
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o);
    {
      // Every assume false in this method is a Repr problem. And a timeout. Pulling out hair.
      var newBuckets:seq<BucketImpl.MutBucket> := [];
      assert MutBucket.ReprSeqDisjoint(newBuckets) by { MutBucket.reveal_ReprSeqDisjoint(); }
      assert MutBucket.ReprSeq(newBuckets) !! Repr by { MutBucket.reveal_ReprSeq(); }
      var i:uint64 := 0;
      assume 0 <= |buckets| < Uint64UpperBound();
      while i < (|buckets| as uint64)
        invariant buckets == old(buckets)
        invariant Inv()
        invariant i as int <= |buckets|
        invariant i as int == |newBuckets|
        invariant forall j :: 0<=j<i ==> newBuckets[j].Inv()
        invariant forall j :: 0<=j<i ==> buckets[j].I() == newBuckets[j].I()
        invariant MutBucket.ReprSeqDisjoint(newBuckets)
        invariant MutBucket.ReprSeq(newBuckets) !! Repr
      {
        assert old(buckets[i].Inv());
        assert buckets[i].Inv();
        var oldKvl := buckets[i].GetKvl();
        var newKvl := KVList.AmassKvl(oldKvl);
        var newBucket := new MutBucket(newKvl);
        newBuckets := newBuckets + [newBucket];
        assert MutBucket.ReprSeqDisjoint(newBuckets) by { MutBucket.reveal_ReprSeqDisjoint(); }
        assert MutBucket.ReprSeq(newBuckets) !! Repr by { assume false; MutBucket.reveal_ReprSeq(); }
        i := i + 1;
      }
      this.buckets := newBuckets;

      Repr := {this} + MutBucket.ReprSeq(buckets);
      assume (forall i | 0 <= i < |buckets| :: buckets[i] in Repr); // This and the next line of Inv contradict each other.

      assert Inv() by { assume false; MutBucket.reveal_ReprSeq(); }

      assert BucketImpl.MutBucket.ISeq(buckets) == BucketImpl.MutBucket.ISeq(old(buckets));
      forall ensures I() == old(I()) {
        calc {
          old(IM.Node(pivotTable, children, BucketImpl.MutBucket.ISeq(buckets)));
            { assume false; }
          IM.Node(pivotTable, children, old(BucketImpl.MutBucket.ISeq(buckets)));
            { assume false; }
          IM.Node(pivotTable, children, BucketImpl.MutBucket.ISeq(old(buckets)));
          IM.Node(pivotTable, children, BucketImpl.MutBucket.ISeq(buckets));
        }
      }

      forall o | o in Repr ensures o in old(Repr) || fresh(o)
      {
        assume false;
      }
    }

    lemma LemmaRepr()
    requires Inv()
    ensures Repr == {this} + MutBucket.ReprSeq(buckets)
    {
    }

    function I() : IM.Node
    reads this, Repr
    requires Inv()
    {
      IM.Node(pivotTable, children,
        BucketImpl.MutBucket.ISeq(buckets))
    }

    method UpdateSlot(slot: uint64, bucket: BucketImpl.MutBucket, childref: BT.G.Reference)
    requires Inv()
    requires bucket.Inv()
    requires children.Some?
    requires 0 <= slot as int < |children.value|
    requires 0 <= slot as int < |buckets|
    requires slot as int + 1 < 0x1_0000_0000_0000_0000
    requires bucket.Repr !! Repr
    modifies Repr
    ensures Inv()
    ensures I() == old(IM.Node(
        I().pivotTable,
        Some(I().children.value[slot as int := childref]),
        I().buckets[slot as int := bucket.Bucket]
      ))
    ensures forall o | o in Repr :: o in old(Repr) || o in old(bucket.Repr) || fresh(o);
    {
      buckets := SeqIndexUpdate(buckets, slot, bucket);
      children := Some(SeqIndexUpdate(children.value, slot, childref));

      MutBucket.reveal_ReprSeq();
      MutBucket.reveal_ReprSeqDisjoint();

      Repr := {this} + MutBucket.ReprSeq(buckets);
      assert Inv();
    }

    lemma LemmaReprFacts()
    requires Repr == {this} + MutBucket.ReprSeq(buckets);
    requires (forall i | 0 <= i < |buckets| :: buckets[i].Inv())
    ensures (forall i | 0 <= i < |buckets| :: buckets[i] in Repr)
    //ensures (forall i | 0 <= i < |buckets| :: this !in buckets[i].Repr)
    {
      MutBucket.reveal_ReprSeq();
    }

    twostate lemma SplitParentReprSeqFacts(new s: seq<MutBucket>)
    requires forall i | 0 <= i < |buckets| :: this !in buckets[i].Repr
    requires forall o | o in MutBucket.ReprSeq(s) :: o in MutBucket.ReprSeq(buckets) || fresh(o)
    ensures forall i | 0 <= i < |s| :: this !in s[i].Repr;
    ensures this !in MutBucket.ReprSeq(s);
    ensures forall o :: o in MutBucket.ReprSeq(s) ==> allocated(o);
    {
      MutBucket.reveal_ReprSeq();
      forall i | 0 <= i < |s| ensures this !in s[i].Repr
      {
        if this in s[i].Repr {
          assert this in MutBucket.ReprSeq(s);
        }
      }
    }

    method SplitParent(slot: uint64, pivot: Key, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
    requires Inv()
    requires IM.WFNode(I())
    requires children.Some?
    requires 0 <= slot as int < |children.value|
    requires 0 <= slot as int < |buckets|
    requires children.Some?
    modifies Repr
    ensures Inv()
    ensures I() == old(NodeModel.SplitParent(I(), pivot, slot as int, left_childref, right_childref))
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o);
    {
      ghost var b := NodeModel.SplitParent(I(), pivot, slot as int, left_childref, right_childref);
      NodeModel.reveal_SplitParent();
      //assert SplitBucketInList(I().buckets, slot as int, pivot)
      //    == b.buckets;

      this.pivotTable := Sequences.Insert(this.pivotTable, pivot, slot);

      ghost var node2 := I();

      var bucks := MutBucket.SplitOneInList(this.buckets, slot, pivot);
      assert forall o | o in MutBucket.ReprSeq(bucks) :: o in MutBucket.ReprSeq(this.buckets) || fresh(o);
      //MutBucket.reveal_ReprSeq();
      assert MutBucket.ISeq(bucks) == SplitBucketInList(node2.buckets, slot as int, pivot);
      assert node2.buckets == old(I()).buckets;
      //assert MutBucket.ISeq(bucks) == SplitBucketInList(old(I()).buckets, slot as int, pivot);
      SplitParentReprSeqFacts(bucks);
      //assert forall o :: o in MutBucket.ReprSeq(bucks) ==> allocated(o);
      //assert forall i | 0 <= i < |bucks| :: bucks[i].Inv();
      //assert forall i | 0 <= i < |bucks| :: this !in bucks[i].Repr;
      //assert this !in MutBucket.ReprSeq(bucks);

      this.buckets := bucks;

      var childrenReplaced := Replace1with2(children.value, left_childref, right_childref, slot);
      this.children := Some(childrenReplaced);

      Repr := {this} + MutBucket.ReprSeq(buckets);
      LemmaReprFacts();
      assert Inv();
      assert forall o | o in Repr :: o in old(Repr) || fresh(o);
      ghost var a := I();
      /*assert a.buckets
          == SplitBucketInList(old(I()).buckets, slot as int, pivot)
          == b.buckets;
      assert a.children == b.children;
      assert a.pivotTable == b.pivotTable;*/
      assert a == b;
    }

    lemma ReprSeqDisjointAppend(s: seq<MutBucket>, t: MutBucket)
    requires MutBucket.ReprSeqDisjoint(s)
    requires MutBucket.ReprSeq(s) !! t.Repr
    ensures MutBucket.ReprSeqDisjoint(s + [t])
    {
      MutBucket.reveal_ReprSeqDisjoint();
      MutBucket.reveal_ReprSeq();
    }

    lemma ReprSeqAppend(s: seq<MutBucket>, t: MutBucket)
    ensures MutBucket.ReprSeq(s + [t]) == MutBucket.ReprSeq(s) + t.Repr
    {
      MutBucket.reveal_ReprSeq();
      var a := MutBucket.ReprSeq(s + [t]);
      var b := MutBucket.ReprSeq(s) + t.Repr;
      forall o | o in a ensures o in b { }
      forall o | o in b ensures o in a {
        if o in MutBucket.ReprSeq(s) {
          var i :| 0 <= i < |s| && o in s[i].Repr;
          assert o in (s + [t])[i].Repr;
          assert o in a;
        } else {
          assert o in (s + [t])[|s|].Repr;
          assert o in a;
        }
      }
    }

    method CutoffNodeAndKeepLeft(pivot: Key) returns (node': Node)
    requires Inv()
    requires IM.WFNode(I())
    ensures node'.Inv()
    //ensures fresh(node'.Repr)
    ensures node'.I() == NodeModel.CutoffNodeAndKeepLeft(old(I()), pivot);
    {
      NodeModel.reveal_CutoffNodeAndKeepLeft();
      var cLeft := Pivots.ComputeCutoffForLeft(this.pivotTable, pivot);
      var leftPivots := this.pivotTable[.. cLeft];
      var leftChildren := if this.children.Some? then Some(this.children.value[.. cLeft + 1]) else None;
      WeightBucketLeBucketList(MutBucket.ISeq(this.buckets), cLeft as int);
      var splitBucket := this.buckets[cLeft].SplitLeft(pivot);
      var slice := MutBucket.CloneSeq(this.buckets[.. cLeft]); // TODO clone not necessary?
      //var slice := this.buckets[.. cLeft];
      var leftBuckets := slice + [splitBucket];
      ReprSeqDisjointAppend(slice, splitBucket);
      ReprSeqAppend(slice, splitBucket);
      node' := new Node(leftPivots, leftChildren, leftBuckets);
    }

    static lemma ReprSeqDisjointPrepend(t: MutBucket, s: seq<MutBucket>)
    requires MutBucket.ReprSeqDisjoint(s)
    requires MutBucket.ReprSeq(s) !! t.Repr
    ensures MutBucket.ReprSeqDisjoint([t] + s)
    {
      MutBucket.reveal_ReprSeqDisjoint();
      MutBucket.reveal_ReprSeq();
    }

    static lemma ReprSeqPrepend(t: MutBucket, s: seq<MutBucket>)
    ensures MutBucket.ReprSeq([t] + s) == MutBucket.ReprSeq(s) + t.Repr
    {
      MutBucket.ReprSeqAdditive([t], s);
      MutBucket.ReprSeq1Eq([t]);
    }

    method CutoffNodeAndKeepRight(pivot: Key) returns (node': Node)
    requires Inv()
    requires IM.WFNode(I())
    ensures node'.Inv()
    //ensures fresh(node'.Repr)
    ensures node'.I() == NodeModel.CutoffNodeAndKeepRight(old(I()), pivot);
    {
      NodeModel.reveal_CutoffNodeAndKeepRight();
      var cRight := Pivots.ComputeCutoffForRight(this.pivotTable, pivot);
      var rightPivots := this.pivotTable[cRight ..];
      var rightChildren := if this.children.Some? then Some(this.children.value[cRight ..]) else None;
      WeightBucketLeBucketList(MutBucket.ISeq(this.buckets), cRight as int);
      var splitBucket := this.buckets[cRight].SplitRight(pivot);
      var slice := MutBucket.CloneSeq(this.buckets[cRight + 1 ..]);
      //var slice := this.buckets[cRight + 1 ..];
      var rightBuckets := [splitBucket] + slice;
      ReprSeqDisjointPrepend(splitBucket, slice);
      ReprSeqPrepend(splitBucket, slice);
      node' := new Node(rightPivots, rightChildren, rightBuckets);
      assert node'.I().buckets == NodeModel.CutoffNodeAndKeepRight(old(I()), pivot).buckets;
      assert node'.I().children == NodeModel.CutoffNodeAndKeepRight(old(I()), pivot).children;
      assert node'.I().pivotTable == NodeModel.CutoffNodeAndKeepRight(old(I()), pivot).pivotTable;
    }

    static method CutoffNode(node: Node, lbound: Option<Key>, rbound: Option<Key>)
    returns (node' : Node)
    requires node.Inv()
    requires IM.WFNode(node.I())
    ensures node'.Inv()
    //ensures fresh(node'.Repr)
    ensures node'.I() == NodeModel.CutoffNode(old(node.I()), lbound, rbound)
    {
      NodeModel.reveal_CutoffNode();
      match lbound {
        case None => {
          match rbound {
            case None => {
              node' := node;
            }
            case Some(rbound) => {
              node' := node.CutoffNodeAndKeepLeft(rbound);
            }
          }
        }
        case Some(lbound) => {
          match rbound {
            case None => {
              node' := node.CutoffNodeAndKeepRight(lbound);
            }
            case Some(rbound) => {
              var node1 := node.CutoffNodeAndKeepLeft(rbound);
              NodeModel.CutoffNodeAndKeepLeftCorrect(node.I(), rbound);
              node' := node1.CutoffNodeAndKeepRight(lbound);
            }
          }
        }
      }
    }

    method SplitChildLeft(num_children_left: uint64)
    returns (node': Node)
    requires Inv()
    requires 0 <= num_children_left as int - 1 <= |this.pivotTable|
    requires this.children.Some? ==> 0 <= num_children_left as int <= |this.children.value|
    requires 0 <= num_children_left as int <= |this.buckets|
    ensures node'.Inv()
    ensures node'.I() == old(NodeModel.SplitChildLeft(I(), num_children_left as int))
    ensures fresh(node'.Repr)
    {
      NodeModel.reveal_SplitChildLeft();
      var slice := MutBucket.CloneSeq(this.buckets[ .. num_children_left]);
      node' := new Node(
        this.pivotTable[ .. num_children_left - 1 ],
        if this.children.Some? then Some(this.children.value[ .. num_children_left ]) else None,
        slice
      );
    }

    method SplitChildRight(num_children_left: uint64)
    returns (node': Node)
    requires Inv()
    requires 0 <= num_children_left as int <= |this.pivotTable|
    requires this.children.Some? ==> 0 <= num_children_left as int <= |this.children.value|
    requires 0 <= num_children_left as int <= |this.buckets|
    requires |this.buckets| < 0x1_0000_0000_0000_0000
    ensures node'.Inv()
    ensures node'.I() == old(NodeModel.SplitChildRight(I(), num_children_left as int))
    ensures fresh(node'.Repr)
    {
      NodeModel.reveal_SplitChildRight();
      var slice := MutBucket.CloneSeq(this.buckets[num_children_left .. ]);
      node' := new Node(
        this.pivotTable[ num_children_left .. ],
        if this.children.Some? then Some(this.children.value[ num_children_left .. ]) else None,
        slice
      );
    }

    twostate lemma ReprSeqDisjointAfterUpdate(buckets: seq<MutBucket>, r: int)
    requires 0 <= r < |buckets|
    requires old(MutBucket.ReprSeqDisjoint(buckets))
    requires forall o | o in buckets[r].Repr :: o in old(buckets[r].Repr) || fresh(o)
    requires forall i | 0 <= i < |buckets| && i != r :: buckets[i].Repr == old(buckets[i].Repr)
    ensures MutBucket.ReprSeqDisjoint(buckets)
    {
      MutBucket.reveal_ReprSeqDisjoint();
      MutBucket.reveal_ReprSeq();
    }

    twostate lemma ReprSeqReplace(buckets: seq<MutBucket>, r: int)
    requires 0 <= r < |buckets|
    requires forall i | 0 <= i < |buckets| && i != r :: buckets[i].Repr == old(buckets[i].Repr)
    ensures MutBucket.ReprSeq(buckets) <= old(MutBucket.ReprSeq(buckets)) + buckets[r].Repr
    {
      MutBucket.reveal_ReprSeq();
    }

    method InsertKeyValue(key: Key, msg: Message)
    requires Inv();
    requires IM.WFNode(I())
    requires WeightBucketList(MutBucket.ISeq(buckets)) + WeightKey(key) + WeightMessage(msg) < 0x1_0000_0000_0000_0000
    modifies Repr
    ensures Inv();
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures I() == NodeModel.NodeInsertKeyValue(old(I()), key, msg)
    {
      NodeModel.reveal_NodeInsertKeyValue();

      var r := Pivots.ComputeRoute(pivotTable, key);

      MutBucket.LemmaReprBucketLeReprSeq(buckets, r as int);
      WeightBucketLeBucketList(MutBucket.ISeq(buckets), r as int);

      buckets[r].Insert(key, msg);

      forall i | 0 <= i < |buckets|
      ensures buckets[i].Inv()
      ensures i != r as int ==> buckets[i].Bucket == old(buckets[i].Bucket)
      ensures i != r as int ==> buckets[i].Repr == old(buckets[i].Repr)
      ensures this !in buckets[i].Repr
      {
        MutBucket.reveal_ReprSeqDisjoint();
      }
      ReprSeqDisjointAfterUpdate(buckets, r as int);
      ReprSeqReplace(buckets, r as int);

      Repr := {this} + MutBucket.ReprSeq(buckets);
      LemmaReprFacts();
      assert Inv();
      assert I().buckets == NodeModel.NodeInsertKeyValue(old(I()), key, msg).buckets;
    }

    lemma LemmaReprSeqBucketsLeRepr()
    requires Inv()
    ensures MutBucket.ReprSeq(buckets) <= Repr
    {
    }
  }
}

