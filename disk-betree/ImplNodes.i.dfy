include "../lib/MutableMapImpl.i.dfy"
include "ImplModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "MutableBucket.i.dfy"
include "ImplModelSplit.i.dfy"
include "ImplModelInsert.i.dfy"

module ImplNode {
  import opened Options
  import opened Sequences
  import opened NativeTypes

  import IM = ImplModel
  import BT = PivotBetreeSpec`Internal
  import Pivots = PivotsLib
  import opened Bounds
  import opened MutableBucket
  import opened BucketsLib
  import opened BucketWeights
  import ImplModelSplit
  import ImplModelInsert

  import MM = MutableMap
  import ReferenceType`Internal

  class Node
  {
    var pivotTable: Pivots.PivotTable;
    var children: Option<seq<BT.G.Reference>>;
    var buckets: seq<MutableBucket.MutBucket>;
    ghost var Repr: set<object>;

    constructor(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<BT.G.Reference>>,
      buckets: seq<MutableBucket.MutBucket>)
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
        MutableBucket.MutBucket.ISeq(buckets))
    }

    method UpdateSlot(slot: uint64, bucket: MutableBucket.MutBucket, childref: BT.G.Reference)
    requires Inv()
    requires bucket.Inv()
    requires children.Some?
    requires 0 <= slot as int < |children.value|
    requires 0 <= slot as int < |buckets|
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
      buckets := buckets[slot as int := bucket];
      children := Some(children.value[slot as int := childref]);

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
    ensures I() == old(ImplModelSplit.SplitParent(I(), pivot, slot as int, left_childref, right_childref))
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o);
    {
      ghost var b := ImplModelSplit.SplitParent(I(), pivot, slot as int, left_childref, right_childref);
      ImplModelSplit.reveal_SplitParent();
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
    ensures node'.I() == ImplModelSplit.CutoffNodeAndKeepLeft(old(I()), pivot);
    {
      ImplModelSplit.reveal_CutoffNodeAndKeepLeft();
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

    lemma ReprSeqDisjointPrepend(t: MutBucket, s: seq<MutBucket>)
    requires MutBucket.ReprSeqDisjoint(s)
    requires MutBucket.ReprSeq(s) !! t.Repr
    ensures MutBucket.ReprSeqDisjoint([t] + s)
    {
      MutBucket.reveal_ReprSeqDisjoint();
      MutBucket.reveal_ReprSeq();
    }

    lemma ReprSeqPrepend(t: MutBucket, s: seq<MutBucket>)
    ensures MutBucket.ReprSeq([t] + s) == MutBucket.ReprSeq(s) + t.Repr

    method CutoffNodeAndKeepRight(pivot: Key) returns (node': Node)
    requires Inv()
    requires IM.WFNode(I())
    ensures node'.Inv()
    //ensures fresh(node'.Repr)
    ensures node'.I() == ImplModelSplit.CutoffNodeAndKeepRight(old(I()), pivot);
    {
      ImplModelSplit.reveal_CutoffNodeAndKeepRight();
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
      assert node'.I().buckets == ImplModelSplit.CutoffNodeAndKeepRight(old(I()), pivot).buckets;
      assert node'.I().children == ImplModelSplit.CutoffNodeAndKeepRight(old(I()), pivot).children;
      assert node'.I().pivotTable == ImplModelSplit.CutoffNodeAndKeepRight(old(I()), pivot).pivotTable;
    }

    method CutoffNode(lbound: Option<Key>, rbound: Option<Key>)
    returns (node' : Node)
    requires Inv()
    requires IM.WFNode(I())
    ensures node'.Inv()
    //ensures fresh(node'.Repr)
    ensures node'.I() == ImplModelSplit.CutoffNode(old(I()), lbound, rbound)
    {
      ImplModelSplit.reveal_CutoffNode();
      match lbound {
        case None => {
          match rbound {
            case None => {
              node' := this;
            }
            case Some(rbound) => {
              node' := this.CutoffNodeAndKeepLeft(rbound);
            }
          }
        }
        case Some(lbound) => {
          match rbound {
            case None => {
              node' := this.CutoffNodeAndKeepRight(lbound);
            }
            case Some(rbound) => {
              var node1 := this.CutoffNodeAndKeepLeft(rbound);
              ImplModelSplit.CutoffNodeAndKeepLeftCorrect(this.I(), rbound);
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
    ensures node'.I() == old(ImplModelSplit.SplitChildLeft(I(), num_children_left as int))
    ensures fresh(node'.Repr)
    {
      ImplModelSplit.reveal_SplitChildLeft();
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
    ensures node'.Inv()
    ensures node'.I() == old(ImplModelSplit.SplitChildRight(I(), num_children_left as int))
    ensures fresh(node'.Repr)
    {
      ImplModelSplit.reveal_SplitChildRight();
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

    method InsertKeyValue(key: Key, value: IM.Message)
    requires Inv();
    requires IM.WFNode(I())
    requires WeightBucketList(MutBucket.ISeq(buckets)) + WeightKey(key) + WeightMessage(value) < 0x1_0000_0000_0000_0000
    modifies Repr
    ensures Inv();
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures I() == ImplModelInsert.NodeInsertKeyValue(old(I()), key, value)
    {
      ImplModelInsert.reveal_NodeInsertKeyValue();

      var r := Pivots.ComputeRoute(pivotTable, key);

      MutBucket.LemmaReprBucketLeReprSeq(buckets, r as int);
      WeightBucketLeBucketList(MutBucket.ISeq(buckets), r as int);

      buckets[r].Insert(key, value);

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
      assert I().buckets == ImplModelInsert.NodeInsertKeyValue(old(I()), key, value).buckets;
    }

    lemma LemmaReprSeqBucketsLeRepr()
    requires Inv()
    ensures MutBucket.ReprSeq(buckets) <= Repr
    {
    }
  }
}

module ImplMutCache {
  import opened ImplNode
  import opened Options
  import opened Maps
  import opened NativeTypes
  import opened MutableBucket
  import opened BucketWeights

  // TODO ARARGHGHESGKSG it sucks that we have to wrap this in a new object type
  // just to have a Repr field. It also sucks that we have to have a Repr field
  // at all instead of an opaque Repr() function, see
  // https://github.com/dafny-lang/dafny/issues/377
  class MutCache
  {
    var cache: MM.ResizingHashMap<Node>;
    ghost var Repr: set<object>;

    constructor()
    ensures Inv();
    ensures I() == map[]
    ensures fresh(Repr);
    {
      cache := new MM.ResizingHashMap(128);
      new;
      Repr := {this} + cache.Repr + MutCacheBucketRepr();
    }

    protected function MutCacheBucketRepr() : set<object>
    reads this, cache
    reads set ref | ref in cache.Contents :: cache.Contents[ref]
    {
      set ref, o | ref in cache.Contents && o in cache.Contents[ref].Repr :: o
    }

    protected predicate CacheReprDisjoint(contents: map<BT.G.Reference, Node>)
    reads set ref | ref in contents :: contents[ref]
    {
      forall ref1, ref2 | ref1 in contents && ref2 in contents && 
          ref1 != ref2 :: contents[ref1].Repr !! contents[ref2].Repr
    }

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    {
      && cache in Repr
      && (forall ref | ref in cache.Contents :: cache.Contents[ref] in Repr)
      && Repr == {this} + cache.Repr + MutCacheBucketRepr()
      && CacheReprDisjoint(cache.Contents)
      && (forall ref | ref in cache.Contents :: cache.Contents[ref].Repr !! cache.Repr)
      && (forall ref | ref in cache.Contents :: this !in cache.Contents[ref].Repr)
      && this !in cache.Repr
      && cache.Inv()
      && (forall ref | ref in cache.Contents :: cache.Contents[ref].Inv())
    }

    protected function I() : map<BT.G.Reference, IM.Node>
    reads this, Repr
    requires Inv()
    {
      map ref | ref in cache.Contents :: cache.Contents[ref].I()
    }

    protected function ptr(ref: BT.G.Reference) : Option<Node>
    reads Repr
    requires Inv()
    ensures ptr(ref).None? ==> ref !in I()
    ensures ptr(ref).Some? ==>
        && ref in I()
        && ptr(ref).value.Inv()
        && I()[ref] == ptr(ref).value.I()
    {
      if ref in cache.Contents then Some(cache.Contents[ref]) else None
    }

    method GetOpt(ref: BT.G.Reference)
    returns (node: Option<Node>)
    requires Inv()
    ensures node == ptr(ref)
    {
      node := cache.Get(ref);
    }

    lemma LemmaNodeReprLeRepr(ref: BT.G.Reference)
    requires Inv()
    ensures ptr(ref).Some? ==> ptr(ref).value.Repr <= Repr

    lemma LemmaSizeEqCount()
    requires Inv()
    ensures |I()| == |cache.Contents|

    protected function method Count() : (c : uint64)
    reads this, Repr
    requires Inv()
    ensures c as int == |I()|
    {
      LemmaSizeEqCount();
      cache.Count
    }

    method Insert(ref: BT.G.Reference, node: Node)
    requires Inv()
    requires node.Inv()
    requires Repr !! node.Repr
    requires |I()| <= 0x10000
    modifies Repr
    ensures Inv()
    ensures I() == old(I()[ref := node.I()])
    ensures forall o | o in Repr :: o in old(Repr) || o in old(node.Repr) || fresh(o)
    {
      LemmaSizeEqCount();
      cache.Insert(ref, node);
      assert cache.Contents[ref] == node;
      Repr := {this} + cache.Repr + MutCacheBucketRepr();

      assert Inv();
    }

    method Remove(ref: BT.G.Reference)
    requires Inv()
    modifies Repr
    ensures Inv()
    ensures I() == MapRemove1(old(I()), ref)
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      LemmaSizeEqCount();
      cache.Remove(ref);
      Repr := {this} + cache.Repr + MutCacheBucketRepr();

      assert Inv();
    }

    // This is used for the 'grow' operation.
    method MoveAndReplace(oldref: BT.G.Reference, newref: BT.G.Reference, node: Node)
    requires Inv()
    requires node.Inv()
    requires Repr !! node.Repr
    requires |I()| <= 0x10000
    requires oldref in I()
    modifies Repr
    ensures Inv()
    ensures I() == old(I()[newref := I()[oldref]][oldref := node.I()])
    ensures forall o | o in Repr :: o in old(Repr) || o in old(node.Repr) || fresh(o)
    {
      LemmaSizeEqCount();
      var oldnodeOpt := cache.Get(oldref);
      var oldnode := oldnodeOpt.value;
      cache.Insert(newref, oldnode);
      cache.Insert(oldref, node);

      Repr := {this} + cache.Repr + MutCacheBucketRepr();
      assert Inv();
    }

    // Like Insert, but with slightly different requires
    method Overwrite(ref: BT.G.Reference, node: Node)
    requires Inv()
    requires node.Inv()
    requires ref in I()
    requires forall o | o in node.Repr :: o in cache.Contents[ref].Repr || o !in Repr
    requires |I()| <= 0x10000
    modifies Repr
    ensures Inv()
    ensures I() == old(I()[ref := node.I()])
    ensures forall o | o in Repr :: o in old(Repr) || o in old(node.Repr) || fresh(o)
    {
      LemmaSizeEqCount();
      cache.Insert(ref, node);
      assert cache.Contents[ref] == node;
      Repr := {this} + cache.Repr + MutCacheBucketRepr();

      assert Inv();
    }

    method UpdateNodeSlot(ref: BT.G.Reference, slot: uint64, bucket: MutBucket, childref: BT.G.Reference)
    requires Inv()
    requires bucket.Inv()
    requires ref in I()
    requires I()[ref].children.Some?
    requires 0 <= slot as int < |I()[ref].children.value|
    requires 0 <= slot as int < |I()[ref].buckets|
    requires bucket.Repr !! Repr
    requires |I()| <= 0x10000
    modifies Repr
    ensures Inv()
    ensures I() == old(I()[ref := IM.Node(
        I()[ref].pivotTable,
        Some(I()[ref].children.value[slot as int := childref]),
        I()[ref].buckets[slot as int := bucket.Bucket]
      )])
    ensures forall o | o in Repr :: o in old(Repr) || o in old(bucket.Repr) || fresh(o)
    {
      var nodeOpt := cache.Get(ref);
      var node := nodeOpt.value;
      node.UpdateSlot(slot, bucket, childref);

      Repr := {this} + cache.Repr + MutCacheBucketRepr();
      assert Inv();
    }

    method SplitParent(ref: BT.G.Reference, slot: uint64, pivot: Key, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
    requires Inv()
    requires ref in I()
    requires IM.WFNode(I()[ref])
    requires I()[ref].children.Some?
    requires 0 <= slot as int < |I()[ref].children.value|
    requires 0 <= slot as int < |I()[ref].buckets|
    requires |I()| <= 0x10000
    modifies Repr
    ensures Inv()
    ensures I() == old(I()[ref := ImplModelSplit.SplitParent(I()[ref], pivot, slot as int, left_childref, right_childref)])
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      var nodeOpt := GetOpt(ref);
      var node := nodeOpt.value;
      node.SplitParent(slot, pivot, left_childref, right_childref);

      Repr := {this} + cache.Repr + MutCacheBucketRepr();
      assert Inv();
    }

    method InsertKeyValue(ref: BT.G.Reference, key: Key, msg: IM.Message)
    requires Inv()
    requires ref in I()
    requires IM.WFNode(I()[ref])
    requires WeightBucketList(I()[ref].buckets) + WeightKey(key) + WeightMessage(msg) < 0x1_0000_0000_0000_0000
    modifies Repr
    ensures Inv()
    ensures I() == old(ImplModelInsert.CacheInsertKeyValue(I(), ref, key, msg))
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      ImplModelInsert.reveal_CacheInsertKeyValue();

      var nodeOpt := GetOpt(ref);
      var node := nodeOpt.value;
      node.InsertKeyValue(key, msg);

      Repr := {this} + cache.Repr + MutCacheBucketRepr();
      assert Inv();
    }
  }
}
