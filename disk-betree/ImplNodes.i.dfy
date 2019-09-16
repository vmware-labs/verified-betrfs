include "../lib/MutableMap.i.dfy"
include "ImplModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "MutableBucket.i.dfy"
include "ImplModelSplit.i.dfy"

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
  import ImplModelSplit

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
    ensures (forall i | 0 <= i < |buckets| :: this !in buckets[i].Repr)
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
      assert SplitBucketInList(I().buckets, slot as int, pivot)
          == b.buckets;

      this.pivotTable := Sequences.insert(this.pivotTable, pivot, slot as int);

      ghost var node2 := I();

      var bucks := MutBucket.SplitOneInList(this.buckets, slot, pivot);
      assert forall o | o in MutBucket.ReprSeq(bucks) :: o in MutBucket.ReprSeq(this.buckets) || fresh(o);
      //MutBucket.reveal_ReprSeq();
      assert MutBucket.ISeq(bucks) == SplitBucketInList(node2.buckets, slot as int, pivot);
      assert node2.buckets == old(I()).buckets;
      assert MutBucket.ISeq(bucks) == SplitBucketInList(old(I()).buckets, slot as int, pivot);
      SplitParentReprSeqFacts(bucks);
      assert forall o :: o in MutBucket.ReprSeq(bucks) ==> allocated(o);
      assert forall i | 0 <= i < |bucks| :: bucks[i].Inv();
      assert forall i | 0 <= i < |bucks| :: this !in bucks[i].Repr;
      assert this !in MutBucket.ReprSeq(bucks);

      this.buckets := bucks;

      this.children := Some(replace1with2(children.value, left_childref, right_childref, slot as int));

      Repr := {this} + MutBucket.ReprSeq(buckets);
      LemmaReprFacts();
      assert Inv();
      assert forall o | o in Repr :: o in old(Repr) || fresh(o);
      ghost var a := I();
      assert a.buckets
          == SplitBucketInList(old(I()).buckets, slot as int, pivot)
          == b.buckets;
      assert a.children == b.children;
      assert a.pivotTable == b.pivotTable;
      assert a == b;
    }

    /*method CutoffNode(lbound: Option<Key>, rbound: Option<Key>) returns (node: Node)
    requires Inv()
    ensures node.Inv()
    ensures fresh(node.Repr)
    ensures 
    {
    }*/
  }
}

module ImplMutCache {
  import opened ImplNode
  import opened Options
  import opened Maps
  import opened NativeTypes
  import opened MutableBucket

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
      var _ := cache.Insert(ref, node);
      assert cache.Contents[ref] == node;
      Repr := {this} + cache.Repr + MutCacheBucketRepr();

      assert Inv();
    }

    method Remove(ref: BT.G.Reference)
    requires Inv()
    modifies Repr
    ensures Inv()
    ensures I() == MapRemove1(I(), ref)
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      LemmaSizeEqCount();
      var _ := cache.Remove(ref);
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
      var _ := cache.Insert(newref, oldnode);
      var _ := cache.Insert(oldref, node);

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
      var _ := cache.Insert(ref, node);
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

    /*method SplitParent(ref: BT.G.Reference, slot: uint64, pivot: Key, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
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
    }*/
  }
}
