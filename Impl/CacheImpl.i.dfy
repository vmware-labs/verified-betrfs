include "../lib/Base/DebugAccumulator.i.dfy"
include "NodeImpl.i.dfy"
//
// Implements map<Reference, Node>
//
// TODO(thance): We need a CacheModel, because this is taking too big a leap
// from map<Reference, Node>.
//

module CacheImpl {
  import DebugAccumulator
  import opened NodeImpl
  import opened Options
  import opened Maps
  import opened NativeTypes
  import opened BucketImpl
  import opened BucketWeights
  import opened KeyType
  import opened ValueMessage
  import NodeModel

  // TODO ARARGHGHESGKSG it sucks that we have to wrap this in a new object type
  // just to have a Repr field. It also sucks that we have to have a Repr field
  // at all instead of an opaque Repr() function, see
  // https://github.com/dafny-lang/dafny/issues/377
  class MutCache
  {
    var cache: MM.ResizingHashMap<Node>;
    ghost var Repr: set<object>;

    method DebugAccumulate()
    returns (acc:DebugAccumulator.DebugAccumulator)
    requires false
    {
      acc := DebugAccumulator.EmptyAccumulator();
      var a := new DebugAccumulator.AccRec(cache.Count, "Node");
      acc := DebugAccumulator.AccPut(acc, "cache", a);
    }

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
    {
    }

    lemma LemmaSizeEqCount()
    requires Inv()
    ensures |I()| == |cache.Contents|
    {
      assert I().Keys == cache.Contents.Keys;
      assert |I()|
          == |I().Keys|
          == |cache.Contents.Keys|
          == |cache.Contents|;
    }

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
    ensures forall r | r != ref :: ptr(r) == old(ptr(r))
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

    method UpdateNodeSlot(ghost ref: BT.G.Reference, node: Node, slot: uint64, bucket: MutBucket, childref: BT.G.Reference)
    requires Inv()
    requires bucket.Inv()
    requires ref in I()
    requires I()[ref].children.Some?
    requires 0 <= slot as int < |I()[ref].children.value|
    requires 0 <= slot as int < |I()[ref].buckets|
    requires slot as int + 1 < 0x1_0000_0000_0000_0000
    requires bucket.Repr !! Repr
    requires |I()| <= 0x10000
    requires ptr(ref) == Some(node)
    modifies Repr
    ensures Inv()
    ensures I() == old(I()[ref := IM.Node(
        I()[ref].pivotTable,
        Some(I()[ref].children.value[slot as int := childref]),
        I()[ref].buckets[slot as int := bucket.Bucket]
      )])
    ensures forall o | o in Repr :: o in old(Repr) || o in old(bucket.Repr) || fresh(o)
    {
      //var nodeOpt := cache.Get(ref);
      //var node := nodeOpt.value;
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
    ensures I() == old(I()[ref := NodeModel.SplitParent(I()[ref], pivot, slot as int, left_childref, right_childref)])
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      var nodeOpt := GetOpt(ref);
      var node := nodeOpt.value;
      node.SplitParent(slot, pivot, left_childref, right_childref);

      Repr := {this} + cache.Repr + MutCacheBucketRepr();
      assert Inv();
    }

    method InsertKeyValue(ref: BT.G.Reference, key: Key, msg: Message)
    requires Inv()
    requires ref in I()
    requires IM.WFNode(I()[ref])
    requires WeightBucketList(I()[ref].buckets) + WeightKey(key) + WeightMessage(msg) < 0x1_0000_0000_0000_0000
    modifies Repr
    ensures Inv()
    ensures I() == old(NodeModel.CacheInsertKeyValue(I(), ref, key, msg))
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      NodeModel.reveal_CacheInsertKeyValue();

      var nodeOpt := GetOpt(ref);
      var node := nodeOpt.value;
      node.InsertKeyValue(key, msg);

      Repr := {this} + cache.Repr + MutCacheBucketRepr();
      assert Inv();
    }
  }
}
