include "../lib/MutableMap.i.dfy"
include "ImplModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "MutableBucket.i.dfy"

module ImplNode {
  import opened Options
  import opened Sequences
  import opened NativeTypes

  import IM = ImplModel
  import BT = PivotBetreeSpec`Internal
  import Pivots = PivotsLib
  import MutableBucket
  import opened Bounds

  import MM = MutableMap
  import ReferenceType`Internal

  predicate {:opaque} BucketListReprDisjoint(buckets: seq<MutableBucket.MutBucket>)
  reads set i | 0 <= i < |buckets| :: buckets[i]
  {
    forall i, j | 0 <= i < |buckets| && 0 <= j < |buckets| && i != j ::
        buckets[i].Repr !! buckets[j].Repr
  }

  lemma BucketListReprDisjointOfLen1(buckets: seq<MutableBucket.MutBucket>)
  requires |buckets| <= 1
  ensures BucketListReprDisjoint(buckets)
  {
    reveal_BucketListReprDisjoint();
  }

  lemma BucketListReprDisjointOfLen2(buckets: seq<MutableBucket.MutBucket>)
  requires |buckets| == 2
  requires buckets[0].Repr !! buckets[1].Repr
  ensures BucketListReprDisjoint(buckets)
  {
    reveal_BucketListReprDisjoint();
  }

  function {:opaque} MutBucketListRepr(buckets: seq<MutableBucket.MutBucket>) : set<object>
  reads buckets
  {
    set o, i | 0 <= i < |buckets| && o in buckets[i].Repr :: o
  }

  lemma MutBucketListReprOfLen2(buckets: seq<MutableBucket.MutBucket>)
  requires |buckets| == 2
  ensures MutBucketListRepr(buckets) == buckets[0].Repr + buckets[1].Repr
  {
    reveal_MutBucketListRepr();
  }

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
    requires BucketListReprDisjoint(buckets)
    ensures this.pivotTable == pivotTable;
    ensures this.children == children;
    ensures this.buckets == buckets;
    ensures Inv();
    ensures forall o | o in Repr :: fresh(o) || o in old(MutBucketListRepr(buckets))
    {
      this.pivotTable := pivotTable;
      this.children := children;
      this.buckets := buckets;

      new;

      this.Repr := {this} + MutBucketListRepr(buckets);
      reveal_MutBucketListRepr();
    }

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    ensures Inv() ==>
      forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    {
      && (forall i | 0 <= i < |buckets| :: buckets[i] in Repr)
      && Repr == {this} + MutBucketListRepr(buckets)
      && BucketListReprDisjoint(buckets)

      && (forall i | 0 <= i < |buckets| :: buckets[i].Inv())
    }

    lemma LemmaRepr()
    requires Inv()
    ensures Repr == {this} + MutBucketListRepr(buckets)
    {
    }

    function I() : IM.Node
    reads this, Repr
    requires Inv()
    {
      IM.Node(pivotTable, children,
        MutableBucket.MutBucket.ISeq(buckets))
    }
  }
}

module ImplMutCache {
  import opened ImplNode
  import opened Options
  import opened Maps

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

    method GetOpt(ref: BT.G.Reference)
    returns (node: Option<Node>)
    requires Inv()
    ensures node.Some? ==> node.value.Inv()
    ensures node.Some? ==> ref in I()
    ensures node.Some? ==> node.value.I() == I()[ref]
    ensures node.None? ==> ref !in I()
    {
      node := cache.Get(ref);
    }

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
  }
}
