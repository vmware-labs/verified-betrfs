include "../lib/MutableMap.i.dfy"
include "ImplModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "MutableBucket.i.dfy"

module ImplNode {
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import TTT = TwoThreeTree
  import IM = ImplModel

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BetreeGraphBlockCache
  import D = AsyncSectorDisk
  import MainDiskIOHandler
  import LruModel
  import MutableLru
  import MutableBucket
  import opened Bounds
  import opened BucketsLib

  import MM = MutableMap
  import ReferenceType`Internal

  predicate {:opaque} BucketListReprDisjoint(buckets: seq<MutableBucket.MutBucket>)
  reads set i | 0 <= i < |buckets| :: buckets[i]
  {
    forall i, j | 0 <= i < |buckets| && 0 <= j < |buckets| && i != j ::
        buckets[i].Repr !! buckets[j].Repr
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
    {
      this.pivotTable := pivotTable;
      this.children := children;
      this.buckets := buckets;

      new;

      this.Repr := {this} + ComputeRepr();
    }

    protected function ComputeRepr() : set<object>
    reads this
    reads set i | 0 <= i < |buckets| :: buckets[i]
    {
      set i, o | 0 <= i < |buckets| && o in buckets[i].Repr :: o
    }


    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    ensures Inv() ==>
      forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    {
      && (forall i | 0 <= i < |buckets| :: buckets[i] in Repr)
      && Repr == {this} + ComputeRepr()
      && BucketListReprDisjoint(buckets)

      && (forall i | 0 <= i < |buckets| :: buckets[i].Inv())
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
  }

  // Some helpful lemmas

  /*lemma LemmaReprCacheInsert(cache: map<BT.G.Reference, Node>, ref: BT.G.Reference, node: Node, s: Variables)
  requires s.cache.Contents == cache[ref := node]
  requires CacheRepr(cache) !! node.Repr
  requires CacheRepr(cache) !! s.NonBucketsRepr()
  requires node.Repr !! s.NonBucketsRepr()
  requires CacheReprInv_(cache)
  requires BucketListReprInv(node.buckets)
  ensures CacheRepr(s.cache.Contents) !! s.NonBucketsRepr()
  ensures CacheReprInv_(s.cache.Contents)
  ensures BucketsInv_(s.cache.Contents, CacheRepr(s.cache.Contents))*/

  /*method CacheInsert(k: M.Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.W()
  requires s.ready
  requires node.Repr !! s.Repr()
  requires WFNode(node)
  requires |s.cache.Contents| <= MaxCacheSize();
  modifies s.Repr()
  ensures s.W()
  ensures forall o | o in s.Repr() :: fresh(o) || o in old(s.Repr()) || o in old(node.Repr)
  ensures s.I() == old(s.I()).(cache := old(s.I()).cache[ref := INode(node)])
  {
    var _ := s.cache.Insert(ref, node);

    s.uucketRepr := CacheRepr(s.cache.Contents);

    reveal_BucketListReprInv();
    reveal_CacheRepr();
    reveal_Cache_();
    reveal_CacheReprInv_();
  }*/

}
