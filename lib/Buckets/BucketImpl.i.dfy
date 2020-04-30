include "../DataStructures/KMBtree.i.dfy"
include "PackedKV.i.dfy"
include "KVList.i.dfy"
include "../../PivotBetree/Bounds.i.dfy"
include "BucketIteratorModel.i.dfy"
include "BucketModel.i.dfy"
include "KVListPartialFlush.i.dfy"
include "KMBPKVOps.i.dfy"

//
// Collects singleton message insertions efficiently, avoiding repeated
// replacement of the immutable root Node. Once this bucket is full,
// it is flushed into the root in a batch.
// This module implements PivotBetreeSpec.Bucket (the model for class
// MutBucket).
// The MutBucket class also supplies Iterators using the functional
// Iterator datatype from BucketIteratorModel, which is why there is no
// BucketIteratorImpl module/class.
// TODO(robj): Littered with assume false!?

module BucketImpl {
  import KMB = KMBtree`API
  import KMBBOps = KMBtreeBulkOperations
  import KVList
  import PackedKV
  import opened ValueMessage`Internal
  import opened Lexicographic_Byte_Order_Impl
  import opened Sequences
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened Bounds
  import opened BucketWeights
  import opened NativeTypes
  import opened KeyType
  import BucketIteratorModel
  import Pivots = PivotsLib
  import opened BucketModel
  import opened DPKV = DynamicPkv
  import KMBPKVOps
  
  type TreeMap = KMB.Node

  // TODO(robj): get rid of these last vestiges of kvl by converting directly from pkv to tree.
  method kvl_to_tree(kvl : KVList.Kvl)
  returns (tree: TreeMap)
  requires KVList.WF(kvl)
  requires |kvl.keys| < Uint64UpperBound() - 1
  ensures KMB.WF(tree)
  ensures forall k | k in KMB.Interpretation(tree) :: |k| <= KeyType.MaxLen() as nat
  ensures KVList.I(kvl) == B(KMB.Interpretation(tree))
  {
    var modelkvl := KMB.Model.KVList(kvl.keys, kvl.messages);
    tree := KMBBOps.BuildTreeForSequence(modelkvl);
    assume false;
  }

  method pkv_to_kvl(pkv: PackedKV.Pkv)
  returns (kvl: KVList.Kvl)
  requires PackedKV.WF(pkv)
  ensures KVList.WF(kvl)
  ensures KVList.I(kvl) == PackedKV.I(pkv)
  {
    assume false;
    var n := |pkv.keys.offsets| as uint64;
    var keys := new Key[n];
    var messages := new Message[n];
    var i: uint64 := 0;
    while i < n {
      keys[i] := PackedKV.GetKey(pkv, i);
      messages[i] := PackedKV.GetMessage(pkv, i);
      i := i + 1;
    }
    return KVList.Kvl(keys[..], messages[..]);
  }

  method pkv_to_tree(pkv: PackedKV.Pkv)
  returns (tree: TreeMap)
  requires PackedKV.WF(pkv)
  ensures KMB.WF(tree)
  ensures forall k | k in KMB.Interpretation(tree) :: |k| <= KeyType.MaxLen() as nat
  ensures PackedKV.I(pkv) == B(KMB.Interpretation(tree))
  {
    var kv := pkv_to_kvl(pkv);
    assume |kv.keys| < Uint64UpperBound() - 1;
    tree := kvl_to_tree(kv);
  }

  method tree_to_pkv(tree: TreeMap) returns (pkv : PackedKV.Pkv)
    requires KMB.WF(tree)
    requires KMBBOps.NumElements(tree) < Uint64UpperBound()
    requires forall k | k in KMB.Interpretation(tree) :: |k| <= KeyType.MaxLen() as nat
    ensures PackedKV.WF(pkv)
    ensures PackedKV.I(pkv) == B(KMB.Interpretation(tree))
  {
    pkv := KMBPKVOps.ToPkv(tree);
    assume false;
  }
  
  datatype Iterator = Iterator(
    ghost next: BucketIteratorModel.IteratorOutput,
    i: uint64,
    ghost decreaser: int)

  function IIterator(it: Iterator) : BucketIteratorModel.Iterator
  {
    BucketIteratorModel.Iterator(it.next, it.i as int, it.decreaser)
  }

  datatype BucketFormat =
      | BFTree
      | BFPkv

  class MutBucket {
    var format: BucketFormat;

    var tree: KMB.Node?;
    var pkv: PackedKV.Pkv;
    
    var Weight: uint64;
    var sorted: bool
    
    ghost var Repr: set<object>;
    ghost var Bucket: Bucket;

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    ensures Inv() ==> Weight as int == WeightBucket(Bucket)
    ensures Inv() ==> WFBucket(Bucket)
    {
      && this in Repr
      && (format.BFTree? ==> (
        && tree != null
        && tree in Repr
        && tree.repr <= Repr
        && KMB.WF(tree)
        && Weight as int < Uint64UpperBound()
        && forall k | k in KMB.Interpretation(tree) :: |k| <= KeyType.MaxLen() as nat
        && var interp := map k: Key | k in KMB.Interpretation(tree) :: KMB.Interpretation(tree)[k];
        && Bucket == B(interp)
      ))
      && (format.BFPkv? ==> (
        && tree == null
        && PackedKV.WF(pkv)
        && Bucket == PackedKV.I(pkv)
      ))
      && WFBucket(Bucket)
      && (Weight as int == WeightBucket(Bucket))
      && (sorted ==> BucketWellMarshalled(Bucket))
    }

    constructor()
    ensures Bucket == EmptyBucket()
    ensures Inv()
    ensures fresh(Repr)
    {
      this.format := BFTree;
      this.sorted := true;
      this.Weight := 0;
      var tmp := KMB.EmptyTree();
      this.tree := tmp;
      this.Repr := {this} + tmp.repr;
      this.Bucket := EmptyBucket();
    }

    constructor InitFromPkv(pkv: PackedKV.Pkv, is_sorted: bool)
      requires PackedKV.WF(pkv)
      requires is_sorted ==> BucketWellMarshalled(PackedKV.I(pkv))
      ensures I() == PackedKV.I(pkv)
      ensures Inv()
      ensures fresh(Repr)
    {
      this.format := BFPkv;
      this.pkv := pkv;
      this.Weight := PackedKV.WeightPkv(pkv);
      this.Repr := {this};
      this.Bucket := PackedKV.I(pkv);
      this.tree := null;
      this.sorted := is_sorted;
      new;
      assume Weight as int == WeightBucket(Bucket);
      assume WFBucket(Bucket);
    }

    lemma NumElementsLteWeight(bucket: Bucket)
      ensures |bucket.b| < WeightBucket(bucket)
    {
      assume false;
    }
    
    method GetPkv() returns (pkv: PKV.Pkv)
    requires Inv()
    ensures PKV.WF(pkv)
    ensures PKV.I(pkv) == Bucket
    {
      if (format.BFTree?) {
        NumElementsLteWeight(B(KMB.Interpretation(tree)));
        assume false;
        pkv := tree_to_pkv(tree);
      } else {
        pkv := this.pkv;
      }
    }

    method WellMarshalled() returns (b: bool)
      requires Inv()
      ensures b == BucketWellMarshalled(Bucket)
      // ensures Inv()
      // ensures Bucket == old(Bucket)
      // ensures Repr == old(Repr)
      // modifies this
    {
      assume false;
      if (format.BFTree?) {
        b := true;
      } else {
        if sorted {
          b := true;
        } else {
          b := PackedKV.ComputeIsSorted(pkv);
          assert Bucket.keys == PackedKV.PSA.I(pkv.keys); // observe
          //sorted := b; // Repr hell
        }
      }
    }

    method Empty() returns (result: bool)
      requires Inv()
      ensures result == (|I().b| == 0)
    {
      assume false;
      if (format.BFTree?) {
        result := KMB.Empty(tree);
      } else {
        assume false;
        result := 0 == |pkv.keys.offsets| as uint64;
      }
    }

    
    method WFBucketAt(pivots: Pivots.PivotTable, i: uint64) returns (result: bool)
      requires Inv()
      requires BucketWellMarshalled(I())
      requires Pivots.WFPivots(pivots)
      requires i as nat <= |pivots| < Uint64UpperBound()
      ensures result == BucketsLib.WFBucketAt(I(), pivots, i as nat)
    {
      var e := Empty();
      if e {
        return true;
      }

      assume 0 < |Bucket.keys|; // Need to fill in defs in BucketsLib to prove this.
      assume false;  // Need to fill in defs in BucketsLib to prove correctness.
      
      
      if i < |pivots| as uint64 {
        var lastkey := GetLastKey();
        var c := cmp(lastkey, pivots[i]);
        if c >= 0 {
          return false;   // Need to fill in defs in BucketsLib to prove correctness.
        }
      }

      if 0 < i {
        var firstkey := GetFirstKey();
        var c := cmp(pivots[i-1], firstkey);
        if 0 < c {
          return false;    // Need to fill in defs in BucketsLib to prove correctness.
        }
      }

      return true;
    }
      
    
    static function {:opaque} ReprSeq(s: seq<MutBucket>) : set<object>
    reads s
    {
      set i, o | 0 <= i < |s| && o in s[i].Repr :: o
    }

    static twostate lemma ReprSeqDependsOnlyOnReprs(s: seq<MutBucket>)
      requires forall i | 0 <= i < |s| :: s[i].Repr == old(s[i].Repr)
      ensures ReprSeq(s) == old(ReprSeq(s))
    {
      reveal_ReprSeq();
    }
    
    
    static predicate {:opaque} InvSeq(s: seq<MutBucket>)
    reads s
    reads ReprSeq(s)
    // Yes this is dumb, to opaque the function and then specify it here anyway,
    // but this keeps the reveal_ReprSeq() from escaping
    ensures InvSeq(s) == (forall i | 0 <= i < |s| :: s[i].Inv())
    {
      reveal_ReprSeq();
      forall i | 0 <= i < |s| :: s[i].Inv()
    }

    function I() : Bucket
    reads this
    {
      this.Bucket
    }

    static function {:opaque} ISeq(s: seq<MutBucket>) : (bs : seq<Bucket>)
    reads s
    reads ReprSeq(s)
    ensures |bs| == |s|
    ensures forall i | 0 <= i < |s| :: bs[i] == s[i].Bucket
    decreases |s|
    {
      reveal_ReprSeq();
      if |s| == 0 then [] else ISeq(DropLast(s)) + [Last(s).I()]
    }

    static lemma ISeqInduction(s: seq<MutBucket>)
    requires |s| > 0
    ensures ISeq(s) == ISeq(DropLast(s)) + [Last(s).I()]
    {
    }

    static lemma ISeqAdditive(a: seq<MutBucket>, b: seq<MutBucket>)
    ensures ISeq(a + b) == ISeq(a) + ISeq(b)
    {
      if |b| == 0 {
        assert ISeq(a + b)
            == ISeq(a)
            == ISeq(a) + ISeq(b);
      } else {
        ISeqAdditive(a, b[..|b|-1]);
        assert ISeq(a + b)
            == ISeq((a + b)[..|a+b|-1]) + [(a+b)[|a+b|-1].I()]
            == ISeq(a + b[..|b|-1]) + [b[|b|-1].I()]
            == ISeq(a) + ISeq(b[..|b|-1]) + [b[|b|-1].I()]
            == ISeq(a) + ISeq(b);
      }
    }

    static twostate lemma AllocatedReprSeq(new s: seq<MutBucket>)
    ensures allocated(ReprSeq(s))
    {
      reveal_ReprSeq();
    }

    static twostate lemma FreshReprSeqOfFreshEntries(new s: seq<MutBucket>)
    requires forall i | 0 <= i < |s| :: fresh(s[i].Repr)
    ensures fresh(ReprSeq(s))
    {
      reveal_ReprSeq();
    }

    static lemma ReprSeqAdditive(a: seq<MutBucket>, b: seq<MutBucket>)
    ensures ReprSeq(a) + ReprSeq(b) == ReprSeq(a + b)
    {
      reveal_ReprSeq();
      var x := ReprSeq(a) + ReprSeq(b);
      var y := ReprSeq(a + b);
      forall o | o in x ensures o in y {
        if o in ReprSeq(a) {
          var i :| 0 <= i < |a| && o in a[i].Repr;
          assert o in (a+b)[i].Repr;
        } else {
          var i :| 0 <= i < |b| && o in b[i].Repr;
          assert o in (a+b)[i + |a|].Repr;
        }
      }
      forall o | o in y ensures o in x {
        var i :| 0 <= i < |a+b| && o in (a+b)[i].Repr;
        if i < |a| {
          assert o in a[i].Repr;
        } else {
          assert o in b[i-|a|].Repr;
        }
      }
    }

    static lemma ReprSeq1Eq(a: seq<MutBucket>)
    requires |a| == 1
    ensures ReprSeq(a) == a[0].Repr
    {
      reveal_ReprSeq();
    }

    static lemma LemmaReprBucketLeReprSeq(buckets: seq<MutBucket>, i: int)
    requires 0 <= i < |buckets|
    ensures buckets[i].Repr <= ReprSeq(buckets)
    {
      reveal_ReprSeq();
    }

    static predicate {:opaque} ReprSeqDisjoint(buckets: seq<MutBucket>)
    reads set i | 0 <= i < |buckets| :: buckets[i]
    {
      forall i, j | 0 <= i < |buckets| && 0 <= j < |buckets| && i != j ::
          buckets[i].Repr !! buckets[j].Repr
    }

    static twostate lemma ReprSeqDisjointDependsOnlyOnReprs(s: seq<MutBucket>)
      requires forall i | 0 <= i < |s| :: s[i].Repr == old(s[i].Repr)
      ensures ReprSeqDisjoint(s) == old(ReprSeqDisjoint(s))
    {
      reveal_ReprSeqDisjoint();
    }
    
    
    static lemma ReprSeqDisjointOfLen1(buckets: seq<MutBucket>)
    requires |buckets| <= 1
    ensures ReprSeqDisjoint(buckets)
    {
      reveal_ReprSeqDisjoint();
    }

    static lemma ReprSeqDisjointOfLen2(buckets: seq<MutBucket>)
    requires |buckets| == 2
    requires buckets[0].Repr !! buckets[1].Repr
    ensures ReprSeqDisjoint(buckets)
    {
      reveal_ReprSeqDisjoint();
    }

    static lemma ISeq_replace1with2(buckets: seq<MutBucket>, l: MutBucket, r: MutBucket, slot: int)
    requires InvSeq(buckets)
    requires 0 <= slot < |buckets|
    requires l.Inv()
    requires r.Inv()
    ensures InvSeq(replace1with2(buckets, l, r, slot))
    ensures ISeq(replace1with2(buckets, l, r, slot))
        == replace1with2(ISeq(buckets), l.I(), r.I(), slot);
    {
      var s := replace1with2(buckets, l, r, slot);
      forall i | 0 <= i < |s|
      ensures s[i].Inv()
      ensures ISeq(replace1with2(buckets, l, r, slot))[i]
          == replace1with2(ISeq(buckets), l.I(), r.I(), slot)[i]
      {
        if i == slot {
          assert s[i] == l;
        } else if i == slot+1 {
          assert s[i] == r;
        } else if i < slot {
          assert s[i] == buckets[i];
        } else {
          assert s[i] == buckets[i-1];
        }
      }
    }

    static lemma ReprSeqDisjointOfReplace1with2(
        buckets: seq<MutBucket>,
        l: MutBucket,
        r: MutBucket,
        slot: int)
    requires 0 <= slot < |buckets|
    requires ReprSeqDisjoint(buckets)
    requires l.Repr !! ReprSeq(buckets)
    requires r.Repr !! ReprSeq(buckets)
    requires l.Repr !! r.Repr
    ensures ReprSeqDisjoint(replace1with2(buckets, l, r, slot))
    {
      reveal_ReprSeqDisjoint();
      var buckets' := replace1with2(buckets, l, r, slot);
      forall i, j | 0 <= i < |buckets'| && 0 <= j < |buckets'| && i != j
      ensures buckets'[i].Repr !! buckets'[j].Repr
      {
        if i == slot {
          assert buckets'[i].Repr == l.Repr;
        }
        else if i == slot+1 {
          assert buckets'[i].Repr == r.Repr;
        }
        else if i < slot {
          assert buckets'[i].Repr == buckets[i].Repr;
          assert buckets[i].Repr <= ReprSeq(buckets) by { reveal_ReprSeq(); }
        }
        else {
          assert buckets'[i].Repr == buckets[i-1].Repr;
          assert buckets[i-1].Repr <= ReprSeq(buckets) by { reveal_ReprSeq(); }
        }

        if j == slot {
          assert buckets'[j].Repr == l.Repr;
        }
        else if j == slot+1 {
          assert buckets'[j].Repr == r.Repr;
        }
        else if j < slot {
          assert buckets'[j].Repr == buckets[j].Repr;
          assert buckets[j].Repr <= ReprSeq(buckets) by { reveal_ReprSeq(); }
        }
        else {
          assert buckets'[j].Repr == buckets[j-1].Repr;
          assert buckets[j-1].Repr <= ReprSeq(buckets) by { reveal_ReprSeq(); }
        }
      }
    }

    static lemma ListReprOfLen1(buckets: seq<MutBucket>)
    requires |buckets| == 1
    ensures ReprSeq(buckets) == buckets[0].Repr
    {
      reveal_ReprSeq();
    }

    static lemma ListReprOfLen2(buckets: seq<MutBucket>)
    requires |buckets| == 2
    ensures ReprSeq(buckets) == buckets[0].Repr + buckets[1].Repr
    {
      reveal_ReprSeq();
    }

    method Insert(key: Key, value: Message)
    requires Inv()
    requires Weight as int + WeightKey(key) + WeightMessage(value) < 0x1_0000_0000_0000_0000
    modifies Repr
    ensures Inv()
    ensures Bucket == BucketInsert(old(Bucket), key, value)
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      assume false;

      if format.BFPkv? {
        format := BFTree;
        tree := pkv_to_tree(pkv);
        var psa := PackedKV.PSA.Psa([], []);
        pkv := PackedKV.Pkv(psa, psa);
      }

      if value.Define? {
        var cur;
        tree, cur := KMB.Insert(tree, key, value);
        if (cur.Some?) {
          Weight := Weight - WeightMessageUint64(cur.value) + WeightMessageUint64(value) as uint64;
        } else {
          Weight := Weight + WeightKeyUint64(key) + WeightMessageUint64(value);
        }
      }

      Bucket := B(KMB.Interpretation(tree));
    }

    method Query(key: Key)
    returns (m: Option<Message>)
    requires Inv()
    ensures m == bucketBinarySearchLookup(I(), key)
    {
      assume false;
      if format.BFTree? {
        m := KMB.Query(tree, key);
      } else if format.BFPkv? {
        m := PackedKV.BinarySearchQuery(pkv, key);
      }
    }

    method SplitLeft(pivot: Key)
    returns (left: MutBucket)
    requires Inv()
    ensures left.Inv()
    ensures left.Bucket == SplitBucketLeft(Bucket, pivot)
    ensures fresh(left.Repr)
    {
      assume false;
      var pkv := GetPkv();
      //WeightSplitBucketLeft(Bucket, pivot);
      var pkvleft := PKV.SplitLeft(pkv, pivot);
      left := new MutBucket.InitFromPkv(pkvleft, sorted);
    }

    method SplitRight(pivot: Key)
    returns (right: MutBucket)
    requires Inv()
    ensures right.Inv()
    ensures right.Bucket == SplitBucketRight(Bucket, pivot)
    ensures fresh(right.Repr)
    {
      assume false;
      var pkv := GetPkv();
      //WeightSplitBucketRight(Bucket, pivot);
      var pkvright := PKV.SplitRight(pkv, pivot);
      right := new MutBucket.InitFromPkv(pkvright, sorted);
    }

    method SplitLeftRight(pivot: Key)
    returns (left: MutBucket, right: MutBucket)
    requires Inv()
    ensures left.Inv()
    ensures right.Inv()
    ensures left.Bucket == SplitBucketLeft(Bucket, pivot)
    ensures right.Bucket == SplitBucketRight(Bucket, pivot)
    ensures fresh(left.Repr)
    ensures fresh(right.Repr)
    ensures left.Repr !! right.Repr
    {
      left := SplitLeft(pivot);
      right := SplitRight(pivot);
    }

    static method SplitOneInList(buckets: seq<MutBucket>, slot: uint64, pivot: Key)
    returns (buckets' : seq<MutBucket>)
    requires InvSeq(buckets)
    requires ReprSeqDisjoint(buckets)
    requires 0 <= slot as int < |buckets|
    requires |buckets| < 0xffff_ffff_ffff_ffff
    ensures InvSeq(buckets')
    ensures ReprSeqDisjoint(buckets')
    ensures ISeq(buckets') == old(SplitBucketInList(ISeq(buckets), slot as int, pivot))
    ensures forall o | o in ReprSeq(buckets') :: o in old(ReprSeq(buckets)) || fresh(o)
    {
      AllocatedReprSeq(buckets);

      var l, r := buckets[slot].SplitLeftRight(pivot);
      buckets' := Replace1with2(buckets, l, r, slot);

      ghost var ghosty := true;
      if ghosty {
        reveal_ISeq();
        reveal_SplitBucketInList();
        ISeq_replace1with2(buckets, l, r, slot as int);
        ReprSeqDisjointOfReplace1with2(buckets, l, r, slot as int);
        forall o | o in ReprSeq(buckets')
        ensures o in old(ReprSeq(buckets)) || fresh(o)
        {
          reveal_ReprSeq();
          var i :| 0 <= i < |buckets'| && o in buckets'[i].Repr;
          if i < slot as int {
            assert o in buckets[i].Repr;
          } else if i == slot as int {
            assert fresh(o);
          } else if i == slot as int + 1 {
            assert fresh(o);
          } else {
            assert o in buckets[i-1].Repr;
          }
        }
      }
    }

    method GetFirstKey() returns (result: Key)
      requires Inv()
      requires BucketWellMarshalled(Bucket)
      requires 0 < |Bucket.keys|
      ensures result in Bucket.keys
      ensures forall k | k in Bucket.keys :: Ord.lte(result, k)
    {
      if format.BFTree? {
        assume false; // Need to fill in BucketsLib to prove 0 < |Interpretation(tree)|
        result := KMB.MinKey(tree);
      } else if format.BFPkv? {
        assume false;
        result := PackedKV.FirstKey(pkv);
      }
    }
    
    method GetMiddleKey() returns (res: Key)
    requires Inv()
    ensures getMiddleKey(I()) == res
    {
      var pkv;

      if format.BFPkv? {
        pkv := this.pkv;
      } else {
        assume false;
        pkv := tree_to_pkv(tree);
      }
      
      if |pkv.keys.offsets| as uint64 == 0 {
        return [0];
      } else {
        var key := PackedKV.GetKey(pkv, |pkv.keys.offsets| as uint64 / 2);
        if |key| as uint64 == 0 {
          return [0];
        } else {
          assume false;
          return key;
        }
      }
    }

    method GetLastKey() returns (result: Key)
      requires Inv()
      requires BucketWellMarshalled(Bucket)
      requires 0 < |Bucket.keys|
      ensures result in Bucket.keys
      ensures forall k | k in Bucket.keys :: Ord.lte(k, result)
    {
      if format.BFTree? {
        assume false; // Need to fill in BucketsLib to prove 0 < |Interpretation(tree)|
        result := KMB.MaxKey(tree);
      } else if format.BFPkv? {
        assume false;
        result := PackedKV.LastKey(pkv);
      }
    }
    
    static method computeWeightOfSeq(buckets: seq<MutBucket>)
    returns (weight: uint64)
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    requires WeightBucketList(ISeq(buckets)) < 0x1_0000_0000_0000_0000
    requires |buckets| < 0x1_0000_0000_0000_0000
    ensures weight as int == WeightBucketList(old(ISeq(buckets)))
    {
      reveal_WeightBucketList();

      ghost var bs := old(ISeq(buckets));

      var w := 0;
      var j: uint64 := 0;
      while j < |buckets| as uint64
      invariant 0 <= j as int <= |buckets|
      invariant w as int == WeightBucketList(bs[0..j]);
      {
        assert DropLast(bs[0..j+1]) == bs[0..j];
        assert Last(bs[0..j+1]) == buckets[j].I();
        WeightBucketListSlice(bs, 0, j as int + 1);

        w := w + buckets[j].Weight;
        j := j + 1;
      }
      assert bs[0..|buckets|] == bs;
      return w;
    }

    static lemma Islice(buckets: seq<MutBucket>, a: int, b: int)
    requires 0 <= a <= b <= |buckets|
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    ensures forall i | 0 <= i < |buckets[a..b]| :: buckets[a..b][i].Inv()
    ensures ISeq(buckets[a..b]) == ISeq(buckets)[a..b]
    {
      if b == |buckets| {
        if (a == b) {
        } else {
          Islice(DropLast(buckets), a, b - 1);
        }
      } else {
        Islice(DropLast(buckets), a, b);
      }
    }

    static lemma Isuffix(buckets: seq<MutBucket>, a: int)
    requires 0 <= a <= |buckets|
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    ensures forall i | 0 <= i < |buckets[a..]| :: buckets[a..][i].Inv()
    ensures ISeq(buckets[a..]) == ISeq(buckets)[a..]
    {
      Islice(buckets, a, |buckets|);
    }

    method Clone() returns (bucket': MutBucket)
    requires Inv()
    ensures bucket'.Inv()
    ensures fresh(bucket'.Repr)
    ensures this.Bucket == bucket'.Bucket
    {
      if format.BFPkv? {
        bucket' := new MutBucket.InitFromPkv(pkv, sorted);
        return;
      }

      var pkv;
      if format.BFTree? {
        assume false; // NumElements issue
        pkv := tree_to_pkv(tree);
      } 
      bucket' := new MutBucket.InitFromPkv(pkv, true);
    }

    static method CloneSeq(buckets: seq<MutBucket>) returns (buckets': seq<MutBucket>)
    requires InvSeq(buckets)
    requires |buckets| < 0x1_0000_0000_0000_0000;
    ensures InvSeq(buckets')
    ensures fresh(ReprSeq(buckets'))
    ensures |buckets'| == |buckets|
    ensures ISeq(buckets) == ISeq(buckets')
    ensures ReprSeqDisjoint(buckets')
    {
      var ar := new MutBucket?[|buckets| as uint64];
      var j: uint64 := 0;
      while j < |buckets| as uint64
      invariant 0 <= j as int <= |buckets|
      invariant ar.Length == |buckets|
      invariant forall i | 0 <= i < j as int :: ar[i] != null
      invariant forall i | 0 <= i < j as int :: ar !in ar[i].Repr
      invariant forall i | 0 <= i < j as int :: ar[i].Inv()
      invariant forall i | 0 <= i < j as int :: ar[i].I() == buckets[i].I()
      invariant forall i | 0 <= i < j as int :: fresh(ar[i].Repr)
      invariant forall i, i' | 0 <= i < j as int && 0 <= i' < j as int && i != i' :: ar[i].Repr !! ar[i'].Repr
      modifies ar
      {
        ar[j] := buckets[j].Clone();
        j := j + 1;
      }
      buckets' := ar[..];

      reveal_InvSeq();
      reveal_ReprSeq();
      reveal_ReprSeqDisjoint();
    }

    protected predicate WFIter(it: Iterator)
    reads this, this.Repr
    ensures this.WFIter(it) ==> this.Inv()
    ensures this.WFIter(it) ==> BucketIteratorModel.WFIter(I(), IIterator(it))
    {
      && this.Inv()
      && BucketIteratorModel.WFIter(I(), IIterator(it))
    }

    static function method makeIter(ghost bucket: Bucket, idx: uint64)
        : (it': Iterator)
    requires WFBucket(bucket)
    requires |bucket.keys| == |bucket.msgs|
    requires 0 <= idx as int <= |bucket.keys|
    ensures IIterator(it')
      == BucketIteratorModel.iterForIndex(bucket, idx as int)
    {
      Iterator(
          (if idx as int == |bucket.keys| then BucketIteratorModel.Done
              else BucketIteratorModel.Next(bucket.keys[idx], bucket.msgs[idx])),
          idx,
          |bucket.keys| - idx as int)
    }

    method IterStart() returns (it': Iterator)
    requires Inv()
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterStart(I())
    {
      BucketIteratorModel.reveal_IterStart();
      it' := makeIter(I(), 0);
    }

    method IterFindFirstGte(key: Key) returns (it': Iterator)
    requires Inv()
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterFindFirstGte(I(), key)
    {
      BucketIteratorModel.reveal_IterFindFirstGte();
      var pkv := GetPkv();
      var i: uint64 := PSA.BinarySearchIndexOfFirstKeyGte(pkv.keys, key);
      it' := makeIter(I(), i);
    }

    method IterFindFirstGt(key: Key) returns (it': Iterator)
    requires Inv()
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterFindFirstGt(I(), key)
    {
      BucketIteratorModel.reveal_IterFindFirstGt();
      var pkv := GetPkv();
      var i: uint64 := PSA.BinarySearchIndexOfFirstKeyGt(pkv.keys, key);
      it' := makeIter(I(), i);
    }

    method IterInc(it: Iterator) returns (it': Iterator)
    requires Inv()
    requires IIterator(it).next.Next?
    requires this.WFIter(it)
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterInc(I(), IIterator(it))
    {
      BucketIteratorModel.lemma_NextFromIndex(I(), IIterator(it));
      assume false;

      BucketIteratorModel.reveal_IterInc();
      it' := makeIter(I(), it.i + 1);
    }

    method GetNext(it: Iterator) returns (next : BucketIteratorModel.IteratorOutput)
    requires Inv()
    requires this.WFIter(it)
    ensures next == IIterator(it).next
    {
      var pkv;
      
      if format.BFPkv? {
        pkv := this.pkv;
      } else {
        assume KMBBOps.NumElements(tree) < Uint64UpperBound();
        pkv := tree_to_pkv(tree);
      }

      assume false;

      BucketIteratorModel.lemma_NextFromIndex(I(), IIterator(it));
        
      if it.i == |pkv.keys.offsets| as uint64 {
        next := BucketIteratorModel.Done;
      } else {
        //assert BucketIteratorModel.WFIter(I(), IIterator(it));
        //assert PackedKV.PSA.I(pkv.keys) == I().keys;
        next := BucketIteratorModel.Next(PackedKV.GetKey(pkv, it.i), PackedKV.GetMessage(pkv, it.i));
      }
    }
  }

  method PartialFlush(top: MutBucket, bots: seq<MutBucket>, pivots: seq<Key>)
    returns (newtop: MutBucket, newbots: seq<MutBucket>, ghost flushedKeys: set<Key>)
    requires top.Inv()
    requires forall i | 0 <= i < |bots| :: bots[i].Inv()
    requires |pivots| + 1 == |bots| < Uint64UpperBound()
    requires PivotsLib.WFPivots(pivots)
    requires WeightBucketList(MutBucket.ISeq(bots)) <= MaxTotalBucketWeight()
    requires BucketWellMarshalled(top.I())
    requires BucketListWellMarshalled(MutBucket.ISeq(bots))
    ensures forall i | 0 <= i < |newbots| :: newbots[i].Inv()
    //ensures forall i | 0 <= i < |newbots| :: fresh(newbots[i].Repr)
    ensures fresh(MutBucket.ReprSeq(newbots))
    ensures MutBucket.ReprSeqDisjoint(newbots)
    ensures newtop.Inv()
    ensures fresh(newtop.Repr)
    ensures newtop.Repr !! MutBucket.ReprSeq(newbots)
    // shouldn't need old in the line below, but dafny doesn't see
    // that WeightBucketList(MutBucket.ISeq(bots)) <=
    // MaxTotalBucketWeight() still holds after the function returns.
    ensures partialFlushResult(newtop.I(), MutBucket.ISeq(newbots), flushedKeys) == BucketModel.partialFlush(top.I(), old(MutBucket.ISeq(bots)), pivots)
  {
    var i: uint64 := 0;
    var totalWeight := 0;
    var botPkvs: array<PKV.Pkv> := new PKV.Pkv[|bots| as uint64];
    while i < |bots| as uint64
      invariant i as nat <= |bots|
    {
      botPkvs[i] := bots[i].GetPkv();
      assume false;
      totalWeight := totalWeight + PKV.WeightPkv(botPkvs[i]);
      i := i + 1;
    }

    assume false;

    var topPkv := top.GetPkv();
    
    var result := MergeToChildren(topPkv, pivots, botPkvs[..], MaxTotalBucketWeightUint64() - totalWeight);

    newtop := new MutBucket.InitFromPkv(result.top, true);

    var anewbots := new MutBucket[|result.bots| as uint64];
    i := 0;
    while i < |result.bots| as uint64
      invariant i as nat <= |result.bots|
    {
      anewbots[i] := new MutBucket.InitFromPkv(result.bots[i], true);
      i := i + 1;
    }

    newbots := anewbots[..];
    assume false;
  }
}

