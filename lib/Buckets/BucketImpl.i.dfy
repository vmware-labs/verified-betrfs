include "../DataStructures/KMBtree.i.dfy"
include "PackedKV.i.dfy"
include "KVList.i.dfy"
include "../../PivotBetree/Bounds.i.dfy"
include "BucketIteratorModel.i.dfy"
include "BucketModel.i.dfy"
include "KVListPartialFlush.i.dfy"

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
  import opened Lexicographic_Byte_Order
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
  import opened KVLPFlush = KVListPartialFlush
  
  type TreeMap = KMB.Node

  method tree_to_kvl(tree: TreeMap)
  returns (kvl : KVList.Kvl)
  requires KMB.WF(tree)
  requires KMBBOps.NumElements(tree) < Uint64UpperBound()
  ensures KVList.WF(kvl)
  ensures KVList.I(kvl) == B(KMB.Interpretation(tree))
  {
    var s := KMBBOps.ToSeq(tree);
    kvl := KVList.Kvl(s.0[..], s.1[..]);
    assume false;
    kvl := KVList.AmassKvl(kvl);  // TODO skip a seq-assembly step here
  }

  method kvl_to_tree(kvl : KVList.Kvl)
  returns (tree: TreeMap)
  requires KVList.WF(kvl)
  requires |kvl.keys| < Uint64UpperBound() - 1
  ensures KMB.WF(tree)
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
  ensures PackedKV.I(pkv) == B(KMB.Interpretation(tree))
  {
    var kv := pkv_to_kvl(pkv);
    assume |kv.keys| < Uint64UpperBound() - 1;
    tree := kvl_to_tree(kv);
  }

  datatype Iterator = Iterator(i: uint64)
  function IIterator(it: Iterator) : BucketIteratorModel.Iterator

  datatype BucketFormat =
      | BFTree
      | BFKvl
      | BFPkv

  class MutBucket {
    var format: BucketFormat;

    var tree: KMB.Node?;
    var kvl: KVList.Kvl;
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
      && (format.BFKvl? ==> (
        && tree == null
        && KVList.WF(kvl)
        && WeightBucket(KVList.I(kvl)) < Uint64UpperBound()
        && Bucket == KVList.I(kvl)
      ))
      && (format.BFTree? ==> (
        && tree != null
        && tree in Repr
        && tree.repr <= Repr
        && KMB.WF(tree)
        && Weight as int < Uint64UpperBound()
        && Bucket == B(KMB.Interpretation(tree))
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

    constructor(kv: KVList.Kvl)
    requires KVList.WF(kv)
    requires WeightBucket(KVList.I(kv)) < Uint64UpperBound()
    ensures Bucket == KVList.I(kv)
    ensures Inv()
    ensures fresh(Repr)
    {
      this.format := BFKvl;
      this.kvl := kv;
      this.tree := null;
      this.Repr := {this};
      var w := KVList.computeWeightKvl(kv);
      this.Weight := w;
      this.Bucket := KVList.I(kv);
      this.sorted := false;
      KVList.WFImpliesWFBucket(kv);
    }

    constructor InitWithWeight(kv: KVList.Kvl, w: uint64)
    requires KVList.WF(kv)
    requires WeightBucket(KVList.I(kv)) == w as int
    requires w as int < Uint64UpperBound()
    ensures Bucket == KVList.I(kv)
    ensures Inv()
    ensures fresh(Repr)
    {
      this.format := BFKvl;
      this.kvl := kv;
      this.tree := null;
      this.Repr := {this};
      this.Weight := w;
      this.Bucket := KVList.I(kv);
      this.sorted := false;
      KVList.WFImpliesWFBucket(kv);
    }

    constructor InitFromPkv(pkv: PackedKV.Pkv)
    requires PackedKV.WF(pkv)
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
      this.sorted := false;
      new;
      assume Weight as int == WeightBucket(Bucket);
      assume WFBucket(Bucket);
    }

    lemma NumElementsLteWeight(bucket: Bucket)
      ensures |bucket.b| < WeightBucket(bucket)
    {
      assume false;
    }
    
    method GetKvl() returns (kv: KVList.Kvl)
    requires Inv()
    ensures KVList.WF(kv)
    ensures KVList.I(kv) == Bucket
    {
      if (format.BFTree?) {
        NumElementsLteWeight(B(KMB.Interpretation(tree)));
        assume false;
        kv := tree_to_kvl(tree);
      } else if (format.BFKvl?) {
        kv := kvl;
      } else {
        var isSorted := PackedKV.ComputeIsSorted(pkv);
        if (!isSorted) {
          // TODO need to sort
          print "pkv is not sorted\n";
        }
        kv := pkv_to_kvl(pkv);
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
      if (format.BFTree?) {
        b := true;
      } else if (format.BFKvl?) {
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
      if (format.BFTree?) {
        result := KMB.Empty(tree);
      } else if (format.BFKvl?) {
        result := 0 == |kvl.keys| as uint64;
      } else {
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

      assume false;  // Need to fill in defs in BucketsLib to prove correctness.
      
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

    static method kvlSeqToMutBucketSeq(kvls: seq<KVList.Kvl>)
    returns (buckets : seq<MutBucket>)
    requires |kvls| < 0x1_0000_0000_0000_0000
    {
      assume false;
      var ar := new MutBucket?[|kvls| as uint64];
      var j: uint64 := 0;
      while j < |kvls| as uint64
      {
        ar[j] := new MutBucket(kvls[j]);
        j := j + 1;
      }
      return ar[..];
    }

    static method mutBucketSeqToKvlSeq(buckets: seq<MutBucket>)
    returns (kvls : seq<KVList.Kvl>)
    requires |buckets| < 0x1_0000_0000_0000_0000
    {
      assume false;
      var ar := new KVList.Kvl[|buckets| as uint64];
      var j: uint64 := 0;
      while j < |buckets| as uint64
      {
        ar[j] := buckets[j].GetKvl();
        j := j + 1;
      }
      return ar[..];
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

      if format.BFKvl? {
        format := BFTree;
        tree := kvl_to_tree(kvl);
        kvl := KVList.Kvl([], []); // not strictly necessary, but frees memory
      } else if format.BFPkv? {
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
      if format.BFTree? {
        m := KMB.Query(tree, key);
      } else if format.BFKvl? {
        KVList.lenKeysLeWeightOver4(kvl);
        m := KVList.Query(kvl, key);
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
      var kv := GetKvl();

      WeightSplitBucketLeft(Bucket, pivot);
      KVList.lenKeysLeWeightOver4(kv);
      var kvlLeft := KVList.SplitLeft(kv, pivot);
//      kvlLeft := KVList.AmassKvl(kvlLeft);
      left := new MutBucket(kvlLeft);
    }

    method SplitRight(pivot: Key)
    returns (right: MutBucket)
    requires Inv()
    ensures right.Inv()
    ensures right.Bucket == SplitBucketRight(Bucket, pivot)
    ensures fresh(right.Repr)
    {
      var kv := GetKvl();

      WeightSplitBucketRight(Bucket, pivot);
      KVList.lenKeysLeWeightOver4(kv);
      var kvlRight := KVList.SplitRight(kv, pivot);
//      kvlRight := KVList.AmassKvl(kvlRight);
      right := new MutBucket(kvlRight);
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
        assume ISeq(replace1with2(buckets, l, r, slot as int))
            == replace1with2(ISeq(buckets), l.I(), r.I(), slot as int);
        ReprSeqDisjointOfReplace1with2(buckets, l, r, slot as int);
        forall i | 0 <= i < |buckets'| ensures buckets'[i].Inv()
        {
          if i < slot as int {
            assert buckets[i].Inv();
            assert buckets'[i].Inv();
          } else if i == slot as int  {
            assert buckets'[i].Inv();
          } else if i == slot as int + 1 {
            assert buckets'[i].Inv();
          } else {
            assert buckets[i-1].Inv();
            assert buckets'[i].Inv();
          }
        }
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
      ensures forall k | k in Bucket.keys :: lte(result, k)
    {
      if format.BFTree? {
        assume false; // Need to fill in BucketsLib to prove 0 < |Interpretation(tree)|
        result := KMB.MinKey(tree);
      } else if format.BFKvl? {
        assume false; // Need to fill in BucketsLib to prove 0 < |KVPairs.PackedStringArray.I(kvl.keys)|
        result := kvl.keys[0];
      } else if format.BFPkv? {
        assume false;
        result := PackedKV.FirstKey(pkv);
      }
    }
    
    method GetMiddleKey() returns (res: Key)
    requires Inv()
    ensures getMiddleKey(I()) == res
    {
      if format.BFPkv? {
        if |pkv.keys.offsets| as uint64 == 0 {
          return [0];
        } else {
          var key := PackedKV.GetKey(pkv, |pkv.keys.offsets| as uint64 / 2);
          if |key| as uint64 == 0 {
            return [0];
          } else {
            return key;
          }
        }
      } else {
        var kvl := GetKvl();
        KVList.lenKeysLeWeightOver4(kvl);
        assume false;
        if |kvl.keys| as uint64 == 0 {
          return [0];
        } else {
          var key := kvl.keys[|kvl.keys| as uint64 / 2];
          if |key| as uint64 == 0 {
            return [0];
          } else {
            return key;
          }
        }
      }
    }

    method GetLastKey() returns (result: Key)
      requires Inv()
      requires BucketWellMarshalled(Bucket)
      requires 0 < |Bucket.keys|
      ensures result in Bucket.keys
      ensures forall k | k in Bucket.keys :: lte(k, result)
    {
      if format.BFTree? {
        assume false; // Need to fill in BucketsLib to prove 0 < |Interpretation(tree)|
        result := KMB.MaxKey(tree);
      } else if format.BFKvl? {
        assume false; // Need to fill in BucketsLib to prove 0 < |KVPairs.PackedStringArray.I(kvl.keys)|
        result := kvl.keys[|kvl.keys| as uint64 - 1];
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
        bucket' := new MutBucket.InitFromPkv(pkv);
        return;
      }

      var kv;
      if format.BFTree? {
        assume false; // NumElements issue
        kv := tree_to_kvl(tree);
      } else {
        kv := kvl;
      }
      bucket' := new MutBucket.InitWithWeight(kv, this.Weight);
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

    predicate WFIter(it: Iterator)
    reads this, this.Repr
    ensures this.WFIter(it) ==> this.Inv()
    ensures this.WFIter(it) ==> BucketIteratorModel.WFIter(I(), IIterator(it))

    method IterStart() returns (it': Iterator)
    requires Inv()
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterStart(I())
    {
      assume false;
      it' := Iterator(0);
    }

    method IterFindFirstGte(key: Key) returns (it': Iterator)
    requires Inv()
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterFindFirstGte(I(), key)
    {
      assume false;
      var kvl := GetKvl();
      var i: uint64 := KVList.IndexOfFirstKeyGte(kvl, key);
      return Iterator(i);
    }

    method IterFindFirstGt(key: Key) returns (it': Iterator)
    requires Inv()
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterFindFirstGt(I(), key)
    {
      assume false;
      var kvl := GetKvl();
      var i: uint64 := KVList.IndexOfFirstKeyGt(kvl, key);
      return Iterator(i);
    }

    method IterInc(it: Iterator) returns (it': Iterator)
    requires Inv()
    requires IIterator(it).next.Next?
    requires this.WFIter(it)
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterInc(I(), IIterator(it))
    {
      assume false;
      return Iterator(it.i + 1);
    }

    method GetNext(it: Iterator) returns (next : BucketIteratorModel.IteratorOutput)
    requires Inv()
    requires this.WFIter(it)
    ensures next == IIterator(it).next
    {
      assume false;
      if format.BFPkv? {
        if it.i == |pkv.keys.offsets| as uint64 {
          next := BucketIteratorModel.Done;
        } else {
          next := BucketIteratorModel.Next(PackedKV.GetKey(pkv, it.i), PackedKV.GetMessage(pkv, it.i));
        }
      } else {
        var kvl := GetKvl();
        if it.i == |kvl.keys| as uint64 {
          next := BucketIteratorModel.Done;
        } else {
          next := BucketIteratorModel.Next(kvl.keys[it.i], kvl.messages[it.i]);
        }
      }
    }
  }

  method KVLPartialFlush(
    parentMutBucket: MutBucket,
    childrenMutBuckets: seq<MutBucket>,
    pivots: seq<Key>)
  returns (newParent: MutBucket, newChildren: seq<MutBucket>)
  /*requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  requires |children| <= MaxNumChildren()
  requires WeightBucket(I(parent)) <= MaxTotalBucketWeight()
  requires WeightBucketList(ISeq(children)) <= MaxTotalBucketWeight()
  requires childrenWeight as int == WeightKvlSeq(children)*/
  //ensures (newParent, newChildren) == partialFlush(parent, children, pivots)
  requires parentMutBucket.Inv()
  requires MutBucket.InvSeq(childrenMutBuckets)
  requires WFBucketList(MutBucket.ISeq(childrenMutBuckets), pivots)
  requires WeightBucket(parentMutBucket.I()) <= MaxTotalBucketWeight() as int
  requires WeightBucketList(MutBucket.ISeq(childrenMutBuckets)) <= MaxTotalBucketWeight() as int
  ensures newParent.Inv()
  ensures MutBucket.InvSeq(newChildren)
  ensures fresh(newParent.Repr)
  ensures fresh(MutBucket.ReprSeq(newChildren))
  ensures newParent.Repr !! MutBucket.ReprSeq(newChildren)
  ensures MutBucket.ReprSeqDisjoint(newChildren)
  ensures bucketPartialFlush(old(parentMutBucket.Bucket), old(MutBucket.ISeq(childrenMutBuckets)), pivots)
      == (newParent.Bucket, MutBucket.ISeq(newChildren))
  {
    assume false;
    KVLPFlush.reveal_partialFlush();

    var parent := parentMutBucket.GetKvl();
    var children := MutBucket.mutBucketSeqToKvlSeq(childrenMutBuckets);
    var childrenWeight := MutBucket.computeWeightOfSeq(childrenMutBuckets);

    WeightBucketLeBucketList(KVList.ISeq(children), 0);
    KVList.lenKeysLeWeight(children[0]);
    KVList.lenKeysLeWeight(parent);
    assert |children[0].keys| + |parent.keys| < 0x8000_0000_0000_0000;

    var maxChildLen: uint64 := 0;
    var idx: uint64 := 0;
    while idx < |children| as uint64
    invariant 0 <= idx as int <= |children|
    invariant forall i | 0 <= i < idx as int :: |children[i].keys| <= maxChildLen as int
    invariant maxChildLen as int + |parent.keys| < 0x8000_0000_0000_0000
    {
      WeightBucketLeBucketList(KVList.ISeq(children), idx as int);
      KVList.lenKeysLeWeight(children[idx]);
      if |children[idx].keys| as uint64 > maxChildLen {
        maxChildLen := |children[idx].keys| as uint64;
      }
      idx := idx + 1;
    }

    var parentIdx: uint64 := 0;
    var childrenIdx: uint64 := 0;
    var childIdx: uint64 := 0;
    var acc := [];

    var cur_keys := new Key[maxChildLen + |parent.keys| as uint64];
    var cur_messages := new Message[maxChildLen + |parent.keys| as uint64];
    var cur_idx: uint64 := 0;

    var newParent_keys := new Key[|parent.keys| as uint64];
    var newParent_messages := new Message[|parent.keys| as uint64];
    var newParent_idx: uint64 := 0;

    var initChildrenWeight := childrenWeight;
    KVList.kvlSeqWeightEq(children);
    var weightSlack: uint64 := MaxTotalBucketWeightUint64() - initChildrenWeight;
    var bucketStartWeightSlack: uint64 := weightSlack;

    while childrenIdx < |children| as uint64
    invariant 0 <= parentIdx as int <= |parent.keys|
    invariant 0 <= childrenIdx as int <= |children|
    invariant (childrenIdx as int < |children| ==> 0 <= childIdx as int <= |children[childrenIdx].keys|)
    invariant 0 <= cur_idx
    invariant 0 <= newParent_idx <= parentIdx
    invariant childrenIdx as int < |children| ==> cur_idx as int <= parentIdx as int + childIdx as int
    invariant childrenIdx as int == |children| ==> cur_idx == 0
    //invariant partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int)
        //== partialFlush(parent, children, pivots)
    decreases |children| - childrenIdx as int
    decreases |parent.keys| - parentIdx as int +
        (if childrenIdx as int < |children| then |children[childrenIdx].keys| - childIdx as int else 0)
    {
      ghost var ghosty := true;
      if ghosty {
        if parentIdx as int < |parent.messages| { WeightMessageBound(parent.messages[parentIdx]); }
        if childIdx as int < |children[childrenIdx].messages| { WeightMessageBound(children[childrenIdx].messages[childIdx]); }
      }

      var child := children[childrenIdx];
      if parentIdx == |parent.keys| as uint64 {
        if childIdx == |child.keys| as uint64 {
          var newChildBucket := KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]);
          var bucket := new MutBucket.InitWithWeight(
            newChildBucket,
            childrenMutBuckets[childrenIdx].Weight + bucketStartWeightSlack - weightSlack);
          bucketStartWeightSlack := weightSlack;
          childrenIdx := childrenIdx + 1;
          childIdx := 0;
          acc := acc + [bucket];
          cur_idx := 0;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        } else {
          cur_keys[cur_idx] := child.keys[childIdx];
          cur_messages[cur_idx] := child.messages[childIdx];
          assert KVList.append(KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), child.keys[childIdx], child.messages[childIdx]) == KVList.Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
          childIdx := childIdx + 1;
          cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        }
      } else {
        if childIdx == |child.keys| as uint64 {
          if childrenIdx == |children| as uint64 - 1 {
            var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.messages[parentIdx]);
            if w <= weightSlack {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_messages[cur_idx] := parent.messages[parentIdx];
              assert KVList.append(KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == KVList.Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              newParent_keys[newParent_idx] := parent.keys[parentIdx];
              newParent_messages[newParent_idx] := parent.messages[parentIdx];

              assert KVList.append(KVList.Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == KVList.Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          } else {
            var c := cmp(parent.keys[parentIdx], pivots[childrenIdx]);
            if c < 0 {
              var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.messages[parentIdx]);
              if w <= weightSlack {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_messages[cur_idx] := parent.messages[parentIdx];
                assert KVList.append(KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == KVList.Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
                weightSlack := weightSlack - w;
                parentIdx := parentIdx + 1;
                cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                newParent_keys[newParent_idx] := parent.keys[parentIdx];
                newParent_messages[newParent_idx] := parent.messages[parentIdx];

                assert KVList.append(KVList.Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == KVList.Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

                parentIdx := parentIdx + 1;
                newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            } else {
              // XXX here's another Kvl allocation
              var bucket := new MutBucket.InitWithWeight(
                KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]),
                childrenMutBuckets[childrenIdx].Weight + bucketStartWeightSlack - weightSlack);
              bucketStartWeightSlack := weightSlack;

              acc := acc + [bucket];
              childrenIdx := childrenIdx + 1;
              childIdx := 0;
              cur_idx := 0;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        } else {
          var c := cmp(child.keys[childIdx], parent.keys[parentIdx]);
          if c == 0 {
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() {
              weightSlack := weightSlack + WeightKeyUint64(child.keys[childIdx]) + WeightMessageUint64(child.messages[childIdx]);
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              assume weightSlack <= 0x1_0000_0000;
              WeightMessageBound(m);

              if weightSlack + WeightMessageUint64(child.messages[childIdx]) >= WeightMessageUint64(m) {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_messages[cur_idx] := m;
                assert KVList.append(KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], m) == KVList.Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
                weightSlack := (weightSlack + WeightMessageUint64(child.messages[childIdx])) - WeightMessageUint64(m);
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_messages[cur_idx] := child.messages[childIdx];

                newParent_keys[newParent_idx] := parent.keys[parentIdx];
                newParent_messages[newParent_idx] := parent.messages[parentIdx];

                assert KVList.append(KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], child.messages[childIdx]) == KVList.Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
                assert KVList.append(KVList.Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == KVList.Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

                newParent_idx := newParent_idx + 1;
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            }
          } else if c < 0 {
            cur_keys[cur_idx] := child.keys[childIdx];
            cur_messages[cur_idx] := child.messages[childIdx];
            assert KVList.append(KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), child.keys[childIdx], child.messages[childIdx]) == KVList.Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
            childIdx := childIdx + 1;
            cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
          } else {
            var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.messages[parentIdx]);
            if w <= weightSlack {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_messages[cur_idx] := parent.messages[parentIdx];
              assert KVList.append(KVList.Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == KVList.Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              newParent_keys[newParent_idx] := parent.keys[parentIdx];
              newParent_messages[newParent_idx] := parent.messages[parentIdx];

              assert KVList.append(KVList.Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == KVList.Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        }
      }
    }

    var bi:uint64 := 0;
    var amassedAcc := [];
    while (bi < |acc| as uint64) {
      var origKvl := acc[bi].GetKvl();
      var amassedKvl := KVList.AmassKvl(origKvl);
      var newAcc := new MutBucket(amassedKvl);
      amassedAcc := amassedAcc + [newAcc];  // quadratic ftw
      bi := bi + 1;
    }

    newChildren := acc;
//    newChildren := amassedAcc;
//    var newParentKvl := Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]);
    var newParentKvl := KVList.AmassKvl(KVList.Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]));
    newParent := new MutBucket(newParentKvl);
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
    newtop, newbots := KVLPartialFlush(top, bots, pivots);
    flushedKeys := {};
    assume false;
  }
}

