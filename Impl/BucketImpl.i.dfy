include "../lib/DataStructures/KMBtree.i.dfy"
include "../lib/DataStructures/PackedKV.i.dfy"
include "../ByteBlockCacheSystem/KVList.i.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "BucketIteratorModel.i.dfy"
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

  type TreeMap = KMB.Node

  method tree_to_kvl(tree: TreeMap)
  returns (kvl : KVList.Kvl)
  requires KMB.WF(tree)
  requires KMBBOps.NumElements(tree) < Uint64UpperBound()
  ensures KVList.WF(kvl)
  ensures KVList.I(kvl) == KMB.Interpretation(tree)
  {
    var s := KMBBOps.ToSeq(tree);
    kvl := KVList.Kvl(s.0[..], s.1[..]);
    assume false;
  }

  method kvl_to_tree(kvl : KVList.Kvl)
  returns (tree: TreeMap)
  requires KVList.WF(kvl)
  requires |kvl.keys| < Uint64UpperBound() - 1
  ensures KMB.WF(tree)
  ensures KVList.I(kvl) == KMB.Interpretation(tree)
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

  method pkv_to_tree(pkv: PackedKV.Pkv)
  returns (tree: TreeMap)
  requires PackedKV.WF(pkv)
  ensures KMB.WF(tree)
  ensures PackedKV.I(pkv) == KMB.Interpretation(tree)
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

    ghost var Repr: set<object>;
    ghost var Bucket: map<Key, Message>;

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
        && Weight as int == WeightBucket(KVList.I(kvl))
        && Bucket == KVList.I(kvl)
      ))
      && (format.BFTree? ==> (
        && tree != null
        && tree in Repr
        && tree.repr <= Repr
        && KMB.WF(tree)
        && Weight as int == WeightBucket(KMB.Interpretation(tree))
        && Weight as int < Uint64UpperBound()
        && Bucket == KMB.Interpretation(tree)
      ))
      && (format.BFPkv? ==> (
        && tree == null
        && PackedKV.WF(pkv)
        && Weight as int == WeightBucket(Bucket)
        && Bucket == PackedKV.I(pkv)
      ))
      && WFBucket(Bucket)
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
      new;
      assume Weight as int == WeightBucket(Bucket);
      assume WFBucket(Bucket);
    }

    lemma NumElementsLteWeight(bucket: Bucket)
      ensures |bucket| < WeightBucket(bucket)
    {
      assume false;
    }
    
    method GetKvl() returns (kv: KVList.Kvl)
    requires Inv()
    ensures KVList.WF(kv)
    ensures KVList.I(kv) == Bucket
    {
      if (format.BFTree?) {
        NumElementsLteWeight(KMB.Interpretation(tree));
        assume false;
        kv := tree_to_kvl(tree);
      } else if (format.BFKvl?) {
        kv := kvl;
      } else {
        kv := pkv_to_kvl(pkv);
      }
    }

    static function {:opaque} ReprSeq(s: seq<MutBucket>) : set<object>
    reads s
    {
      set i, o | 0 <= i < |s| && o in s[i].Repr :: o
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

    static protected function ISeq(s: seq<MutBucket>) : (bs : seq<Bucket>)
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
        var psa := PackedKV.PackedStringArray.Psa([], []);
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

      Bucket := KMB.Interpretation(tree);
    }

    method Query(key: Key)
    returns (m: Option<Message>)
    requires Inv()
    ensures m.None? ==> key !in Bucket
    ensures m.Some? ==> key in Bucket && Bucket[key] == m.value
    {
      if format.BFTree? {
        m := KMB.Query(tree, key);
      } else if format.BFKvl? {
        KVList.lenKeysLeWeightOver4(kvl);
        m := KVList.Query(kvl, key);
      } else if format.BFPkv? {
        m := PackedKV.Query(pkv, key);
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

    static method computeWeightOfSeq(buckets: seq<MutBucket>)
    returns (weight: uint64)
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    requires WeightBucketList(ISeq(buckets)) < 0x1_0000_0000_0000_0000
    requires |buckets| < 0x1_0000_0000_0000
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
      var i: uint64 := KVList.IndexOfFirstKeyGte(kvl, key);
      return Iterator(i);
    }

    method IterFindFirstGt(key: Key) returns (it': Iterator)
    requires Inv()
    ensures this.WFIter(it')
    ensures IIterator(it') == BucketIteratorModel.IterFindFirstGt(I(), key)
    {
      assume false;
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
      var kvl := GetKvl();
      if it.i == |kvl.keys| as uint64 {
        next := BucketIteratorModel.Done;
      } else {
        next := BucketIteratorModel.Next(kvl.keys[it.i], kvl.messages[it.i]);
      }
    }
  }
}

