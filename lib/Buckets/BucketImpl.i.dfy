// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../DataStructures/KMBtree.i.dfy"
include "PackedKV.i.dfy"
include "../../PivotBetree/Bounds.i.dfy"
include "BucketIteratorModel.i.dfy"
include "BucketFlushModel.i.dfy"
include "LKMBPKVOps.i.dfy"
include "../Lang/Inout.i.dfy"

//
// Collects singleton message insertions efficiently, avoiding repeated
// replacement of the immutable root Node. Once this bucket is full,
// it is flushed into the root in a batch.
// This module implements PivotBetreeSpec.Bucket (the model for class
// MutBucket).
// The MutBucket class also supplies Iterators using the functional
// Iterator datatype from BucketIteratorModel, which is why there is no
// BucketIteratorImpl module/class.

module BucketImpl {
  import LKMB = LKMBtree`All
  import PackedKV
  import ValueType = ValueType`Internal
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
  import Pivots = BoundedPivotsLib
  import opened BucketFlushModel
  import opened DPKV = DynamicPkv
  import LKMBPKVOps
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened Inout
  import Lexicographic_Byte_Order

  type TreeMap = LKMB.Model.Node

  method pkv_to_tree(pkv: PackedKV.Pkv)
  returns (linear tree: TreeMap, weight: uint64)
  requires PackedKV.WF(pkv)
  ensures LKMB.WF(tree)
  ensures LKMBPKVOps.IsKeyMessageTree(tree)
  ensures PackedKV.I(pkv).as_map() == LKMB.Interpretation(tree)
  ensures weight as nat == BucketWeights.WeightBucket(BucketsLib.B(LKMB.Interpretation(tree)))
  {
    tree, weight := LKMBPKVOps.FromPkv(pkv);
  }

  method tree_to_pkv(shared tree: TreeMap) returns (pkv : PackedKV.Pkv)
    requires LKMB.WF(tree)
    requires LKMBPKVOps.IsKeyMessageTree(tree)
    requires BucketWeights.WeightBucket(BucketsLib.B(LKMB.Interpretation(tree))) < Uint32UpperBound()
    ensures PackedKV.WF(pkv)
    ensures PackedKV.I(pkv) == B(LKMB.Interpretation(tree))
  {
    LKMBPKVOps.WeightImpliesCanAppend(tree);
    pkv := LKMBPKVOps.ToPkv(tree);
  }

  datatype Iterator = Iterator(
    ghost next: BucketIteratorModel.IteratorOutput,
    i: uint64,
    ghost decreaser: int)

  function IIterator(it: Iterator) : BucketIteratorModel.Iterator
  {
    BucketIteratorModel.Iterator(it.next, it.i as int, it.decreaser)
  }

  linear datatype BucketFormat =
      | BFTree(linear tree: TreeMap)
      | BFPkv(pkv: PackedKV.Pkv)
  
  function method FreeBucketFormat(linear format: BucketFormat) : ()
  requires format.BFTree? ==> LKMB.WF(format.tree)
  {
    linear match format {
      case BFTree(tree) => 
        var _ := LKMB.FreeNode(tree);
        ()
      case BFPkv(_) =>
        ()
    }
  }

  linear datatype MutBucket = MutBucket(linear format: BucketFormat, weight: uint64, sorted: bool, ghost bucket: Bucket)
  {
    predicate Inv()
    ensures Inv() ==> weight as int == WeightBucket(bucket)
    ensures Inv() ==> WFBucket(bucket)
    {
      && (format.BFTree? ==> (
        && LKMB.WF(format.tree)
        && LKMBPKVOps.IsKeyMessageTree(format.tree)
        && bucket == B(LKMB.Interpretation(format.tree))
      ))
      && (format.BFPkv? ==> (
        && PackedKV.WF(format.pkv)
        && bucket == PackedKV.I(format.pkv)
      ))
      && WFBucket(bucket)
      && (weight as int == WeightBucket(bucket))
      && weight as int < Uint32UpperBound()
      && (sorted ==> BucketWellMarshalled(bucket))
    }
  
    static method Alloc() returns (linear mb: MutBucket)
    ensures mb.bucket == EmptyBucket()
    ensures mb.Inv()
    {
      linear var tmp := LKMB.EmptyTree();
      mb := MutBucket(BFTree(tmp), 0, true, EmptyBucket());

      B_empty_map();
    }

    static method AllocPkv(pkv: PackedKV.Pkv, is_sorted: bool) returns (linear mb: MutBucket)
    requires PackedKV.WF(pkv)
    requires is_sorted ==> BucketWellMarshalled(PackedKV.I(pkv))
    requires PackedKV.WeightPkv(pkv) as nat < Uint32UpperBound()
    ensures mb.I() == PackedKV.I(pkv)
    ensures mb.Inv()
    {
      mb := MutBucket(BFPkv(pkv), PackedKV.WeightPkv(pkv), is_sorted, PackedKV.I(pkv));
      WeightBucketIs(pkv);
    }

    static lemma WeightKeyListIs(psa: PackedKV.PSA.Psa, k: int)
    requires PSA.WF(psa)
    requires 0 <= k <= |psa.offsets|
    requires PackedKV.ValidKeyLens(PSA.I(psa))
    ensures WeightKeyList(PackedKV.IKeys(psa)[.. k]) ==
      4 * k + (if k == 0 then 0 else PSA.psaEnd(psa, (k - 1) as uint64) as int);
    {
      if k == 0 {
      } else {
        var keys:seq<Key> := PackedKV.IKeys(psa);
        var weights := ApplyOpaque(WeightKey, keys[.. k]);
        var weights' := ApplyOpaque(WeightKey, keys[.. k - 1]);
        var key := keys[k - 1];
        calc {
          WeightKeyList(keys[.. k]);
          {
            assert keys[.. k-1] + [key] == keys[.. k];
          //}
          //WeightKeyList(keys[.. k - 1] + [key]);
          //{
            WeightKeyListPushBack(keys[.. k - 1], key);
          }
          WeightKey(key) + WeightKeyList(keys[.. k - 1]);
          { WeightKeyListIs(psa, k - 1); }
          4 * k + PackedKV.PSA.psaEnd(psa, (k - 1) as uint64) as int;
        }
      }
    }

    static lemma WeightMessageListIs(psa: PackedKV.PSA.Psa, k: int)
    requires PSA.WF(psa)
    requires 0 <= k <= |psa.offsets|
    requires ValueType.ValidMessageBytestrings(PSA.I(psa));
    ensures WeightMessageList(PackedKV.IMessages(psa)[.. k]) ==
      4 * k + (if k == 0 then 0 else PSA.psaEnd(psa, (k - 1) as uint64) as int);
    {
      if k == 0 {
      } else {
        var msgs:seq<Message> := PackedKV.IMessages(psa);
        var weights := ApplyOpaque(WeightMessage, msgs[.. k]);
        var weights' := ApplyOpaque(WeightMessage, msgs[.. k - 1]);
        var msg := msgs[k - 1];
        calc {
          WeightMessageList(msgs[.. k]);
          {
            assert msgs[.. k-1] + [msg] == msgs[.. k];
          //}
          //WeightMessageList(msgs[.. k - 1] + [msg]);
          //{
            WeightMessageListPushBack(msgs[.. k - 1], msg);
          }
          WeightMessage(msg) + WeightMessageList(msgs[.. k - 1]);
          { WeightMessageListIs(psa, k - 1); }
          { PackedKV.DefineIMessage(psa, k - 1); }
          4 * k + PackedKV.PSA.psaEnd(psa, (k - 1) as uint64) as int;
        }
      }
    }

    static lemma WeightBucketIs(pkv: PackedKV.Pkv)
    requires PackedKV.WF(pkv)
    ensures WeightBucket(PackedKV.I(pkv)) == PackedKV.WeightPkv(pkv) as int
    {
      var bucket := PackedKV.I(pkv);
      var n := |pkv.keys.offsets|;
      var keys:seq<Key> := PSA.I(pkv.keys);
      var msgs:seq<Message> := PackedKV.IMessages(pkv.messages);
      assert keys == keys[0..n];
      assert msgs == msgs[0..n];
      WeightKeyListIs(pkv.keys, n);
      WeightMessageListIs(pkv.messages, n);
    }

    shared method GetPkvSorted(must_be_sorted:bool) returns (pkv: PKV.Pkv)
    requires Inv()
    ensures PKV.WF(pkv)
    ensures !must_be_sorted ==> PKV.I(pkv) == bucket
    ensures must_be_sorted ==> PKV.I(pkv) == B(bucket.as_map())
    ensures WeightBucket(PKV.I(pkv)) <= weight as nat
    {
      if (format.BFTree?) {
        NumElementsLteWeight(B(LKMB.Interpretation(format.tree)));
        pkv := tree_to_pkv(format.tree);
      } else if !must_be_sorted || sorted {
        pkv := this.format.pkv;

        assert PKV.WF(pkv);
        assert !must_be_sorted ==> PKV.I(pkv) == bucket;
        assert sorted ==> PKV.I(pkv) == B(bucket.as_map()) by {
          if sorted {
            B_of_as_map_sorted(bucket);
          }
        }
      } else {
        linear var tree;
        var weight;
        tree, weight := pkv_to_tree(this.format.pkv);
        BucketWeights.Weight_SortedBucket_le_UnsortedBucket(
            PKV.I(this.format.pkv), B(LKMB.Interpretation(tree)));
        NumElementsLteWeight(bucket);
        pkv := tree_to_pkv(tree);
        var _ := LKMB.FreeNode(tree);
      }
    }

    shared method GetPkv() returns (pkv: PKV.Pkv)
    requires Inv()
    ensures PKV.WF(pkv)
    ensures PKV.I(pkv) == bucket
    {
      pkv := GetPkvSorted(false);
    }

    shared method WellMarshalled() returns (b: bool)
    requires Inv()
    ensures b == BucketWellMarshalled(I())
    {
      if (format.BFTree?) {
        b := true;
      } else {
        if sorted {
          b := true;
        } else {
          b := PackedKV.ComputeIsSorted(format.pkv);
          assert bucket.keys == PackedKV.PSA.I(format.pkv.keys); // observe
        }
      }
    }

    shared method Empty() returns (result: bool)
    requires Inv()
    ensures result == (|I().keys| == 0)
    {
      if (format.BFTree?) {
        result := LKMB.Empty(format.tree);
        MapSeqs.emptiness_map_of_seqs(I().keys, I().msgs);
      } else {
        SetCardinality0(PackedKV.IKeys(format.pkv.keys));
        result := 0 == |format.pkv.keys.offsets| as uint64;
      }
    }

    shared method WFBucketAt(pivots: Pivots.PivotTable, i: uint64) returns (result: bool)
    requires Inv()
    requires BucketWellMarshalled(I())
    requires Pivots.WFPivots(pivots)
    requires forall k | k in bucket.keys :: Pivots.BoundedKey(pivots, k)
    requires i as nat < Pivots.NumBuckets(pivots) < Uint64UpperBound()
    ensures result == BucketsLib.WFBucketAt(I(), pivots, i as nat)
    {
      var e := Empty();
      if e {
        return true;
      }

      Lexicographic_Byte_Order.reveal_IsStrictlySorted();

      var firstkey := GetFirstKey();
      var c := Pivots.KeyspaceImpl.cmp(pivots[i], Pivots.Keyspace.Element(firstkey));
      if 0 < c {
        return false;    // Need to fill in defs in BucketsLib to prove correctness.
      }

      var lastkey := GetLastKey();
      c := Pivots.KeyspaceImpl.cmp(Pivots.Keyspace.Element(lastkey), pivots[i+1]);
      if c >= 0 {
        return false;   // Need to fill in defs in BucketsLib to prove correctness.
      }

      return true;
    }

    static predicate InvSeq(s: seq<MutBucket>)
    ensures InvSeq(s) == (forall i | 0 <= i < |s| :: s[i].Inv())
    {
      forall i | 0 <= i < |s| :: s[i].Inv()
    }

    function I() : Bucket
    {
      bucket
    }

    // related ISeq
    static function {:opaque} ISeq(s: seq<MutBucket>) : (bs : seq<Bucket>)
    ensures |bs| == |s|
    ensures forall i | 0 <= i < |s| :: bs[i] == s[i].bucket
    decreases |s|
    {
      if |s| == 0 then [] else ISeq(DropLast(s)) + [Last(s).I()]
    }

    static lemma ISeqInduction(s: seq<MutBucket>)
    requires |s| > 0
    ensures ISeq(s) == ISeq(DropLast(s)) + [Last(s).I()]
    {
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

    static predicate InvLseq(s: lseq<MutBucket>)
    {
      && lseq_has_all(s)
      && InvSeq(lseqs(s))
      && |s| < Uint64UpperBound()
    }

    static function ILseq(s: lseq<MutBucket>) : (bs : seq<Bucket>)
    ensures |s| == |bs|
    ensures forall i | 0 <= i < |s| :: bs[i] == s[i].I()
    {
      ISeq(lseqs(s))
    }

    shared method GetFirstKey() returns (result: Key)
    requires Inv()
    requires BucketWellMarshalled(bucket)
    requires 0 < |bucket.keys|
    ensures result in bucket.keys
    ensures forall k | k in bucket.keys :: Ord.lte(result, k)
    {
      MapSeqs.key_sets_eq(bucket.keys, bucket.msgs);
      MapSeqs.emptiness_map_of_seqs(bucket.keys, bucket.msgs);

      if format.BFTree? {
        result := LKMB.MinKey(format.tree);
      } else {
        assert format.BFPkv?;
        result := PackedKV.FirstKey(format.pkv);
        assert result == PackedKV.I(format.pkv).keys[0];
        reveal BucketsLib.Lexicographic_Byte_Order.IsSorted();
      }
    }

    shared method GetMiddleKey() returns (res: Key)
    requires Inv()
    ensures getMiddleKey(I()) == res
    {
      var pkv;

      if format.BFPkv? {
        pkv := format.pkv;
      } else {
        NumElementsLteWeight(B(LKMB.Interpretation(format.tree)));
        pkv := tree_to_pkv(format.tree);
      }
      
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
    }

    shared method GetLastKey() returns (result: Key)
    requires Inv()
    requires BucketWellMarshalled(bucket)
    requires 0 < |bucket.keys|
    ensures result in bucket.keys
    ensures forall k | k in bucket.keys :: Ord.lte(k, result)
    {
      MapSeqs.key_sets_eq(bucket.keys, bucket.msgs);
      MapSeqs.emptiness_map_of_seqs(bucket.keys, bucket.msgs);

      if format.BFTree? {
        result := LKMB.MaxKey(format.tree);
      } else {
        assert format.BFPkv?;
        result := PackedKV.LastKey(format.pkv);
        assert result == Last(PackedKV.I(format.pkv).keys);
        reveal BucketsLib.Lexicographic_Byte_Order.IsSorted();
      }
    }

    linear inout method Insert(key: Key, value: Message)
    requires old_self.Inv()
    requires old_self.weight as int + WeightKey(key) + WeightMessage(value) < 0x1_0000_0000
    ensures self.Inv()
    ensures self.bucket == BucketInsert(old_self.bucket, key, value)
    {
      WFBucketInsert(self.bucket, key, value);

      // the semantics of the insert operation (defined in terms of a bucket)
      // tells us to (i) interpret it as a map (as_map)
      // (ii) do the insertion
      // (iii) convert it back to sequence form
      //
      // on the other hand,
      // the tree gives a map, and B is an interpretation of that map
      // which gives us a bucket in sequence form.
      //
      // If we start in tree form, then the bucket interpreation is sorted.
      // B and as_map are inverses for a sorted "bucket" object, so what
      // happens is something like this:
      //
      //            B
      // old tree ------> old bucket
      //    |     <-----
      //    |     as_map
      //    |
      //    |
      //    | do insert
      //    |
      //    v       B
      // new tree -----> new bucket
      //
      // if we start in pkv form, what happens is more like this:
      //
      //         PKV.I()
      // pkv ------------ old bucket
      //    |            /
      //    |           /
      //    |          /   as_map
      //    v         /
      // old tree  <--
      //    |   
      //    |
      //    | do insert
      //    |
      //    v       B
      // new tree -----> new bucket
      //

      if self.format.BFPkv? {
        linear var tree;
        var weight;
        tree, weight := pkv_to_tree(self.format.pkv);
        inout self.weight := weight;
        linear var prevformat := Replace(inout self.format, BFTree(tree));
        var _ := FreeBucketFormat(prevformat);
        inout ghost self.bucket := B(self.bucket.as_map());
        Weight_SortedBucket_le_UnsortedBucket(old_self.bucket, self.bucket);
      }

      ghost var old_bucket_map := LKMB.Interpretation(self.format.tree);
      ghost var old_bucket := self.bucket;
      Weight_BucketMap_eq_Bucket(self.bucket);

      assert old_bucket.as_map() == old_bucket_map;
      assert B(old_bucket_map) == old_bucket;
      assert old_bucket_map == old_self.bucket.as_map();

      if value.Define? {
        linear var MutBucket(format, weight, sorted, bucket) := self;
        linear var BFTree(tree) := format;
        var cur;
        tree, cur := LKMB.Insert(tree, key, value);
        if (cur.Some?) {
          ghost var map0 := Maps.MapRemove1(old_bucket_map, key);
          WeightBucketInduct(map0, key, cur.value);
          WeightBucketInduct(map0, key, value);
          assert bucket.as_map()[key := value] == map0[key := value];
          assert bucket.as_map() == map0[key := cur.value];
          weight := weight - WeightMessageUint64(cur.value) + WeightMessageUint64(value) as uint64;
        } else {
          WeightBucketInduct(bucket.as_map(), key, value);
          weight := weight + WeightKeyUint64(key) + WeightMessageUint64(value);
        }
        self := MutBucket(BFTree(tree), weight, sorted, B(LKMB.Interpretation(tree)));
      }

      ghost var mergedMsg := Merge(value, BucketMaps.BucketGet(old_bucket_map, key));
      assert mergedMsg == IdentityMessage() ==> LKMB.Interpretation(self.format.tree) == MapRemove1(old_self.bucket.as_map(), key) by {
        // NOTE: according to the state machine model, wee're supposed to remove
        // the value in this case, but it turns out that the structure of the messages
        // means we can infer it wasn't there to begin with.
        if (key in old_bucket_map) {
          var j := MapSeqs.GetIndex(old_self.bucket.keys, old_self.bucket.msgs, key);
          assert old_bucket_map[key] != IdentityMessage();
        }
      }
      assert mergedMsg != IdentityMessage() ==> LKMB.Interpretation(self.format.tree) == old_self.bucket.as_map()[key := mergedMsg];

      Weight_BucketMap_eq_Bucket(self.bucket);
    }

    shared method Query(key: Key)
    returns (m: Option<Message>)
    requires Inv()
    ensures m == bucketBinarySearchLookup(I(), key)
    {
      if format.BFTree? {
        m := LKMB.Query(format.tree, key);
      } else if format.BFPkv? {
        m := PackedKV.BinarySearchQuery(format.pkv, key);
      }
    }

    shared method SplitLeft(pivot: Key)
    returns (linear left: MutBucket)
    requires Inv()
    ensures left.Inv()
    ensures left.bucket == SplitBucketLeft(bucket, pivot)
    {
      reveal_SplitBucketLeft();
      var pkv := GetPkvSorted(false);
      var pkvleft := PKV.SplitLeft(pkv, pivot);
      WeightSplitBucketLeft(PKV.I(pkv), pivot);
      WeightBucketPkv_eq_WeightPkv(pkvleft);
      assert sorted ==> BucketWellMarshalled(PackedKV.I(pkvleft)) by {
        reveal_SplitBucketLeft();
        Lexicographic_Byte_Order.reveal_IsStrictlySorted();
      }
      left := AllocPkv(pkvleft, sorted);
    }

    shared method SplitRight(pivot: Key)
    returns (linear right: MutBucket)
    requires Inv()
    ensures right.Inv()
    ensures right.bucket == SplitBucketRight(bucket, pivot)
    {
      var pkv := GetPkvSorted(false);
      //WeightSplitBucketRight(bucket, pivot);
      var pkvright := PKV.SplitRight(pkv, pivot);
      WeightSplitBucketRight(PKV.I(pkv), pivot);
      WeightBucketPkv_eq_WeightPkv(pkvright);
      assert sorted ==> BucketWellMarshalled(PackedKV.I(pkvright)) by {
        reveal_SplitBucketRight();
        Lexicographic_Byte_Order.reveal_IsStrictlySorted();
      }
      right := AllocPkv(pkvright, sorted);
    }

    static method SplitLeftRight(shared b: MutBucket, pivot: Key)
    returns (linear left: MutBucket, linear right: MutBucket)
    requires b.Inv()
    ensures left.Inv()
    ensures right.Inv()
    ensures left.bucket == SplitBucketLeft(b.bucket, pivot)
    ensures right.bucket == SplitBucketRight(b.bucket, pivot)
    {
      left := b.SplitLeft(pivot);
      right := b.SplitRight(pivot);
    }
  
    static method SplitOneInList(linear inout buckets: lseq<MutBucket>, slot: uint64, pivot: Key)
    requires InvLseq(old_buckets)
    requires 0 <= slot as int < |old_buckets|
    requires |old_buckets| < 0xffff_ffff_ffff_ffff
    ensures InvLseq(buckets)
    ensures ILseq(buckets) == SplitBucketInList(ILseq(old_buckets), slot as int, pivot)
    {
      linear var l, r := SplitLeftRight(lseq_peek(buckets, slot), pivot);
      linear var replaced;
      replaced := Replace1With2Lseq_inout(inout buckets, l, r, slot);
      var _ := FreeMutBucket(replaced);

      ghost var ghosty := true;
      if ghosty {
        reveal_ISeq();
        reveal_SplitBucketInList();
        ISeq_replace1with2(lseqs(buckets), l, r, slot as int);
      }
    }

    static method computeWeightOfSeq(shared buckets: lseq<MutBucket>)
    returns (weight: uint64)
    requires InvLseq(buckets)
    requires WeightBucketList(ILseq(buckets)) < 0x1_0000_0000_0000_0000
    requires |buckets| < 0x1_0000_0000_0000_0000
    ensures weight as int == WeightBucketList(ILseq(buckets))
    {
      reveal_WeightBucketList();
      ghost var bs := ILseq(buckets);

      var w := 0;
      var j: uint64 := 0;
      while j < lseq_length_raw(buckets)
      invariant 0 <= j as int <= |buckets|
      invariant w as int == WeightBucketList(bs[0..j]);
      {
        assert DropLast(bs[0..j+1]) == bs[0..j];
        assert Last(bs[0..j+1]) == lseq_peek(buckets, j).I();
        WeightBucketListSlice(bs, 0, j as int + 1);

        w := w + lseq_peek(buckets, j).weight;
        j := j + 1;
      }
      assert bs[0..|buckets|] == bs;
      return w;
    }

    static lemma Islice(buckets: lseq<MutBucket>, a: int, b: int)
    requires 0 <= a <= b <= |buckets|
    requires InvLseq(buckets)
    ensures forall i | 0 <= i < |lseqs(buckets)[a..b]| :: lseqs(buckets)[a..b][i].Inv()
    ensures ISeq(lseqs(buckets)[a..b]) == ILseq(buckets)[a..b]
    decreases |buckets|
    {
      if b == |buckets| {
        if (a == b) {
        } else {
          Islice(ldroplast(buckets), a, b - 1);
        }
      } else {
        Islice(ldroplast(buckets), a, b);
      }
    }


    shared method Clone() returns (linear bucket': MutBucket)
    requires Inv()
    ensures bucket'.Inv()
    ensures this.bucket == bucket'.bucket
    {
      if format.BFPkv? {
        DPKV.WeightBucketPkv_eq_WeightPkv(format.pkv);
        bucket' := AllocPkv(format.pkv, sorted);
      } else {
        var pkv;
        NumElementsLteWeight(B(LKMB.Interpretation(format.tree)));
        pkv := tree_to_pkv(format.tree);
        DPKV.WeightBucketPkv_eq_WeightPkv(pkv);
        bucket' := AllocPkv(pkv, true);
      }
    }

    static method CloneSeq(shared buckets: lseq<MutBucket>, start: uint64, end: uint64) returns (linear buckets': lseq<MutBucket>)
    requires InvLseq(buckets)
    requires 0 <= start as int <= end as int <= |buckets|
    requires |buckets| < 0x1_0000_0000_0000_0000;
    ensures InvLseq(buckets')
    ensures |buckets'| == (end-start) as int
    ensures ILseq(buckets') == ILseq(buckets)[start..end]
    {
      buckets' := lseq_alloc(end-start);

      var j := start;
      while j < end
      invariant start <= j <= end
      invariant |buckets'| == (end-start) as int
      invariant forall i | (j-start) as int <= i < |buckets'| :: !lseq_has(buckets')[i]
      invariant forall i | 0 <= i < (j-start) as int :: lseq_has(buckets')[i]
      invariant forall i | 0 <= i < (j-start) as int :: lseqs(buckets')[i].Inv()
      invariant forall i | 0 <= i < (j-start) as int :: lseqs(buckets')[i].I() == lseqs(buckets)[i+(start as int)].I()
      {
        linear var newbucket := lseq_peek(buckets, j).Clone();
        buckets' := lseq_give(buckets', j-start, newbucket);
        j := j + 1;
      }
    }
  }

  function method FreeMutBucket(linear bucket: MutBucket) : ()
  requires bucket.Inv()
  {
    linear var MutBucket(format, _ ,_ ,_) := bucket;
    var _ := FreeBucketFormat(format);
    ()
  }

  function method FreeMutBucketSeqRecur(linear buckets: lseq<MutBucket>, i: uint64) : (linear ebuckets: lseq<MutBucket>)
  requires |buckets| < Uint64UpperBound()
  requires 0 <= i as nat < |buckets|
  requires MutBucket.InvSeq(lseqs(buckets)[i..])
  requires forall j | i as nat <= j < |buckets| :: j in buckets
  ensures |ebuckets| == |buckets|
  ensures forall j | 0 <= j < |buckets| :: j !in buckets ==> j !in ebuckets
  ensures forall j | i as nat <= j < |ebuckets| :: j !in ebuckets
  decreases |buckets| as uint64 - i
  {
    linear var (buckets', wastebucket) := lseq_take_fun(buckets, i);
    var _ := FreeMutBucket(wastebucket);

    if i+1 == lseq_length_as_uint64(buckets') then
      buckets'
    else
      linear var e := FreeMutBucketSeqRecur(buckets', i+1);
      e
  }

  function method FreeMutBucketSeq(linear buckets: lseq<MutBucket>) : ()
  requires |buckets| < Uint64UpperBound()
  requires MutBucket.InvLseq(buckets)
  {
    if lseq_length_as_uint64(buckets) == 0 then
      lseq_free_fun(buckets)
    else 
      linear var buckets' := FreeMutBucketSeqRecur(buckets, 0);
      lseq_free_fun(buckets')
  }

  linear datatype BucketIter = BucketIter(it: Iterator, pkv: PackedKV.Pkv, ghost bucket: Bucket)
  {
    predicate WFIter()
    {
      && PackedKV.WF(pkv)
      && bucket == PackedKV.I(pkv)
      && BucketIteratorModel.WFIter(bucket, IIterator(it))
    } 

    linear method Free()
    {
      linear var BucketIter(_,_,_) := this;
    }

    static function method makeIter(ghost bucket: Bucket, idx: uint64): (it': Iterator)
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

    static method IterStart(shared bucket: MutBucket) returns (linear biter: BucketIter)
    requires bucket.Inv()
    ensures biter.WFIter()
    ensures biter.bucket == bucket.I()
    ensures IIterator(biter.it) == BucketIteratorModel.IterStart(biter.bucket)
    {
      BucketIteratorModel.reveal_IterStart();
      ghost var b := bucket.I();
      var pkv := bucket.GetPkv();
      var it := makeIter(b, 0);
      biter := BucketIter(it, pkv, b);
    }

    static method IterFindFirstGte(shared bucket: MutBucket, key: Key) returns (linear biter: BucketIter)
    requires bucket.Inv()
    ensures biter.WFIter()
    ensures biter.bucket == bucket.I()
    ensures IIterator(biter.it) == BucketIteratorModel.IterFindFirstGte(biter.bucket, key)
    {
      BucketIteratorModel.reveal_IterFindFirstGte();
      ghost var b := bucket.I();
      var pkv := bucket.GetPkv();
      var i: uint64 := PSA.BinarySearchIndexOfFirstKeyGte(pkv.keys, key);
      var it := makeIter(b, i);
      biter := BucketIter(it, pkv, b);
    }

    static method IterFindFirstGt(shared bucket: MutBucket, key: Key) returns (linear biter: BucketIter)
    requires bucket.Inv()
    ensures biter.WFIter()
    ensures biter.bucket == bucket.I()
    ensures IIterator(biter.it) == BucketIteratorModel.IterFindFirstGt(biter.bucket, key)
    {
      BucketIteratorModel.reveal_IterFindFirstGt();
      ghost var b := bucket.I();
      var pkv := bucket.GetPkv();
      var i: uint64 := PSA.BinarySearchIndexOfFirstKeyGt(pkv.keys, key);
      var it := makeIter(b, i);
      biter := BucketIter(it, pkv, b);
    }

    linear inout method IterInc()
    requires old_self.WFIter()
    requires IIterator(old_self.it).next.Next?
    ensures self.WFIter()
    ensures old_self.bucket == self.bucket
    ensures IIterator(self.it) == BucketIteratorModel.IterInc(old_self.bucket, IIterator(old_self.it))
    {
      BucketIteratorModel.lemma_NextFromIndex(self.bucket, IIterator(self.it));

      BucketIteratorModel.reveal_IterInc();
      NumElementsLteWeight(self.bucket);
      inout self.it := makeIter(self.bucket, self.it.i + 1);
    }

    shared method GetNext() returns (next : BucketIteratorModel.IteratorOutput)
    requires this.WFIter()
    ensures next == IIterator(this.it).next
    {
      BucketIteratorModel.lemma_NextFromIndex(bucket, IIterator(it));
        
      if it.i == |pkv.keys.offsets| as uint64 {
        next := BucketIteratorModel.Done;
      } else {
        next := BucketIteratorModel.Next(PackedKV.GetKey(pkv, it.i), PackedKV.GetMessage(pkv, it.i));
      }
    }
  }

  method pkvList2BucketList(pkvs: seq<PKV.Pkv>, sorted: bool)
  returns (linear buckets: lseq<MutBucket>)
  requires |pkvs| < Uint64UpperBound()
  requires forall i | 0 <= i < |pkvs| :: PKV.WF(pkvs[i])
  requires forall i | 0 <= i < |pkvs| :: PackedKV.WeightPkv(pkvs[i]) as nat < Uint32UpperBound()
  requires sorted ==>
           forall i | 0 <= i < |pkvs| :: BucketWellMarshalled(PKV.I(pkvs[i]))
  ensures |buckets| == |pkvs|
  ensures MutBucket.InvLseq(buckets)
  ensures MutBucket.ILseq(buckets) == DPKV.PKVISeq(pkvs)
  {
    buckets := lseq_alloc(|pkvs| as uint64);
    var i: uint64 := 0;
    while i < |pkvs| as uint64
      invariant i as nat <= |pkvs|
      invariant |pkvs| == |buckets|
      invariant forall j | i as int <= j < |buckets| :: !lseq_has(buckets)[j]
      invariant forall j | 0 <= j < i as int :: lseq_has(buckets)[j]
      invariant forall j | 0 <= j < i :: lseqs(buckets)[j].Inv()
      invariant forall j | 0 <= j < i :: lseqs(buckets)[j].bucket == PKV.I(pkvs[j])
    {
      linear var newbucket := MutBucket.AllocPkv(pkvs[i], sorted);
      buckets := lseq_give(buckets, i, newbucket);
      i := i + 1;
    }
  }

  method PartialFlush(shared top: MutBucket, shared bots: lseq<MutBucket>, pivots: Pivots.PivotTable)
    returns (linear newtop: MutBucket, linear newbots: lseq<MutBucket>)
    requires top.Inv()
    requires MutBucket.InvLseq(bots)
    requires Pivots.WFPivots(pivots)
    requires |pivots| < Uint64UpperBound()
    requires Pivots.NumBuckets(pivots) == |bots|
    requires WeightBucket(top.I()) <= MaxTotalBucketWeight()
    requires WeightBucketList(MutBucket.ILseq(bots)) <= MaxTotalBucketWeight()
    ensures MutBucket.InvLseq(newbots)
    ensures newtop.Inv()
    ensures partialFlushResult(newtop.I(), MutBucket.ILseq(newbots))
        == BucketFlushModel.partialFlush(top.I(), pivots, MutBucket.ILseq(bots))
  {
    var i: uint64 := 0;
    var bots_len := lseq_length_raw(bots);

    var botPkvs: array<PKV.Pkv> := new PKV.Pkv[bots_len];
    var sorted := true;
    while i < bots_len
      invariant i as nat <= |bots|
      invariant forall j | 0 <= j < i :: PKV.WF(botPkvs[j])
      invariant forall j | 0 <= j < i :: PKV.I(botPkvs[j]) == lseqs(bots)[j].bucket
      invariant forall j | 0 <= j < i :: |PKV.IKeys(botPkvs[j].keys)| < 0x1000_0000
      invariant sorted ==> forall j | 0 <= j < i ::
          BucketWellMarshalled(PKV.I(botPkvs[j]))
    {
      botPkvs[i] := lseq_peek(bots, i).GetPkv();
      NumElementsLteWeight(PKV.I(botPkvs[i]));
      WeightBucketLeBucketList(MutBucket.ILseq(bots), i as int);

      if !lseq_peek(bots, i).sorted {
        sorted := false;
      }
      // assert |PKV.IKeys(botPkvs[i].keys)|
      //    <= WeightBucket(PKV.I(botPkvs[i]))
      //    <= WeightBucketList(MutBucket.ILseq(bots))
      //    < 0x1000_0000;
      i := i + 1;
    }

    var botPkvsSeq := botPkvs[..];

    NumElementsLteWeight(top.bucket);
    assert DPKV.PKVISeq(botPkvsSeq) == MutBucket.ILseq(bots);

    var topPkv := top.GetPkv();
    if !top.sorted {
      sorted := false;
    }

    var result := DPKV.PartialFlush(topPkv, pivots, botPkvsSeq);

    assert sorted ==>
      && BucketWellMarshalled(PKV.I(result.top)) 
      && (forall j | 0 <= j < |result.bots| ::
          BucketWellMarshalled(PKV.I(result.bots[j])))
    by {
      if sorted {
        partialFlushPreservesSorted(top.bucket, pivots, MutBucket.ILseq(bots));
      }
    }

    partialFlushWeightBound(top.I(), pivots, MutBucket.ILseq(bots));
    DPKV.WeightBucketPkv_eq_WeightPkv(result.top);
    forall i | 0 <= i < |result.bots|
      ensures PackedKV.WeightPkv(result.bots[i]) as nat < Uint32UpperBound()
    {
      WeightBucketLeBucketList(DPKV.PKVISeq(result.bots), i);
      DPKV.WeightBucketPkv_eq_WeightPkv(result.bots[i]);
    }
    newtop := MutBucket.AllocPkv(result.top, sorted);
    newbots := pkvList2BucketList(result.bots, sorted);
  }
}
