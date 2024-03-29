// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../DataStructures/KMBtree.i.dfy"
include "PackedKV.i.dfy"
include "../../PivotBetree/Bounds.i.dfy"
include "BucketFlushModel.i.dfy"
include "LKMBPKVOps.i.dfy"
include "../Lang/Inout.i.dfy"
include "TranslationLib.i.dfy"

//
// Collects singleton message insertions efficiently, avoiding repeated
// replacement of the immutable root Node. Once this bucket is full,
// it is flushed into the root in a batch.
// This module implements PivotBetreeSpec.Bucket (the model for class
// MutBucket).
//

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
  import Pivots = BoundedPivotsLib
  import opened BucketFlushModel
  import opened DPKV = DynamicPkv
  import LKMBPKVOps
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened Inout
  import opened TranslationLib

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

      BoundedKeyspace.reveal_IsStrictlySorted();

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
        reveal BoundedKeyspace.IsSorted();
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
        reveal BoundedKeyspace.IsSorted();
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
        BoundedKeyspace.reveal_IsStrictlySorted();
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
        BoundedKeyspace.reveal_IsStrictlySorted();
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

    static method computeWeightOfSeq(shared buckets: lseq<MutBucket>) returns (weight: uint64)
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

    static method tryComputeWeightOfSeq(shared buckets: lseq<MutBucket>, start: uint64, end: uint64)
    returns (succ: bool, weight: uint64)
    requires InvLseq(buckets)
    requires 0 <= start as nat <= end as nat <= |buckets|
    requires |buckets| < 0x1_0000_0000_0000_0000
    ensures succ ==> weight as int == WeightBucketList(ILseq(buckets)[start..end])
    ensures !succ ==> MaxTotalBucketWeight() < WeightBucketList(ILseq(buckets)[start..end])
    {
      reveal_WeightBucketList();
      ghost var bs := ILseq(buckets);

      var w := 0;
      var j: uint64 := start;
      var max : uint64 := 0xffff_ffff_ffff_ffff;

      while j < end
      invariant start <= j <= end
      invariant WeightBucketList(bs[start..j]) < 0x1_0000_0000_0000_0000
      invariant w as int == WeightBucketList(bs[start..j]);
      {
        assert DropLast(bs[start..j+1]) == bs[start..j];
        assert Last(bs[start..j+1]) == lseq_peek(buckets, j).I();

        var bucketweight := lseq_peek(buckets, j).weight;
        var diff := max - bucketweight;

        if diff < w {
          WeightBucketListSlice(bs[start..end], 0, (j - start) as int);
          assert bs[start..end][0..j-start] == bs[start..j];
          succ := false;
          weight := w;
          return;
        }

        w := w + bucketweight;
        j := j + 1;
      }

      succ := true;
      weight := w;
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

    static method CloneSeq(shared buckets: lseq<MutBucket>, start: uint64, end: uint64)
    returns (linear buckets': lseq<MutBucket>)
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

    static method SplitSeq(linear buckets: lseq<MutBucket>, split: uint64)
    returns (linear left: lseq<MutBucket>, linear right: lseq<MutBucket>)
    requires InvLseq(buckets)
    requires 0 <= split as int <= |buckets|
    requires |buckets| < 0x1_0000_0000_0000_0000
    ensures InvLseq(left)
    ensures InvLseq(right)
    ensures ILseq(left) == ILseq(buckets)[..split]
    ensures ILseq(right) == ILseq(buckets)[split..]
    {
      linear var buckets' := buckets;
      ghost var gbuckets := ILseq(buckets');
      var len := lseq_length_as_uint64(buckets');

      left := lseq_alloc(split);
      right := lseq_alloc(len-split);

      var j := 0 as uint64;
      while j < len
      invariant 0 <= j <= len
      invariant split as int == |left|
      invariant (len-split) as int == |right|
      invariant len as int == |buckets'| == |gbuckets|
      invariant forall i | j as int <= i < |buckets'| :: lseq_has(buckets')[i]
      invariant forall i | j as int <= i < |buckets'| :: lseqs(buckets')[i].Inv()
      invariant forall i | j as int <= i < |buckets'| :: lseqs(buckets')[i].I() == gbuckets[i]
      invariant forall i | j as int <= i < |left| :: !lseq_has(left)[i]
      invariant j < split ==> (forall i | 0 <= i < |right| :: !lseq_has(right)[i])
      invariant j >= split ==> (forall i | (j-split) as int <= i < |right| :: !lseq_has(right)[i])
      invariant forall i | 0 <= i < j as int :: !lseq_has(buckets')[i]
      invariant forall i | 0 <= i < j as int && i < |left| :: lseq_has(left)[i]
      invariant forall i | 0 <= i < j as int && i < |left| :: lseqs(left)[i].Inv()
      invariant forall i | 0 <= i < j as int && i < |left| :: lseqs(left)[i].I() == gbuckets[i]
      invariant j >= split ==> forall i | 0 <= i < (j-split) as int :: lseq_has(right)[i]
      invariant j >= split ==> forall i | 0 <= i < (j-split) as int :: lseqs(right)[i].Inv()
      invariant j >= split ==> forall i | 0 <= i < (j-split) as int :: lseqs(right)[i].I() == gbuckets[i+split as int]
      {
        linear var newbucket := lseq_take_inout(inout buckets', j);
        if j < split {
          lseq_give_inout(inout left, j, newbucket);
        } else {
          lseq_give_inout(inout right, j-split, newbucket);
        }
        j := j + 1;
      }

      assert forall i | 0 <= i < |left| :: lseqs(left)[i].Inv();
      assert  forall i | 0 <= i < |right| :: lseqs(right)[i].Inv();
      lseq_free(buckets');
    }

    static method EmptySeq(size: uint64) returns (linear buckets: lseq<MutBucket>)
    ensures InvLseq(buckets)
    ensures |buckets| == size as int
    ensures ILseq(buckets) == EmptyBucketList(size as int)
    {
      buckets := lseq_alloc(size);
      
      var j := 0 as uint64;
      while j < size
      invariant 0 <= j <= size
      invariant |buckets| == size as int
      invariant forall i | j as int <= i < |buckets| :: !lseq_has(buckets)[i]
      invariant forall i | 0 <= i < j as int :: lseq_has(buckets)[i]
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].Inv()
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].I() == EmptyBucket()
      {
        linear var newbucket := MutBucket.Alloc();
        buckets := lseq_give(buckets, j, newbucket);
        j := j + 1;
      }
    }

    shared method NoKeyWithPrefix(prefix: Key) returns (b: bool)
    requires Inv()
    ensures b == BucketNoKeyWithPrefix(this.I(), prefix)
    {
      var pkv := GetPkv();
      var len := PackedKV.PSA.psaNumStrings(pkv.keys);
      assert len as int == |bucket.keys|;

      if sorted {
        PackedKV.Keyspace.reveal_IsStrictlySorted();
        var i := PackedKV.PSA.BinarySearchIndexOfFirstKeyGte(pkv.keys, prefix);
        if i == len {
          AllKeysLtPrefix(prefix);
          return true;
        }

        var key : Key := PackedKV.GetKey(pkv, i);
        var isprefix := (|prefix| as uint64 <= |key| as uint64 && prefix == key[..|prefix|]);
        assert isprefix == IsPrefix(prefix, key) by { reveal_IsPrefix(); }
        b := !isprefix;

        assert b == BucketNoKeyWithPrefix(I(), prefix) by {
          if b {
            AllKeysLtPrefix(prefix);
            forall j | i as int < j < |bucket.keys| && IsPrefix(prefix, bucket.keys[j])
            ensures !IsPrefix(prefix, bucket.keys[j]) {
              KeyWithPrefixLt(prefix, key, bucket.keys[j]);
              assert false;
            }
          }
        }
      } else {
        var i := 0 as uint64;
        while i < len 
        invariant 0 <= i <= len
        invariant len as int <= |bucket.keys|
        invariant forall j | 0 <= j < i :: !IsPrefix(prefix, bucket.keys[j])
        {
          var key : Key := PackedKV.GetKey(pkv, i);
          assert key == bucket.keys[i];

          var isprefix := (|prefix| as uint64 <= |key| as uint64 && prefix == key[..|prefix|]);
          assert isprefix == IsPrefix(prefix, key) by { reveal_IsPrefix(); }
          if isprefix {
            return false;
          }
          i := i + 1;
        }
        b := true;
      }
    }

    static method SeqNoKeyWithPrefix(shared buckets: lseq<MutBucket>, prefix: Key, start: uint64, end: uint64)
    returns (b: bool)
    requires InvLseq(buckets)
    requires 0 <= start as int < end as int <= |buckets|
    requires |buckets| < 0x1_0000_0000_0000_0000
    ensures b == BucketListNoKeyWithPrefix(ILseq(buckets)[start..end], prefix)
    {
      var i := start as uint64;
      while i < end
      invariant start <= i <= end
      invariant end as int <= |buckets|
      invariant forall j | start <= j < i :: BucketNoKeyWithPrefix(lseqs(buckets)[j].I(), prefix)
      {
        b := lseq_peek(buckets, i).NoKeyWithPrefix(prefix);
        if !b {
          return false;
        }
        i := i + 1;
      }
      b := true;
    }

    static method {:timeLimitMultiplier 2} BucketListConcat(linear left: lseq<MutBucket>, linear bucket: MutBucket, linear right: lseq<MutBucket>)
    returns (linear buckets: lseq<MutBucket>)
    requires bucket.Inv()
    requires InvLseq(left)
    requires InvLseq(right)
    requires |left| + |right| + 1 < 0x1_0000_0000_0000_0000
    ensures InvLseq(buckets)
    ensures ILseq(buckets) == ILseq(left) + [bucket.I()] + ILseq(right)
    {
      var leftsize := lseq_length_as_uint64(left);
      var rightsize := lseq_length_as_uint64(right);
      var size := leftsize + rightsize + 1;

      linear var l := left;
      linear var r := right;

      buckets := lseq_alloc(size);
      ghost var gbuckets := ILseq(l) + [bucket.I()] + ILseq(r);

      var j := 0 as uint64;
      while j < leftsize
      invariant 0 <= j <= leftsize
      invariant |l| == leftsize as int
      invariant |l| < |buckets| == |gbuckets|
      invariant forall i | j as int <= i < |left| :: lseq_has(l)[i]
      invariant forall i | j as int <= i < |left| :: lseqs(l)[i].Inv()
      invariant forall i | j as int <= i < |left| :: lseqs(l)[i].I() == gbuckets[i]
      invariant forall i | j as int <= i < |buckets| :: !lseq_has(buckets)[i]
      invariant forall i | 0 <= i < j as int :: !lseq_has(l)[i]
      invariant forall i | 0 <= i < j as int :: lseq_has(buckets)[i]
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].Inv()
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].I() == gbuckets[i]
      {
        linear var newbucket := lseq_take_inout(inout l, j);
        lseq_give_inout(inout buckets, j, newbucket);
        j := j + 1;
      }

      lseq_give_inout(inout buckets, leftsize, bucket);
      assert lseq_has(buckets)[leftsize];

      j := leftsize + 1;
      while j < size
      invariant size as int == |buckets|
      invariant rightsize as int == |r|
      invariant leftsize < j <= size;
      invariant size-leftsize-1 == rightsize
      invariant forall i | 0 <= i < (j-leftsize-1) as int :: !lseq_has(r)[i];
      invariant forall i | 0 <= i < j as int :: lseq_has(buckets)[i];
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].Inv();
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].I() == gbuckets[i];
      invariant forall i | (j-leftsize-1) as int <= i < |r| :: lseq_has(r)[i]
      invariant forall i | (j-leftsize-1) as int <= i < |r| :: lseqs(r)[i].Inv()
      invariant forall i | (j-leftsize-1) as int <= i < |r| :: lseqs(r)[i].I() == gbuckets[i+leftsize as int+1]
      invariant forall i | j <= i < size :: !lseq_has(buckets)[i]
      {
        linear var newbucket := lseq_take_inout(inout r, j-leftsize-1);
        lseq_give_inout(inout buckets, j, newbucket);
        j := j + 1;
      }

      lseq_free(l);
      lseq_free(r);
    }

    static method {:timeLimitMultiplier 4} BucketListConcat3(linear left: lseq<MutBucket>, linear leftBucket: MutBucket,
      linear mid: lseq<MutBucket>, linear rightBucket: MutBucket, linear right: lseq<MutBucket>)
    returns (linear buckets: lseq<MutBucket>)
    requires leftBucket.Inv()
    requires rightBucket.Inv()
    requires InvLseq(left)
    requires InvLseq(mid)
    requires InvLseq(right)
    requires |left| + |right| + |mid| + 2 < 0x1_0000_0000_0000_0000
    ensures InvLseq(buckets)
    ensures ILseq(buckets) == ILseq(left) + [leftBucket.I()] + ILseq(mid) + [rightBucket.I()] + ILseq(right)
    {
      var leftsize := lseq_length_as_uint64(left);
      var midsize := lseq_length_as_uint64(mid);
      var rightsize := lseq_length_as_uint64(right);
      var size := leftsize + rightsize + midsize + 2;

      linear var l := left;
      linear var m := mid;
      linear var r := right;

      buckets := lseq_alloc(size);
      ghost var gbuckets := ILseq(left) + [leftBucket.I()] + ILseq(mid) + [rightBucket.I()] + ILseq(right);

      var j := 0 as uint64;
      while j < leftsize
      invariant 0 <= j <= leftsize
      invariant |l| == leftsize as int
      invariant |l| < |buckets| == |gbuckets|
      invariant forall i | j as int <= i < |left| :: lseq_has(l)[i]
      invariant forall i | j as int <= i < |left| :: lseqs(l)[i].Inv()
      invariant forall i | j as int <= i < |left| :: lseqs(l)[i].I() == gbuckets[i]
      invariant forall i | j as int <= i < |buckets| :: !lseq_has(buckets)[i]
      invariant forall i | 0 <= i < j as int :: !lseq_has(l)[i]
      invariant forall i | 0 <= i < j as int :: lseq_has(buckets)[i]
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].Inv()
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].I() == gbuckets[i]
      {
        linear var newbucket := lseq_take_inout(inout l, j);
        lseq_give_inout(inout buckets, j, newbucket);
        j := j + 1;
      }

      lseq_give_inout(inout buckets, leftsize, leftBucket);

      j := leftsize + 1;
      while j < leftsize+1+midsize
      invariant midsize as int == |m|
      invariant leftsize < j <= leftsize+1+midsize;
      invariant (leftsize+1+midsize) as int < |buckets| == |gbuckets|
      invariant forall i | 0 <= i < (j-leftsize-1) as int :: !lseq_has(m)[i];
      invariant forall i | 0 <= i < j as int :: lseq_has(buckets)[i];
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].Inv();
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].I() == gbuckets[i];
      invariant forall i | (j-leftsize-1) as int <= i < |m| :: lseq_has(m)[i]
      invariant forall i | (j-leftsize-1) as int <= i < |m| :: lseqs(m)[i].Inv()
      invariant forall i | (j-leftsize-1) as int <= i < |m| :: lseqs(m)[i].I() == gbuckets[i+leftsize as int+1]
      invariant forall i | j as int <= i < |buckets| :: !lseq_has(buckets)[i]
      {
        linear var newbucket := lseq_take_inout(inout m, j-leftsize-1);
        lseq_give_inout(inout buckets, j, newbucket);
        j := j + 1;
      }

      assert leftsize+1+midsize == j;
      lseq_give_inout(inout buckets, j, rightBucket);
  

      j := j + 1;
      while j < size
      invariant size as int == |buckets| == |gbuckets|
      invariant rightsize as int == |r|
      invariant leftsize+midsize+2 <= j <= size;
      invariant forall i | 0 <= i < (j-leftsize-midsize-2) as int :: !lseq_has(r)[i];
      invariant forall i | 0 <= i < j as int :: lseq_has(buckets)[i];
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].Inv();
      invariant forall i | 0 <= i < j as int :: lseqs(buckets)[i].I() == gbuckets[i];
      invariant forall i | (j-leftsize-midsize-2) as int <= i < |r| :: lseq_has(r)[i]
      invariant forall i | (j-leftsize-midsize-2) as int <= i < |r| :: lseqs(r)[i].Inv()
      invariant forall i | (j-leftsize-midsize-2) as int <= i < |r| :: lseqs(r)[i].I() == gbuckets[i+leftsize as int+2+midsize as int]
      invariant forall i | j as int <= i < |buckets| :: !lseq_has(buckets)[i]
      {
        linear var newbucket := lseq_take_inout(inout r, j-leftsize-midsize-2);
        lseq_give_inout(inout buckets, j, newbucket);
        j := j + 1;
      }

      lseq_free(l);
      lseq_free(m);
      lseq_free(r);
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

  method pkvList2BucketList(linear inout bots: lseq<MutBucket>, pkvs: seq<PKV.Pkv>, sorted: bool)
  requires |pkvs| < Uint64UpperBound()
  requires forall i | 0 <= i < |pkvs| :: PKV.WF(pkvs[i])
  requires forall i | 0 <= i < |pkvs| :: PackedKV.WeightPkv(pkvs[i]) as nat < Uint32UpperBound()
  requires sorted ==>
           forall i | 0 <= i < |pkvs| :: BucketWellMarshalled(PKV.I(pkvs[i]))
  requires |old_bots| == |pkvs|
  requires MutBucket.InvLseq(old_bots)
  ensures |bots| == |pkvs|
  ensures MutBucket.InvLseq(bots)
  ensures MutBucket.ILseq(bots) == DPKV.PKVISeq(pkvs)
  {
    var i: uint64 := 0;
    while i < |pkvs| as uint64
      invariant i as nat <= |pkvs|
      invariant |pkvs| == |bots|
      invariant forall j | 0 <= j < |pkvs| as int :: lseq_has(bots)[j]
      invariant forall j | 0 <= j < |pkvs| as int :: bots[j].Inv()
      invariant forall j | 0 <= j < i :: lseqs(bots)[j].bucket == PKV.I(pkvs[j])
    {
      linear var newbucket := MutBucket.AllocPkv(pkvs[i], sorted);
      linear var oldbucket := lseq_swap_inout(inout bots, i, newbucket);
      var _ := FreeMutBucket(oldbucket);
      i := i + 1;
    }
  }

  method PartialFlush(linear inout bots: lseq<MutBucket>, shared top: MutBucket,  pivots: Pivots.PivotTable)
  returns (linear newtop: MutBucket)
  requires top.Inv()
  requires MutBucket.InvLseq(old_bots)
  requires Pivots.WFPivots(pivots)
  requires |pivots| < Uint64UpperBound()
  requires Pivots.NumBuckets(pivots) == |old_bots|
  requires WeightBucket(top.I()) <= MaxTotalBucketWeight()
  requires WeightBucketList(MutBucket.ILseq(old_bots)) <= MaxTotalBucketWeight()
  ensures MutBucket.InvLseq(bots)
  ensures |bots| == |old_bots|
  ensures newtop.Inv()
  ensures partialFlushResult(newtop.I(), MutBucket.ILseq(bots))
      == BucketFlushModel.partialFlush(top.I(), pivots, MutBucket.ILseq(old_bots))
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
    pkvList2BucketList(inout bots, result.bots, sorted);
  }
}
