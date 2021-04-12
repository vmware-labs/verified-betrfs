// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Buckets/BucketsLib.i.dfy"
include "../lib/Buckets/TranslationLib.i.dfy"
include "../lib/Base/Sets.i.dfy"

//
// A mathematical description of bucket iterators for successor query.
//

module BucketIteratorModel {
  import opened Options
  import opened Sets
  import opened BucketsLib
  import Keyspace = Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Sequences
  import opened KeyType
  import opened BucketMaps
  import opened TranslationLib
  import MapSeqs

  datatype IteratorOutput = Next(key: Key, msg: Message) | Done

  datatype Iterator = Iterator(
    pset: Option<PrefixSet>,
    ghost next: IteratorOutput,
    ghost idx: int,
    ghost decreaser: int
  )

  function SetGte(bucket: BucketMap, key: Key) : set<Key>
  {
    set k | k in bucket && Keyspace.lte(key, k)
  }

  function SuccBucket(bucket: Bucket, pset: Option<PrefixSet>): Bucket
  requires PreWFBucket(bucket)
  {
    if pset.None? then bucket else TranslateBucket(bucket, pset.value.prefix, pset.value.newPrefix)
  }

  function SuccIdx(bucket: Bucket, pset: Option<PrefixSet>, idx: int): (i: int)
  requires PreWFBucket(bucket)
  requires 0 <= idx < |bucket.keys|
  requires pset.Some? ==> IsPrefix(pset.value.prefix, bucket.keys[idx])
  ensures 0 <= i < |SuccBucket(bucket, pset).keys|
  ensures SuccBucket(bucket, pset).keys[i] == ApplyPrefixSet(pset, bucket.keys[idx])
  {
    if pset.None? then idx else (
      var tbucket := TranslateBucketInternal(bucket, pset.value.prefix, pset.value.newPrefix, 0);
      var i :| 0 <= i < |tbucket.idxs| && tbucket.idxs[i] == idx;
      i
    )
  }

  predicate WFIterNext(bucket: Bucket, it: Iterator)
  requires PreWFBucket(bucket)
  requires it.next.Next?
  {
    && it.decreaser > 0
    && 0 <= it.idx < |bucket.keys|
    && (it.pset.Some? ==> IsPrefix(it.pset.value.prefix, bucket.keys[it.idx]))
    && it.next.key == ApplyPrefixSet(it.pset, bucket.keys[it.idx])
    && it.next.msg == bucket.msgs[it.idx]
  }

  predicate {:opaque} WFIter(bucket: Bucket, it: Iterator)
  ensures WFIter(bucket, it) ==>
      && PreWFBucket(bucket)
      && it.decreaser >= 0
      && (it.next.Next? && BucketWellMarshalled(bucket) ==> (
        && it.next.key in SuccBucket(bucket, it.pset).as_map()
        && it.next.msg == SuccBucket(bucket, it.pset).as_map()[it.next.key]
      ))
  {
    && PreWFBucket(bucket)
    && it.decreaser >= 0
    && it.idx >= 0
    && it.idx + it.decreaser == |bucket.keys|
    && |bucket.keys| == |bucket.msgs|
    && (it.next.Next? ==> WFIterNext(bucket, it))
    && (it.next.Done? ==> it.decreaser == 0)
    && (it.next.Next? && BucketWellMarshalled(bucket) ==> (
        && it.next.key in SuccBucket(bucket, it.pset).as_map()
        && it.next.msg == SuccBucket(bucket, it.pset).as_map()[it.next.key]
    ))
  }

  function iterForIndex(bucket: Bucket, pset: Option<PrefixSet>,  idx: int) : (it: Iterator)
  requires PreWFBucket(bucket)
  requires 0 <= idx <= |bucket.keys|
  requires idx < |bucket.keys| && pset.Some? ==> IsPrefix(pset.value.prefix, bucket.keys[idx])
  ensures WFIter(bucket, it)
  {
    reveal WFIter();

    var next := if idx == |bucket.keys| then Done else Next(ApplyPrefixSet(pset, bucket.keys[idx]), bucket.msgs[idx]);

    var it := Iterator(pset, next, idx, |bucket.keys| - idx);
    assert (it.next.Next? && BucketWellMarshalled(bucket) ==> (
      var succidx := SuccIdx(bucket, pset, idx);
      var succbucket := SuccBucket(bucket, pset);

      MapSeqs.MapMapsIndex(succbucket.keys, succbucket.msgs, succidx);
      && it.next.key in succbucket.as_map()
      && it.next.msg == succbucket.as_map()[it.next.key]
    ));
    it
  }

  function iterEnd(bucket: Bucket) : (it: Iterator)
  requires |bucket.keys| == |bucket.msgs|
  ensures WFIter(bucket, it)
  {
    reveal WFIter();
    Iterator(None, Done, |bucket.keys|, 0)
  }

  ///// Functions for initializing and manipulating iterators

  // linear search
  // function iterNextWithPrefix(bucket: Bucket, prefix: Key, idx: int) : (i: int)
  // requires PreWFBucket(bucket)
  // requires 0 <= idx <= |bucket.keys|
  // ensures idx <= i <= |bucket.keys|
  // ensures i < |bucket.keys| ==> IsPrefix(prefix, bucket.keys[i])
  // ensures forall j | idx <= j < i :: !IsPrefix(prefix, bucket.keys[j])
  // decreases |bucket.keys| - idx
  // {
  //   if idx < |bucket.keys| && !IsPrefix(prefix, bucket.keys[idx]) then (
  //     iterNextWithPrefix(bucket, prefix, idx+1)
  //   ) else (
  //     idx
  //   )
  // }

  function iterNextWithPrefix(bucket: Bucket, prefix: Key, idx: int) : (i: int)
  requires PreWFBucket(bucket)
  requires 0 <= idx <= |bucket.keys|
  ensures idx <= i <= |bucket.keys|
  ensures i < |bucket.keys| ==> IsPrefix(prefix, bucket.keys[i])
  ensures BucketWellMarshalled(bucket) ==> forall j | idx <= j < i :: !IsPrefix(prefix, bucket.keys[j])
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IsPrefix();

    if idx == |bucket.keys| then (
      idx
    ) else if IsPrefix(prefix, bucket.keys[idx]) then (
      idx
    ) else if Keyspace.lt(bucket.keys[idx], prefix) then (
      var i := Keyspace.binarySearchIndexOfFirstKeyGteWithLowerBound(bucket.keys, prefix, idx+1);
      AllKeysLtPrefix(prefix);

      if i < |bucket.keys| then (
        if IsPrefix(prefix, bucket.keys[i]) then (
          i
        ) else (
          AllKeysWithPrefixLt(prefix, bucket.keys[i]);
          |bucket.keys|
        )
      ) else (
        |bucket.keys|
      )
    ) else (
      AllKeysWithPrefixLt(prefix, bucket.keys[idx]);
      |bucket.keys|
    )
  }

  function {:opaque} IterStart(bucket: Bucket, pset: Option<PrefixSet>) : (it' : Iterator)
  requires WFBucket(bucket)
  ensures WFIter(bucket, it')
  ensures it'.pset == pset
  {
    reveal WFIter();

    var i := if pset.None? then 0 else iterNextWithPrefix(bucket, pset.value.prefix, 0);
    iterForIndex(bucket, pset, i)
  }

  function {:opaque} IterFindFirstGte(bucket: Bucket, pset: Option<PrefixSet>, key: Key) : (it' : Iterator)
  requires WFBucket(bucket)
  requires pset.Some? ==> IsPrefix(pset.value.newPrefix, key)
  ensures WFIter(bucket, it')
  ensures it'.pset == pset
  {
    var key' := ApplyPrefixSet(RevPrefixSet(pset), key);
    var start := Keyspace.binarySearchIndexOfFirstKeyGte(bucket.keys, key');
    var i := if pset.None? then start else iterNextWithPrefix(bucket, pset.value.prefix, start);
    iterForIndex(bucket, pset, i)
  }

  function {:opaque} IterFindFirstGt(bucket: Bucket, pset: Option<PrefixSet>, key: Key) : (it' : Iterator)
  requires WFBucket(bucket)
  requires pset.Some? ==> IsPrefix(pset.value.newPrefix, key)
  ensures WFIter(bucket, it')
  ensures it'.pset == pset
  {
    reveal WFIter();

    var key' := ApplyPrefixSet(RevPrefixSet(pset), key);
    var start := Keyspace.binarySearchIndexOfFirstKeyGt(bucket.keys, key');
    var i := if pset.None? then start else iterNextWithPrefix(bucket, pset.value.prefix, start);
    iterForIndex(bucket, pset, i)
  }

  function {:opaque} IterInc(bucket: Bucket, it: Iterator) : (it' : Iterator)
  requires WFBucket(bucket)
  requires WFIter(bucket, it)
  requires it.next.Next?
  ensures WFIter(bucket, it')
  ensures it'.pset == it.pset
  ensures it'.decreaser < it.decreaser
  {
    reveal WFIter();

    var i := if it.pset.None? then it.idx+1 else iterNextWithPrefix(bucket, it.pset.value.prefix, it.idx+1);
    iterForIndex(bucket, it.pset, i)
  }

  lemma KeyIdx(bucket: Bucket, pset:Option<PrefixSet>, key: Key) returns (i: int)
  requires PreWFBucket(bucket)
  requires key in SuccBucket(bucket, pset).as_map()
  ensures 0 <= i < |bucket.keys|
  ensures pset.Some? ==> IsPrefix(pset.value.prefix, bucket.keys[i])
  ensures ApplyPrefixSet(pset, bucket.keys[i]) == key
  {
    if pset.None? {
      i := MapSeqs.GetIndex(bucket.keys, bucket.msgs, key);
    } else {
      var tbucket := TranslateBucketInternal(bucket, pset.value.prefix, pset.value.newPrefix, 0);
      var succidx := MapSeqs.GetIndex(tbucket.b.keys, tbucket.b.msgs, key);
      i := tbucket.idxs[succidx];
    }
  }

  lemma noKeyBetweenIterAndIterInc(bucket: Bucket, it: Iterator, key: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires WFIter(bucket, it)
  requires key in SuccBucket(bucket, it.pset).as_map()
  requires it.next.Next?
  ensures IterInc(bucket, it).next.Next? ==>
      ( Keyspace.lte(key, it.next.key) || Keyspace.lte(IterInc(bucket, it).next.key, key))
  ensures IterInc(bucket, it).next.Done? ==>
        Keyspace.lte(key, it.next.key)
  {
    reveal WFIter();
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterInc();

    var idx := KeyIdx(bucket, it.pset, key);
    if it.pset.Some? {
      var itinc := IterInc(bucket, it);
      assert idx <= it.idx || itinc.idx <= idx;
      if idx <= it.idx {
        PrefixLteProperties(it.pset.value.prefix, bucket.keys[idx], bucket.keys[it.idx]);
        PrefixLteProperties(it.pset.value.newPrefix, key, it.next.key);
        assert Keyspace.lte(key, it.next.key);
      } else {
        PrefixLteProperties(it.pset.value.prefix, bucket.keys[itinc.idx], bucket.keys[idx]);
        PrefixLteProperties(it.pset.value.newPrefix, itinc.next.key, key);
        assert Keyspace.lte(itinc.next.key, key);
      }
    }   
  }

  lemma IterIncKeyGreater(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  requires it.next.Next?
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  ensures IterInc(bucket, it).next.Next? ==>
      Keyspace.lt(it.next.key, IterInc(bucket, it).next.key)
  {
    reveal WFIter();
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterInc();

    var itinc := IterInc(bucket, it);
    if itinc.next.Next? && it.pset.Some? {
      PrefixLteProperties(it.pset.value.prefix, bucket.keys[it.idx], bucket.keys[itinc.idx]);
      PrefixLteProperties(it.pset.value.newPrefix, it.next.key, itinc.next.key);
    }
  }

  lemma noKeyBetweenIterFindFirstGte(bucket: Bucket, pset: Option<PrefixSet>, key: Key, key0: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires key0 in SuccBucket(bucket, pset).as_map()
  requires pset.Some? ==> IsPrefix(pset.value.newPrefix, key)
  ensures IterFindFirstGte(bucket, pset, key).next.Next? ==>
      (Keyspace.lt(key0, key) || Keyspace.lte(IterFindFirstGte(bucket, pset, key).next.key, key0))
  ensures IterFindFirstGte(bucket, pset, key).next.Done? ==>
      (Keyspace.lt(key0, key))
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterFindFirstGte();

    var idx := KeyIdx(bucket, pset, key0);
    if pset.Some? {
      var itgte := IterFindFirstGte(bucket, pset, key);
      if itgte.next.Done? || idx < itgte.idx {
        var k := ApplyPrefixSet(RevPrefixSet(pset), key);
        assert Keyspace.lt(bucket.keys[idx], k); // observe
        PrefixLteProperties(pset.value.prefix, bucket.keys[idx], k);
        PrefixLteProperties(pset.value.newPrefix, key0, key);
        assert Keyspace.lt(key0, key);
      } else {
        PrefixLteProperties(pset.value.prefix, bucket.keys[itgte.idx], bucket.keys[idx]);
        PrefixLteProperties(pset.value.newPrefix, itgte.next.key, key0);
        assert Keyspace.lte(itgte.next.key, key0);
      }
    } 
  }

  lemma IterFindFirstGteKeyGreater(bucket: Bucket, pset: Option<PrefixSet>, key: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires pset.Some? ==> IsPrefix(pset.value.newPrefix, key)
  ensures IterFindFirstGte(bucket, pset, key).next.Next? ==> 
      Keyspace.lte(key, IterFindFirstGte(bucket, pset, key).next.key)
  {
    reveal WFIter();
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterFindFirstGte();

    var itgte := IterFindFirstGte(bucket, pset, key);
    if itgte.next.Next? && pset.Some? {
      var key' := ApplyPrefixSet(RevPrefixSet(pset), key);
      PrefixLteProperties(pset.value.prefix, key',  bucket.keys[itgte.idx]);
      PrefixLteProperties(pset.value.newPrefix, key, itgte.next.key);
    }
  }

  lemma noKeyBetweenIterFindFirstGt(bucket: Bucket, pset: Option<PrefixSet>, key: Key, key0: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires key0 in SuccBucket(bucket, pset).as_map()
  requires pset.Some? ==> IsPrefix(pset.value.newPrefix, key)
  ensures IterFindFirstGt(bucket, pset, key).next.Next? ==>
      (Keyspace.lte(key0, key) || Keyspace.lte(IterFindFirstGt(bucket, pset, key).next.key, key0))
  ensures IterFindFirstGt(bucket, pset, key).next.Done? ==>
      (Keyspace.lte(key0, key))
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterFindFirstGt();

    var idx := KeyIdx(bucket, pset, key0);
    var itgt := IterFindFirstGt(bucket, pset, key);
    if pset.Some? {
      if itgt.next.Done? || idx < itgt.idx {
        var k := ApplyPrefixSet(RevPrefixSet(pset), key);
        assert Keyspace.lte(bucket.keys[idx], k); // observe
        PrefixLteProperties(pset.value.prefix, bucket.keys[idx], k);
        PrefixLteProperties(pset.value.newPrefix, key0, key);
        assert Keyspace.lte(key0, key);
      } else {
        PrefixLteProperties(pset.value.prefix, bucket.keys[itgt.idx], bucket.keys[idx]);
        PrefixLteProperties(pset.value.newPrefix, itgt.next.key, key0);
        assert Keyspace.lte(itgt.next.key, key0);
      }
    }
  }

  lemma IterFindFirstGtKeyGreater(bucket: Bucket, pset: Option<PrefixSet>, key: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires pset.Some? ==> IsPrefix(pset.value.newPrefix, key)
  ensures IterFindFirstGt(bucket, pset, key).next.Next? ==> 
      Keyspace.lt(key, IterFindFirstGt(bucket, pset, key).next.key)
  {
    reveal WFIter();
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterFindFirstGt();

    var itgt := IterFindFirstGt(bucket, pset, key);
    if itgt.next.Next? && pset.Some? {
      var key' := ApplyPrefixSet(RevPrefixSet(pset), key);
      assert Keyspace.lt(key', bucket.keys[itgt.idx]); // observe
      PrefixLteProperties(pset.value.prefix, key', bucket.keys[itgt.idx]);
      PrefixLteProperties(pset.value.newPrefix, key, itgt.next.key);
    }
  }

  lemma noKeyBeforeIterStart(bucket: Bucket, pset: Option<PrefixSet>, key0: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires key0 in SuccBucket(bucket, pset).as_map()
  ensures IterStart(bucket, pset).next.Next?
  ensures Keyspace.lte(IterStart(bucket, pset).next.key, key0)
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterStart();

    var idx := KeyIdx(bucket, pset, key0);
    var itstart := IterStart(bucket, pset);
    if pset.Some? && itstart.idx < idx {
      PrefixLteProperties(pset.value.prefix, bucket.keys[itstart.idx], bucket.keys[idx]);
      PrefixLteProperties(pset.value.newPrefix, itstart.next.key, key0);
    }
  }

  lemma lemma_NextFromIndex(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  ensures |bucket.keys| == |bucket.msgs|
  ensures 0 <= it.idx <= |bucket.keys|
  ensures 0 <= it.idx < |bucket.keys| ==>
    && it.next.Next?
    && (it.pset.Some? ==> IsPrefix(it.pset.value.prefix, bucket.keys[it.idx]))
    && it.next.key == ApplyPrefixSet(it.pset, bucket.keys[it.idx])
    && it.next.msg == bucket.msgs[it.idx]
  ensures it.idx == |bucket.keys| ==>
    && it.next.Done?
  {
    reveal WFIter();
  }

}
