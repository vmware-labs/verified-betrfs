include "BucketsLib.i.dfy"
include "../Base/Sets.i.dfy"
//
// A mathematical description of bucket iterators.
// The implementation is defined in BucketImpl together with MutBucket.
//

module BucketIteratorModel {
  import opened Options
  import opened Sets
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences
  import opened KeyType

  datatype IteratorOutput = Next(key: Key, msg: Message) | Done

  datatype Iterator = Iterator(
    ghost next: IteratorOutput,
    ghost idx: int,
    ghost decreaser: int
  ) 

  function SetGte(bucket: BucketMap, key: Key) : set<Key>
  {
    set k | k in bucket && Keyspace.lte(key, k)
  }

  protected predicate WFIter(bucket: Bucket, it: Iterator)
  ensures WFIter(bucket, it) ==>
      && it.decreaser >= 0
      && (it.next.Next? && BucketWellMarshalled(bucket) ==> (
        && it.next.key in bucket.b
        && bucket.b[it.next.key] == it.next.msg
      ))
  {
    && it.decreaser >= 0
    && it.idx >= 0
    && it.idx + it.decreaser == |bucket.keys|
    && |bucket.keys| == |bucket.msgs|
    && (it.next.Next? ==> (
      && it.decreaser > 0
      && it.next.key == bucket.keys[it.idx]
      && it.next.msg == bucket.msgs[it.idx]
    ))
    && (it.next.Done? ==> (
      && it.decreaser == 0
    ))
    && (it.next.Next? && BucketWellMarshalled(bucket) ==> (
      && it.next.key in bucket.b
      && bucket.b[it.next.key] == it.next.msg
    ))
  }

  function iterForIndex(bucket: Bucket, idx: int) : (it: Iterator)
  requires WFBucket(bucket)
  requires |bucket.keys| == |bucket.msgs|
  requires 0 <= idx <= |bucket.keys|
  ensures WFIter(bucket, it)
  {
    var it := Iterator(
      (if idx == |bucket.keys| then Done
          else Next(bucket.keys[idx], bucket.msgs[idx])),
      idx,
      |bucket.keys| - idx);

    assert (it.next.Next? && BucketWellMarshalled(bucket) ==> (
      WFWellMarshalledBucketMapI(bucket, idx);
      && it.next.key in bucket.b
      && bucket.b[it.next.key] == it.next.msg
    ));

    it
  }

  function iterEnd(bucket: Bucket) : (it: Iterator)
  requires |bucket.keys| == |bucket.msgs|
  ensures WFIter(bucket, it)
  {
    Iterator(Done, |bucket.keys|, 0)
  }

  ///// Functions for initializing and manipulating iterators

  function {:opaque} IterStart(bucket: Bucket) : (it' : Iterator)
  requires WFBucket(bucket)
  ensures WFIter(bucket, it')
  {
    iterForIndex(bucket, 0)
  }

  function {:opaque} IterFindFirstGte(bucket: Bucket, key: Key) : (it' : Iterator)
  requires WFBucket(bucket)
  ensures WFIter(bucket, it')
  ensures it'.next.Next? ==> Keyspace.lte(key, it'.next.key)
  {
    iterForIndex(bucket,
      Keyspace.binarySearchIndexOfFirstKeyGte(bucket.keys, key))
  }

  function {:opaque} IterFindFirstGt(bucket: Bucket, key: Key) : (it' : Iterator)
  requires WFBucket(bucket)
  ensures WFIter(bucket, it')
  ensures it'.next.Next? ==> Keyspace.lt(key, it'.next.key)
  {
    iterForIndex(bucket,
      Keyspace.binarySearchIndexOfFirstKeyGt(bucket.keys, key))
  }

  function {:opaque} IterInc(bucket: Bucket, it: Iterator) : (it' : Iterator)
  requires WFBucket(bucket)
  requires WFIter(bucket, it)
  requires it.next.Next?
  ensures WFIter(bucket, it')
  ensures it'.decreaser < it.decreaser
  {
    iterForIndex(bucket, it.idx + 1)
  }

  lemma noKeyBetweenIterAndIterInc(bucket: Bucket, it: Iterator, key: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires WFIter(bucket, it)
  requires key in bucket.b
  requires it.next.Next?
  ensures IterInc(bucket, it).next.Next? ==>
      (Keyspace.lte(key, it.next.key) || Keyspace.lte(IterInc(bucket, it).next.key, key))
  ensures IterInc(bucket, it).next.Done? ==>
      Keyspace.lte(key, it.next.key)
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterInc();
  }

  lemma IterIncKeyGreater(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  requires it.next.Next?
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  ensures IterInc(bucket, it).next.Next? ==>
      Keyspace.lt(it.next.key, IterInc(bucket, it).next.key)
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterInc();
  }

  lemma noKeyBetweenIterFindFirstGte(bucket: Bucket, key: Key, key0: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires key0 in bucket.b
  ensures IterFindFirstGte(bucket, key).next.Next? ==>
      (Keyspace.lt(key0, key) || Keyspace.lte(IterFindFirstGte(bucket, key).next.key, key0))
  ensures IterFindFirstGte(bucket, key).next.Done? ==>
      (Keyspace.lt(key0, key))
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterFindFirstGte();
  }

  lemma noKeyBetweenIterFindFirstGt(bucket: Bucket, key: Key, key0: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires key0 in bucket.b
  ensures IterFindFirstGt(bucket, key).next.Next? ==>
      (Keyspace.lte(key0, key) || Keyspace.lte(IterFindFirstGt(bucket, key).next.key, key0))
  ensures IterFindFirstGt(bucket, key).next.Done? ==>
      (Keyspace.lte(key0, key))
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterFindFirstGt();
  }

  lemma noKeyBeforeIterStart(bucket: Bucket, key0: Key)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires key0 in bucket.b
  ensures IterStart(bucket).next.Next?
  ensures Keyspace.lte(IterStart(bucket).next.key, key0)
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_IterStart();
  }

  lemma lemma_NextFromIndex(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  ensures |bucket.keys| == |bucket.msgs|
  ensures 0 <= it.idx <= |bucket.keys|
  ensures 0 <= it.idx < |bucket.keys| ==>
    && it.next.Next?
    && it.next.key == bucket.keys[it.idx]
    && it.next.msg == bucket.msgs[it.idx]
  ensures it.idx == |bucket.keys| ==>
    && it.next.Done?
  {
  }
}
