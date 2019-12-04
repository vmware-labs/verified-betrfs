include "BucketsLib.i.dfy"
//
// A mathematical description of bucket iterators.
//

module BucketIterator {
  import opened Options
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences

  datatype IteratorOutput = Next(key: Key, msg: Message) | Done

  datatype Iterator = Iterator(
    next: IteratorOutput,
    ghost decreaser: int
  ) 

  predicate WFIter(bucket: Bucket, it: Iterator)
  {
    && it.decreaser >= 0
    && (it.next.Next? ==> (
      && it.next.key in bucket
      && bucket[it.next.key] == it.next.msg
      && it.decreaser > 0
    ))
    && (it.next.Done? ==> (
      && it.decreaser == 0
    ))
  }

  function iterForKey(bucket: Bucket, key: Key) : (it: Iterator)
  requires key in bucket
  ensures WFIter(bucket, it)
  {
    var setOfKeysGte := (set k | k in bucket && Keyspace.lte(key, k));
    assert key in setOfKeysGte;
    Iterator(Next(key, bucket[key]), |setOfKeysGte|)
  }

  function iterEnd(bucket: Bucket) : (it: Iterator)
  ensures WFIter(bucket, it)
  {
    Iterator(Done, 0)
  }

  function iterForKeyOpt(bucket: Bucket, key: Option<Key>) : (it : Iterator)
  requires key.Some? ==> key.value in bucket
  ensures WFIter(bucket, it)
  {
    if key.Some? then iterForKey(bucket, key.value) else iterEnd(bucket)
  }

  ///// Functions for initializing and manipulating iterators

  function {:opaque} IterStart(bucket: Bucket) : (it' : Iterator)
  ensures WFIter(bucket, it')
  {
    iterForKeyOpt(bucket, Keyspace.minimumOpt(bucket.Keys))
  }

  function {:opaque} IterFindFirstGte(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Next? ==> Keyspace.lte(key, it'.next.key)
  {
    iterForKeyOpt(bucket, Keyspace.minimumOpt(
        set k | k in bucket && Keyspace.lte(key, k)))
  }

  function {:opaque} IterFindFirstGt(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Next? ==> Keyspace.lt(key, it'.next.key)
  {
    iterForKeyOpt(bucket, Keyspace.minimumOpt(
        set k | k in bucket && Keyspace.lt(key, k)))
  }

  function {:opaque} IterInc(bucket: Bucket, it: Iterator) : (it' : Iterator)
  requires WFIter(bucket, it)
  requires it.next.Next?
  {
    IterFindFirstGt(bucket, it.next.key)
  }

  function {:opaque} IterEnd(bucket: Bucket) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Done?
  {
    iterEnd(bucket)
  }
}
