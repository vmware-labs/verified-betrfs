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

  datatype KeyMessage = KeyMessage(key: Key, msg: Message)

  datatype Iterator = Iterator(
    next: Option<KeyMessage>,
    ghost decreaser: int
  ) 

  predicate WFIter(bucket: Bucket, it: Iterator)
  {
    && it.decreaser >= 0
    && (it.next.Some? ==> (
      && it.next.value.key in bucket
      && bucket[it.next.value.key] == it.next.value.msg
      && it.decreaser > 0
    ))
    && (it.next.None? ==> (
      && it.decreaser == 0
    ))
  }

  function iterForKey(bucket: Bucket, key: Key) : (it: Iterator)
  requires key in bucket
  ensures WFIter(bucket, it)
  {
    var setOfKeysGte := (set k | k in bucket && Keyspace.lte(key, k));
    assert key in setOfKeysGte;
    Iterator(Some(KeyMessage(key, bucket[key])), |setOfKeysGte|)
  }

  function iterEnd(bucket: Bucket) : (it: Iterator)
  ensures WFIter(bucket, it)
  {
    Iterator(None, 0)
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
  ensures it'.next.Some? ==> Keyspace.lte(key, it'.next.value.key)
  {
    iterForKeyOpt(bucket, Keyspace.minimumOpt(
        set k | k in bucket && Keyspace.lte(key, k)))
  }

  function {:opaque} IterFindFirstGt(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Some? ==> Keyspace.lt(key, it'.next.value.key)
  {
    iterForKeyOpt(bucket, Keyspace.minimumOpt(
        set k | k in bucket && Keyspace.lt(key, k)))
  }

  function {:opaque} IterInc(bucket: Bucket, it: Iterator) : (it' : Iterator)
  requires WFIter(bucket, it)
  requires it.next.Some?
  {
    IterFindFirstGt(bucket, it.next.value.key)
  }

  function {:opaque} IterEnd(bucket: Bucket) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.None?
  {
    iterEnd(bucket)
  }
}
