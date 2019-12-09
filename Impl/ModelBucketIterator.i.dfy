include "../PivotBetree/BucketsLib.i.dfy"
include "../lib/Base/Sets.i.dfy"
//
// A mathematical description of bucket iterators.
//

module ModelBucketIterator {
  import opened Options
  import opened Sets
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences

  datatype IteratorOutput = Next(key: Key, msg: Message) | Done

  datatype Iterator = Iterator(
    next: IteratorOutput,
    ghost decreaser: int
  ) 

  function SetGte(bucket: Bucket, key: Key) : set<Key>
  {
    set k | k in bucket && Keyspace.lte(key, k)
  }

  protected predicate WFIter(bucket: Bucket, it: Iterator)
  ensures WFIter(bucket, it) ==>
      && it.decreaser >= 0
      && (it.next.Next? ==> (
        && it.next.key in bucket
        && bucket[it.next.key] == it.next.msg
      ))
  {
    && (it.next.Next? ==> (
      && it.next.key in bucket
      && bucket[it.next.key] == it.next.msg
      && it.decreaser == |SetGte(bucket, it.next.key)|
    ))
    && (it.next.Done? ==> (
      && it.decreaser == 0
    ))
  }

  function iterForKey(bucket: Bucket, key: Key) : (it: Iterator)
  requires key in bucket
  ensures WFIter(bucket, it)
  {
    var setOfKeysGte := SetGte(bucket, key);
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

  lemma lemmaFindFirstGtSmallerSet(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  requires it.next.Next?
  ensures IterFindFirstGt(bucket, it.next.key).decreaser < it.decreaser
  {
    var it' := IterFindFirstGt(bucket, it.next.key);
    assert it.next.key in SetGte(bucket, it.next.key);
    if it'.next.Next? {
      SetInclusionImpliesStrictlySmallerCardinality(
          SetGte(bucket, it'.next.key), SetGte(bucket, it.next.key));
    }
  }

  function {:opaque} IterInc(bucket: Bucket, it: Iterator) : (it' : Iterator)
  requires WFIter(bucket, it)
  requires it.next.Next?
  ensures WFIter(bucket, it')
  ensures it'.decreaser < it.decreaser
  {
    lemmaFindFirstGtSmallerSet(bucket, it);
    IterFindFirstGt(bucket, it.next.key)
  }

  lemma noKeyBetweenIterAndIterInc(bucket: Bucket, it: Iterator, key: Key)
  requires WFIter(bucket, it)
  requires key in bucket
  requires it.next.Next?
  ensures IterInc(bucket, it).next.Next? ==>
      (Keyspace.lte(key, it.next.key) || Keyspace.lte(IterInc(bucket, it).next.key, key))
  ensures IterInc(bucket, it).next.Done? ==>
      Keyspace.lte(key, it.next.key)

  lemma IterIncKeyGreater(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  requires it.next.Next?
  ensures IterInc(bucket, it).next.Next? ==>
      Keyspace.lt(it.next.key, IterInc(bucket, it).next.key)

  lemma noKeyBetweenIterFindFirstGte(bucket: Bucket, key: Key, key0: Key)
  requires key0 in bucket
  ensures IterFindFirstGte(bucket, key).next.Next? ==>
      (Keyspace.lt(key0, key) || Keyspace.lte(IterFindFirstGte(bucket, key).next.key, key0))
  ensures IterFindFirstGte(bucket, key).next.Done? ==>
      (Keyspace.lt(key0, key))

  lemma noKeyBetweenIterFindFirstGt(bucket: Bucket, key: Key, key0: Key)
  requires key0 in bucket
  ensures IterFindFirstGt(bucket, key).next.Next? ==>
      (Keyspace.lte(key0, key) || Keyspace.lte(IterFindFirstGt(bucket, key).next.key, key0))
  ensures IterFindFirstGt(bucket, key).next.Done? ==>
      (Keyspace.lte(key0, key))

  lemma noKeyBeforeIterStart(bucket: Bucket, key0: Key)
  requires key0 in bucket
  ensures IterStart(bucket).next.Next?
  ensures Keyspace.lte(IterStart(bucket).next.key, key0)
}
