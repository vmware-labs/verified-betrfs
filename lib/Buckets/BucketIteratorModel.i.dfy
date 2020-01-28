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
    next: IteratorOutput,
    ghost decreaser: int
  ) 

  function SetGte(bucket: BucketMap, key: Key) : set<Key>
  {
    set k | k in bucket && Keyspace.lte(key, k)
  }

  protected predicate WFIter(bucket: Bucket, it: Iterator)
  ensures WFIter(bucket, it) ==>
      && it.decreaser >= 0
      && (it.next.Next? && bucket.Bucket? ==> (
        && it.next.key in bucket.b
        && bucket.b[it.next.key] == it.next.msg
      ))
  {
    && it.decreaser >= 0
    && (bucket.Bucket? ==> (
      && (it.next.Next? ==> (
        && it.next.key in bucket.b
        && bucket.b[it.next.key] == it.next.msg
        && it.decreaser == |SetGte(bucket.b, it.next.key)|
      ))
    ))
    && (bucket.IllMarshalledBucket? ==> (
      && |bucket.keys| - it.decreaser >= 0
      && (it.next.Next? ==> (
        && |bucket.keys| == |bucket.msgs|
        && it.decreaser > 0
        && it.next.key == bucket.keys[|bucket.keys| - it.decreaser]
        && it.next.msg == bucket.msgs[|bucket.msgs| - it.decreaser]
      ))
    ))
    && (it.next.Done? ==> (
      && it.decreaser == 0
    ))
  }

  function iterForKey(bucket: Bucket, key: Key) : (it: Iterator)
  requires bucket.Bucket?
  requires key in bucket.b
  ensures WFIter(bucket, it)
  {
    var setOfKeysGte := SetGte(bucket.b, key);
    assert key in setOfKeysGte;
    Iterator(Next(key, bucket.b[key]), |setOfKeysGte|)
  }

  function iterEnd(bucket: Bucket) : (it: Iterator)
  ensures WFIter(bucket, it)
  {
    Iterator(Done, 0)
  }

  function iterForKeyOpt(bucket: Bucket, key: Option<Key>) : (it : Iterator)
  requires bucket.IllMarshalledBucket? ==> |bucket.keys| == |bucket.msgs|
  requires bucket.Bucket? && key.Some? ==> key.value in bucket.b
  ensures WFIter(bucket, it)
  {
    assume false;
    if key.Some? then iterForKey(bucket, key.value) else iterEnd(bucket)
  }

  ///// Functions for initializing and manipulating iterators

  function {:opaque} IterStart(bucket: Bucket) : (it' : Iterator)
  ensures WFIter(bucket, it')
  {
    assume false;
    iterForKeyOpt(bucket, Keyspace.minimumOpt(bucket.b.Keys))
  }

  function {:opaque} IterFindFirstGte(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Next? ==> Keyspace.lte(key, it'.next.key)
  {
    assume false;
    iterForKeyOpt(bucket, Keyspace.minimumOpt(
        set k | k in bucket.b && Keyspace.lte(key, k)))
  }

  function {:opaque} IterFindFirstGt(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Next? ==> Keyspace.lt(key, it'.next.key)
  {
    assume false;
    iterForKeyOpt(bucket, Keyspace.minimumOpt(
        set k | k in bucket.b && Keyspace.lt(key, k)))
  }

  lemma lemmaFindFirstGtSmallerSet(bucket: Bucket, it: Iterator)
  requires bucket.Bucket?
  requires WFIter(bucket, it)
  requires it.next.Next?
  ensures IterFindFirstGt(bucket, it.next.key).decreaser < it.decreaser
  {
    var it' := IterFindFirstGt(bucket, it.next.key);
    assert it.next.key in SetGte(bucket.b, it.next.key);
    if it'.next.Next? {
      SetInclusionImpliesStrictlySmallerCardinality(
          SetGte(bucket.b, it'.next.key), SetGte(bucket.b, it.next.key));
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
  requires bucket.Bucket?
  requires WFIter(bucket, it)
  requires key in bucket.b
  requires it.next.Next?
  ensures IterInc(bucket, it).next.Next? ==>
      (Keyspace.lte(key, it.next.key) || Keyspace.lte(IterInc(bucket, it).next.key, key))
  ensures IterInc(bucket, it).next.Done? ==>
      Keyspace.lte(key, it.next.key)
  {
    reveal_IterInc();
    reveal_IterFindFirstGt();
    var it' := IterInc(bucket, it);
    if it'.next.Done? {
      if !Keyspace.lte(key, it.next.key) {
        assert key !in (set k | k in bucket.b && Keyspace.lt(it.next.key, k));
        assert false;
      }
    }
  }

  lemma IterIncKeyGreater(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  requires it.next.Next?
  requires bucket.Bucket?
  ensures IterInc(bucket, it).next.Next? ==>
      Keyspace.lt(it.next.key, IterInc(bucket, it).next.key)
  {
    reveal_IterInc();
    reveal_IterFindFirstGt();
  }

  lemma noKeyBetweenIterFindFirstGte(bucket: Bucket, key: Key, key0: Key)
  requires bucket.Bucket?
  requires key0 in bucket.b
  ensures IterFindFirstGte(bucket, key).next.Next? ==>
      (Keyspace.lt(key0, key) || Keyspace.lte(IterFindFirstGte(bucket, key).next.key, key0))
  ensures IterFindFirstGte(bucket, key).next.Done? ==>
      (Keyspace.lt(key0, key))
  {
    reveal_IterFindFirstGte();
    var it := IterFindFirstGte(bucket, key);
    if it.next.Done? {
      //assert Keyspace.minimumOpt(set k | k in bucket && Keyspace.lte(key, k)) == None;
      //assert (set k | k in bucket && Keyspace.lte(key, k)) == {};
      if !Keyspace.lt(key0, key) {
        assert key0 in (set k | k in bucket.b && Keyspace.lte(key, k));
        assert false;
      }
    }
  }

  lemma noKeyBetweenIterFindFirstGt(bucket: Bucket, key: Key, key0: Key)
  requires bucket.Bucket?
  requires key0 in bucket.b
  ensures IterFindFirstGt(bucket, key).next.Next? ==>
      (Keyspace.lte(key0, key) || Keyspace.lte(IterFindFirstGt(bucket, key).next.key, key0))
  ensures IterFindFirstGt(bucket, key).next.Done? ==>
      (Keyspace.lte(key0, key))
  {
    reveal_IterFindFirstGt();
    var it := IterFindFirstGt(bucket, key);
    if it.next.Done? {
      //assert Keyspace.minimumOpt(set k | k in bucket && Keyspace.lt(key, k)) == None;
      //assert (set k | k in bucket && Keyspace.lt(key, k)) == {};
      if !Keyspace.lte(key0, key) {
        assert key0 in (set k | k in bucket.b && Keyspace.lt(key, k));
        assert false;
      }
    }
  }

  lemma noKeyBeforeIterStart(bucket: Bucket, key0: Key)
  requires bucket.Bucket?
  requires key0 in bucket.b
  ensures IterStart(bucket).next.Next?
  ensures Keyspace.lte(IterStart(bucket).next.key, key0)
  {
    reveal_IterStart();
  }
}
