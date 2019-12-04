include "../PivotBetree/BucketsLib.i.dfy"
include "../lib/Base/Option.s.dfy"

module ModelBucket {
  import opened Options
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences

  ///// Iterators

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

  function IterStart(bucket: Bucket) : (it' : Iterator)
  ensures WFIter(bucket, it')

  function IterFindFirstGe(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Some? ==> Keyspace.lte(key, it'.next.value.key)

  function IterFindFirstGt(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.Some? ==> Keyspace.lt(key, it'.next.value.key)

  function IterInc(bucket: Bucket, it: Iterator) : (it' : Iterator)
  requires WFIter(bucket, it)
  requires it.next.Some?
  ensures WFIter(bucket, it')
  ensures it'.decreaser < it.decreaser

  function IterEnd(bucket: Bucket) : (it' : Iterator)
  ensures WFIter(bucket, it')
  ensures it'.next.None?

  function decreaserSum(its: seq<Iterator>) : int
  ensures decreaserSum(its) >= 0
  {
    if |its| == 0 then 0 else decreaserSum(DropLast(its)) + Last(its).decreaser
  }

  lemma noKeyBetweenIterAndIterInc(bucket: Bucket, it: Iterator, key: Key)
  requires WFIter(bucket, it)
  requires key in bucket
  requires it.next.Some?
  ensures IterInc(bucket, it).next.Some? ==>
      (Keyspace.lte(key, it.next.value.key) || Keyspace.lte(IterInc(bucket, it).next.value.key, key))
  ensures IterInc(bucket, it).next.None? ==>
      Keyspace.lte(key, it.next.value.key)

  lemma IterIncKeyGreater(bucket: Bucket, it: Iterator)
  requires WFIter(bucket, it)
  requires it.next.Some?
  ensures IterInc(bucket, it).next.Some? ==>
      Keyspace.lt(it.next.value.key, IterInc(bucket, it).next.value.key)

  lemma noKeyBetweenIterFindFirstGe(bucket: Bucket, key: Key, key0: Key)
  requires key0 in bucket
  ensures IterFindFirstGe(bucket, key).next.Some? ==>
      (Keyspace.lt(key0, key) || Keyspace.lte(IterFindFirstGe(bucket, key).next.value.key, key0))
  ensures IterFindFirstGe(bucket, key).next.None? ==>
      (Keyspace.lt(key0, key))

  lemma noKeyBetweenIterFindFirstGt(bucket: Bucket, key: Key, key0: Key)
  requires key0 in bucket
  ensures IterFindFirstGt(bucket, key).next.Some? ==>
      (Keyspace.lte(key0, key) || Keyspace.lte(IterFindFirstGt(bucket, key).next.value.key, key0))
  ensures IterFindFirstGt(bucket, key).next.None? ==>
      (Keyspace.lte(key0, key))

  lemma noKeyBeforeIterStart(bucket: Bucket, key0: Key)
  requires key0 in bucket
  ensures IterStart(bucket).next.Some?
  ensures Keyspace.lte(IterStart(bucket).next.value.key, key0)
}
