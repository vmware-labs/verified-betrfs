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

  function IterFindFirstGt(bucket: Bucket, key: Key) : (it' : Iterator)
  ensures WFIter(bucket, it')

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
}
