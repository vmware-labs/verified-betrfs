include "BucketsLib.i.dfy"

module BucketWeights {
  import opened PivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import ValueWithDefault
  import opened Maps
  import opened Sequences
  import opened BucketsLib

  function WeightKey(key: Key) : int
  {
    8 + |key|
  }
 
  function WeightKeySeq(keys: seq<Key>) : int
  {
    if |keys| == 0 then 0 else WeightKeySeq(DropLast(keys)) + WeightKey(Last(keys))
  }

  function WeightMessage(msg: Message) : int
  {
    match msg {
      case Define(value) => ValueWithDefault.Len(value)
      case Update(delta) => 0
    }
  }

  function WeightMessageSeq(msgs: seq<Message>) : int
  {
    if |msgs| == 0 then 0 else WeightMessageSeq(DropLast(msgs)) + WeightMessage(Last(msgs))
  }

  function {:opaque} ChooseKey(bucket: Bucket) : (key : Key)
  requires |bucket| > 0
  ensures key in bucket
  {
    var key :| key in bucket;
    key
  }

  function {:opaque} WeightBucket(bucket: Bucket) : int
  {
    if |bucket| == 0 then 0 else (
      var key := ChooseKey(bucket);
      var msg := bucket[key];
      WeightBucket(MapRemove1(bucket, key)) + WeightKey(key) + WeightMessage(msg)
    )
  }

  function {:opaque} WeightBucketList(buckets: BucketList) : int
  {
    if |buckets| == 0 then 0 else (
      WeightBucketList(DropLast(buckets)) + WeightBucket(Last(buckets))
    )
  }

  lemma WeightSplitBucketListLeft(blist: BucketList, pivots: seq<Key>, cLeft: int, key: Key)
  requires SplitBucketListLeft.requires(blist, pivots, cLeft, key)
  ensures WeightBucketList(SplitBucketListLeft(blist, pivots, cLeft, key))
      <= WeightBucketList(blist)

  lemma WeightSplitBucketListRight(blist: BucketList, pivots: seq<Key>, cRight: int, key: Key)
  requires SplitBucketListRight.requires(blist, pivots, cRight, key)
  ensures WeightBucketList(SplitBucketListRight(blist, pivots, cRight, key))
      <= WeightBucketList(blist)

  lemma WeightBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable)
  requires WFPivots(pivots)
  ensures WeightBucketList(BucketListFlush(parent, children, pivots))
      <= WeightBucket(parent) + WeightBucketList(children)

  lemma WeightBucketListClearEntry(blist: BucketList, i: int)
  requires 0 <= i < |blist|
  ensures WeightBucketList(blist[i := map[]]) <= WeightBucketList(blist)

  lemma WeightSplitBucketInList(blist: BucketList, slot: int, pivot: Key)
  requires 0 <= slot < |blist|
  ensures WeightBucketList(SplitBucketInList(blist, slot, pivot))
      == WeightBucketList(blist)

  lemma WeightBucketListSlice(blist: BucketList, a: int, b: int)
  requires 0 <= a <= b <= |blist|
  ensures WeightBucketList(blist[a..b]) <= WeightBucketList(blist)

  lemma WeightBucketListSuffix(blist: BucketList, a: int)
  requires 0 <= a <= |blist|
  ensures WeightBucketList(blist[a..]) <= WeightBucketList(blist)

  lemma WeightBucketListConcat(left: BucketList, right: BucketList)
  ensures WeightBucketList(left + right)
      == WeightBucketList(left) + WeightBucketList(right)

  lemma WeightMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures WeightBucketList(MergeBucketsInList(blist, slot)) == WeightBucketList(blist)

  lemma WeightJoinBucketList(blist: BucketList)
  ensures WeightBucket(JoinBucketList(blist)) <= WeightBucketList(blist)

  lemma WeightSplitBucketOnPivots(bucket: Bucket, pivots: seq<Key>)
  ensures WeightBucketList(SplitBucketOnPivots(bucket, pivots)) == WeightBucket(bucket)
}
