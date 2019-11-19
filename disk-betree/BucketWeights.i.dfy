include "BucketsLib.i.dfy"
//
// Assigning weights to buckets guides the flushing algorithm to decide
// which child to push messages towards. TODO(thance): help!
//

module BucketWeights {
  import opened PivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import ValueWithDefault`Internal
  import opened Maps
  import opened Sequences
  import opened BucketsLib
  import opened NativeTypes

  function WeightKey(key: Key) : (w:int)
  ensures w >= 0
  {
    8 + |key|
  }
 
  function WeightKeySeq(keys: seq<Key>) : (w:int)
  ensures w >= 0
  {
    if |keys| == 0 then 0 else WeightKeySeq(DropLast(keys)) + WeightKey(Last(keys))
  }

  function WeightMessage(msg: Message) : (w:int)
  ensures w >= 0
  {
    match msg {
      case Define(value) => 8 + ValueWithDefault.Len(value)
      case Update(delta) => 0
    }
  }

  function method WeightKeyUint64(key: Key) : (w:uint64)
  ensures w as int == WeightKey(key)
  {
    8 + |key| as uint64
  }

  function method WeightMessageUint64(msg: Message) : (w:uint64)
  ensures w as int == WeightMessage(msg)
  {
    match msg {
      case Define(value) => 8 + |value| as uint64
      case Update(delta) => 0
    }
  }

  function WeightMessageSeq(msgs: seq<Message>) : (w:int)
  ensures w >= 0
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

  function {:opaque} WeightBucket(bucket: Bucket) : (w:int)
  ensures w >= 0
  {
    if |bucket| == 0 then 0 else (
      var key := ChooseKey(bucket);
      var msg := bucket[key];
      WeightBucket(MapRemove1(bucket, key)) + WeightKey(key) + WeightMessage(msg)
    )
  }

  function {:opaque} WeightBucketList(buckets: BucketList) : (w:int)
  ensures w >= 0
  {
    if |buckets| == 0 then 0 else (
      WeightBucketList(DropLast(buckets)) + WeightBucket(Last(buckets))
    )
  }

  lemma WeightBucketInduct(bucket: Bucket, key: Key, msg: Message)
  requires key !in bucket
  ensures WeightBucket(bucket[key := msg]) == WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)

  lemma WeightSplitBucketLeft(bucket: Bucket, key: Key)
  ensures WeightBucket(SplitBucketLeft(bucket, key)) <= WeightBucket(bucket)

  lemma WeightSplitBucketRight(bucket: Bucket, key: Key)
  ensures WeightBucket(SplitBucketRight(bucket, key)) <= WeightBucket(bucket)

  lemma WeightSplitBucketAdditive(bucket: Bucket, key: Key)
  ensures WeightBucket(SplitBucketLeft(bucket, key)) +
          WeightBucket(SplitBucketRight(bucket, key)) == WeightBucket(bucket)

  lemma WeightBucketList2(a: Bucket, b: Bucket)
  ensures WeightBucketList([a,b]) == WeightBucket(a) + WeightBucket(b)

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

  lemma WeightBucketListItemFlush(parent: Bucket, children: BucketList, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  ensures WeightBucket(BucketListItemFlush(parent, children[i], pivots, i))
      <= WeightBucket(parent) + WeightBucket(children[i])

  lemma WeightBucketListShrinkEntry(blist: BucketList, i: int, bucket: Bucket)
  requires 0 <= i < |blist|
  requires WeightBucket(bucket) <= WeightBucket(blist[i])
  ensures WeightBucketList(blist[i := bucket]) <= WeightBucketList(blist)

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

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma LenLeWeight(bucket: Bucket)
  ensures |bucket| <= WeightBucket(bucket)

  lemma WeightBucketEmpty()
  ensures WeightBucket(map[]) == 0
  {
    reveal_WeightBucket();
  }

  lemma WeightBucketListOneEmpty()
  ensures WeightBucketList([map[]]) == 0

  lemma WeightBucketPut(bucket: Bucket, key: Key, msg: Message)
  ensures WeightBucket(bucket[key := msg]) <=
      WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)

  lemma WeightBucketLeBucketList(blist: BucketList, i: int)
  requires 0 <= i < |blist|
  ensures WeightBucket(blist[i]) <= WeightBucketList(blist)

  lemma WeightBucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message)
  requires WFBucketList(blist, pivots)
  ensures WeightBucketList(BucketListInsert(blist, pivots, key, msg)) <=
      WeightBucketList(blist) + WeightKey(key) + WeightMessage(msg)

  lemma WeightBucketIntersect(bucket: Bucket, keys: set<Key>)
  ensures WeightBucket(BucketIntersect(bucket, keys)) <= WeightBucket(bucket)

  lemma WeightBucketComplement(bucket: Bucket, keys: set<Key>)
  ensures WeightBucket(BucketComplement(bucket, keys)) <= WeightBucket(bucket)

  lemma WeightMessageBound(msg: Message)
  ensures WeightMessage(msg) <= 8 + 1024
}
