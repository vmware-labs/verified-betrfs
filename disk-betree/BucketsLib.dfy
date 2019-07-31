include "PivotsLib.dfy"
include "Message.dfy"
include "../lib/maps.dfy"

module BucketsLib {
  import opened PivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Maps
  import opened Sequences

  type Bucket = map<Key, Message>
  type BucketList = seq<Bucket>

  predicate {:opaque} WFBucket(bucket: Bucket)
  {
    && (forall key | key in bucket :: bucket[key] != IdentityMessage())
  }

  predicate WFBucketAt(bucket: Bucket, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  {
    && (forall key | key in bucket :: bucket[key] != IdentityMessage())
    && (forall key | key in bucket :: Route(pivots, key) == i)
  }

  predicate WFBucketList(blist: BucketList, pivots: PivotTable)
  {
    && WFPivots(pivots)
    && |blist| == |pivots| + 1
    && (forall i | 0 <= i < |blist| :: WFBucketAt(blist[i], pivots, i))
  }

  function BucketGet(bucket: Bucket, key: Key) : Message
  {
    if key in bucket then bucket[key] else IdentityMessage()
  }

  function BucketListGet(blist: BucketList, pivots: PivotTable, key: Key) : Message
  requires WFBucketList(blist, pivots)
  {
    BucketGet(blist[Route(pivots, key)], key)
  }

  function BucketInsert(bucket: Bucket, key: Key, msg: Message) : Bucket
  {
    var msg := Merge(msg, BucketGet(bucket, key));
    if msg == IdentityMessage() then
      MapRemove1(bucket, key)
    else
      bucket[key := msg]
  }

  function BucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message) : BucketList
  requires WFBucketList(blist, pivots)
  {
    var i := Route(pivots, key);
    blist[i := BucketInsert(blist[i], key, msg)]
  }

  function BucketListItemFlush(child: Bucket, pivots: PivotTable, parent: Bucket, i: int) : Bucket
  requires WFPivots(pivots)
  {
    map key
    | && (key in (child.Keys + parent.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Route(pivots, key) == i
      && Merge(BucketGet(parent, key), BucketGet(child, key)) != IdentityMessage()
    :: Merge(BucketGet(parent, key), BucketGet(child, key))
  }

  function BucketListFlush'(blist: BucketList, pivots: PivotTable, parent: Bucket, i: int) : BucketList
  requires WFBucketList(blist, pivots)
  requires 0 <= i <= |blist|
  {
    if i == 0 then [] else (
      BucketListFlush'(blist, pivots, parent, i-1) + [BucketListItemFlush(blist[i-1], pivots, parent, i-1)]
    )
  }

  function BucketListFlush(blist: BucketList, pivots: PivotTable, parent: Bucket) : BucketList
  requires WFBucketList(blist, pivots)
  {
    BucketListFlush'(blist, pivots, parent, |blist|)
  }

  function JoinBucketList(buckets: seq<Bucket>) : (bucket : Bucket)
  {
    if |buckets| == 0 then map[] else MapUnion(JoinBucketList(DropLast(buckets)), Last(buckets))
  }

  function SplitBucketOnPivots(bucket: Bucket, pivots: seq<Key>) : (buckets: BucketList)
  ensures |buckets| == |pivots| + 1
  {
    if |pivots| == 0 then (
      [bucket]
    ) else (
      var l := map key | key in bucket && Keyspace.lt(key, Last(pivots)) :: bucket[key];
      var r := map key | key in bucket && Keyspace.lte(Last(pivots), key) :: bucket[key];

      SplitBucketOnPivots(l, DropLast(pivots)) + [r]
    )
  }

  ///// Splitting stuff

  function SplitBucketLeft(bucket: Bucket, pivot: Key) : Bucket
  {
    map key | key in bucket && Keyspace.lt(key, pivot) :: bucket[key]
  }

  function SplitBucketRight(bucket: Bucket, pivot: Key) : Bucket
  {
    map key | key in bucket && Keyspace.lte(pivot, key) :: bucket[key]
  }

  function SplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key) : BucketList
  requires WFBucketList(blist, pivots)
  requires CutoffForLeft(pivots, key) == cLeft
  {
    blist[.. cLeft] + [SplitBucketLeft(blist[cLeft], key)]
  }

  function SplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key) : BucketList
  requires WFBucketList(blist, pivots)
  requires CutoffForRight(pivots, key) == cRight
  {
    [SplitBucketRight(blist[cRight], key)] + blist[cRight + 1 ..]
  }

  lemma WFSplitBucketLeft(bucket: Bucket, pivot: Key, pivots: seq<Key>, i: int)
  requires 0 <= i <= |pivots|
  requires WFPivots(pivots)
  requires WFBucketAt(bucket, pivots, i)
  ensures WFPivots(pivots[.. i])
  ensures WFBucketAt(SplitBucketLeft(bucket, pivot), pivots[.. i], i)
  {
    WFSlice(pivots, 0, i);
    forall key | key in SplitBucketLeft(bucket, pivot)
    ensures Route(pivots[.. i], key) == i
    {
      RouteIs(pivots[.. i], key, i);
    }
  }

  lemma WFSplitBucketRight(bucket: Bucket, pivot: Key, pivots: seq<Key>, i: int)
  requires 0 <= i <= |pivots|
  requires WFPivots(pivots)
  requires WFBucketAt(bucket, pivots, i)
  ensures WFPivots(pivots[i ..])
  ensures WFBucketAt(SplitBucketRight(bucket, pivot), pivots[i ..], 0)
  {
    WFSuffix(pivots, i);
    forall key | key in SplitBucketRight(bucket, pivot)
    ensures Route(pivots[i ..], key) == 0
    {
      RouteIs(pivots[i ..], key, 0);
    }
  }

  lemma WFSplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key)
  requires WFBucketList(blist, pivots)
  requires CutoffForLeft(pivots, key) == cLeft
  ensures WFBucketList(SplitBucketListLeft(blist, pivots, cLeft, key), pivots[.. cLeft])

  lemma WFSplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key)
  requires WFBucketList(blist, pivots)
  requires CutoffForRight(pivots, key) == cRight
  ensures WFBucketList(SplitBucketListRight(blist, pivots, cRight, key), pivots[cRight ..])

  // This is useful for proving NodeHasWFBuckets(node')
  // for indices over the given interval [a, b],
  // assuming we already know the buckets and pivots come from some other
  // well-formed node (possibly shifted by the amount d).
  lemma BucketListHasWFBucketAtIdenticalSlice(
      blist: BucketList, pivots: PivotTable, blist': BucketList, pivots': PivotTable, a: int, b: int, d: int)
  requires WFBucketList(blist, pivots)
  requires WFPivots(pivots')
  requires |pivots'| + 1 == |blist'|
  requires 0 <= a
  requires b < |blist'|
  requires a-d >= 0
  requires b-d < |blist|
  requires forall i | a <= i <= b :: blist'[i] == blist[i-d]
  requires forall i | a <= i < b :: pivots'[i] == pivots[i-d]
  requires b >= a && b < |pivots'| ==> (
      || (b-d < |pivots| && pivots'[b] == pivots[b-d])
      || (forall key | key in blist'[b] :: Keyspace.lt(key, pivots'[b]))
    )
  requires b >= a && a-1 >= 0 ==> (
      || (a-1-d >= 0 && pivots'[a-1] == pivots[a-1-d])
      || (forall key | key in blist'[a] :: Keyspace.lte(pivots'[a-1], key))
    )
  ensures forall i | a <= i <= b :: WFBucketAt(blist'[i], pivots', i)
  /*{
    forall i | a <= i <= b
    ensures NodeHasWFBucketAt(node', i)
    {
      assert NodeHasWFBucketAt(node, i - d);
      forall key | key in node'.buckets[i]
      {
        Pivots.RouteIs(node'.pivotTable, key, i);
      }
    }
  }*/

  ///// Other lemmas

  lemma JoinBucketsSplitBucketOnPivotsCancel(bucket: Bucket, pivots: seq<Key>)
  requires WFPivots(pivots)
  requires WFBucket(bucket)
  ensures WFBucketList(SplitBucketOnPivots(bucket, pivots), pivots)
  ensures JoinBucketList(SplitBucketOnPivots(bucket, pivots)) == bucket
  /*
  {
    if |pivots| == 0 {
    } else {
      var l := map key | key in bucket && Keyspace.lt(key, Last(pivots)) :: bucket[key];
      var r := map key | key in bucket && Keyspace.lte(Last(pivots), key) :: bucket[key];

      var bucketsPref := SplitBucketOnPivots(DropLast(pivots), l);
      Pivots.WFSlice(pivots, 0, |pivots| - 1);
      SplitBucketOnPivotsCorrect(DropLast(pivots), l, bucketsPref);

      forall i | 0 <= i < |buckets|
      ensures WFBucket(buckets[i], pivots, i)
      {
        if i < |buckets| - 1 {
          assert WFBucket(bucketsPref[i], DropLast(pivots), i);
          forall key | key in buckets[i] ensures Pivots.Route(pivots, key) == i
          {
            assert Pivots.Route(DropLast(pivots), key) == i;
            assert buckets[i] == bucketsPref[i];
            assert key in bucketsPref[i];
            assert key in l;
            Pivots.RouteIs(pivots, key, i);
          }
          assert WFBucket(buckets[i], pivots, i);
        } else {
          forall key | key in buckets[i] ensures Pivots.Route(pivots, key) == i
          {
            Pivots.RouteIs(pivots, key, i);
          }
          assert WFBucket(buckets[i], pivots, i);
        }
      }
    }
  }
  */

  lemma WFJoinBuckets(buckets: seq<Bucket>)
  ensures WFBucket(JoinBucketList(buckets))
  /*
  {
    if |buckets| == 0 {
    } else {
      JoinBucketsNoIdentity(DropLast(buckets));
    }
  }
  */

  lemma WFBucketListFlush(blist: BucketList, pivots: PivotTable, parent: Bucket)
  requires WFBucketList(blist, pivots)
  ensures WFBucketList(BucketListFlush(blist, pivots, parent), pivots)
}
