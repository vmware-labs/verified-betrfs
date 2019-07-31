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

  function BucketListItemFlush(parent: Bucket, child: Bucket, pivots: PivotTable, i: int) : Bucket
  requires WFPivots(pivots)
  {
    map key
    | && (key in (child.Keys + parent.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Route(pivots, key) == i
      && Merge(BucketGet(parent, key), BucketGet(child, key)) != IdentityMessage()
    :: Merge(BucketGet(parent, key), BucketGet(child, key))
  }

  function BucketListFlush'(parent: Bucket, children: BucketList, pivots: PivotTable, i: int) : (res : BucketList)
  requires WFPivots(pivots)
  requires 0 <= i <= |children|
  ensures |res| == i
  {
    if i == 0 then [] else (
      BucketListFlush'(parent, children, pivots, i-1) + [BucketListItemFlush(parent, children[i-1], pivots, i-1)]
    )
  }

  function BucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable) : (res : BucketList)
  requires WFPivots(pivots)
  ensures |res| == |children|
  {
    BucketListFlush'(parent, children, pivots, |children|)
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

  function ClampToSlot(bucket: Bucket, pivots: PivotTable, i: int) : Bucket
  requires WFPivots(pivots)
  {
    map key | key in bucket && Route(pivots, key) == i :: bucket[key]
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

  lemma WFJoinBucketList(buckets: seq<Bucket>)
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
  ensures WFBucketList(BucketListFlush(parent, blist, pivots), pivots)

  lemma GetBucketListFlushEqMerge(blist: BucketList, pivots: PivotTable, parent: Bucket, key: Key)
  requires WFBucketList(blist, pivots)
  ensures WFBucketList(BucketListFlush(parent, blist, pivots), pivots)
  ensures BucketListGet(BucketListFlush(parent, blist, pivots), pivots, key)
      == Merge(BucketGet(parent, key), BucketListGet(blist, pivots, key))

  lemma GetJoinBucketListEq(blist: BucketList, pivots: PivotTable, key: Key)
  requires WFBucketList(blist, pivots)
  ensures BucketGet(JoinBucketList(blist), key) == BucketListGet(blist, pivots, key)
  /*{
    if |pivots| == 0 {
      assert BucketGet(buckets[Route(pivots, key)], key) == BucketGet(P.JoinBuckets(buckets), key);
    } else {
      var b1 := P.JoinBuckets(DropLast(buckets));
      var b2 := Last(buckets);

      var piv := Last(pivots);
      WFSlice(pivots, 0, |pivots| - 1);

      forall i | 0 <= i < |DropLast(buckets)| ensures P.WFBucket(DropLast(buckets)[i], DropLast(pivots), i)
      {
        var bucket := DropLast(buckets)[i];
        assert P.WFBucket(buckets[i], pivots, i);
        forall key | key in bucket ensures Route(DropLast(pivots), key) == i {
          RouteIs(DropLast(pivots), key, i);
        }
      }

      BucketLookupEqJoinLookup(DropLast(buckets), DropLast(pivots), key);


      if Keyspace.lt(key, piv) {
        assert P.WFBucket(buckets[|buckets| - 1], pivots, |buckets| - 1);
        //if (key in b2) {
        //  assert Keyspace.lte(piv, key);
        //  assert false;
        //}
        assert key !in b2;
        assert BucketGet(buckets[Route(pivots, key)], key) == BucketGet(P.JoinBuckets(buckets), key);
      } else {
        if (key in b1) {
          var i := KeyInJoinedBucketsInSomeBucket(DropLast(buckets), key);
          assert false;
        }
        assert key !in b1;
        assert BucketGet(buckets[Route(pivots, key)], key) == BucketGet(P.JoinBuckets(buckets), key);
      }
    }
  }*/

  lemma BucketListItemFlushAddParentKey(parent: Bucket, child: Bucket, pivots: PivotTable, key: Key, msg: Message)
  requires WFPivots(pivots)
  requires key !in parent
  requires key !in child
  requires msg != IdentityMessage()
  ensures BucketListItemFlush(parent, child, pivots, Route(pivots, key))[key := msg]
      == BucketListItemFlush(parent[key := msg], child, pivots, Route(pivots, key))
  {
  }

  lemma BucketListItemFlushAddChildKey(parent: Bucket, child: Bucket, pivots: PivotTable, key: Key, msg: Message)
  requires WFPivots(pivots)
  requires key !in parent
  requires key !in child
  requires msg != IdentityMessage()
  ensures BucketListItemFlush(parent, child, pivots, Route(pivots, key))[key := msg]
      == BucketListItemFlush(parent, child[key := msg], pivots, Route(pivots, key))
  {
  }

  lemma BucketListItemFlushAddParentAndChildKey(parent: Bucket, child: Bucket, pivots: PivotTable, key: Key, msgParent: Message, msgChild: Message)
  requires WFPivots(pivots)
  requires key !in parent
  requires key !in child
  requires ValueMessage.Merge(msgParent, msgChild) != IdentityMessage()
  ensures BucketListItemFlush(parent, child, pivots, Route(pivots, key))[key := ValueMessage.Merge(msgParent, msgChild)]
      == BucketListItemFlush(parent[key := msgParent], child[key := msgChild], pivots, Route(pivots, key))
  {
  }

  lemma BucketListItemFlushEmpty(pivots: seq<Key>)
  requires WFPivots(pivots)
  ensures BucketListItemFlush(map[], map[], pivots, 0) == map[]
  {
  }

  lemma BucketListItemFlushOfKeysLt(m: map<Key, Message>, pivots: seq<Key>, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < |pivots|
  requires forall key | key in m :: lt(key, pivots[i])
  ensures BucketListItemFlush(m, map[], pivots, i+1) == map[]
  {
  }

  lemma BucketListItemFlushEq(p1: Bucket, p2: Bucket, child: Bucket, pivots: seq<Key>, i: int)
  requires WFPivots(pivots)
  requires 0 <= i <= |pivots|
  requires forall key | Route(pivots, key) == i :: MapsAgreeOnKey(p1, p2, key)
  ensures BucketListItemFlush(p1, child, pivots, i)
       == BucketListItemFlush(p2, child, pivots, i)
  {
  }


  lemma SplitBucketOnPivotsAt(bucket: map<Key, Message>, pivots: seq<Key>, i: int)
  requires WFPivots(pivots)
  requires 0 <= i <= |pivots|
  ensures SplitBucketOnPivots(bucket, pivots)[i] == ClampToSlot(bucket, pivots, i)
  /*{
    if i == |pivots| {
    } else {
      var l := map key | key in bucket && lt(key, Last(pivots)) :: bucket[key];
      P.WFSlice(pivots, 0, |pivots| - 1);
      SplitBucketOnPivotsAt(l, DropLast(pivots), i);
      var a := BT.SplitBucketOnPivots(pivots, bucket)[i];
      var b := map key | key in bucket && P.Route(pivots, key) == i :: bucket[key];

      forall key | key in a
      ensures key in b
      ensures a[key] == b[key];
      {
        assert key in bucket;
        P.RouteIs(pivots, key, i);
      }

      forall key | key in b
      ensures key in a
      {
        //assert key in l;
        P.RouteIs(DropLast(pivots), key, i);
        //assert key in (map key | key in l && P.Route(DropLast(pivots), key) == i :: l[key]);
        //assert key in BT.SplitBucketOnPivots(DropLast(pivots), l)[i];
      }

      assert a == b;
    }
  }*/

  lemma AddMessagesToBucketsEmpAt(bucket: map<Key, Message>, pivots: seq<Key>, emp: seq<map<Key, Message>>, i: int)
  requires WFPivots(pivots)
  requires 0 <= i <= |pivots|
  requires |emp| == |pivots| + 1
  requires forall i | 0 <= i < |emp| :: emp[i] == map[]
  requires forall key | key in bucket :: bucket[key] != IdentityMessage();
  ensures BucketListFlush(bucket, emp, pivots)[i] == map key | key in bucket && Route(pivots, key) == i :: bucket[key]
  /*{
    var a := BucketListFlush(pivots, |emp|, emp, bucket)[i];
    var b := map key | key in bucket && P.Route(pivots, key) == i :: bucket[key];
    forall key | key in a
    ensures key in b
    ensures a[key] == b[key];
    {
      PivotBetreeSpecRefinement.AddMessagesToBucketsResult(pivots, |emp|, emp, bucket, key);
      P.RouteIs(pivots, key, i);

      //assert BT.BucketLookup(a, key) != IdentityMessage();
      //assert BT.BucketLookup(emp[i], key) == IdentityMessage();
      //assert BT.BucketLookup(bucket, key) != IdentityMessage();

      //assert key in bucket;
    }
    forall key | key in b
    ensures key in a
    {
      PivotBetreeSpecRefinement.AddMessagesToBucketsResult(pivots, |emp|, emp, bucket, key);
    }
    assert a == b;
  }*/

  lemma LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket: map<Key, Message>, pivots: seq<Key>, emp: seq<map<Key, Message>>)
  requires WFPivots(pivots)
  requires |emp| == |pivots| + 1
  requires forall i | 0 <= i < |emp| :: emp[i] == map[]
  requires forall key | key in bucket :: bucket[key] != IdentityMessage();
  ensures SplitBucketOnPivots(bucket, pivots) == BucketListFlush(bucket, emp, pivots)
  /*{
    var a := BT.SplitBucketOnPivots(pivots, bucket);
    var b := BucketListFlush(pivots, |emp|, emp, bucket);
    assert |a| == |emp|;
    assert |b| == |emp|;
    forall i | 0 <= i < |emp|
    ensures a[i] == b[i]
    {
      SplitBucketOnPivotsAt(bucket, pivots, i);
      AddMessagesToBucketsEmpAt(bucket, pivots, emp, i);
    }
  }*/
}
