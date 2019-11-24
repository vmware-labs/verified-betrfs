include "../PivotBetree/PivotsLib.i.dfy"
include "../lib/Base/Message.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/total_order.i.dfy"
//
// A Bucket maps keys to Messages. A BucketList imparts a Message meaning
// to every key obeying the Message composition rules. This module shows
// how pushing messages down a tree towards a child still produces equivalent
// values as viewed through the Message chain.
//

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

  function {:opaque} BucketIntersect(bucket: Bucket, keys: set<Key>) : Bucket
  {
    map key | key in bucket && key in keys :: bucket[key]
  }

  function {:opaque} BucketComplement(bucket: Bucket, keys: set<Key>) : Bucket
  {
    map key | key in bucket && key !in keys :: bucket[key]
  }

  lemma WFBucketIntersect(bucket: Bucket, keys: set<Key>)
  requires WFBucket(bucket)
  ensures WFBucket(BucketIntersect(bucket, keys))
  {
    reveal_WFBucket();
    reveal_BucketIntersect();
  }

  lemma WFBucketComplement(bucket: Bucket, keys: set<Key>)
  requires WFBucket(bucket)
  ensures WFBucket(BucketComplement(bucket, keys))
  {
    reveal_WFBucket();
    reveal_BucketComplement();
  }

  ///// Splitting stuff

  // NB(jonh): These definitions are timeout monsters.
  function {:opaque} SplitBucketLeft(bucket: Bucket, pivot: Key) : Bucket
  {
    map key | key in bucket && Keyspace.lt(key, pivot) :: bucket[key]
  }

  function {:opaque} SplitBucketRight(bucket: Bucket, pivot: Key) : Bucket
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

  function {:opaque} SplitBucketInList(blist: BucketList, slot: int, pivot: Key) : BucketList
  requires 0 <= slot < |blist|
  {
    replace1with2(blist,
        SplitBucketLeft(blist[slot], pivot),
        SplitBucketRight(blist[slot], pivot),
        slot)
  }

  function {:opaque} MergeBuckets(left: Bucket, right: Bucket) : Bucket
  {
    MapUnionPreferA(left, right)
  }

  function {:opaque} MergeBucketsInList(blist: BucketList, slot: int) : (blist' : BucketList)
  requires 0 <= slot < |blist| - 1
  ensures |blist'| == |blist| - 1
  {
    replace2with1(blist,
        MergeBuckets(blist[slot], blist[slot+1]),
        slot)
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
  {
    WFSlice(pivots, 0, cLeft);

    var res := SplitBucketListLeft(blist, pivots, cLeft, key);
    forall i | 0 <= i < |res|
    ensures WFBucketAt(res[i], pivots[..cLeft], i)
    {
      forall key | key in res[i]
      ensures Route(pivots[..cLeft], key) == i
      {
        RouteIs(pivots[..cLeft], key, i);
      }
    }
  }

  lemma WFSplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key)
  requires WFBucketList(blist, pivots)
  requires CutoffForRight(pivots, key) == cRight
  ensures WFBucketList(SplitBucketListRight(blist, pivots, cRight, key), pivots[cRight ..])
  {
    WFSuffix(pivots, cRight);

    var res := SplitBucketListRight(blist, pivots, cRight, key);
    forall i | 0 <= i < |res|
    ensures WFBucketAt(res[i], pivots[cRight..], i)
    {
      forall key | key in res[i]
      ensures Route(pivots[cRight..], key) == i
      {
        RouteIs(pivots[cRight..], key, i);
      }
    }
  }

  lemma WFSplitBucketInList(blist: BucketList, slot: int, pivot: Key, pivots: PivotTable)
  requires WFBucketList(blist, pivots)
  requires 0 <= slot < |blist|
  requires PivotInsertable(pivots, slot, pivot)
  ensures WFPivots(insert(pivots, pivot, slot))
  ensures WFBucketList(SplitBucketInList(blist, slot, pivot), insert(pivots, pivot, slot))
  {
    reveal_SplitBucketInList();

    var blist' := SplitBucketInList(blist, slot, pivot);
    var pivots' := insert(pivots, pivot, slot);
    WFPivotsInsert(pivots, slot, pivot);

    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', 0, slot-1, 0);
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', slot+2, |blist'|-1, 1);
    assert WFBucketAt(blist'[slot], pivots', slot);
    assert WFBucketAt(blist'[slot+1], pivots', slot+1);
  }

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
  {
    forall i | a <= i <= b
    ensures WFBucketAt(blist'[i], pivots', i)
    {
      assert WFBucketAt(blist[i-d], pivots, i - d);
      forall key | key in blist'[i]
      {
        RouteIs(pivots', key, i);
      }
    }
  }

  lemma WFMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures WFBucketList(MergeBucketsInList(blist, slot), remove(pivots, slot))
  {
    reveal_MergeBucketsInList();
    WFPivotsRemoved(pivots, slot);
    var blist' := MergeBucketsInList(blist, slot);
    var pivots' := remove(pivots, slot);
    BucketListHasWFBucketAtIdenticalSlice(
        blist, pivots, blist', pivots', 0, slot-1, 0);
    BucketListHasWFBucketAtIdenticalSlice(
        blist, pivots, blist', pivots', slot+1, |blist'|-1, -1);
    reveal_MergeBuckets();
    assert WFBucketAt(blist'[slot], pivots', slot);
  }

  lemma SplitOfMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures SplitBucketLeft(MergeBucketsInList(blist, slot)[slot], pivots[slot]) == blist[slot]
  ensures SplitBucketRight(MergeBucketsInList(blist, slot)[slot], pivots[slot]) == blist[slot+1]
  {
    reveal_MergeBucketsInList();
    reveal_MergeBuckets();
  }

  ///// Other lemmas

  lemma WFJoinBucketList(buckets: seq<Bucket>)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  ensures WFBucket(JoinBucketList(buckets))
  {
    reveal_WFBucket();
    if |buckets| == 0 {
    } else {
      WFJoinBucketList(DropLast(buckets));
    }
  }

  lemma BucketListFlush'At(parent: Bucket, blist: BucketList, pivots: PivotTable, j: int, i: int)
  requires 0 <= i < j <= |blist|
  requires WFPivots(pivots)
  ensures BucketListFlush'(parent, blist, pivots, j)[i] == BucketListItemFlush(parent, blist[i], pivots, i)
  {
    if j == i + 1 {
    } else {
      BucketListFlush'At(parent, blist, pivots, j-1, i);
    }
  }

  lemma BucketListFlushAt(parent: Bucket, blist: BucketList, pivots: PivotTable, i: int)
  requires 0 <= i < |blist|
  requires WFPivots(pivots)
  ensures BucketListFlush(parent, blist, pivots)[i] == BucketListItemFlush(parent, blist[i], pivots, i)
  {
    BucketListFlush'At(parent, blist, pivots, |blist|, i);
  }

  lemma WFBucketListFlush(parent: Bucket, blist: BucketList, pivots: PivotTable)
  requires WFBucketList(blist, pivots)
  ensures WFBucketList(BucketListFlush(parent, blist, pivots), pivots)
  {
    var f := BucketListFlush(parent, blist, pivots);
    forall i | 0 <= i < |f|
    ensures WFBucketAt(f[i], pivots, i)
    {
      BucketListFlushAt(parent, blist, pivots, i);
    }
  }

  lemma GetBucketListFlushEqMerge(parent: Bucket, blist: BucketList, pivots: PivotTable, key: Key)
  requires WFBucketList(blist, pivots)
  ensures WFBucketList(BucketListFlush(parent, blist, pivots), pivots)
  ensures BucketListGet(BucketListFlush(parent, blist, pivots), pivots, key)
      == Merge(BucketGet(parent, key), BucketListGet(blist, pivots, key))
  {
    WFBucketListFlush(parent, blist, pivots);
    var i := Route(pivots, key);
    BucketListFlushAt(parent, blist, pivots, i);
  }

  lemma KeyInJoinedBucketsInSomeBucket(buckets: seq<Bucket>, key: Key)
  returns (i : int)
  requires key in JoinBucketList(buckets)
  ensures 0 <= i < |buckets|
  ensures key in buckets[i]
  {
    assert |buckets| > 0;
    if key in Last(buckets) {
      i := |buckets| - 1;
    } else {
      i := KeyInJoinedBucketsInSomeBucket(DropLast(buckets), key);
    }
  }

  lemma GetJoinBucketListEq(blist: BucketList, pivots: PivotTable, key: Key)
  requires WFBucketList(blist, pivots)
  ensures BucketGet(JoinBucketList(blist), key) == BucketListGet(blist, pivots, key)
  {
    if |pivots| == 0 {
      assert BucketGet(blist[Route(pivots, key)], key) == BucketGet(JoinBucketList(blist), key);
    } else {
      var b1 := JoinBucketList(DropLast(blist));
      var b2 := Last(blist);

      var piv := Last(pivots);
      WFSlice(pivots, 0, |pivots| - 1);

      forall i | 0 <= i < |DropLast(blist)| ensures WFBucketAt(DropLast(blist)[i], DropLast(pivots), i)
      {
        var bucket := DropLast(blist)[i];
        assert WFBucketAt(blist[i], pivots, i);
        forall key | key in bucket ensures Route(DropLast(pivots), key) == i {
          RouteIs(DropLast(pivots), key, i);
        }
      }

      GetJoinBucketListEq(DropLast(blist), DropLast(pivots), key);

      if Keyspace.lt(key, piv) {
        assert WFBucketAt(blist[|blist| - 1], pivots, |blist| - 1);
        //if (key in b2) {
        //  assert Keyspace.lte(piv, key);
        //  assert false;
        //}
        assert key !in b2;
        assert BucketGet(blist[Route(pivots, key)], key) == BucketGet(JoinBucketList(blist), key);
      } else {
        if (key in b1) {
          var i := KeyInJoinedBucketsInSomeBucket(DropLast(blist), key);
          assert false;
        }
        assert key !in b1;
        assert BucketGet(blist[Route(pivots, key)], key) == BucketGet(JoinBucketList(blist), key);
      }
    }
  }

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
  {
    if i == |pivots| {
    } else {
      var l := map key | key in bucket && lt(key, Last(pivots)) :: bucket[key];
      WFSlice(pivots, 0, |pivots| - 1);
      SplitBucketOnPivotsAt(l, DropLast(pivots), i);
      var a := SplitBucketOnPivots(bucket, pivots)[i];
      var b := map key | key in bucket && Route(pivots, key) == i :: bucket[key];

      forall key | key in a
      ensures key in b
      ensures a[key] == b[key];
      {
        assert key in bucket;
        RouteIs(pivots, key, i);
      }

      forall key | key in b
      ensures key in a
      {
        //assert key in l;
        RouteIs(DropLast(pivots), key, i);
        //assert key in (map key | key in l && Route(DropLast(pivots), key) == i :: l[key]);
        //assert key in SplitBucketOnPivots(l, DropLast(pivots))[i];
      }

      assert a == b;
    }
  }

  lemma AddMessagesToBucketsEmpAt(bucket: map<Key, Message>, pivots: seq<Key>, emp: seq<map<Key, Message>>, i: int)
  requires WFPivots(pivots)
  requires 0 <= i <= |pivots|
  requires |emp| == |pivots| + 1
  requires forall i | 0 <= i < |emp| :: emp[i] == map[]
  requires forall key | key in bucket :: bucket[key] != IdentityMessage();
  ensures BucketListFlush(bucket, emp, pivots)[i] == map key | key in bucket && Route(pivots, key) == i :: bucket[key]
  {
    var a := BucketListFlush(bucket, emp, pivots)[i];
    var b := map key | key in bucket && Route(pivots, key) == i :: bucket[key];
    forall key | key in a
    ensures key in b
    ensures a[key] == b[key];
    {
      GetBucketListFlushEqMerge(bucket, emp, pivots, key);
      RouteIs(pivots, key, i);

      //assert BT.BucketLookup(a, key) != IdentityMessage();
      //assert BT.BucketLookup(emp[i], key) == IdentityMessage();
      //assert BT.BucketLookup(bucket, key) != IdentityMessage();

      //assert key in bucket;
    }
    forall key | key in b
    ensures key in a
    {
      GetBucketListFlushEqMerge(bucket, emp, pivots, key);
    }
    assert a == b;
  }

  lemma LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket: map<Key, Message>, pivots: seq<Key>, emp: seq<map<Key, Message>>)
  requires WFPivots(pivots)
  requires |emp| == |pivots| + 1
  requires forall i | 0 <= i < |emp| :: emp[i] == map[]
  requires forall key | key in bucket :: bucket[key] != IdentityMessage();
  ensures SplitBucketOnPivots(bucket, pivots) == BucketListFlush(bucket, emp, pivots)
  {
    var a := SplitBucketOnPivots(bucket, pivots);
    var b := BucketListFlush(bucket, emp, pivots);
    assert |a| == |emp|;
    assert |b| == |emp|;
    forall i | 0 <= i < |emp|
    ensures a[i] == b[i]
    {
      SplitBucketOnPivotsAt(bucket, pivots, i);
      AddMessagesToBucketsEmpAt(bucket, pivots, emp, i);
    }
  }

  lemma BucketListFlushParentEmpty(blist: BucketList, pivots: PivotTable)
  requires WFPivots(pivots)
  requires WFBucketList(blist, pivots)
  ensures BucketListFlush(map[], blist, pivots) == blist
  {
    var a := BucketListFlush(map[], blist, pivots);
    var b := blist;
    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      BucketListFlushAt(map[], blist, pivots, i);
    }
  }

  function emptyList(n: int) : (l : BucketList)
  requires n >= 0
  ensures |l| == n
  ensures forall i | 0 <= i < |l| :: l[i] == map[]
  {
    if n == 0 then [] else emptyList(n-1) + [map[]]
  }

  lemma WFSplitBucketOnPivots(bucket: Bucket, pivots: seq<Key>)
  requires WFBucket(bucket)
  requires WFPivots(pivots)
  ensures WFBucketList(SplitBucketOnPivots(bucket, pivots), pivots)
  {
    reveal_WFBucket();
    var e := emptyList(|pivots| + 1);
    LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket, pivots, e);
    WFBucketListFlush(bucket, e, pivots);
  }

  lemma JoinBucketsSplitBucketOnPivotsCancel(bucket: Bucket, pivots: seq<Key>)
  requires WFPivots(pivots)
  requires WFBucket(bucket)
  ensures WFBucketList(SplitBucketOnPivots(bucket, pivots), pivots)
  ensures JoinBucketList(SplitBucketOnPivots(bucket, pivots)) == bucket
  {
    WFSplitBucketOnPivots(bucket, pivots);
    reveal_WFBucket();

    if |pivots| == 0 {
    } else {
      var buckets := SplitBucketOnPivots(bucket, pivots);
      var l := map key | key in bucket && Keyspace.lt(key, Last(pivots)) :: bucket[key];
      var r := map key | key in bucket && Keyspace.lte(Last(pivots), key) :: bucket[key];

      var bucketsPref := SplitBucketOnPivots(l, DropLast(pivots));
      WFSlice(pivots, 0, |pivots| - 1);
      JoinBucketsSplitBucketOnPivotsCancel(l, DropLast(pivots));

      forall i | 0 <= i < |buckets|
      ensures WFBucketAt(buckets[i], pivots, i)
      {
        if i < |buckets| - 1 {
          assert WFBucketAt(bucketsPref[i], DropLast(pivots), i);
          forall key | key in buckets[i] ensures Route(pivots, key) == i
          {
            assert Route(DropLast(pivots), key) == i;
            assert buckets[i] == bucketsPref[i];
            assert key in bucketsPref[i];
            SplitBucketOnPivotsAt(l, DropLast(pivots), i);
            assert key in l;
            RouteIs(pivots, key, i);
          }
          assert WFBucketAt(buckets[i], pivots, i);
        } else {
          forall key | key in buckets[i] ensures Route(pivots, key) == i
          {
            RouteIs(pivots, key, i);
          }
          assert WFBucketAt(buckets[i], pivots, i);
        }
      }
    }
  }

  lemma WFBucketsOfWFBucketList(blist: BucketList, pivots: PivotTable)
  requires WFBucketList(blist, pivots)
  ensures forall i | 0 <= i < |blist| :: WFBucket(blist[i])
  {
    reveal_WFBucket();
    forall i | 0 <= i < |blist| ensures WFBucket(blist[i])
    {
      assert WFBucketAt(blist[i], pivots, i);
    }
  }

  lemma WFBucketListSplitLeft(blist: BucketList, pivots: PivotTable, i: int)
  requires WFBucketList(blist, pivots)
  requires 1 <= i <= |blist|
  ensures WFBucketList(blist[.. i], pivots[.. i-1])
  {
    WFSlice(pivots, 0, i-1);
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist[.. i], pivots[.. i-1], 0, i-1, 0);
  }

  lemma WFBucketListSplitRight(blist: BucketList, pivots: PivotTable, i: int)
  requires WFBucketList(blist, pivots)
  requires 0 <= i < |blist|
  ensures WFBucketList(blist[i ..], pivots[i ..])
  {
    WFSuffix(pivots, i);
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist[i..], pivots[i..], 0, |blist|-i-1, -i);
  }

  lemma BucketListInsertBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable, key: Key, msg: Message)
  requires WFBucketList(children, pivots)
  ensures WFBucketList(BucketListFlush(parent, children, pivots), pivots)
  ensures BucketListInsert(BucketListFlush(parent, children, pivots), pivots, key, msg)
      == BucketListFlush(BucketInsert(parent, key, msg), children, pivots)
  {
    WFBucketListFlush(parent, children, pivots);

    var a := BucketListInsert(BucketListFlush(parent, children, pivots), pivots, key, msg);
    var b := BucketListFlush(BucketInsert(parent, key, msg), children, pivots);

    assert |a| == |b|;
    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      BucketListFlushAt(parent, children, pivots, i);
      BucketListFlushAt(BucketInsert(parent, key, msg), children, pivots, i);
      MergeIsAssociative(msg, BucketGet(parent, key), BucketGet(children[i], key));
    }
  }
}
