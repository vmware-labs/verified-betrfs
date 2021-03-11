// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BoundedPivotsLib.i.dfy"
include "../Base/Message.i.dfy"
include "../Base/Maps.i.dfy"
include "../Base/Multisets.i.dfy"
include "../Base/total_order.i.dfy"
include "../../MapSpec/UI.s.dfy"
include "../../MapSpec/MapSpec.s.dfy"
include "MapSeqs.i.dfy"
include "BucketMap.i.dfy"

//
// A Bucket is two sequences: a sequence of keys and
// a sequence of messages. The interpretation of a bucket
// is a map, given by to_map().
//
// Buckets generally should have keys in sorted order.
// However, most operations are defined so as it make sense
// without that requirement, thus the implementation can
// avoid costly sortedness checks.
//
// The on-disk representation and the most common in-memory
// representation of a bucket is as 2 sequences (PackedKV)
// so this is the most straightforward representation of such
// a thing.
//

module BucketsLib {
  import opened BoundedPivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Maps
  import opened Sequences
  import opened KeyType
  import opened Options
  import UI
  import MS = MapSpec
  import Multisets
  import opened MapSeqs
  import opened BucketMaps
  import BoundedKeyspace = Lexicographic_Byte_Order
  import Upperbounded_Lexicographic_Byte_Order

  datatype Bucket = Bucket(keys: seq<Key>, msgs: seq<Message>)
  {
    function as_map() : BucketMap
    requires |this.keys| == |this.msgs|
    ensures WFBucket(this) ==> WFBucketMap(as_map())
    {
      value_sets_le(keys, msgs);
      map_of_seqs(keys, msgs)
    }
  }

  predicate WFBucketMap(bucket: BucketMap)
  {
    forall message: Message :: message in bucket.Values ==> message != IdentityMessage()
  }

  type BucketList = seq<Bucket>

  predicate WFMessageSeq(messages: seq<Message>)
  {
    forall i | 0 <= i < |messages| :: messages[i] != IdentityMessage()
  }

  // TODO(robj): convert as much of this file as possible to require only PreWFBucket
  predicate PreWFBucket(bucket: Bucket)
  {
    && |bucket.keys| == |bucket.msgs|
  }
  
  predicate WFBucket(bucket: Bucket)
  {
    && PreWFBucket(bucket)
    && WFMessageSeq(bucket.msgs)
  }

  predicate BucketWellMarshalled(bucket: Bucket)
  {
    IsStrictlySorted(bucket.keys)
  }

  predicate BucketListWellMarshalled(blist: BucketList)
  {
    forall i | 0 <= i < |blist| :: BucketWellMarshalled(blist[i])
  }

  function EmptyBucket() : (result: Bucket)
    ensures WFBucket(result)
    ensures result.as_map() == map[]
    ensures BucketWellMarshalled(result)
  {
    MapOfEmptySeq();
    Bucket([], [])
  }
  
  function SingletonBucket(key: Key, msg: Message) : (result: Bucket)
    ensures PreWFBucket(result)
    ensures BucketWellMarshalled(result)
    ensures msg != IdentityMessage() ==> WFBucket(result)
  {
    Bucket([key], [msg])
  }
  
  function BucketDropLast(bucket: Bucket) : Bucket
    requires PreWFBucket(bucket)
    requires 0 < |bucket.keys|
  {
    Bucket(DropLast(bucket.keys), DropLast(bucket.msgs))
  }

  lemma BucketDropLastWF(bucket: Bucket)
    requires PreWFBucket(bucket)
    requires 0 < |bucket.keys|
    ensures PreWFBucket(BucketDropLast(bucket))
    ensures WFBucket(bucket) ==> WFBucket(BucketDropLast(bucket))
  {
  }

  lemma BucketDropLastWellMarshalled(bucket: Bucket)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires 0 < |bucket.keys|
    ensures BucketWellMarshalled(BucketDropLast(bucket))
  {
    reveal_IsStrictlySorted();
  }

  lemma BucketMapMapsIndex(bucket: Bucket, i: int)
  requires PreWFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires 0 <= i < |bucket.keys|
  ensures bucket.keys[i] in bucket.as_map()
  ensures bucket.as_map()[bucket.keys[i]] == bucket.msgs[i]
  {
    MapMapsIndex(bucket.keys, bucket.msgs, i);
  }

  predicate WFBucketAt(bucket: Bucket, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  {
    && WFBucket(bucket)
    && (forall key | key in bucket.keys :: BoundedKey(pivots, key))
    && (forall key | key in bucket.keys :: Route(pivots, key) == i)
  }

  lemma WellMarshalledBucketsEq(a: Bucket, b: Bucket)
    requires PreWFBucket(a)
    requires PreWFBucket(b)
    requires BucketWellMarshalled(a)
    requires BucketWellMarshalled(b)
    requires a.as_map() == b.as_map()
    ensures a == b
    decreases |a.keys|
  {
    SeqsEqOfMapsEq(a.keys, a.msgs, b.keys, b.msgs);
  }

  predicate WFBucketList(blist: BucketList, pivots: PivotTable)
  {
    && WFPivots(pivots)
    && |blist| == NumBuckets(pivots)
    && (forall i | 0 <= i < |blist| :: WFBucket(blist[i]))
  }

  predicate WFBucketListProper(blist: BucketList, pivots: PivotTable)
  {
    && WFBucketList(blist, pivots)
    && (forall i | 0 <= i < |blist| :: WFBucketAt(blist[i], pivots, i))
  }

  predicate BoundedBucket(bucket: Bucket, pivots: PivotTable)
  {
    && WFPivots(pivots)
    && (forall key | key in bucket.keys :: BoundedKey(pivots, key))
  }

  predicate BoundedBucketList(blist: BucketList, pivots: PivotTable)
  {
    && WFPivots(pivots)
    && (forall i | 0 <= i < |blist| ::
        && PreWFBucket(blist[i])
        && BoundedBucket(blist[i], pivots))
  }

  function {:opaque} B(m: map<Key, Message>) : (b : Bucket)
  ensures PreWFBucket(b)
  ensures IsStrictlySorted(b.keys)
  ensures b.as_map() == m
  ensures WFBucketMap(m) ==> WFBucket(b)
  {  
    IsStrictlySorted_seqs_of_map(m);
    map_of_seqs_of_seqs_of_map(m);
    var sp := seqs_of_map(m);
    var b := Bucket(sp.keys, sp.msgs);
    assert b.as_map() == map_of_seqs(b.keys, b.msgs);
    test(m, sp, b);
    b
  }

  lemma test(m: map<Key, Message>, sp: SeqPair, b: Bucket)
  requires sp == seqs_of_map(m);
  requires b == Bucket(sp.keys, sp.msgs);
  ensures WFBucketMap(m) ==> WFBucket(b)
  {
    if WFBucketMap(m) {
      assert Set(b.msgs) == m.Values by {
        seqs_of_map_preserves_values(m, sp);
      }
      assert forall i : int :: 0 <= i < |b.msgs| ==> b.msgs[i] != IdentityMessage()
      by {
        forall i | 0 <= i < |b.msgs|
          ensures b.msgs[i] != IdentityMessage()
        {
          assert b.msgs[i] in m.Values;
        }
      }
    }
  }

  function BucketInsert(bucket: Bucket, key: Key, msg: Message) : Bucket
  requires PreWFBucket(bucket)
  {
    var m := bucket.as_map();
    var mergedMsg := Merge(msg, BucketGet(m, key));
    if mergedMsg == IdentityMessage() then
      B(MapRemove1(m, key))
    else
      B(m[key := mergedMsg])
  }

  function BucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message) : BucketList
  requires WFBucketList(blist, pivots)
  requires BoundedKey(pivots, key)
  {
    var i := Route(pivots, key);
    blist[i := BucketInsert(blist[i], key, msg)]
  }


  function BucketListGet(blist: BucketList, pivots: PivotTable, key: Key) : Message
  requires WFBucketList(blist, pivots)
  requires BoundedKey(pivots, key)
  {
    BucketGet(blist[Route(pivots, key)].as_map(), key)
  }

  lemma WFBucketInsert(bucket: Bucket, key: Key, msg: Message)
  requires WFBucket(bucket)
  ensures WFBucket(BucketInsert(bucket, key, msg))
  {
    var m := bucket.as_map();
    var mergedMsg := Merge(msg, BucketGet(m, key));
    var m':= 
      if mergedMsg == IdentityMessage() then
        MapRemove1(m, key)
      else
        m[key := mergedMsg];
    var bucket' := BucketInsert(bucket, key, msg);
    assert m' == bucket'.as_map();
    assert m' == map_of_seqs(bucket'.keys, bucket'.msgs);

    forall i | 0 <= i < |bucket'.msgs|
    ensures bucket'.msgs[i] != IdentityMessage()
    {
      MapMapsIndex(bucket'.keys, bucket'.msgs, i);
      var k := bucket'.keys[i];
      assert m'[k] == bucket'.msgs[i];
      if k != key {
        assert m[k] == bucket'.msgs[i];
        var j := GetIndex(bucket.keys, bucket.msgs, k);
      }
    }
  }

  function {:opaque} SplitBucketLeft(bucket: Bucket, pivot: Key) : (res: Bucket)
  requires PreWFBucket(bucket)
  ensures PreWFBucket(res)
  {
    var i := BoundedKeyspace.binarySearchIndexOfFirstKeyGte(bucket.keys, pivot);
    Bucket(bucket.keys[..i], bucket.msgs[..i])
  }

  function {:opaque} SplitBucketRight(bucket: Bucket, pivot: Key) : (res: Bucket)
  requires PreWFBucket(bucket)
  ensures PreWFBucket(res)
  {
    var i := BoundedKeyspace.binarySearchIndexOfFirstKeyGte(bucket.keys, pivot);
    Bucket(bucket.keys[i..], bucket.msgs[i..])
  }

  function SplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key) : BucketList
  requires WFBucketList(blist, pivots)
  requires ValidLeftCutOffKey(pivots, key)
  requires CutoffForLeft(pivots, key) == cLeft
  {
    blist[.. cLeft] + [ SplitBucketLeft(blist[cLeft], key) ] 
  }

  function SplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key) : BucketList
  requires WFBucketList(blist, pivots)
  requires BoundedKey(pivots, key)
  requires CutoffForRight(pivots, key) == cRight
  {
    [SplitBucketRight(blist[cRight], key)] + blist[cRight + 1 ..]
  }

  function {:opaque} SplitBucketInList(blist: BucketList, slot: int, pivot: Key) : BucketList
  requires 0 <= slot < |blist|
  requires PreWFBucket(blist[slot])
  {
    replace1with2(blist,
        SplitBucketLeft(blist[slot], pivot),
        SplitBucketRight(blist[slot], pivot),
        slot)
  }

  function {:opaque} MergeBuckets(left: Bucket, right: Bucket) : (res : Bucket)
  requires PreWFBucket(left)
  requires PreWFBucket(right)
  ensures PreWFBucket(res)
  {
    Bucket(left.keys + right.keys, left.msgs + right.msgs)
  }

  function {:opaque} MergeBucketsInList(blist: BucketList, slot: int) : (blist' : BucketList)
    requires 0 <= slot < |blist| - 1
    requires PreWFBucket(blist[slot])
    requires PreWFBucket(blist[slot+1])
    ensures |blist'| == |blist| - 1
    ensures PreWFBucket(blist'[slot])
  {
    replace2with1(blist,
        MergeBuckets(blist[slot], blist[slot+1]),
        slot)
  }

  lemma WFSplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key)
  requires WFBucketList(blist, pivots)
  requires ValidLeftCutOffKey(pivots, key)
  requires CutoffForLeft(pivots, key) == cLeft
  ensures WFBucketList(SplitBucketListLeft(blist, pivots, cLeft, key), SplitLeft(pivots, key))
  {
    reveal_SplitBucketLeft();
  }

  lemma WFProperSplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key)
  requires WFBucketListProper(blist, pivots)
  requires ValidLeftCutOffKey(pivots, key)
  requires CutoffForLeft(pivots, key) == cLeft
  requires IsStrictlySorted(blist[cLeft].keys)
  ensures WFBucketListProper(SplitBucketListLeft(blist, pivots, cLeft, key), SplitLeft(pivots, key))
  {
    reveal_SplitBucketLeft();
    var pivots' := SplitLeft(pivots, key);
    var blist' := SplitBucketListLeft(blist, pivots, cLeft, key); 
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', 0, cLeft-1, 0);
    assert pivots[cLeft] == pivots'[cLeft]; // observe

    //SplitBucketLeftRightCmp(blist[cLeft], key);
    //reveal_IsStrictlySorted();

    //assert WFBucket(blist'[cLeft]);
    assert WFBucketAt(blist'[cLeft], pivots', cLeft) by {
      reveal_IsStrictlySorted();
      forall k | k in blist'[cLeft].keys
      ensures BoundedKey(pivots', k)
      ensures Route(pivots', k) == cLeft
      {
        assert k in blist[cLeft].keys;
        //assert WFBucketAt(blist[cLeft], pivots, cLeft);

        //assert BoundedKey(pivots, k);
        //assert Route(pivots, k) == cLeft;

        //var i := BoundedKeyspace.binarySearchIndexOfFirstKeyGte(blist[cLeft].keys, key);
        //assert Lexicographic_Byte_Order.lt(k, blist[cLeft].keys
        //assert Lexicographic_Byte_Order.lt(k, key);
        //assert Upperbounded_Lexicographic_Byte_Order.lt(KeyToElement(k), pivots'[cLeft+1]);
        //RouteIs(pivots', k, cLeft);
      }
    }
  }

  lemma WFSplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key)
  requires WFBucketList(blist, pivots)
  requires BoundedKey(pivots, key)
  requires CutoffForRight(pivots, key) == cRight
  ensures WFBucketList(SplitBucketListRight(blist, pivots, cRight, key), SplitRight(pivots, key))
  {
    reveal_SplitBucketRight();
    WFSuffix(pivots, cRight);
  }

  lemma WFProperSplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key)
  requires WFBucketListProper(blist, pivots)
  requires BoundedKey(pivots, (key))
  requires CutoffForRight(pivots, key) == cRight
  requires IsStrictlySorted(blist[cRight].keys)
  ensures WFBucketListProper(SplitBucketListRight(blist, pivots, cRight, key), SplitRight(pivots, key))
  {
    reveal_SplitBucketRight();

    var blist' := SplitBucketListRight(blist, pivots, cRight, key);
    var pivots' := SplitRight(pivots, key);

    assert pivots[cRight+1] == pivots'[1]; // observe
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', 1, |blist'|-1, 0-cRight);

    assert WFBucketAt(blist'[0], pivots', 0) by {
      reveal_IsStrictlySorted();
      forall k | k in blist'[0].keys
      ensures BoundedKey(pivots', k)
      ensures Route(pivots', k) == 0
      {
        assert k in blist[cRight].keys;

        assert WFBucketAt(blist[cRight], pivots, cRight);

        assert BoundedKey(pivots, k);
        assert Route(pivots, k) == cRight;
      }
    }
  }

  lemma WFSplitBucketInList(blist: BucketList, slot: int, pivot: Key, pivots: PivotTable)
  requires WFBucketList(blist, pivots)
  requires 1 <= slot <= |blist|
  requires BoundedKey(pivots, pivot)
  requires PivotInsertable(pivots, slot, pivot)
  ensures WFPivots(InsertPivot(pivots, slot, pivot))
  ensures WFBucketList(SplitBucketInList(blist, slot-1, pivot), InsertPivot(pivots, slot, pivot))
  {
    WFPivotsInsert(pivots, slot, pivot);    
    reveal_SplitBucketInList();
    var newbuckets := SplitBucketInList(blist, slot-1, pivot);
    forall i | 0 <= i < |newbuckets|
      ensures WFBucket(newbuckets[i])
    {
      if i < slot-1 {
        assert newbuckets[i] == blist[i];
      } else if i == slot-1 {
        reveal_SplitBucketLeft();
      } else if i == slot {
        reveal_SplitBucketRight();
      } else {
        assert newbuckets[i] == blist[i-1];
      }
    }
  }

  lemma WFProperSplitBucketInList(blist: BucketList, slot: int, pivot: Key, pivots: PivotTable)
  requires WFBucketListProper(blist, pivots)
  requires BoundedKey(pivots, pivot)
  requires 1 <= slot <= |blist|
  requires PivotInsertable(pivots, slot, pivot)
  requires IsStrictlySorted(blist[slot-1].keys)
  ensures WFPivots(InsertPivot(pivots, slot, pivot))
  ensures WFBucketListProper(SplitBucketInList(blist, slot-1, pivot), InsertPivot(pivots, slot, pivot))
  {
    var blist' := SplitBucketInList(blist, slot-1, pivot);
    assert |blist'| == |blist|+1 by { reveal_SplitBucketInList(); }
    var pivots' := InsertPivot(pivots, slot, pivot);
    WFPivotsInsert(pivots, slot, pivot);

    assert WFBucketAt(blist[slot-1], pivots, slot-1);
    assert WFBucketAt(blist'[slot-1], pivots', slot-1) by {
      assert blist'[slot - 1] == SplitBucketLeft(blist[slot - 1], pivot)
        by { reveal_SplitBucketInList(); }
      reveal_SplitBucketLeft();
      assert WFBucket(blist'[slot-1]);
      forall k | k in blist'[slot-1].keys
      ensures BoundedKey(pivots', k)
      ensures Route(pivots', k) == slot - 1
      {
        assert k in blist[slot-1].keys;
        reveal_IsStrictlySorted();
        assert Keyspace.lte(pivots'[slot - 1], KeyToElement(k));
        assert Keyspace.lte(KeyToElement(k), pivots'[slot]);
      }
    }
    assert WFBucketAt(blist'[slot], pivots', slot) by {
      assert blist'[slot] == SplitBucketRight(blist[slot - 1], pivot)
        by { reveal_SplitBucketInList(); }
      reveal_IsStrictlySorted();
      reveal_SplitBucketRight();
      assert WFBucket(blist'[slot]);
      forall k | k in blist'[slot].keys
      ensures BoundedKey(pivots', k)
      ensures Route(pivots', k) == slot
      {
        assert k in blist[slot-1].keys;
        reveal_IsStrictlySorted();
      }
    }

    reveal_SplitBucketInList();
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', 0, slot-2, 0);
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', slot+1, |blist'|-1, 1);
  }

  lemma WellMarshalledSplitBucketInList(blist: BucketList, slot: int, pivot: Key)
  requires 0 <= slot < |blist|
  requires BucketListWellMarshalled(blist)
  requires PreWFBucket(blist[slot])
  ensures BucketListWellMarshalled(SplitBucketInList(blist, slot, pivot))
  {
    var blist' := SplitBucketInList(blist, slot, pivot);
    reveal_SplitBucketInList();
    assert BucketWellMarshalled(SplitBucketLeft(blist[slot], pivot))
      by { reveal_SplitBucketLeft(); reveal_IsStrictlySorted(); }
    assert BucketWellMarshalled(SplitBucketRight(blist[slot], pivot))
      by { reveal_SplitBucketRight(); reveal_IsStrictlySorted(); }
    forall i | 0 <= i < |blist'|
    ensures BucketWellMarshalled(blist'[i])
    {
      if i < slot {
        assert BucketWellMarshalled(blist[i]);
      } else if i > slot+1 {
        assert BucketWellMarshalled(blist[i-1]);
      }
    }
  }

  lemma WFMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures WFBucketList(MergeBucketsInList(blist, slot), remove(pivots, slot+1))
  {
    reveal_MergeBucketsInList();
    WFPivotsRemoved(pivots, slot+1);
    reveal_MergeBuckets();
  }

  lemma WFProperMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketListProper(blist, pivots)
  ensures WFBucketListProper(MergeBucketsInList(blist, slot), remove(pivots, slot+1))
  {
    reveal_MergeBucketsInList();
    WFPivotsRemoved(pivots, slot+1);
    var blist' := MergeBucketsInList(blist, slot);
    var pivots' := remove(pivots, slot+1);
    BucketListHasWFBucketAtIdenticalSlice(
        blist, pivots, blist', pivots', 0, slot-1, 0);
    BucketListHasWFBucketAtIdenticalSlice(
        blist, pivots, blist', pivots', slot+1, |blist'|-1, -1);
    reveal_MergeBuckets();
    Keyspace.reveal_IsStrictlySorted();
    assert Keyspace.lt(pivots'[slot], pivots'[slot+1]); // observe
  }

  lemma WellMarshalledMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires PreWFBucket(blist[slot])
  requires PreWFBucket(blist[slot+1])
  requires BucketListWellMarshalled(blist)
  requires WFBucketListProper(blist, pivots)
  ensures BucketListWellMarshalled(MergeBucketsInList(blist, slot))
  {
    reveal_MergeBuckets();
    reveal_MergeBucketsInList();
    reveal_IsStrictlySorted();

    var merged := MergeBucketsInList(blist, slot)[slot];
    var pivot := GetKey(pivots, slot+1);

    assert forall k | k in blist[slot].keys :: lt(k, pivot);
    assert forall k | k in blist[slot+1].keys :: lte(pivot, k);

    forall i, j | 0 <= i < j < |merged.keys|
    ensures lt(merged.keys[i], merged.keys[j])
    {
      if i < |blist[slot].keys| && j >= |blist[slot].keys| {
        assert lt(merged.keys[i], pivot);
        assert lte(pivot, merged.keys[j]);
        assert lt(merged.keys[i], merged.keys[j]);
      }
    }
  }

  lemma SplitOfMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketListProper(blist, pivots)
  ensures SplitBucketLeft(MergeBucketsInList(blist, slot)[slot], GetKey(pivots, slot+1)) == blist[slot]
  ensures SplitBucketRight(MergeBucketsInList(blist, slot)[slot], GetKey(pivots, slot+1)) == blist[slot+1]
  {
    reveal_MergeBucketsInList();
    reveal_MergeBuckets();

    var merged := MergeBucketsInList(blist, slot)[slot];
    var pivot := GetKey(pivots, slot+1);

    assert forall k | k in blist[slot].keys :: lt(k, pivot);
    assert forall k | k in blist[slot+1].keys :: lte(pivot, k);

    assert BoundedKeyspace.binarySearchIndexOfFirstKeyGte(merged.keys, pivot) == |blist[slot].keys|
    by {
      assert forall i | 0 <= i < |merged.keys| :: 
        && (i < |blist[slot].keys| ==> lt(merged.keys[i], pivot)) 
        && (i >= |blist[slot].keys| ==> lte(pivot, merged.keys[i]));
    }

    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
  }

  lemma BucketListWellMarshalledSlice(blist: BucketList, i: int, j: int)
  requires BucketListWellMarshalled(blist)
  requires 0 <= i <= j <= |blist|
  ensures BucketListWellMarshalled(blist[i..j])
  {
  }


  // This is useful for proving NodeHasWFBuckets(node')
  // for indices over the given interval [a, b],
  // assuming we already know the buckets and pivots come from some other
  // well-formed node (possibly shifted by the amount d).
  // TODO(travis) I think(?) this lemma and some others are only used in
  // PivotBetreeSpecWFNodes.i.dfy so maybe move these there to reduce clutter here
  lemma BucketListHasWFBucketAtIdenticalSlice(
      blist: BucketList, pivots: PivotTable, blist': BucketList, pivots': PivotTable, a: int, b: int, d: int)
  requires WFBucketListProper(blist, pivots)
  requires WFPivots(pivots')
  requires |blist'| == NumBuckets(pivots')
  requires 0 <= a
  requires b < |blist'|
  requires a-d >= 0
  requires b-d < |blist|
  requires forall i | a <= i <= b :: blist'[i] == blist[i-d]
  requires forall i | a <= i <= b :: pivots'[i] == pivots[i-d]
  requires 0 <= (b-d+1) && 0 <= (b+1) ==> Upperbounded_Lexicographic_Byte_Order.lte(pivots[b-d+1], pivots'[b+1])
  requires b >= a && b < |pivots'| ==> (
      || (b-d < |pivots| && pivots'[b] == pivots[b-d])
      || (forall key | key in blist'[b].keys :: Upperbounded_Lexicographic_Byte_Order.lt(KeyToElement(key), pivots'[b]))
    )
  requires b >= a && a-1 >= 0 ==> (
      || (a-1-d >= 0 && pivots'[a-1] == pivots[a-1-d])
      || (forall key | key in blist'[a].keys :: Upperbounded_Lexicographic_Byte_Order.lte(pivots'[a-1], KeyToElement(key)))
    )
  ensures forall i | a <= i <= b :: WFBucketAt(blist'[i], pivots', i)
  {
    forall i | a <= i <= b
    ensures WFBucketAt(blist'[i], pivots', i)
    {
      assert pivots[i-d] == pivots'[i];
      assert Upperbounded_Lexicographic_Byte_Order.lte(pivots[i-d+1], pivots'[i+1]);
    }
  }

  // TODO(travis) there is already some binary search functionality in the
  // total_order file. Move this there, standardize the patterns used, etc.
  function binarySearch(keys: seq<Key>, key: Key) : (i : Option<nat>)
    ensures IsStrictlySorted(keys) ==> i.None? ==> key !in keys
    ensures i.Some? ==> 0 <= i.value < |keys| && key == keys[i.value]
  {
    if |keys| == 0 then
      None
    else
      reveal_IsStrictlySorted();
      var mid := |keys| / 2;
      if lt(key, keys[mid]) then
        binarySearch(keys[..mid], key)
      else if keys[mid] == key then
        Some(mid)
      else
        var sub := binarySearch(keys[mid+1..], key);
        if sub.Some? then
          Some(mid + 1 + sub.value)
        else
          None
  }
  
  // This binary searches on the keys list in bucket.
  // If it happens to be in sorted order, it will return the correct
  // answer.
  function bucketBinarySearchLookup(bucket: Bucket, key: Key)
    : (msg : Option<Message>)
    requires WFBucket(bucket)
    ensures BucketWellMarshalled(bucket) ==> msg.None? ==> key !in bucket.as_map()
    ensures BucketWellMarshalled(bucket) ==> msg.Some? ==>
      key in bucket.as_map() && bucket.as_map()[key] == msg.value
  {
    var i := binarySearch(bucket.keys, key);
    if i.Some? then 
      (if BucketWellMarshalled(bucket) then
        //WFWellMarshalledBucketMap(bucket, key);
        PosEqLargestLte(bucket.keys, key, i.value);
        MapMapsIndex(bucket.keys, bucket.msgs, i.value);
        Some(bucket.msgs[i.value])
      else
        Some(bucket.msgs[i.value]))
    else
      assert BucketWellMarshalled(bucket) ==> key !in bucket.as_map() by {
        if key in bucket.as_map() {
          var j := GetIndex(bucket.keys, bucket.msgs, key);
        }
      }
      None
  }
  
  function getMiddleKey(bucket: Bucket) : Key
  requires WFBucket(bucket)
  {
    if |bucket.keys| == 0 then
      [0] // Just pick an arbitary key
    else (
      var key := bucket.keys[|bucket.keys| / 2];
      if |key| == 0 then 
        [0]
      else
        key
    )
  }

  lemma WFPivotsOfGetMiddleKey(bucket: Bucket)
  requires WFBucket(bucket)
  ensures WFPivots(insert(InitPivotTable(), KeyToElement(getMiddleKey(bucket)), 1))
  {
    reveal_IsStrictlySorted();
    SeqComparison.reveal_lte();
    assert InitPivotTable()[1].Max_Element?; // observe
    WFPivotsInsert(InitPivotTable(), 1, getMiddleKey(bucket));
  }

  function {:opaque} MapsOfBucketList(blist: BucketList) : (res : seq<BucketMap>)
  requires forall i | 0 <= i < |blist| :: PreWFBucket(blist[i])
  ensures |res| == |blist|
  ensures forall i | 0 <= i < |res| :: res[i] == blist[i].as_map()
  {
    seq(|blist|,
      i requires 0 <= i < |blist| => blist[i].as_map())
  }

  lemma B_empty_map()
  ensures B(map[]) == EmptyBucket();
  {
    MapSeqs.empty_seqs_of_map();
    reveal_B();
  }

  lemma B_of_as_map_sorted(b: Bucket)
  requires PreWFBucket(b)
  requires IsStrictlySorted(b.keys)
  ensures B(b.as_map()) == b;
  {
    assert B(b.as_map()).as_map() == b.as_map();
    SeqsEqOfMapsEq(b.keys, b.msgs,
        B(b.as_map()).keys, B(b.as_map()).msgs);
  }
}
