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
// A Bucket maps keys to Messages. A BucketList imparts a Message meaning
// to every key obeying the Message composition rules. This module shows
// how pushing messages down a tree towards a child still produces equivalent
// values as viewed through the Message chain.
//
// Unfortunately this currently has a lot of tech debt. Here is the situation:
// Originally, a "bucket" was defined to be a map<Key, Value>, and the PivotBetree
// was defined in terms of the Buckets.
// Many operations (split, flush) were defined on these Buckets.
// The implementation used data structures whose
// interpretations were these map<Key, Value> objects.
//
// However, key/value pairs are stored on disk as sequences. In order to avoid demarshalling
// costs, it slowly became clear that it would be more useful that the PivotBetree should
// use sequences, and that it should maintain an invariant that the sequences are sorted,
// and that the implementation should primarily operate on sequences.
//
// Unfortunately (blame tjhance) the move to this second option is a little undercooked,
// and this file
// remains in a messy mid-refactor state where a Bucket is *both* a BucketMap and
// a key/value sequence. TODO fix all of this
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
    {
      map_of_seqs(keys, msgs)
    }
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

  /*lemma WFMessageMultiset(bucket: Bucket)
    requires PreWFBucket(bucket)
    ensures Multisets.ValueMultiset(bucket.b) <= multiset(bucket.msgs)
    ensures BucketWellMarshalled(bucket) ==> Multisets.ValueMultiset(bucket.b) == multiset(bucket.msgs)
    decreases |bucket.keys|
  {
    if |bucket.keys| == 0 {
    } else {
      var lastkey := Last(bucket.keys);
      var lastmsg := Last(bucket.msgs);

      var prekeys := DropLast(bucket.keys);
      var premsgs := DropLast(bucket.msgs);
      var preb := BucketMapOfSeq(prekeys, premsgs);
      var prebucket := BucketMapWithSeq(preb, prekeys, premsgs);

      calc == {
        Multisets.ValueMultiset(bucket.b);
        Multisets.Apply(Multisets.ValueMultisetFn(bucket.b), multiset(bucket.b.Keys));
        {
          assert multiset(bucket.b.Keys) == multiset(prebucket.b.Keys) - multiset{lastkey} + multiset{lastkey};
        }
        Multisets.Apply(Multisets.ValueMultisetFn(bucket.b),
          multiset(prebucket.b.Keys) - multiset{lastkey} + multiset{lastkey});
        {
          Multisets.ApplyAdditive(Multisets.ValueMultisetFn(bucket.b),
                                  multiset(prebucket.b.Keys) - multiset{lastkey},
                                  multiset{lastkey});
        }
        Multisets.Apply(Multisets.ValueMultisetFn(bucket.b), multiset(prebucket.b.Keys) - multiset{lastkey})
          + Multisets.Apply(Multisets.ValueMultisetFn(bucket.b), multiset{lastkey});
        {
          Multisets.ApplySingleton(Multisets.ValueMultisetFn(bucket.b), lastkey);
          assert bucket.b[lastkey] == lastmsg by {
            reveal_BucketMapOfSeq();
          }
        }
        Multisets.Apply(Multisets.ValueMultisetFn(bucket.b), multiset(prebucket.b.Keys) - multiset{lastkey})
          + multiset{lastmsg};
        {
          reveal_BucketMapOfSeq();
          Multisets.ApplyEquivalentFns(Multisets.ValueMultisetFn(bucket.b),
            Multisets.ValueMultisetFn(prebucket.b),
            multiset(prebucket.b.Keys) - multiset{lastkey});
        }
        Multisets.Apply(Multisets.ValueMultisetFn(prebucket.b), multiset(prebucket.b.Keys) - multiset{lastkey})
          + multiset{lastmsg};
      }

      if BucketWellMarshalled(bucket) {
        calc {
          Multisets.Apply(Multisets.ValueMultisetFn(prebucket.b), multiset(prebucket.b.Keys) - multiset{lastkey});
          {
            assert multiset(prebucket.b.Keys) - multiset{lastkey} == multiset(prebucket.b.Keys) by {
              reveal_IsStrictlySorted();
            }
          }
          Multisets.Apply(Multisets.ValueMultisetFn(prebucket.b), multiset(prebucket.b.Keys));
          {
            StrictlySortedSubsequence(bucket.keys, 0, |bucket.keys| - 1);
            WFMessageMultiset(prebucket);
          }
          multiset(prebucket.msgs);
        }
      } else {
        calc <= {
          Multisets.Apply(Multisets.ValueMultisetFn(prebucket.b), multiset(prebucket.b.Keys) - multiset{lastkey});
          {
            Multisets.ApplyMonotonic(Multisets.ValueMultisetFn(prebucket.b),
              multiset(prebucket.b.Keys) - multiset{lastkey},
              multiset(prebucket.b.Keys));
          }
          Multisets.Apply(Multisets.ValueMultisetFn(prebucket.b), multiset(prebucket.b.Keys));
          {
            WFMessageMultiset(prebucket);
          }
          multiset(prebucket.msgs);
        }
      }

      assert bucket.msgs == prebucket.msgs + [ lastmsg ];
    }
  }*/
  
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

  predicate BoundedBucket(bucket: map<Key, Message>, pivots: PivotTable)
  {
    && WFPivots(pivots)
    && (forall key | key in bucket :: BoundedKey(pivots, key))
  }

  predicate BoundedBucketList(blist: BucketList, pivots: PivotTable)
  {
    && WFPivots(pivots)
    && (forall i | 0 <= i < |blist| ::
        && PreWFBucket(blist[i])
        && BoundedBucket(blist[i].as_map(), pivots))
  }

  function {:opaque} B(m: map<Key, Message>) : (b : Bucket)
  ensures PreWFBucket(b)
  ensures IsStrictlySorted(b.keys)
  ensures b.as_map() == m
  {
    IsStrictlySorted_seqs_of_map(m);
    map_of_seqs_of_seqs_of_map(m);
    var sp := seqs_of_map(m);
    Bucket(sp.keys, sp.msgs)
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
  }

  /*
  function BucketInsert(bucket: Bucket, key: Key, msg: Message) : Bucket
  {
    var mergedMsg := Merge(msg, BucketGet(bucket, key));
    if mergedMsg == IdentityMessage() then
      B(MapRemove1(bucket.b, key))
    else
      B(bucket.b[key := mergedMsg])
  }

  function BucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message) : BucketList
  requires WFBucketList(blist, pivots)
  requires BoundedKey(pivots, key)
  {
    var i := Route(pivots, key);
    blist[i := BucketInsert(blist[i], key, msg)]
  }*/

  /*function JoinBucketList(buckets: seq<Bucket>) : (bucket : Bucket)
    requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
    ensures PreWFBucket(bucket)
    //ensures (forall i | 0 <= i < |buckets| :: WFBucketMap(buckets[i].b)) ==> WFBucket(bucket)
  {
    if |buckets| == 0 then
      EmptyBucket()
    else
      MergeBuckets(
        JoinBucketList(DropLast(buckets)),
        Last(buckets))
  }*/

  /*function SplitBucketOnPivots(bucket: Bucket, pivots: PivotTable) : (buckets: BucketList)
    requires BoundedBucket(bucket, pivots)
    ensures |buckets| == NumBuckets(pivots)
    ensures forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
    ensures BucketListWellMarshalled(buckets)
    ensures forall i | 0 <= i < |buckets| :: buckets[i].b.Keys <= bucket.b.Keys
    ensures forall i | 0 <= i < |buckets| :: buckets[i].b.Values <= bucket.b.Values
    ensures forall i | 0 <= i < |buckets| :: |buckets[i].keys| == |buckets[i].msgs|
    ensures WFBucketMap(bucket.b) ==> forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
    decreases |pivots|
  {
    if |pivots| == 2 then (
      [B(bucket.b)]
    ) else (
      var piv := GetKey(pivots, NumBuckets(pivots)-1);
      var pivots' := remove(pivots, NumBuckets(pivots)-1);

      var l := SplitBucketLeft(bucket, piv);
      var r := SplitBucketRight(bucket, piv);

      reveal_SplitBucketLeft();
      reveal_SplitBucketRight();

      WFPivotsRemoved(pivots, NumBuckets(pivots)-1);
      SplitBucketOnPivots(l, pivots') + [r]
    )
  }*/

  /*function ClampToSlot(bucket: Bucket, pivots: PivotTable, i: int) : (res : Bucket)
  requires WFPivots(pivots)
  {
    B(map key | key in bucket.b && BoundedKey(pivots, key) && Route(pivots, key) == i :: bucket.b[key])
  }*/

  /*predicate BucketsEquivalentForKey(a: Bucket, b: Bucket, key: Key)
  {
    BucketGet(a, key) == BucketGet(b, key)
  }

  predicate BucketsEquivalent(a: Bucket, b: Bucket)
  {
    forall key :: BucketsEquivalentForKey(a, b, key)
  }*/
 
  /*predicate FlushEquivalentParentChild(oldparent: Bucket, oldchild: Bucket, newparent: Bucket, newchild: Bucket)
  {
    Compose(oldparent, oldchild) == Compose(newparent, newchild)
  }

  predicate FlushEquivalent(oldparent: Bucket, oldchildren: seq<Bucket>, newparent: Bucket, newchildren: seq<Bucket>)
  {
    && |oldchildren| == |newchildren|
    && (forall i | 0 <= i < |oldchildren| :: FlushEquivalentParentChild(oldparent, oldchildren[i], newparent, newchildren[i]))
  }*/
 
  /*function {:opaque} SplitBucketLeftAtIdx(bucket: Bucket, idx: int) : (res: Bucket)
  requires 0 <= idx <= |bucket.keys|
  requires PreWFBucket(bucket)
  ensures PreWFBucket(res)
  {
    Bucket(bucket.keys[..idx], bucket.msgs[..idx])
  }

  function {:opaque} SplitBucketRightAtIdx(bucket: Bucket, idx: int) : (res: Bucket)
  requires 0 <= idx <= |bucket.keys|
  requires PreWFBucket(bucket)
  ensures PreWFBucket(res)
  {
    Bucket(bucket.keys[idx..], bucket.msgs[idx..])
  }*/

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

  /*lemma SplitBucketLeftRightCmp(bucket: Bucket, pivot: Key)
  requires PreWFBucket(bucket)
  requires IsStrictlySorted(bucket.keys)
  ensures forall k | k in SplitBucketLeft(bucket, pivot).keys :: Lexicographic_Byte_Order.lt(k, pivot)
  ensures forall k | k in SplitBucketRight(bucket, pivot).keys :: Lexicographic_Byte_Order.lte(pivot, k)
  {
  }*/


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
  
  /*
  // merge needs to remove the pivot after slot
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
    BoundedKeyspace.reveal_IsStrictlySorted();
    assert BoundedKeyspace.lt(pivots'[slot], pivots'[slot+1]); // observe
  }

  lemma WellMarshalledMergeBucketsInList(blist: BucketList, slot: int)
  requires 0 <= slot < |blist| - 1
  requires BucketListWellMarshalled(blist)
  ensures BucketListWellMarshalled(MergeBucketsInList(blist, slot))
  {
    reveal_MergeBucketsInList();
  }

  lemma SplitOfMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketListProper(blist, pivots)
  ensures SplitBucketLeft(MergeBucketsInList(blist, slot)[slot], GetKey(pivots, slot+1)).b == blist[slot].b
  ensures SplitBucketRight(MergeBucketsInList(blist, slot)[slot], GetKey(pivots, slot+1)).b == blist[slot+1].b
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    reveal_MergeBucketsInList();
    reveal_MergeBuckets();
  }

  ///// Other lemmas

  lemma WFJoinBucketList(buckets: seq<Bucket>)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  ensures WFBucket(JoinBucketList(buckets))
  {
    if |buckets| == 0 {
    } else {
      WFJoinBucketList(DropLast(buckets));
    }
  }

  lemma BucketListFlushPartialAt(parent: Bucket, blist: BucketList, pivots: PivotTable, j: int, i: int)
  requires 0 <= i < j <= |blist|
  requires WFPivots(pivots)
  ensures BucketListFlushPartial(parent, blist, pivots, j)[i] == BucketListItemFlush(parent, blist[i], pivots, i)
  {
    if j == i + 1 {
    } else {
      BucketListFlushPartialAt(parent, blist, pivots, j-1, i);
    }
  }

  lemma BucketListFlushAt(parent: Bucket, blist: BucketList, pivots: PivotTable, i: int)
  requires 0 <= i < |blist|
  requires WFPivots(pivots)
  ensures BucketListFlush(parent, blist, pivots)[i] == BucketListItemFlush(parent, blist[i], pivots, i)
  {
    BucketListFlushPartialAt(parent, blist, pivots, |blist|, i);
  }

  lemma WFBucketListFlush(parent: Bucket, blist: BucketList, pivots: PivotTable)
  requires WFBucketList(blist, pivots)
  ensures WFBucketList(BucketListFlush(parent, blist, pivots), pivots)
  {
  }

  lemma KeyInJoinedBucketsInSomeBucket(buckets: seq<Bucket>, key: Key)
  returns (i : int)
  requires key in JoinBucketList(buckets).b
  ensures 0 <= i < |buckets|
  ensures key in buckets[i].b
  {
    assert |buckets| > 0;
    if key in Last(buckets).b {
      i := |buckets| - 1;
    } else {
      i := KeyInJoinedBucketsInSomeBucket(DropLast(buckets), key);
    }
  }

  lemma GetJoinBucketListEq(blist: BucketList, pivots: PivotTable, key: Key)
  requires WFBucketListProper(blist, pivots)
  requires BoundedKey(pivots, key)
  ensures BucketGet(JoinBucketList(blist), key) == BucketListGet(blist, pivots, key)
  {
    if |pivots| == 2 {
      assert BucketGet(blist[Route(pivots, key)], key) == BucketGet(JoinBucketList(blist), key);
    } else {
      var b1 := JoinBucketList(DropLast(blist));
      var b2 := Last(blist);

      var piv := pivots[NumBuckets(pivots)-1];
      var pivots' := remove(pivots, NumBuckets(pivots)-1);
      WFPivotsRemoved(pivots, NumBuckets(pivots)-1);

      forall i | 0 <= i < |DropLast(blist)| ensures WFBucketAt(DropLast(blist)[i], pivots', i)
      {
        var bucket := DropLast(blist)[i];
        assert WFBucketAt(blist[i], pivots, i);
        forall key | key in bucket.b ensures Route(pivots', key) == i {
          RouteIs(pivots', key, i);
        }
      }
      GetJoinBucketListEq(DropLast(blist), pivots', key);

      if BoundedKeyspace.lt(KeyToElement(key), piv) {
        assert WFBucketAt(blist[|blist| - 1], pivots, |blist| - 1);
        assert key !in b2.b;
        assert BucketGet(blist[Route(pivots, key)], key) == BucketGet(JoinBucketList(blist), key);
      } else {
        if (key in b1.b) {
          var i := KeyInJoinedBucketsInSomeBucket(DropLast(blist), key);
          assert false;
        }
        assert key !in b1.b;
        assert BucketGet(blist[Route(pivots, key)], key) == BucketGet(JoinBucketList(blist), key);
      }
    }
  }

  lemma SplitBucketOnPivotsAt(bucket: Bucket, pivots: PivotTable, i: int)
  requires 0 <= i < NumBuckets(pivots)
  requires BoundedBucket(bucket, pivots)
  ensures SplitBucketOnPivots(bucket, pivots)[i].b == ClampToSlot(bucket, pivots, i).b
  decreases |pivots|
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();

    if NumBuckets(pivots)-1 == i {
    } else {
      var piv := pivots[NumBuckets(pivots)-1];
      var pivots' := remove(pivots, NumBuckets(pivots)-1);
      WFPivotsRemoved(pivots, NumBuckets(pivots)-1);

      var l := map key | key in bucket.b && BoundedKeyspace.lt(KeyToElement(key), piv) :: bucket.b[key];
      SplitBucketOnPivotsAt(B(l), pivots', i);

      var a := SplitBucketOnPivots(bucket, pivots)[i].b;
      var b := map key | key in bucket.b && BoundedKey(pivots, key) && Route(pivots, key) == i :: bucket.b[key];

      forall key | key in a
      ensures key in b
      ensures a[key] == b[key];
      {
        assert key in bucket.b;
        RouteIs(pivots, key, i);
      }

      forall key | key in b
      ensures key in a
      {
        RouteIs(pivots', key, i);
      }
      assert a == b;     
      assert SplitBucketOnPivots(bucket, pivots)[i].b == ClampToSlot(bucket, pivots, i).b;
    }
  }

  lemma AddMessagesToBucketsEmpAt(bucket: Bucket, pivots: PivotTable, emp: BucketList, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < NumBuckets(pivots)
  requires |emp| == NumBuckets(pivots)
  requires forall i | 0 <= i < |emp| :: emp[i] == B(map[])
  requires forall key | key in bucket.b :: bucket.b[key] != IdentityMessage();
  ensures BucketListFlush(bucket, emp, pivots)[i]
       == B(map key | key in bucket.b && BoundedKey(pivots, key) && Route(pivots, key) == i :: bucket.b[key])
  {
    var a := BucketListFlush(bucket, emp, pivots)[i].b;
    var b := map key | key in bucket.b && BoundedKey(pivots, key) && Route(pivots, key) == i :: bucket.b[key];
    forall key | key in a
    ensures key in b
    ensures a[key] == b[key];
    {
      GetBucketListFlushEqMerge(bucket, emp, pivots, key);
      RouteIs(pivots, key, i);
    }
    forall key | key in b
    ensures key in a
    {
      GetBucketListFlushEqMerge(bucket, emp, pivots, key);
    }
    assert a == b;
    assert BucketListFlush(bucket, emp, pivots)[i].keys == B(b).keys;
    assert BucketListFlush(bucket, emp, pivots)[i].msgs == B(b).msgs;
  }

  lemma LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket: Bucket, pivots: PivotTable, emp: seq<Bucket>)
  requires WFBucket(bucket)
  requires BoundedBucket(bucket, pivots)
  requires |emp| == NumBuckets(pivots)
  requires forall i | 0 <= i < |emp| :: emp[i] == B(map[])
  requires forall key | key in bucket.b :: bucket.b[key] != IdentityMessage();
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
      WellMarshalledBucketsEq(a[i], b[i]);
    }
  }

  function emptyList(n: int) : (l : BucketList)
  requires n >= 0
  ensures |l| == n
  ensures forall i | 0 <= i < |l| :: l[i] == B(map[])
  {
    if n == 0 then [] else emptyList(n-1) + [B(map[])]
  }

  lemma WFSplitBucketOnPivots(bucket: Bucket, pivots: PivotTable)
  requires WFBucket(bucket)
  requires BoundedBucket(bucket, pivots)
  ensures WFBucketListProper(SplitBucketOnPivots(bucket, pivots), pivots)
  {
    var e := emptyList(NumBuckets(pivots));
    LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket, pivots, e);
    WFBucketListFlush(bucket, e, pivots);
  }

  lemma JoinBucketsSplitBucketOnPivotsCancel(bucket: Bucket, pivots: PivotTable)
  requires WFBucket(bucket)
  requires BoundedBucket(bucket, pivots)
  ensures WFBucketListProper(SplitBucketOnPivots(bucket, pivots), pivots)
  ensures JoinBucketList(SplitBucketOnPivots(bucket, pivots)).b == bucket.b
  decreases |pivots|
  {
    WFSplitBucketOnPivots(bucket, pivots);

    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    // reveal_WFBucket();
  
    if |pivots| == 2 {
    } else {
      var buckets := SplitBucketOnPivots(bucket, pivots);
      var piv := pivots[NumBuckets(pivots)-1];
      var pivots' := remove(pivots, NumBuckets(pivots)-1);
      WFPivotsRemoved(pivots, NumBuckets(pivots)-1);

      var l := map key | key in bucket.b && BoundedKeyspace.lt(KeyToElement(key), piv) :: bucket.b[key];
      var r := map key | key in bucket.b && BoundedKeyspace.lte(piv, KeyToElement(key)) :: bucket.b[key];

      var bucketsPref := SplitBucketOnPivots(B(l), pivots');
      JoinBucketsSplitBucketOnPivotsCancel(B(l), pivots');

      forall i | 0 <= i < |buckets|
      ensures WFBucketAt(buckets[i], pivots, i)
      {
        if i < |buckets| - 1 {
          assert WFBucketAt(bucketsPref[i], pivots', i);
          forall key | key in buckets[i].b ensures Route(pivots, key) == i
          {
            RouteIs(pivots', key, i);
            assert Route(pivots', key) == i;
            SplitBucketOnPivotsAt(B(l), pivots', i);
            assert key in l;
            RouteIs(pivots, key, i);
          }
          assert WFBucketAt(buckets[i], pivots, i);
        } else {
          forall key | key in buckets[i].b ensures Route(pivots, key) == i
          {
            RouteIs(pivots, key, i);
          }
          assert WFBucketAt(buckets[i], pivots, i);
        }
      }
    }
  }

  lemma WFBucketListSplitLeft(blist: BucketList, pivots: PivotTable, i: int)
  requires WFBucketList(blist, pivots)
  requires 1 <= i <= |blist|
  ensures WFBucketList(blist[.. i], pivots[.. i+1])
  {
    BoundedKeyspace.StrictlySortedSubsequence(pivots, 0, i+1);
  }

  lemma WFBucketListSplitRight(blist: BucketList, pivots: PivotTable, i: int)
  requires WFBucketList(blist, pivots)
  requires 0 <= i < |blist|
  ensures WFBucketList(blist[i ..], pivots[i ..])
  {
    assert pivots[i..] == pivots[i..|pivots|];
    BoundedKeyspace.StrictlySortedSubsequence(pivots, i, |pivots|);
    if 0 < i < |pivots| {
      BoundedKeyspace.IsStrictlySortedImpliesLt(pivots, 0, i);
    }
  }

  lemma BoundedBucketListJoin(blist: BucketList, pivots: PivotTable)
  requires BoundedBucketList(blist, pivots)
  ensures BoundedBucket(JoinBucketList(blist), pivots)
  {
  }
  */

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
