include "PivotsLib.i.dfy"
include "../Base/Message.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/Multisets.i.dfy"
include "../Base/total_order.i.dfy"
include "../../MapSpec/UI.s.dfy"
include "../../MapSpec/MapSpec.s.dfy"

//
// A Bucket maps keys to Messages. A BucketList imparts a Message meaning
// to every key obeying the Message composition rules. This module shows
// how pushing messages down a tree towards a child still produces equivalent
// values as viewed through the Message chain.
//
// NOTE(travis): this should probably be split up into two things: (i) a library of utilities for describing the relationship between a map and a pair of (possibly sorted) lists and (ii) actual application-bucket operations. Furthermore, the whole thing where a Bucket has *both* the list representation and map representation was a bit of a crutch and should probably be changed.

module BucketsLib {
  import opened PivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Maps
  import opened Sequences
  import opened KeyType
  import opened Options
  import UI
  import MS = MapSpec
  import Multisets
  
  type BucketMap = map<Key, Message>
  datatype Bucket = BucketMapWithSeq(b: BucketMap, keys: seq<Key>, msgs: seq<Message>)
  type BucketList = seq<Bucket>

  function maximumKey(b: set<Key>) : Option<Key>
  {
    var m := Lexicographic_Byte_Order.maximumOpt(b);
    if m.Some? then
      assert |m.value| <= KeyType.MaxLen() as nat;
      var k: Key := m.value;
      Some(k)
    else
      None
  }
  
  function minimumKey(b: set<Key>) : Option<Key>
  {
    var m := Lexicographic_Byte_Order.minimumOpt(b);
    if m.Some? then
      assert |m.value| <= KeyType.MaxLen() as nat;
      var k: Key := m.value;
      Some(k)
    else
      None
  }

  function {:opaque} BucketMapOfSeq(keys: seq<Key>, msgs: seq<Message>) : (result: BucketMap)
    requires |keys| == |msgs|
    ensures result.Keys == Set(keys)
    ensures result.Values <= Set(msgs)
  {
    if |keys| == 0 then
      map[]
    else
      var r' := BucketMapOfSeq(DropLast(keys), DropLast(msgs));
      var r := r'[Last(keys) := Last(msgs)];
      assert r.Values <= r'.Values + {Last(msgs)};
      r
  }

  lemma StrictlySortedIsBucketMapOfSeq(keys: seq<Key>, msgs: seq<Message>, bmap: BucketMap)
    requires IsStrictlySorted(keys)
    requires Set(keys) == bmap.Keys
    requires |keys| == |msgs|
    requires forall i | 0 <= i < |keys| :: bmap[keys[i]] == msgs[i]
    ensures bmap == BucketMapOfSeq(keys, msgs)
  {
    reveal_BucketMapOfSeq();
    if |keys| == 0 {
    } else {
      var prebmap := MapRemove1(bmap, Last(keys));
      StrictlySortedSubsequence(keys, 0, |keys| - 1);
      reveal_IsStrictlySorted();
      StrictlySortedIsBucketMapOfSeq(DropLast(keys), DropLast(msgs), prebmap);
    }
  }
  
  function BucketOfSeq(keys: seq<Key>, msgs: seq<Message>) : (result: Bucket)
  requires |keys| == |msgs|
  {
    BucketMapWithSeq(BucketMapOfSeq(keys, msgs), keys, msgs)
  }

  lemma BucketMapOfSeqGetIndex(keys: seq<Key>, msgs: seq<Message>, key: Key)
  returns (i: int)
  requires |keys| == |msgs|
  requires key in BucketMapOfSeq(keys, msgs)
  ensures 0 <= i < |keys|
  ensures keys[i] == key
  ensures msgs[i] == BucketMapOfSeq(keys, msgs)[key]
  {
    reveal_BucketMapOfSeq();
    if key == keys[|keys| - 1] && msgs[|keys| - 1] == BucketMapOfSeq(keys, msgs)[key] {
      i := |keys| - 1;
    } else {
      i := BucketMapOfSeqGetIndex(DropLast(keys), DropLast(msgs), key);
    }
  }

  lemma BucketMapOfSeqMapsIndex(keys: seq<Key>, msgs: seq<Message>, i: int)
  requires |keys| == |msgs|
  requires 0 <= i < |keys|
  requires IsStrictlySorted(keys)
  ensures keys[i] in BucketMapOfSeq(keys, msgs)
  ensures msgs[i] == BucketMapOfSeq(keys, msgs)[keys[i]]
  {
    reveal_BucketMapOfSeq();
    if i == |keys| - 1 {
    } else {
      reveal_IsStrictlySorted();
      BucketMapOfSeqMapsIndex(DropLast(keys), DropLast(msgs), i);
    }
  }

  lemma WFBucketMapOfWFMessageSeq(keys: seq<Key>, msgs: seq<Message>)
  requires |keys| == |msgs|
  requires WFMessageSeq(msgs)
  ensures WFBucketMap(BucketMapOfSeq(keys, msgs))
  {
    forall key | key in BucketMapOfSeq(keys, msgs)
    ensures BucketMapOfSeq(keys, msgs)[key] != IdentityMessage()
    {
      var i := BucketMapOfSeqGetIndex(keys, msgs, key);
    }
  }
  
  predicate WFBucketMap(bucket: BucketMap)
  {
    forall key | key in bucket :: bucket[key] != IdentityMessage()
  }

  predicate WFMessageSeq(messages: seq<Message>)
  {
    forall i | 0 <= i < |messages| :: messages[i] != IdentityMessage()
  }

  // TODO(robj): convert as much of this file as possible to require only PreWFBucket
  predicate PreWFBucket(bucket: Bucket)
  {
    && |bucket.keys| == |bucket.msgs|
    && BucketMapOfSeq(bucket.keys, bucket.msgs) == bucket.b
  }
  
  predicate WFBucket(bucket: Bucket)
  {
    && PreWFBucket(bucket)
    && WFBucketMap(bucket.b)
    && WFMessageSeq(bucket.msgs)
  }

  predicate BucketWellMarshalled(bucket: Bucket)
  {
    IsStrictlySorted(bucket.keys)
  }

  lemma WellMarshalledKeyMultiset(bucket: Bucket)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    ensures multiset(Set(bucket.keys)) == multiset(bucket.keys)
    ensures bucket.b.Keys == Set(bucket.keys)
  {
    StrictlySortedImpliesNoDupes(bucket.keys);
    assert NoDupes(bucket.keys) by {
      // StrictlySortedImpliesNoDupes() gives us
      //    NoDupes<Element>().
      // We need
      //    NoDupes<Key>().
      reveal_NoDupes();
    }
    NoDupesMultiset(bucket.keys);
  }

  predicate BucketListWellMarshalled(blist: BucketList)
  {
    forall i | 0 <= i < |blist| :: BucketWellMarshalled(blist[i])
  }

  function BInternal(m: BucketMap) : (bucket: Bucket)
    ensures bucket.b == m
    ensures |bucket.keys| == |bucket.msgs|
  {
    if |m.Keys| == 0 then
      BucketMapWithSeq(m, [], [])
    else 
      var maxkey := maximum(m.Keys);
      var maxmsg := m[maxkey];
      var subm := MapRemove1(m, maxkey);
      var subbucket := BInternal(subm);
      BucketMapWithSeq(m, subbucket.keys + [maxkey], subbucket.msgs + [maxmsg])
  }

  lemma BInternalPreWFWellMarshalled(m: BucketMap)
    ensures PreWFBucket(BInternal(m))
    ensures BucketWellMarshalled(BInternal(m))
  //ensures WFBucketMap(m) ==> WFBucket(BInternal(m))
  {
    if |m| == 0 {
      reveal_IsStrictlySorted();
    // } else if |m| == 1 {
    //   reveal_BucketMapOfSeq();
    //   reveal_IsStrictlySorted();
    } else {
      var maxkey := maximum(m.Keys);
      var subm := MapRemove1(m, maxkey);
      var subbucket := BInternal(subm);      
      BInternalPreWFWellMarshalled(subm);
      StrictlySortedAugment(subbucket.keys, maxkey);
      reveal_BucketMapOfSeq();
    }
  }
  
  lemma BInternalWFBucket(m: BucketMap)
    requires WFBucketMap(m)
    ensures WFBucket(BInternal(m))
  {
    // reveal_WFBucket();
    reveal_BucketMapOfSeq();
  }

  function {:opaque} B(m: BucketMap) : (bucket: Bucket)
    ensures bucket.b == m
    ensures PreWFBucket(bucket)
    ensures BucketWellMarshalled(bucket)
    ensures |bucket.keys| == |bucket.msgs|
    ensures WFBucketMap(m) ==> WFBucket(bucket)
  {
    BInternalPreWFWellMarshalled(m);
    if WFBucketMap(m) then
      BInternalWFBucket(m);
      BInternal(m)
    else 
      BInternal(m)
  }

  function EmptyBucket() : (result: Bucket)
    ensures EmptyBucket() == B(map[])
    ensures WFBucket(result)
    ensures BucketWellMarshalled(result)
  {
    var b := BucketMapWithSeq(map[], [], []);
    assert b == B(map[]) by {
      reveal_B();
    }
    b
  }
  
  function SingletonBucket(key: Key, msg: Message) : (result: Bucket)
    ensures PreWFBucket(result)
    ensures BucketWellMarshalled(result)
    ensures msg != IdentityMessage() ==> WFBucket(result)
  {
    assert map[key := msg] == BucketMapOfSeq([key], [msg]) by {
      reveal_BucketMapOfSeq();
    }
    BucketMapWithSeq(map[key := msg], [key], [msg])
  }
  
  function BucketDropLast(bucket: Bucket) : Bucket
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires 0 < |bucket.keys|
  {
    var submap := MapRemove1(bucket.b, Last(bucket.keys));
    BucketMapWithSeq(submap, DropLast(bucket.keys), DropLast(bucket.msgs))
  }

  lemma BucketDropLastWF(bucket: Bucket)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires 0 < |bucket.keys|
    ensures PreWFBucket(BucketDropLast(bucket))
    ensures WFBucket(bucket) ==> WFBucket(BucketDropLast(bucket))
  {
    reveal_IsStrictlySorted();
    reveal_BucketMapOfSeq();
  }

  lemma BucketDropLastWellMarshalled(bucket: Bucket)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires 0 < |bucket.keys|
    ensures BucketWellMarshalled(BucketDropLast(bucket))
  {
    reveal_IsStrictlySorted();
  }
  
  lemma WFWellMarshalledBucketMap(bucket: Bucket, key: Key)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires key in bucket.b
    ensures bucket.b[key] == bucket.msgs[LargestLte(bucket.keys, key)]
    decreases |bucket.keys|
  {
    reveal_BucketMapOfSeq();
    var i :| 0 <= i < |bucket.keys| && bucket.keys[i] == key;
    PosEqLargestLte(bucket.keys, key, i);
    if i == |bucket.keys| - 1 {
      assert bucket.b[key] == Last(bucket.msgs);
    } else {
      var bdl := BucketDropLast(bucket);
      BucketDropLastWF(bucket);
      BucketDropLastWellMarshalled(bucket);
      WFWellMarshalledBucketMap(bdl, key);
    }
  }

  lemma WFWellMarshalledBucketMapI(bucket: Bucket, i: int)
  requires PreWFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires 0 <= i < |bucket.keys|
  ensures bucket.keys[i] in bucket.b
  ensures bucket.b[bucket.keys[i]] == bucket.msgs[i]
  {
    WFWellMarshalledBucketMap(bucket, bucket.keys[i]);
    assert LargestLte(bucket.keys, bucket.keys[i]) == i by {
      reveal_IsStrictlySorted();
    }
  }

//~  lemma WFWellMarshalledBucketNoIdentityMsgs(bucket: Bucket)
//~    requires WFBucket(bucket)
//~    requires BucketWellMarshalled(bucket)
//~    ensures IdentityMessage() !in bucket.msgs
//~  {
//~    forall i | 0 <= i < |bucket.msgs|
//~      ensures bucket.msgs[i] != IdentityMessage()
//~    {
//~      PosEqLargestLte(bucket.keys, bucket.keys[i], i);
//~      WFWellMarshalledBucketMap(bucket, bucket.keys[i]);
//~    }
//~  }

  lemma WFMessageMultiset(bucket: Bucket)
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
  }
  
  predicate WFBucketAt(bucket: Bucket, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  {
    && WFBucket(bucket)
    && (forall key | key in bucket.b :: bucket.b[key] != IdentityMessage())
    && (forall key | key in bucket.b :: Route(pivots, key) == i)
  }

  lemma WellMarshalledBucketsEq(a: Bucket, b: Bucket)
    requires PreWFBucket(a)
    requires PreWFBucket(b)
    requires BucketWellMarshalled(a)
    requires BucketWellMarshalled(b)
    requires a.b == b.b
    ensures a == b
    decreases |a.keys|
  {
    if |a.b| == 0 {
      if 0 < |a.keys| {
        assert a.keys[0] in Set(a.keys);
        assert false;
      }
      if 0 < |b.keys| {
        assert b.keys[0] in Set(b.keys);
        assert false;
      }
    } else {
      var maxkey := Last(a.keys);
      var maxval := Last(a.msgs);
      WFWellMarshalledBucketMap(a, maxkey);
      WFWellMarshalledBucketMap(b, maxkey);
      
      var adl := BucketDropLast(a);
      BucketDropLastWF(a);
      BucketDropLastWellMarshalled(a);
      var bdl := BucketDropLast(b);
      BucketDropLastWF(b);
      BucketDropLastWellMarshalled(b);
      WellMarshalledBucketsEq(adl, bdl);
    }
  }

  predicate WFBucketList(blist: BucketList, pivots: PivotTable)
  {
    && WFPivots(pivots)
    && |blist| == |pivots| + 1
    && (forall i | 0 <= i < |blist| :: WFBucket(blist[i]))
  }

  predicate WFBucketListProper(blist: BucketList, pivots: PivotTable)
  {
    && WFBucketList(blist, pivots)
    && (forall i | 0 <= i < |blist| :: WFBucketAt(blist[i], pivots, i))
  }

  function BucketGet(bucket: Bucket, key: Key) : Message
  {
    if key in bucket.b then bucket.b[key] else IdentityMessage()
  }

  function BucketListGet(blist: BucketList, pivots: PivotTable, key: Key) : Message
  requires WFBucketList(blist, pivots)
  {
    BucketGet(blist[Route(pivots, key)], key)
  }

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
  {
    var i := Route(pivots, key);
    blist[i := BucketInsert(blist[i], key, msg)]
  }

  // Gives a new child bucket that merges the old child bucket plus the
  // messages from the parent destined for this child.
  function BucketListItemFlush(parent: Bucket, child: Bucket, pivots: PivotTable, i: int) : Bucket
  requires WFPivots(pivots)
  {
    B(map key
    | && (key in (child.b.Keys + parent.b.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Route(pivots, key) == i
      && Merge(BucketGet(parent, key), BucketGet(child, key)) != IdentityMessage()
    :: Merge(BucketGet(parent, key), BucketGet(child, key))
    )
  }

  lemma BucketListItemFlushDependsOnlyOnB(parent: Bucket, child: Bucket,
                                          parent': Bucket, child': Bucket, 
                                          pivots: PivotTable, i: int)
    requires WFPivots(pivots)
    requires parent.b == parent'.b
    requires ClampToSlot(child, pivots, i) == ClampToSlot(child', pivots, i)
    ensures BucketListItemFlush(parent, child, pivots, i) == BucketListItemFlush(parent', child', pivots, i)
  {
    var c := ClampToSlot(child, pivots, i);
    var c' := ClampToSlot(child', pivots, i);
    var m := map key
    | && (key in (child.b.Keys + parent.b.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Route(pivots, key) == i
      && Merge(BucketGet(parent, key), BucketGet(child, key)) != IdentityMessage()
      :: Merge(BucketGet(parent, key), BucketGet(child, key));
    var cm := map key
    | && (key in (c.b.Keys + parent.b.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Route(pivots, key) == i
      && Merge(BucketGet(parent, key), BucketGet(c, key)) != IdentityMessage()
      :: Merge(BucketGet(parent, key), BucketGet(c, key));

   assert m == cm;

   var m' := map key
    | && (key in (child'.b.Keys + parent'.b.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Route(pivots, key) == i
      && Merge(BucketGet(parent', key), BucketGet(child', key)) != IdentityMessage()
      :: Merge(BucketGet(parent', key), BucketGet(child', key));

    assert m == m';
  }
                                          
  function BucketListFlushPartial(parent: Bucket, children: BucketList, pivots: PivotTable, i: int) : (res : BucketList)
  requires WFPivots(pivots)
  requires 0 <= i <= |children|
  ensures |res| == i
  ensures forall h :: 0 <= h < i ==> res[h] == BucketListItemFlush(parent, children[h], pivots, h);
  {
    if i == 0 then [] else (
      BucketListFlushPartial(parent, children, pivots, i-1) + [BucketListItemFlush(parent, children[i-1], pivots, i-1)]
    )
  }

  lemma BucketListFlushPartialDependsOnlyOnB(parent: Bucket, children: BucketList,
                                             parent': Bucket, children': BucketList,
                                             pivots: PivotTable, i: int)
    requires WFPivots(pivots)
    requires 0 <= i <= |children|
    requires parent.b == parent'.b
    requires |children| == |children'|
    requires forall j | 0 <= j < |children| :: ClampToSlot(children[j], pivots, j) == ClampToSlot(children'[j], pivots, j)
    ensures BucketListFlushPartial(parent, children, pivots, i) == BucketListFlushPartial(parent', children', pivots, i)
  {
    if i == 0 {
    } else {
      BucketListFlushPartialDependsOnlyOnB(parent, children, parent', children', pivots, i-1);
      BucketListItemFlushDependsOnlyOnB(parent, children[i-1], parent', children'[i-1], pivots, i-1);
      assert BucketListItemFlush(parent, children[i-1], pivots, i-1) == BucketListItemFlush(parent', children'[i-1], pivots, i-1);
    }
  }
  
  function BucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable) : (res : BucketList)
  requires WFPivots(pivots)
  ensures |res| == |children|
  ensures BucketListWellMarshalled(res)
  ensures forall h :: 0 <= h < |res| ==> res[h] == BucketListItemFlush(parent, children[h], pivots, h);
  {
    BucketListFlushPartial(parent, children, pivots, |children|)
  }

  function JoinBucketList(buckets: seq<Bucket>) : (bucket : Bucket)
    ensures PreWFBucket(bucket)
    ensures BucketWellMarshalled(bucket)
    ensures (forall i | 0 <= i < |buckets| :: WFBucketMap(buckets[i].b)) ==> WFBucket(bucket)
  {
    if |buckets| == 0 then B(map[]) else B(MapUnion(JoinBucketList(DropLast(buckets)).b, Last(buckets).b))
  }

  function SplitBucketOnPivots(bucket: Bucket, pivots: seq<Key>) : (buckets: BucketList)
    ensures |buckets| == |pivots| + 1
    ensures forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
    ensures BucketListWellMarshalled(buckets)
    ensures forall i | 0 <= i < |buckets| :: buckets[i].b.Keys <= bucket.b.Keys
    ensures forall i | 0 <= i < |buckets| :: buckets[i].b.Values <= bucket.b.Values
    ensures forall i | 0 <= i < |buckets| :: |buckets[i].keys| == |buckets[i].msgs|
    ensures WFBucketMap(bucket.b) ==> forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
    decreases |pivots|
  {
    if |pivots| == 0 then (
      [B(bucket.b)]
    ) else (
      var l := B(map key | key in bucket.b && Keyspace.lt(key, Last(pivots)) :: bucket.b[key]);
      var r := B(map key | key in bucket.b && Keyspace.lte(Last(pivots), key) :: bucket.b[key]);

      SplitBucketOnPivots(l, DropLast(pivots)) + [r]
    )
  }

  function ClampToSlot(bucket: Bucket, pivots: PivotTable, i: int) : (res : Bucket)
  requires WFPivots(pivots)
  {
    B(map key | key in bucket.b && Route(pivots, key) == i :: bucket.b[key])
  }

  function {:opaque} BucketIntersect(bucket: Bucket, keys: set<Key>) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  {
    B(map key | key in bucket.b && key in keys :: bucket.b[key])
  }

  function {:opaque} BucketComplement(bucket: Bucket, keys: set<Key>) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  {
    B(map key | key in bucket.b && key !in keys :: bucket.b[key])
  }

  lemma WFBucketIntersect(bucket: Bucket, keys: set<Key>)
  requires WFBucket(bucket)
  ensures WFBucket(BucketIntersect(bucket, keys))
  {
    // reveal_WFBucket();
    reveal_BucketIntersect();
  }

  lemma WFBucketComplement(bucket: Bucket, keys: set<Key>)
  requires WFBucket(bucket)
  ensures WFBucket(BucketComplement(bucket, keys))
  {
    // reveal_WFBucket();
    reveal_BucketComplement();
  }

  ///// Composeing

  predicate BucketsEquivalentForKey(a: Bucket, b: Bucket, key: Key)
  {
    BucketGet(a, key) == BucketGet(b, key)
  }

  predicate BucketsEquivalent(a: Bucket, b: Bucket)
  {
    forall key :: BucketsEquivalentForKey(a, b, key)
  }
  
  // Note: does NOT necessarily return a WFBucket!
  // It might contain NoOp messages
  function {:opaque} Compose(top: Bucket, bot: Bucket) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  {
    B(map key
    | key in (top.b.Keys + bot.b.Keys)
    :: Merge(BucketGet(top, key), BucketGet(bot, key))
    )
  }
  
  function {:opaque} ComposeSeq(buckets: seq<Bucket>) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  {
    if |buckets| == 0 then B(map[]) else Compose(ComposeSeq(DropLast(buckets)), Last(buckets))
  }

  lemma ComposeSeq1(b: Bucket)
  ensures ComposeSeq([b]).b == b.b
  {
    calc {
      ComposeSeq([b]).b;
        { reveal_ComposeSeq(); }
      Compose(ComposeSeq([]), b).b;
        { reveal_ComposeSeq(); }
      Compose(B(map[]), b).b;
        {
          reveal_Compose();
        }
      b.b;
    }
  }

  lemma ComposeAssoc(a: Bucket, b: Bucket, c: Bucket)
  ensures Compose(Compose(a, b), c).b == Compose(a, Compose(b, c)).b
  {
    reveal_Compose();
    var ab_c := Compose(Compose(a, b), c).b;
    var a_bc := Compose(a, Compose(b, c)).b;

    forall key | key in ab_c.Keys
      ensures ab_c[key] == a_bc[key]
    {
      var av := BucketGet(a, key);
      var bv := BucketGet(b, key);
      var cv := BucketGet(c, key);
      MergeIsAssociative(av, bv, cv);
    }
  }

  lemma ComposeSeqAdditive(a: seq<Bucket>, b: seq<Bucket>)
  ensures BucketListWellMarshalled(a) && BucketListWellMarshalled(b)
      ==> BucketListWellMarshalled(a + b)
  ensures ComposeSeq(a + b).b == Compose(ComposeSeq(a), ComposeSeq(b)).b
  {
    reveal_ComposeSeq();
    reveal_Compose();
    if |b| == 0 {
      assert b == [];
      assert a + b == a;
      assert ComposeSeq(a + b).b
          == ComposeSeq(a).b
          == Compose(ComposeSeq(a), B(map[])).b
          == Compose(ComposeSeq(a), ComposeSeq(b)).b;
    } else {
      ComposeSeqAdditive(a, b[..|b|-1]);
      assert (a + b)[..|a+b|-1] == a + b[..|b|-1];
      assert (a+b)[|a+b|-1] == b[|b|-1];
      ComposeAssoc(ComposeSeq(a), ComposeSeq(b[..|b|-1]), b[|b|-1]);
      assert ComposeSeq(a + b).b
          == Compose(ComposeSeq((a + b)[..|a+b|-1]), (a+b)[|a+b|-1]).b
          == Compose(ComposeSeq(a + b[..|b|-1]), b[|b|-1]).b
          == Compose(Compose(ComposeSeq(a), ComposeSeq(b[..|b|-1])), b[|b|-1]).b
          == Compose(ComposeSeq(a), Compose(ComposeSeq(b[..|b|-1]), b[|b|-1])).b
          == Compose(ComposeSeq(a), ComposeSeq(b)).b;
    }
  }

  predicate FlushEquivalentParentChild(oldparent: Bucket, oldchild: Bucket, newparent: Bucket, newchild: Bucket)
  {
    Compose(oldparent, oldchild) == Compose(newparent, newchild)
  }

  predicate FlushEquivalent(oldparent: Bucket, oldchildren: seq<Bucket>, newparent: Bucket, newchildren: seq<Bucket>)
  {
    && |oldchildren| == |newchildren|
    && (forall i | 0 <= i < |oldchildren| :: FlushEquivalentParentChild(oldparent, oldchildren[i], newparent, newchildren[i]))
  }
  
  function InterpretBucketStack(buckets: seq<Bucket>, key: Key) : Message
  {
    if |buckets| == 0 then
      Update(NopDelta())
    else
      Merge(InterpretBucketStack(DropLast(buckets), key), BucketGet(Last(buckets), key))
  }

  lemma BucketGetComposeSeq(buckets: seq<Bucket>, key: Key)
  ensures BucketGet(ComposeSeq(buckets), key) == InterpretBucketStack(buckets, key);
  {
    reveal_ComposeSeq();
    reveal_Compose();
    if |buckets| == 0 {
    } else {
      BucketGetComposeSeq(DropLast(buckets), key);
    }
  }

  ////// Clamping based on RangeStart and RangeEnd

  function {:opaque} ClampRange(bucket: Bucket, start: UI.RangeStart, end: UI.RangeEnd) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  {
    B(map key | key in bucket.b && MS.InRange(start, key, end) :: bucket.b[key])
  }

  function {:opaque} ClampStart(bucket: Bucket, start: UI.RangeStart) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  {
    B(map key | key in bucket.b && MS.LowerBound(start, key) :: bucket.b[key])
  }

  function {:opaque} ClampEnd(bucket: Bucket, end: UI.RangeEnd) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  {
    B(map key | key in bucket.b && MS.UpperBound(key, end) :: bucket.b[key])
  }

  ///// KeyValueMapOfBucket

  function {:opaque} KeyValueMapOfBucket(bucket: Bucket) : map<Key, Value>
  {
    map key | key in bucket.b && Merge(bucket.b[key], DefineDefault()).value != DefaultValue()
      :: Merge(bucket.b[key], DefineDefault()).value
  }

  function {:opaque} SortedSeqOfKeyValueMap(m: map<Key, Value>) : seq<UI.SuccResult>
  {
    var max := Keyspace.maximumOpt(m.Keys);
    if max.None? then
      []
    else
      SortedSeqOfKeyValueMap(MapRemove1(m, max.value))
          + [UI.SuccResult(max.value, m[max.value])]
  }

  lemma SortedSeqOfKeyValueHasKey(m: map<Key, Value>, key: Key)
  requires key in m
  ensures var s := SortedSeqOfKeyValueMap(m);
      exists i :: 0 <= i < |s| && s[i].key == key
  {
    reveal_SortedSeqOfKeyValueMap();
    var max := Keyspace.maximumOpt(m.Keys);
    if max.Some? {
      if key != max.value {
        SortedSeqOfKeyValueHasKey(MapRemove1(m, max.value), key);
        var i :| 0 <= i < |SortedSeqOfKeyValueMap(MapRemove1(m, max.value))| &&
            SortedSeqOfKeyValueMap(MapRemove1(m, max.value))[i].key == key;
        assert SortedSeqOfKeyValueMap(m)[i].key == key;
      } else {
        assert Last(SortedSeqOfKeyValueMap(m)).key == key;
      }
    }
  }

  lemma SortedSeqOfKeyValueMaps(m: map<Key, Value>, i: int)
  requires 0 <= i < |SortedSeqOfKeyValueMap(m)|
  ensures MapsTo(m, SortedSeqOfKeyValueMap(m)[i].key, SortedSeqOfKeyValueMap(m)[i].value)
  {
    reveal_SortedSeqOfKeyValueMap();
    var max := Keyspace.maximumOpt(m.Keys);
    if max.Some? && i != |SortedSeqOfKeyValueMap(m)| - 1 {
      SortedSeqOfKeyValueMaps(MapRemove1(m, max.value), i);
    }
  }

  lemma SortedSeqOfKeyValueMapHasSortedKeys(m: map<Key, Value>)
  ensures var s := SortedSeqOfKeyValueMap(m);
      forall i, j | 0 <= i < j < |s| :: Keyspace.lt(s[i].key, s[j].key)
  {
    var s := SortedSeqOfKeyValueMap(m);
    reveal_SortedSeqOfKeyValueMap();
    var max := Keyspace.maximumOpt(m.Keys);
    if max.Some? {
      SortedSeqOfKeyValueMapHasSortedKeys(MapRemove1(m, max.value));
    }
    forall i, j | 0 <= i < j < |s| ensures Keyspace.lt(s[i].key, s[j].key)
    {
      if j == |s| - 1 {
        SortedSeqOfKeyValueMaps(MapRemove1(m, max.value), i);
        assert Keyspace.lt(s[i].key, s[j].key);
      } else {
        var s1 := SortedSeqOfKeyValueMap(MapRemove1(m, max.value));
        assert Keyspace.lt(s1[i].key, s1[j].key);
      }
    }
  }

  ///// Splitting stuff

  // NB(jonh): These definitions are timeout monsters.
  function {:opaque} SplitBucketLeft(bucket: Bucket, pivot: Key) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  ensures |res.keys| == |res.msgs|
  ensures WFBucketMap(bucket.b) ==> WFBucket(res)
  ensures BucketWellMarshalled(res)
  {
    B(map key | key in bucket.b && Keyspace.lt(key, pivot) :: bucket.b[key])
  }

  function {:opaque} SplitBucketRight(bucket: Bucket, pivot: Key) : (res : Bucket)
  ensures BucketWellMarshalled(res)
  ensures |res.keys| == |res.msgs|
  ensures WFBucketMap(bucket.b) ==> WFBucket(res)
  ensures BucketWellMarshalled(res)
  {
    B(map key | key in bucket.b && Keyspace.lte(pivot, key) :: bucket.b[key])
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

  function {:opaque} MergeBuckets(left: Bucket, right: Bucket) : (res : Bucket)
    ensures BucketWellMarshalled(res)
    ensures PreWFBucket(res)
    ensures WFBucketMap(left.b) && WFBucketMap(right.b) ==> WFBucket(res)
  {
    B(MapUnionPreferA(left.b, right.b))
  }

  function {:opaque} MergeBucketsInList(blist: BucketList, slot: int) : (blist' : BucketList)
    requires 0 <= slot < |blist| - 1
    ensures |blist'| == |blist| - 1
    ensures BucketWellMarshalled(blist'[slot])
  {
    replace2with1(blist,
        MergeBuckets(blist[slot], blist[slot+1]),
        slot)
  }

//~  lemma WFSplitBucketLeft(bucket: Bucket, pivot: Key, pivots: seq<Key>, i: int)
//~  requires 0 <= i <= |pivots|
//~  requires WFPivots(pivots)
//~  requires WFBucketAt(bucket, pivots, i)
//~  ensures WFPivots(pivots[.. i])
//~  ensures WFBucketAt(SplitBucketLeft(bucket, pivot), pivots[.. i], i)
//~  {
//~    reveal_SplitBucketLeft();
//~    WFSlice(pivots, 0, i);
//~    forall key | key in SplitBucketLeft(bucket, pivot).b
//~    ensures Route(pivots[.. i], key) == i
//~    {
//~      RouteIs(pivots[.. i], key, i);
//~    }
//~  }

//~  lemma WFSplitBucketRight(bucket: Bucket, pivot: Key, pivots: seq<Key>, i: int)
//~  requires 0 <= i <= |pivots|
//~  requires WFPivots(pivots)
//~  requires WFBucketAt(bucket, pivots, i)
//~  ensures WFPivots(pivots[i ..])
//~  ensures WFBucketAt(SplitBucketRight(bucket, pivot), pivots[i ..], 0)
//~  {
//~    reveal_SplitBucketRight();
//~    WFSuffix(pivots, i);
//~    forall key | key in SplitBucketRight(bucket, pivot).b
//~    ensures Route(pivots[i ..], key) == 0
//~    {
//~      RouteIs(pivots[i ..], key, 0);
//~    }
//~  }

  lemma WFSplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key)
  requires WFBucketList(blist, pivots)
  requires CutoffForLeft(pivots, key) == cLeft
  ensures WFBucketList(SplitBucketListLeft(blist, pivots, cLeft, key), pivots[.. cLeft])
  {
    reveal_SplitBucketLeft();
    WFSlice(pivots, 0, cLeft);
    // reveal_WFBucket();
  }

  lemma WFProperSplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key)
  requires WFBucketListProper(blist, pivots)
  requires CutoffForLeft(pivots, key) == cLeft
  ensures WFBucketListProper(SplitBucketListLeft(blist, pivots, cLeft, key), pivots[.. cLeft])
  {
    reveal_SplitBucketLeft();
    WFSlice(pivots, 0, cLeft);

    var res := SplitBucketListLeft(blist, pivots, cLeft, key);
    forall i | 0 <= i < |res|
    ensures WFBucketAt(res[i], pivots[..cLeft], i)
    {
      forall key | key in res[i].b
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
    reveal_SplitBucketRight();
    WFSuffix(pivots, cRight);
    // reveal_WFBucket();
  }

  lemma WFProperSplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key)
  requires WFBucketListProper(blist, pivots)
  requires CutoffForRight(pivots, key) == cRight
  ensures WFBucketListProper(SplitBucketListRight(blist, pivots, cRight, key), pivots[cRight ..])
  {
    reveal_SplitBucketRight();
    WFSuffix(pivots, cRight);

    var res := SplitBucketListRight(blist, pivots, cRight, key);
    forall i | 0 <= i < |res|
    ensures WFBucketAt(res[i], pivots[cRight..], i)
    {
      forall key | key in res[i].b
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
    WFPivotsInsert(pivots, slot, pivot);
    reveal_SplitBucketInList();
    var newbuckets := SplitBucketInList(blist, slot, pivot);
    forall i | 0 <= i < |newbuckets|
      ensures WFBucket(newbuckets[i])
    {
      if i < slot {
        assert newbuckets[i] == blist[i];
      } else if i == slot {
        reveal_SplitBucketLeft();
      } else if i == slot + 1 {
        reveal_SplitBucketRight();
      } else {
        assert newbuckets[i] == blist[i-1];
      }
    }
    //WFSplitBucketRight(blist[slot], pivot, pivots, slot);
  }

  lemma WFProperSplitBucketInList(blist: BucketList, slot: int, pivot: Key, pivots: PivotTable)
  requires WFBucketListProper(blist, pivots)
  requires 0 <= slot < |blist|
  requires PivotInsertable(pivots, slot, pivot)
  ensures WFPivots(insert(pivots, pivot, slot))
  ensures WFBucketListProper(SplitBucketInList(blist, slot, pivot), insert(pivots, pivot, slot))
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    reveal_SplitBucketInList();

    var blist' := SplitBucketInList(blist, slot, pivot);
    var pivots' := insert(pivots, pivot, slot);
    WFPivotsInsert(pivots, slot, pivot);

    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', 0, slot-1, 0);
    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist', pivots', slot+2, |blist'|-1, 1);
    assert WFBucketAt(blist'[slot], pivots', slot);
    assert WFBucketAt(blist'[slot+1], pivots', slot+1);
  }

  lemma WellMarshalledSplitBucketInList(blist: BucketList, slot: int, pivot: Key)
  requires 0 <= slot < |blist|
  requires BucketListWellMarshalled(blist)
  ensures BucketListWellMarshalled(SplitBucketInList(blist, slot, pivot))
  {
    var blist' := SplitBucketInList(blist, slot, pivot);
    reveal_SplitBucketInList();
    assert BucketWellMarshalled(SplitBucketLeft(blist[slot], pivot))
      by { reveal_SplitBucketLeft(); }
    assert BucketWellMarshalled(SplitBucketRight(blist[slot], pivot))
      by { reveal_SplitBucketRight(); }
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
  lemma BucketListHasWFBucketAtIdenticalSlice(
      blist: BucketList, pivots: PivotTable, blist': BucketList, pivots': PivotTable, a: int, b: int, d: int)
  requires WFBucketListProper(blist, pivots)
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
      || (forall key | key in blist'[b].b :: Keyspace.lt(key, pivots'[b]))
    )
  requires b >= a && a-1 >= 0 ==> (
      || (a-1-d >= 0 && pivots'[a-1] == pivots[a-1-d])
      || (forall key | key in blist'[a].b :: Keyspace.lte(pivots'[a-1], key))
    )
  ensures forall i | a <= i <= b :: WFBucketAt(blist'[i], pivots', i)
  {
    forall i | a <= i <= b
    ensures WFBucketAt(blist'[i], pivots', i)
    {
      assert WFBucketAt(blist[i-d], pivots, i - d);
      forall key | key in blist'[i].b
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
    reveal_MergeBuckets();
  }

  lemma WFProperMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketListProper(blist, pivots)
  ensures WFBucketListProper(MergeBucketsInList(blist, slot), remove(pivots, slot))
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
  ensures SplitBucketLeft(MergeBucketsInList(blist, slot)[slot], pivots[slot]).b == blist[slot].b
  ensures SplitBucketRight(MergeBucketsInList(blist, slot)[slot], pivots[slot]).b == blist[slot+1].b
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
    // reveal_WFBucket();
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

//~  lemma WFProperBucketListFlush(parent: Bucket, blist: BucketList, pivots: PivotTable)
//~  requires WFBucketListProper(blist, pivots)
//~  ensures WFBucketListProper(BucketListFlush(parent, blist, pivots), pivots)
//~  {
//~    var f := BucketListFlush(parent, blist, pivots);
//~    forall i | 0 <= i < |f|
//~    ensures WFBucketAt(f[i], pivots, i)
//~    {
//~      BucketListFlushAt(parent, blist, pivots, i);
//~    }
//~  }

  lemma GetBucketListFlushEqMerge(parent: Bucket, blist: BucketList, pivots: PivotTable, key: Key)
  requires WFBucketListProper(blist, pivots)
  ensures WFBucketListProper(BucketListFlush(parent, blist, pivots), pivots)
  ensures BucketListGet(BucketListFlush(parent, blist, pivots), pivots, key)
      == Merge(BucketGet(parent, key), BucketListGet(blist, pivots, key))
  {
    WFBucketListFlush(parent, blist, pivots);
    var i := Route(pivots, key);
    BucketListFlushAt(parent, blist, pivots, i);
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
        forall key | key in bucket.b ensures Route(DropLast(pivots), key) == i {
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

//~  lemma BucketListItemFlushAddParentKey(parent: Bucket, child: Bucket, pivots: PivotTable, key: Key, msg: Message)
//~  requires WFPivots(pivots)
//~  requires key !in parent.b
//~  requires key !in child.b
//~  requires msg != IdentityMessage()
//~  ensures B(BucketListItemFlush(parent, child, pivots, Route(pivots, key)).b[key := msg])
//~      == BucketListItemFlush(B(parent.b[key := msg]), child, pivots, Route(pivots, key))
//~  {
//~    assert BucketListItemFlush(parent, child, pivots, Route(pivots, key)).b[key := msg]
//~        == BucketListItemFlush(B(parent.b[key := msg]), child, pivots, Route(pivots, key)).b;
//~  }

//~  lemma BucketListItemFlushAddChildKey(parent: Bucket, child: Bucket, pivots: PivotTable, key: Key, msg: Message)
//~  requires WFPivots(pivots)
//~  requires key !in parent.b
//~  requires key !in child.b
//~  requires msg != IdentityMessage()
//~  ensures B(BucketListItemFlush(parent, child, pivots, Route(pivots, key)).b[key := msg])
//~      == BucketListItemFlush(parent, B(child.b[key := msg]), pivots, Route(pivots, key))
//~  {
//~    assert BucketListItemFlush(parent, child, pivots, Route(pivots, key)).b[key := msg]
//~        == BucketListItemFlush(parent, B(child.b[key := msg]), pivots, Route(pivots, key)).b;
//~  }

//~  lemma BucketListItemFlushAddParentAndChildKey(parent: Bucket, child: Bucket, pivots: PivotTable, key: Key, msgParent: Message, msgChild: Message)
//~  requires WFPivots(pivots)
//~  requires key !in parent.b
//~  requires key !in child.b
//~  requires ValueMessage.Merge(msgParent, msgChild) != IdentityMessage()
//~  ensures B(BucketListItemFlush(parent, child, pivots, Route(pivots, key)).b[key := ValueMessage.Merge(msgParent, msgChild)])
//~      == BucketListItemFlush(B(parent.b[key := msgParent]), B(child.b[key := msgChild]), pivots, Route(pivots, key))
//~  {
//~    assert BucketListItemFlush(parent, child, pivots, Route(pivots, key)).b[key := ValueMessage.Merge(msgParent, msgChild)]
//~        == BucketListItemFlush(B(parent.b[key := msgParent]), B(child.b[key := msgChild]), pivots, Route(pivots, key)).b;
//~  }

//~  lemma BucketListItemFlushEmpty(pivots: seq<Key>)
//~  requires WFPivots(pivots)
//~  ensures BucketListItemFlush(B(map[]), B(map[]), pivots, 0) == B(map[])
//~  {
//~    assert BucketListItemFlush(B(map[]), B(map[]), pivots, 0).b == map[];
//~  }

//~  lemma BucketListItemFlushOfKeysLt(m: Bucket, pivots: seq<Key>, i: int)
//~  requires WFPivots(pivots)
//~  requires 0 <= i < |pivots|
//~  requires forall key | key in m.b :: lt(key, pivots[i])
//~  ensures BucketListItemFlush(m, B(map[]), pivots, i+1) == B(map[])
//~  {
//~  }

//~  lemma BucketListItemFlushEq(p1: Bucket, p2: Bucket, child: Bucket, pivots: seq<Key>, i: int)
//~  requires WFPivots(pivots)
//~  requires 0 <= i <= |pivots|
//~  requires forall key | Route(pivots, key) == i :: MapsAgreeOnKey(p1.b, p2.b, key)
//~  ensures BucketListItemFlush(p1, child, pivots, i)
//~       == BucketListItemFlush(p2, child, pivots, i)
//~  {
//~    assert BucketListItemFlush(p1, child, pivots, i).b
//~        == BucketListItemFlush(p2, child, pivots, i).b;
//~  }

  lemma SplitBucketOnPivotsAt(bucket: Bucket, pivots: seq<Key>, i: int)
  requires WFPivots(pivots)
  requires 0 <= i <= |pivots|
  ensures SplitBucketOnPivots(bucket, pivots)[i].b == ClampToSlot(bucket, pivots, i).b
  decreases |pivots|
  {
    if i == |pivots| {
    } else {
      var l := map key | key in bucket.b && lt(key, Last(pivots)) :: bucket.b[key];
      WFSlice(pivots, 0, |pivots| - 1);
      SplitBucketOnPivotsAt(B(l), DropLast(pivots), i);
      var a := SplitBucketOnPivots(bucket, pivots)[i].b;
      var b := map key | key in bucket.b && Route(pivots, key) == i :: bucket.b[key];

      forall key | key in a
      ensures key in b
      ensures a[key] == b[key];
      {
        assert key in bucket.b;
        if 0 < i {
        }
        if i < |pivots| {
        }
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

  lemma AddMessagesToBucketsEmpAt(bucket: Bucket, pivots: seq<Key>, emp: BucketList, i: int)
  requires WFPivots(pivots)
  requires 0 <= i <= |pivots|
  requires |emp| == |pivots| + 1
  requires forall i | 0 <= i < |emp| :: emp[i] == B(map[])
  requires forall key | key in bucket.b :: bucket.b[key] != IdentityMessage();
  ensures BucketListFlush(bucket, emp, pivots)[i]
       == B(map key | key in bucket.b && Route(pivots, key) == i :: bucket.b[key])
  {
    var a := BucketListFlush(bucket, emp, pivots)[i].b;
    var b := map key | key in bucket.b && Route(pivots, key) == i :: bucket.b[key];
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

  lemma LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket: Bucket, pivots: seq<Key>, emp: seq<Bucket>)
  requires WFBucket(bucket)
  requires WFPivots(pivots)
  requires |emp| == |pivots| + 1
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

//~  lemma BucketListFlushParentEmpty(blist: BucketList, pivots: PivotTable)
//~  requires WFPivots(pivots)
//~  requires WFBucketListProper(blist, pivots)
//~  requires BucketListWellMarshalled(blist)
//~  ensures BucketListFlush(B(map[]), blist, pivots) == blist
//~  {
//~    var a := BucketListFlush(B(map[]), blist, pivots);
//~    var b := blist;
//~    forall i | 0 <= i < |a|
//~    ensures a[i] == b[i]
//~    {
//~      BucketListFlushAt(B(map[]), blist, pivots, i);
//~      WellMarshalledBucketsEq(a[i], b[i]);
//~    }
//~  }

  function emptyList(n: int) : (l : BucketList)
  requires n >= 0
  ensures |l| == n
  ensures forall i | 0 <= i < |l| :: l[i] == B(map[])
  {
    if n == 0 then [] else emptyList(n-1) + [B(map[])]
  }

  lemma WFSplitBucketOnPivots(bucket: Bucket, pivots: seq<Key>)
  requires WFBucket(bucket)
  requires WFPivots(pivots)
  ensures WFBucketListProper(SplitBucketOnPivots(bucket, pivots), pivots)
  {
    // reveal_WFBucket();
    var e := emptyList(|pivots| + 1);
    LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket, pivots, e);
    WFBucketListFlush(bucket, e, pivots);
  }

  lemma JoinBucketsSplitBucketOnPivotsCancel(bucket: Bucket, pivots: seq<Key>)
  requires WFPivots(pivots)
  requires WFBucket(bucket)
  ensures WFBucketListProper(SplitBucketOnPivots(bucket, pivots), pivots)
  ensures JoinBucketList(SplitBucketOnPivots(bucket, pivots)).b == bucket.b
  decreases |pivots|
  {
    WFSplitBucketOnPivots(bucket, pivots);
    // reveal_WFBucket();

    if |pivots| == 0 {
    } else {
      var buckets := SplitBucketOnPivots(bucket, pivots);
      var l := map key | key in bucket.b && Keyspace.lt(key, Last(pivots)) :: bucket.b[key];
      var r := map key | key in bucket.b && Keyspace.lte(Last(pivots), key) :: bucket.b[key];

      var bucketsPref := SplitBucketOnPivots(B(l), DropLast(pivots));
      WFSlice(pivots, 0, |pivots| - 1);
      JoinBucketsSplitBucketOnPivotsCancel(B(l), DropLast(pivots));

      forall i | 0 <= i < |buckets|
      ensures WFBucketAt(buckets[i], pivots, i)
      {
        if i < |buckets| - 1 {
          assert WFBucketAt(bucketsPref[i], DropLast(pivots), i);
          forall key | key in buckets[i].b ensures Route(pivots, key) == i
          {
            RouteIs(DropLast(pivots), key, i);
            assert Route(DropLast(pivots), key) == i;
            //assert buckets[i] == bucketsPref[i];
            //assert key in bucketsPref[i].b;
            SplitBucketOnPivotsAt(B(l), DropLast(pivots), i);
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
  ensures WFBucketList(blist[.. i], pivots[.. i-1])
  {
    StrictlySortedSubsequence(pivots, 0, i-1);
  }

  lemma WFBucketListSplitRight(blist: BucketList, pivots: PivotTable, i: int)
  requires WFBucketList(blist, pivots)
  requires 0 <= i < |blist|
  ensures WFBucketList(blist[i ..], pivots[i ..])
  {
    assert pivots[i..] == pivots[i..|pivots|];
    StrictlySortedSubsequence(pivots, i, |pivots|);
    if 0 < i < |pivots| {
      IsStrictlySortedImpliesLt(pivots, 0, i);
      IsNotMinimum(pivots[0], pivots[i]);
    }
  }

//~  lemma WFProperBucketListSplitLeft(blist: BucketList, pivots: PivotTable, i: int)
//~  requires WFBucketListProper(blist, pivots)
//~  requires 1 <= i <= |blist|
//~  ensures WFBucketListProper(blist[.. i], pivots[.. i-1])
//~  {
//~    WFSlice(pivots, 0, i-1);
//~    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist[.. i], pivots[.. i-1], 0, i-1, 0);
//~  }

//~  lemma WFProperBucketListSplitRight(blist: BucketList, pivots: PivotTable, i: int)
//~  requires WFBucketListProper(blist, pivots)
//~  requires 0 <= i < |blist|
//~  ensures WFBucketListProper(blist[i ..], pivots[i ..])
//~  {
//~    WFSuffix(pivots, i);
//~    BucketListHasWFBucketAtIdenticalSlice(blist, pivots, blist[i..], pivots[i..], 0, |blist|-i-1, -i);
//~  }

//~  lemma BucketListInsertBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable, key: Key, msg: Message)
//~  requires WFBucketListProper(children, pivots)
//~  ensures WFBucketListProper(BucketListFlush(parent, children, pivots), pivots)
//~  ensures BucketListInsert(BucketListFlush(parent, children, pivots), pivots, key, msg)
//~      == BucketListFlush(BucketInsert(parent, key, msg), children, pivots)
//~  {
//~    WFBucketListFlush(parent, children, pivots);
//~
//~    var a := BucketListInsert(BucketListFlush(parent, children, pivots), pivots, key, msg);
//~    var b := BucketListFlush(BucketInsert(parent, key, msg), children, pivots);
//~
//~    assert |a| == |b|;
//~    forall i | 0 <= i < |a|
//~    ensures a[i] == b[i]
//~    {
//~      BucketListFlushAt(parent, children, pivots, i);
//~      BucketListFlushAt(BucketInsert(parent, key, msg), children, pivots, i);
//~      MergeIsAssociative(msg, BucketGet(parent, key), BucketGet(children[i], key));
//~      WellMarshalledBucketsEq(a[i], b[i]);
//~    }
//~  }

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
    ensures BucketWellMarshalled(bucket) ==> msg.None? ==> key !in bucket.b
    ensures BucketWellMarshalled(bucket) ==> msg.Some? ==>
      key in bucket.b && bucket.b[key] == msg.value
  {
    var i := binarySearch(bucket.keys, key);
    if i.Some? then 
      (if BucketWellMarshalled(bucket) then
        WFWellMarshalledBucketMap(bucket, key);
        PosEqLargestLte(bucket.keys, key, i.value);
        Some(bucket.msgs[i.value])
      else
        Some(bucket.msgs[i.value]))
    else
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
  ensures WFPivots([getMiddleKey(bucket)])
  {
    reveal_IsStrictlySorted();
    SeqComparison.reveal_lte();
    IsNotMinimum([], getMiddleKey(bucket));
  }
}
