// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Base/KeyType.s.dfy"
include "../Base/Message.i.dfy"
include "BoundedPivotsLib.i.dfy"
include "../../MapSpec/MapSpec.s.dfy"

module BucketMaps {
  import opened BoundedPivotsLib
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import UI
  import MS = MapSpec
  import opened Maps
  import UnboundedKeyspace = Lexicographic_Byte_Order

  type BucketMap = map<Key, Message>

  function BucketGet(m: BucketMap, key: Key) : Message
  {
    if key in m then m[key] else IdentityMessage()
  }

  // Gives a new child bucket that merges the old child bucket plus the
  // messages from the parent destined for this child.
  function BucketListItemFlush(parent: BucketMap, child: BucketMap, pivots: PivotTable, i: int) : BucketMap
  requires WFPivots(pivots)
  {
    map key
    | && (key in (child.Keys + parent.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && BoundedKey(pivots, key)
      && Route(pivots, key) == i
      && Merge(BucketGet(parent, key), BucketGet(child, key)) != IdentityMessage()
    :: Merge(BucketGet(parent, key), BucketGet(child, key))
  }

  function BucketListFlushPartial(parent: BucketMap, children: seq<BucketMap>, pivots: PivotTable, i: int) : (res : seq<BucketMap>)
  requires WFPivots(pivots)
  requires 0 <= i <= |children|
  ensures |res| == i
  ensures forall h :: 0 <= h < i ==> res[h] == BucketListItemFlush(parent, children[h], pivots, h);
  {
    if i == 0 then [] else (
      BucketListFlushPartial(parent, children, pivots, i-1) + [BucketListItemFlush(parent, children[i-1], pivots, i-1)]
    )
  }
  
  function BucketListFlush(parent: BucketMap, children: seq<BucketMap>, pivots: PivotTable) : (res : seq<BucketMap>)
  requires WFPivots(pivots)
  ensures |res| == |children|
  ensures forall h :: 0 <= h < |res| ==> res[h] == BucketListItemFlush(parent, children[h], pivots, h);
  {
    BucketListFlushPartial(parent, children, pivots, |children|)
  }

  function {:opaque} BucketIntersect(bucket: BucketMap, keys: set<Key>) : (res : BucketMap)
  {
    map key | key in bucket && key in keys :: bucket[key]
  }

  function {:opaque} BucketComplement(bucket: BucketMap, keys: set<Key>) : (res : BucketMap)
  {
    map key | key in bucket && key !in keys :: bucket[key]
  }

  ////// Clamping based on RangeStart and RangeEnd

  function {:opaque} ClampRange(bucket: BucketMap, start: UI.RangeStart, end: UI.RangeEnd) : (res : BucketMap)
  {
    map key | key in bucket && MS.InRange(start, key, end) :: bucket[key]
  }

  function {:opaque} ClampStart(bucket: BucketMap, start: UI.RangeStart) : (res : BucketMap)
  {
    map key | key in bucket && MS.LowerBound(start, key) :: bucket[key]
  }

  function {:opaque} ClampEnd(bucket: BucketMap, end: UI.RangeEnd) : (res : BucketMap)
  {
    map key | key in bucket && MS.UpperBound(key, end) :: bucket[key]
  }

  ///// Composing
 
  // Note: does NOT necessarily return a WFBucket!
  // It might contain NoOp messages
  function {:opaque} Compose(top: BucketMap, bot: BucketMap) : (res : BucketMap)
  {
    map key
    | key in (top.Keys + bot.Keys)
    :: Merge(BucketGet(top, key), BucketGet(bot, key))
  }
  
  function {:opaque} ComposeSeq(buckets: seq<BucketMap>) : (res : BucketMap)
  {
    if |buckets| == 0 then map[] else Compose(ComposeSeq(DropLast(buckets)), Last(buckets))
  }

  lemma ComposeSeq1(b: BucketMap)
  ensures ComposeSeq([b]) == b
  {
    calc {
      ComposeSeq([b]);
        { reveal_ComposeSeq(); }
      Compose(ComposeSeq([]), b);
        { reveal_ComposeSeq(); }
      Compose(map[], b);
        {
          reveal_Compose();
        }
      b;
    }
  }

  lemma ComposeAssoc(a: BucketMap, b: BucketMap, c: BucketMap)
  ensures Compose(Compose(a, b), c) == Compose(a, Compose(b, c))
  {
    reveal_Compose();
    var ab_c := Compose(Compose(a, b), c);
    var a_bc := Compose(a, Compose(b, c));

    forall key | key in ab_c.Keys
      ensures ab_c[key] == a_bc[key]
    {
      var av := BucketGet(a, key);
      var bv := BucketGet(b, key);
      var cv := BucketGet(c, key);
      MergeIsAssociative(av, bv, cv);
    }
  }

  lemma ComposeSeqAdditive(a: seq<BucketMap>, b: seq<BucketMap>)
  ensures ComposeSeq(a + b) == Compose(ComposeSeq(a), ComposeSeq(b))
  {
    reveal_ComposeSeq();
    reveal_Compose();
    if |b| == 0 {
      assert b == [];
      assert a + b == a;
      assert ComposeSeq(a + b)
          == ComposeSeq(a)
          == Compose(ComposeSeq(a), map[])
          == Compose(ComposeSeq(a), ComposeSeq(b));
    } else {
      ComposeSeqAdditive(a, b[..|b|-1]);
      assert (a + b)[..|a+b|-1] == a + b[..|b|-1];
      assert (a+b)[|a+b|-1] == b[|b|-1];
      ComposeAssoc(ComposeSeq(a), ComposeSeq(b[..|b|-1]), b[|b|-1]);
      assert ComposeSeq(a + b)
          == Compose(ComposeSeq((a + b)[..|a+b|-1]), (a+b)[|a+b|-1])
          == Compose(ComposeSeq(a + b[..|b|-1]), b[|b|-1])
          == Compose(Compose(ComposeSeq(a), ComposeSeq(b[..|b|-1])), b[|b|-1])
          == Compose(ComposeSeq(a), Compose(ComposeSeq(b[..|b|-1]), b[|b|-1]))
          == Compose(ComposeSeq(a), ComposeSeq(b));
    }
  }

  ///// KeyValueMapOfBucket

  function {:opaque} KeyValueMapOfBucket(bucket: BucketMap) : map<Key, Value>
  {
    map key | key in bucket && Merge(bucket[key], DefineDefault()).value != DefaultValue()
      :: Merge(bucket[key], DefineDefault()).value
  }

  function {:opaque} SortedSeqOfKeyValueMap(m: map<Key, Value>) : seq<UI.SuccResult>
  {
    var max := UnboundedKeyspace.maximumOpt(m.Keys);
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
    var max := UnboundedKeyspace.maximumOpt(m.Keys);
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
    var max := UnboundedKeyspace.maximumOpt(m.Keys);
    if max.Some? && i != |SortedSeqOfKeyValueMap(m)| - 1 {
      SortedSeqOfKeyValueMaps(MapRemove1(m, max.value), i);
    }
  }

  lemma SortedSeqOfKeyValueMapHasSortedKeys(m: map<Key, Value>)
  ensures var s := SortedSeqOfKeyValueMap(m);
      forall i, j | 0 <= i < j < |s| :: UnboundedKeyspace.lt(s[i].key, s[j].key)
  {
    var s := SortedSeqOfKeyValueMap(m);
    reveal_SortedSeqOfKeyValueMap();
    var max := UnboundedKeyspace.maximumOpt(m.Keys);
    if max.Some? {
      SortedSeqOfKeyValueMapHasSortedKeys(MapRemove1(m, max.value));
    }
    forall i, j | 0 <= i < j < |s| ensures UnboundedKeyspace.lt(s[i].key, s[j].key)
    {
      if j == |s| - 1 {
        SortedSeqOfKeyValueMaps(MapRemove1(m, max.value), i);
        assert UnboundedKeyspace.lt(s[i].key, s[j].key);
      } else {
        var s1 := SortedSeqOfKeyValueMap(MapRemove1(m, max.value));
        assert UnboundedKeyspace.lt(s1[i].key, s1[j].key);
      }
    }
  }

  ///// Splitting stuff

  // NB(jonh): These definitions are timeout monsters.
  /*function {:opaque} SplitBucketMapLeft(bucket: BucketMap, pivot: Key) : (res : BucketMap)
  {
    map key | key in bucket && Keyspace.lt(KeyToElement(key), KeyToElement(pivot)) :: bucket[key]
  }

  function {:opaque} SplitBucketMapRight(bucket: BucketMap, pivot: Key) : (res : BucketMap)
  {
    map key | key in bucket && Keyspace.lte(KeyToElement(pivot), KeyToElement(key)) :: bucket[key]
  }*/
}
