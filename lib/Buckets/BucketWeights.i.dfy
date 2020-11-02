include "../Base/Sets.i.dfy"
include "../Base/Multisets.i.dfy"
include "BucketsLib.i.dfy"

//
// Assigning weights to buckets guides the flushing algorithm to decide
// which child to push messages towards. TODO(thance): help!
//
// TODO(jonh&robj) Proposed restructuring: Weights don't belong at the
// BucketsLib layer.  They belong at the concrete representation
// layer, where the byte encoding is known.  The only reason they are
// at this layer is that we use a function definition of flushing,
// which means we have to deterministically know which flush we are
// going to do.  If we use a predicate definition instead, then we can
// describe the non-deterministic universe of valid flushes and
// concretize at a lower layer.

module BucketWeights {
  import Sets
  import opened BoundedPivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage`Internal
  import ValueType`Internal
  import opened Maps
  import opened Sequences
  import opened BucketsLib
  import opened NativeTypes
  import opened KeyType
  import opened BucketMaps
  import MSets = Multisets

  
  function WeightKey(key: Key) : (w:nat)
  ensures w >= 0
  {
    4 + |key|
  }
 
  function WeightMessage(msg: Message) : (w:nat)
  ensures w >= 0
  {
    match msg {
      case Define(value) => 4 + ValueType.Len(value)
      case Update(delta) => 0
    }
  }

  function {:opaque} WeightKeyMultiset(keys: multiset<Key>) : (result: nat)
    ensures |keys| == 0 ==> result == 0
  {
    var weights := MSets.Apply(WeightKey, keys);
    assert |keys| == 0 ==> |weights| == 0;
    MSets.FoldSimple<nat>(0, MSets.AddNat, weights)
  }

  function {:opaque} WeightMessageMultiset(msgs: multiset<Message>) : (result: nat)
    ensures |msgs| == 0 ==> result == 0
  {
    var weights := MSets.Apply(WeightMessage, msgs);
    assert |msgs| == 0 ==> |weights| == 0;
    MSets.FoldSimple<nat>(0, MSets.AddNat, weights)
  }
 
  function WeightKeyList(keys: seq<Key>) : (result: nat)
    ensures |keys| == 0 ==> result == 0
  {
    WeightKeyMultiset(multiset(keys))
  }

  function WeightMessageList(msgs: seq<Message>) : (result: nat)
    ensures |msgs| == 0 ==> result == 0
  {
    WeightMessageMultiset(multiset(msgs))
  }

  function WeightBucket(bucket: Bucket) : (w:nat)
    ensures |bucket.keys| == |bucket.msgs| == 0 ==> WeightBucket(bucket) == 0
  {
    WeightKeyList(bucket.keys) + WeightMessageList(bucket.msgs)
  }

  function {:opaque} WeightBucketList(buckets: BucketList) : (w:nat)
  {
    if |buckets| == 0 then 0 else (
      WeightBucketList(DropLast(buckets)) +
          WeightBucket(Last(buckets))
    )
  }

  function {:opaque} WeightBucketMap(m: BucketMap) : (w: nat)
  {
    WeightKeyMultiset(multiset(m.Keys)) + WeightMessageMultiset(Multisets.ValueMultiset(m))
  }

  function method WeightKeyUint64(key: Key) : (w:uint64)
  ensures w as int == WeightKey(key)
  {
    4 + |key| as uint64
  }

  function method WeightMessageUint64(msg: Message) : (w:uint64)
  ensures w as int == WeightMessage(msg)
  {
    match msg {
      case Define(value) => 4 + |value| as uint64
      case Update(delta) => 0
    }
  }

  lemma WeightKeyMultisetAdditive(things1: multiset<Key>, things2: multiset<Key>)
    ensures WeightKeyMultiset(things1 + things2) == WeightKeyMultiset(things1) + WeightKeyMultiset(things2)
  {
    var weights1 := MSets.Apply(WeightKey, things1);
    var weights2 := MSets.Apply(WeightKey, things2);
    MSets.ApplyAdditive(WeightKey, things1, things2);
    MSets.reveal_IsIdentity();
    MSets.reveal_IsAssociative();
    MSets.reveal_IsCommutative();
    MSets.FoldSimpleAdditive<nat>(0, MSets.AddNat, weights1, weights2);
    reveal_WeightKeyMultiset();
  }

  lemma WeightMessageMultisetAdditive(things1: multiset<Message>, things2: multiset<Message>)
    ensures WeightMessageMultiset(things1 + things2) == WeightMessageMultiset(things1) + WeightMessageMultiset(things2)
  {
    var weights1 := MSets.Apply(WeightMessage, things1);
    var weights2 := MSets.Apply(WeightMessage, things2);
    MSets.ApplyAdditive(WeightMessage, things1, things2);
    MSets.reveal_IsIdentity();
    MSets.reveal_IsAssociative();
    MSets.reveal_IsCommutative();
    MSets.FoldSimpleAdditive<nat>(0, MSets.AddNat, weights1, weights2);
    reveal_WeightMessageMultiset();
  }
  
  lemma WeightKeyListFlatten(keys: seq<Key>)
    ensures WeightKeyList(keys) == FlattenLength(FlattenShape(keys)) + 4 * |keys|
  {
    if |keys| == 0 {
    } else {
      WeightKeyListAdditive(DropLast(keys),[ Last(keys) ]);
      assert keys == DropLast(keys) + [ Last(keys) ];
      WeightKeyListFlatten(DropLast(keys));
      WeightKeySingleton(Last(keys));
      reveal_FlattenShape();
      reveal_FlattenLength();
    }
  }
  
  lemma WeightMessageListFlatten(msgs: seq<Message>)
    requires EncodableMessageSeq(msgs)
    ensures WeightMessageList(msgs) == FlattenLength(FlattenShape(messageSeq_to_bytestringSeq(msgs))) + 4 * |msgs|
  {
    if |msgs| == 0 {
    } else {
      assert msgs == DropLast(msgs) + [ Last(msgs) ];
      messageSeq_to_bytestringSeq_Additive(DropLast(msgs), [ Last(msgs) ]);
      WeightMessageListAdditive(DropLast(msgs),[ Last(msgs) ]);
      WeightMessageSingleton(Last(msgs));
      reveal_FlattenShape();
      reveal_FlattenLength();
    }
  }

  lemma WeightBucketEmpty()
  ensures WeightBucket(EmptyBucket()) == 0
  {
  }

  lemma WeightKeySingleton(key: Key)
    ensures WeightKeyMultiset(multiset{key}) == WeightKey(key)
  {
    MSets.ApplySingleton(WeightKey, key);
    MSets.FoldSimpleSingleton<nat>(0, MSets.AddNat, WeightKey(key));
    reveal_WeightKeyMultiset();
  }
  
  lemma WeightMessageSingleton(msg: Message)
    ensures WeightMessageMultiset(multiset{msg}) == WeightMessage(msg)
  {
    MSets.ApplySingleton(WeightMessage, msg);
    MSets.FoldSimpleSingleton<nat>(0, MSets.AddNat, WeightMessage(msg));
    reveal_WeightMessageMultiset();
  }

  lemma WeightBucketSingleton(key:Key, msg: Message)
    ensures WeightBucket(SingletonBucket(key, msg))
    == WeightKey(key) + WeightMessage(msg);
  {
    WeightKeySingleton(key);
    WeightMessageSingleton(msg);
  }

  // when going seqs -> map, weight might decrease if there are dupe keys
  lemma Weight_BucketMap_le_Bucket(b: Bucket)
  requires PreWFBucket(b)
  ensures WeightBucketMap(b.as_map()) <= WeightBucket(b)
  {
    var m := b.as_map();
    MapSeqs.lemma_multisets_le(b.keys, b.msgs);
    assert WeightKeyMultiset(multiset(m.Keys)) <= WeightKeyMultiset(multiset(b.keys)) by {
      var x := multiset(b.keys) - multiset(m.Keys);
      assert multiset(m.Keys) + x == multiset(b.keys);
      WeightKeyMultisetAdditive(multiset(m.Keys), x);
    }
    assert WeightMessageMultiset(Multisets.ValueMultiset(m))
        <= WeightMessageMultiset(multiset(b.msgs)) by {
      var x := multiset(b.msgs) - Multisets.ValueMultiset(m);
      assert Multisets.ValueMultiset(m) + x == multiset(b.msgs);
      WeightMessageMultisetAdditive(Multisets.ValueMultiset(m), x);
    }
    reveal_WeightBucketMap();
  }

  // but seqs -> map preserves the 'weight' if the input keys are sorted
  lemma Weight_BucketMap_eq_Bucket(b: Bucket)
  requires PreWFBucket(b)
  requires IsStrictlySorted(b.keys)
  ensures WeightBucketMap(b.as_map()) == WeightBucket(b)
  {
    Weight_Bucket_eq_BucketMap(b.as_map());
    B_of_as_map_sorted(b);
  }

  // going from map -> seqs preserves weights
  lemma Weight_Bucket_eq_BucketMap(m: BucketMap)
  ensures WeightBucket(B(m)) == WeightBucketMap(m)
  {
    var b := B(m);
    assert MapSeqs.map_of_seqs(b.keys, b.msgs) == m;
    MapSeqs.lemma_multisets_eq(b.keys, b.msgs);
    reveal_WeightBucketMap();
  }

  lemma Weight_SortedBucket_le_UnsortedBucket(unsorted: Bucket, sorted: Bucket)
    requires PreWFBucket(unsorted)
    requires PreWFBucket(sorted)
    requires BucketWellMarshalled(sorted)
    requires unsorted.as_map() == sorted.as_map()
    ensures WeightBucket(sorted) <= WeightBucket(unsorted)
  {
    calc <= {
      WeightBucket(sorted);
      {
        assert B(sorted.as_map()).as_map() == sorted.as_map();
        MapSeqs.SeqsEqOfMapsEq(sorted.keys, sorted.msgs,
            B(sorted.as_map()).keys,
            B(sorted.as_map()).msgs);
        assert sorted == B(sorted.as_map());
      }
      WeightBucket(B(sorted.as_map()));
      {
        Weight_Bucket_eq_BucketMap(sorted.as_map());
      }
      WeightBucketMap(sorted.as_map());
      {
        Weight_BucketMap_le_Bucket(unsorted);
      }
      WeightBucket(unsorted);
    }
  }

  lemma WeightBucketMapSubsetLe(smaller: BucketMap, larger: BucketMap)
    requires smaller.Keys <= larger.Keys
    requires forall k | k in smaller.Keys :: smaller[k] == larger[k];
    ensures WeightBucketMap(smaller) <= WeightBucketMap(larger)
  {
    calc <= {
      WeightKeyMultiset(multiset(smaller.Keys));
      {
        assert multiset(larger.Keys) == multiset(smaller.Keys) + (multiset(larger.Keys) - multiset(smaller.Keys));
        WeightKeyMultisetAdditive(multiset(smaller.Keys), multiset(larger.Keys) - multiset(smaller.Keys));
      }
      WeightKeyMultiset(multiset(larger.Keys));
    }

    calc <= {
      WeightMessageMultiset(Multisets.ValueMultiset(smaller));
      {
        calc <= {
          Multisets.ValueMultiset(smaller);
          //MSets.Apply(MSets.ValueMultisetFn(smaller), multiset(smaller.Keys));
          { MSets.ApplyEquivalentFns(MSets.ValueMultisetFn(smaller), MSets.ValueMultisetFn(larger), multiset(smaller.Keys)); }
          MSets.Apply(MSets.ValueMultisetFn(larger), multiset(smaller.Keys));
          { MSets.ApplyMonotonic(MSets.ValueMultisetFn(larger), multiset(smaller.Keys), multiset(larger.Keys)); }
          MSets.Apply(MSets.ValueMultisetFn(larger), multiset(larger.Keys));
          Multisets.ValueMultiset(larger);
        }
        assert Multisets.ValueMultiset(larger) == Multisets.ValueMultiset(smaller) + (Multisets.ValueMultiset(larger) - Multisets.ValueMultiset(smaller));
        WeightMessageMultisetAdditive(Multisets.ValueMultiset(smaller), Multisets.ValueMultiset(larger) - Multisets.ValueMultiset(smaller));
      }
      WeightMessageMultiset(Multisets.ValueMultiset(larger));
    }

    reveal_WeightBucketMap();
  }

  lemma WeightBucketInduct(bucket: BucketMap, key: Key, msg: Message)
    requires key !in bucket
    ensures WeightBucketMap(bucket[key := msg]) == WeightBucketMap(bucket) + WeightKey(key) + WeightMessage(msg)
  {
    calc {
      WeightKeyMultiset(multiset(bucket[key := msg].Keys));
      {
        calc {
          multiset(bucket[key := msg].Keys);
          multiset(bucket.Keys) + multiset{key};
        }
        WeightKeyMultisetAdditive(multiset(bucket.Keys), multiset{key});
        WeightKeySingleton(key);
        //assert WeightKeyMultiset(multiset{key}) == WeightKey(key);
      }
      WeightKeyMultiset(multiset(bucket.Keys)) + WeightKey(key);
    }

    calc {
      WeightMessageMultiset(Multisets.ValueMultiset(bucket[key := msg]));
      {
        calc {
          Multisets.ValueMultiset(bucket[key := msg]);
          {
            Multisets.ValueMultisetInduct(bucket, key, msg);
          }
          Multisets.ValueMultiset(bucket) + multiset{msg};
        }
        WeightMessageMultisetAdditive(Multisets.ValueMultiset(bucket), multiset{msg});
        WeightMessageSingleton(msg);
      }
      WeightMessageMultiset(Multisets.ValueMultiset(bucket)) + WeightMessage(msg);
    }

    reveal_WeightBucketMap();
  }

  // used internally

  lemma WeightSplitBucketLeft(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    //requires BucketWellMarshalled(bucket)
    ensures WeightBucket(SplitBucketLeft(bucket, pivot)) <= WeightBucket(bucket)
  {
    var i := BoundedKeyspace.binarySearchIndexOfFirstKeyGte(bucket.keys, pivot);
    WeightKeyListAdditive(bucket.keys[..i], bucket.keys[i..]);
    WeightMessageListAdditive(bucket.msgs[..i], bucket.msgs[i..]);
    assert bucket.keys[..i] + bucket.keys[i..] == bucket.keys;
    assert bucket.msgs[..i] + bucket.msgs[i..] == bucket.msgs;
    reveal_SplitBucketLeft();
  }

  // used internally

  lemma WeightSplitBucketRight(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    //requires BucketWellMarshalled(bucket)
    ensures WeightBucket(SplitBucketRight(bucket, pivot)) <= WeightBucket(bucket)
  {
    var i := BoundedKeyspace.binarySearchIndexOfFirstKeyGte(bucket.keys, pivot);
    WeightKeyListAdditive(bucket.keys[..i], bucket.keys[i..]);
    WeightMessageListAdditive(bucket.msgs[..i], bucket.msgs[i..]);
    assert bucket.keys[..i] + bucket.keys[i..] == bucket.keys;
    assert bucket.msgs[..i] + bucket.msgs[i..] == bucket.msgs;
    reveal_SplitBucketRight();
  }

  lemma WeightSplitBucketAdditive(bucket: Bucket, pivot: Key)
    requires PreWFBucket(bucket)
    ensures WeightBucket(SplitBucketLeft(bucket, pivot)) +
            WeightBucket(SplitBucketRight(bucket, pivot)) == WeightBucket(bucket)
  {
    var l := SplitBucketLeft(bucket, pivot);
    var r := SplitBucketRight(bucket, pivot);
    assert bucket.keys == l.keys + r.keys
        && bucket.msgs == l.msgs + r.msgs 
    by {
      reveal_SplitBucketLeft();
      reveal_SplitBucketRight();
    }
    WeightKeyListAdditive(l.keys, r.keys);
    WeightMessageListAdditive(l.msgs, r.msgs);
  }

  lemma WeightBucketList2(a: Bucket, b: Bucket)
    ensures WeightBucketList([a,b]) == WeightBucket(a) + WeightBucket(b)
  {
    calc {
      WeightBucketList([a,b]);
        { reveal_WeightBucketList(); }
      WeightBucketList(DropLast([a,b])) + WeightBucket(Last([a,b]));
        { assert DropLast([a,b]) == [a]; }
      WeightBucketList([a]) + WeightBucket(b);
        { reveal_WeightBucketList(); }
      WeightBucket(a) + WeightBucket(b);
    }
  }

  lemma WeightBucketListConcat(left: BucketList, right: BucketList)
    ensures WeightBucketList(left + right)
         == WeightBucketList(left) + WeightBucketList(right)
  {
    if |right| == 0 {
      reveal_WeightBucketList();
      assert left + right == left;  // trigger
    } else {
      var lessRight := DropLast(right);
      calc {
        WeightBucketList(left + right);
          { assert left + right == left + lessRight + [Last(right)]; }  // trigger
        WeightBucketList(left + lessRight + [Last(right)]);
          { reveal_WeightBucketList(); }
        WeightBucketList(left + lessRight) + WeightBucket(Last(right));
          { WeightBucketListConcat(left, lessRight); }
        WeightBucketList(left) + WeightBucketList(lessRight) + WeightBucket(Last(right));
          { reveal_WeightBucketList(); }
        WeightBucketList(left) + WeightBucketList(right);
      }
    }
  }

  lemma WeightBucketListSlice(blist: BucketList, a: int, b: int)
  requires 0 <= a <= b <= |blist|
  ensures WeightBucketList(blist[a..b]) <= WeightBucketList(blist)
  {
    calc {
      WeightBucketList(blist[a..b]);
      <=
      WeightBucketList(blist[..a]) + WeightBucketList(blist[a..b]) + WeightBucketList(blist[b..]);
        { WeightBucketListConcat(blist[a..b], blist[b..]); }
        { assert blist[a..b] + blist[b..] == blist[a..]; }
      WeightBucketList(blist[..a]) + WeightBucketList(blist[a..]);
        { WeightBucketListConcat(blist[..a], blist[a..]); }
        { assert blist[..a] + blist[a..] == blist; }
      WeightBucketList(blist);
    }
  }
  
  lemma WeightSplitBucketListLeft(blist: BucketList, pivots: PivotTable, cLeft: int, key: Key)
    requires SplitBucketListLeft.requires(blist, pivots, cLeft, key)
    //requires BucketWellMarshalled(blist[cLeft])
    ensures WeightBucketList(SplitBucketListLeft(blist, pivots, cLeft, key))
            <= WeightBucketList(blist)
  {
    // This proof can get away with reveal_WeightBucketList, but maybe for
    // symmetry with the *Right version it should be rewritten with
    // WeightBucketListConcat.
    calc {
      WeightBucketList(SplitBucketListLeft(blist, pivots, cLeft, key));
        { reveal_WeightBucketList(); }
      WeightBucketList(blist[.. cLeft]) + WeightBucket(SplitBucketLeft(blist[cLeft], key));
      <=
        { WeightSplitBucketLeft(blist[cLeft], key); }
      WeightBucketList(blist[.. cLeft]) + WeightBucket(blist[cLeft]);
        {
          reveal_WeightBucketList();
          assert DropLast(blist[.. cLeft + 1]) == blist[.. cLeft];
        }
      WeightBucketList(blist[.. cLeft + 1]);
      <=
        { WeightBucketListSlice(blist, 0, cLeft + 1); }
      WeightBucketList(blist);
    }
  }

  lemma WeightSplitBucketListRight(blist: BucketList, pivots: PivotTable, cRight: int, key: Key)
    requires SplitBucketListRight.requires(blist, pivots, cRight, key)
    //requires BucketWellMarshalled(blist[cRight])
    ensures WeightBucketList(SplitBucketListRight(blist, pivots, cRight, key))
      <= WeightBucketList(blist)
  {
    calc {
      WeightBucketList(SplitBucketListRight(blist, pivots, cRight, key));
      WeightBucketList([SplitBucketRight(blist[cRight], key)] + blist[cRight + 1 ..]);
        { WeightBucketListConcat([SplitBucketRight(blist[cRight], key)], blist[cRight + 1 ..]); }
      WeightBucketList([SplitBucketRight(blist[cRight], key)]) + WeightBucketList(blist[cRight + 1 ..]);
        { reveal_WeightBucketList(); }
      WeightBucket(SplitBucketRight(blist[cRight], key)) + WeightBucketList(blist[cRight + 1 ..]);
      <=
        { WeightSplitBucketRight(blist[cRight], key); }
      WeightBucket(blist[cRight]) + WeightBucketList(blist[cRight + 1 ..]);
        { reveal_WeightBucketList(); }
      WeightBucketList([blist[cRight]]) + WeightBucketList(blist[cRight + 1 ..]);
        { WeightBucketListConcat([blist[cRight]], blist[cRight + 1 ..]); }
        { assert blist[cRight ..] == [blist[cRight]] + blist[cRight + 1 ..]; }
      WeightBucketList(blist[cRight ..]);
      <=
      WeightBucketList(blist[.. cRight]) + WeightBucketList(blist[cRight ..]);
        { WeightBucketListConcat(blist[.. cRight], blist[cRight ..]); }
        { assert blist == blist[.. cRight] + blist[cRight ..]; }
      WeightBucketList(blist);
    }
  }

  // used internally
  lemma WeightBucketListReplace(blist: BucketList, i: int, bucket: Bucket)
  requires 0 <= i < |blist|
  ensures WeightBucketList(blist[i := bucket]) == WeightBucketList(blist) - WeightBucket(blist[i]) + WeightBucket(bucket)
  {
    assert blist[i := bucket] == (blist[..i] + [bucket]) + blist[i+1..];
    calc {
      WeightBucketList(blist[i := bucket]);
        { WeightBucketListConcat(blist[..i] + [bucket], blist[i+1..]); }
      WeightBucketList(blist[..i] + [bucket]) + WeightBucketList(blist[i+1..]);
        { WeightBucketListConcat(blist[..i], [bucket]); }
      WeightBucketList(blist[..i]) + WeightBucketList([bucket]) + WeightBucketList(blist[i+1..]);
        { reveal_WeightBucketList(); }
      WeightBucketList(blist[..i]) + WeightBucket(bucket) + WeightBucketList(blist[i+1..]);
    }
    assert blist == (blist[..i] + [blist[i]]) + blist[i+1..];
    calc {
      WeightBucketList(blist);
        { WeightBucketListConcat(blist[..i] + [blist[i]], blist[i+1..]); }
      WeightBucketList(blist[..i] + [blist[i]]) + WeightBucketList(blist[i+1..]);
        { WeightBucketListConcat(blist[..i], [blist[i]]); }
      WeightBucketList(blist[..i]) + WeightBucketList([blist[i]]) + WeightBucketList(blist[i+1..]);
        { reveal_WeightBucketList(); }
      WeightBucketList(blist[..i]) + WeightBucket(blist[i]) + WeightBucketList(blist[i+1..]);
    }
  }

  // used
  lemma WeightBucketListShrinkEntry(blist: BucketList, i: int, bucket: Bucket)
  requires 0 <= i < |blist|
  requires WeightBucket(bucket) <= WeightBucket(blist[i])
  ensures WeightBucketList(blist[i := bucket]) <= WeightBucketList(blist)
  {
    WeightBucketListReplace(blist, i, bucket);
  }

  // Analogous to WeightBucketListReplace, except we're changing the size of the subsequence in the middle.
  // used internally
  lemma WeightSplitBucketInList(blist: BucketList, i: int, pivot: Key)
    requires 0 <= i < |blist|
    requires WFBucket(blist[i])
    ensures WeightBucketList(SplitBucketInList(blist, i, pivot))
    == WeightBucketList(blist)
  {
    assert blist == (blist[..i] + [blist[i]]) + blist[i+1..];
    calc {  // Take the old list apart
      WeightBucketList(blist);
        { WeightBucketListConcat(blist[..i] + [blist[i]], blist[i+1..]); }
      WeightBucketList(blist[..i] + [blist[i]]) + WeightBucketList(blist[i+1..]);
        { WeightBucketListConcat(blist[..i], [blist[i]]); }
      WeightBucketList(blist[..i]) + WeightBucketList([blist[i]]) + WeightBucketList(blist[i+1..]);
        { reveal_WeightBucketList(); }
      WeightBucketList(blist[..i]) + WeightBucket(blist[i]) + WeightBucketList(blist[i+1..]);
    }

    calc {  // Take the new list apart
      SplitBucketInList(blist, i, pivot);
        { reveal_SplitBucketInList(); }
      replace1with2(blist, SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot), i);
        { reveal_replace1with2(); }
      blist[..i] + [SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot)] + blist[i+1..];
    }
    calc {
      WeightBucketList(SplitBucketInList(blist, i, pivot));
      WeightBucketList((blist[..i] + [SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot)]) + blist[i+1..]);
        { WeightBucketListConcat((blist[..i] + [SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot)]), blist[i+1..]); }
      WeightBucketList(blist[..i] + [SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot)])
        + WeightBucketList(blist[i+1..]);
        { WeightBucketListConcat(blist[..i], [SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot)]); }
      WeightBucketList(blist[..i])
        + WeightBucketList([SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot)])
        + WeightBucketList(blist[i+1..]);
    }

    // And then relate the replaced terms.
    WeightBucketList2(SplitBucketLeft(blist[i], pivot), SplitBucketRight(blist[i], pivot));
    WeightSplitBucketAdditive(blist[i], pivot);
  }

  // used
  lemma WeightBucketListSuffix(blist: BucketList, a: int)
  requires 0 <= a <= |blist|
  ensures WeightBucketList(blist[a..]) <= WeightBucketList(blist)
  {
    WeightBucketListConcat(blist[..a], blist[a..]);
    assert blist == blist[..a] + blist[a..];
  }

  lemma KeyMultisetLeWeight(keys: multiset<Key>)
    ensures 4 * |keys| <= WeightKeyMultiset(keys)
  {
    if |keys| == 0 {
    } else {
      var weights := MSets.Apply(WeightKey, keys);
      var key :| key in keys;
      var rest := keys - multiset{key};
      assert keys == rest + multiset{key};
      
      calc <= {
        4 * |keys|;
        4 * |rest| + 4 * |multiset{key}|;
        {
          KeyMultisetLeWeight(rest);
        }
        WeightKeyMultiset(rest) + WeightKey(key);
        {
          reveal_WeightKeyMultiset();
          MSets.ApplySingleton(WeightKey, key);
          MSets.FoldSimpleSingleton<nat>(0, MSets.AddNat, WeightKey(key));
        }
        WeightKeyMultiset(rest) + WeightKeyMultiset(multiset{key});
        { WeightKeyMultisetAdditive(rest, multiset{key}); }
        WeightKeyMultiset(keys);
      }
    }
  }

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma NumElementsLteWeight(bucket: Bucket)
    requires PreWFBucket(bucket)
    ensures |bucket.keys| <= WeightBucket(bucket)
    decreases bucket.keys
  {
    KeyMultisetLeWeight(multiset(bucket.keys));
    SetCardinality(bucket.keys);
  }

  // used
  lemma WeightBucketListOneEmpty()
  ensures WeightBucketList([EmptyBucket()]) == 0
  {
    reveal_WeightBucketList();
    WeightBucketEmpty();
  }

  // used
  lemma WeightBucketLeBucketList(blist: BucketList, i: int)
  requires 0 <= i < |blist|
  ensures WeightBucket(blist[i]) <= WeightBucketList(blist)
  {
    calc {
      WeightBucket(blist[i]);
        { reveal_WeightBucketList(); }
      WeightBucketList([blist[i]]);
        { assert [blist[i]] == blist[i..i+1]; } // trigger
      WeightBucketList(blist[i..i+1]);
      <=
        { WeightBucketListSlice(blist, i, i+1); }
      WeightBucketList(blist);
    }
  }

  lemma WeightBucketInsert(bucket: Bucket, key: Key, msg: Message)
  requires PreWFBucket(bucket)
  ensures WeightBucket(BucketInsert(bucket, key, msg)) <=
      WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)
  {
    var mergedMsg := Merge(msg, BucketGet(bucket.as_map(), key));
    if mergedMsg == IdentityMessage() {
      // case 1: entry from map is removed
      calc <= {
        WeightBucket(BucketInsert(bucket, key, msg));
        WeightBucket(B(MapRemove1(bucket.as_map(), key)));
        {
         Weight_Bucket_eq_BucketMap(MapRemove1(bucket.as_map(), key));
        }
        WeightBucketMap(MapRemove1(bucket.as_map(), key));
        {
          WeightBucketMapSubsetLe(MapRemove1(bucket.as_map(), key), bucket.as_map());
        }
        WeightBucketMap(bucket.as_map());
        {
          Weight_BucketMap_le_Bucket(bucket);
        }
        WeightBucket(bucket);
        WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg);
      }
    } else if key !in bucket.as_map() {
      // case 2: entry inserted into map
      calc <= {
        WeightBucket(BucketInsert(bucket, key, msg));
        WeightBucket(B(bucket.as_map()[key := mergedMsg]));
        {
          Weight_Bucket_eq_BucketMap(bucket.as_map()[key := mergedMsg]);
        }
        WeightBucketMap(bucket.as_map()[key := mergedMsg]);
        {
          WeightBucketInduct(bucket.as_map(), key, mergedMsg);
        }
        WeightBucketMap(bucket.as_map()) + WeightKey(key) + WeightMessage(mergedMsg);
        WeightBucketMap(bucket.as_map()) + WeightKey(key) + WeightMessage(msg);
        {
          Weight_BucketMap_le_Bucket(bucket);
        }
        WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg);
      }
    } else {
      // case 3: entry is replaced
      // relies on weight(mergedMsg) <= weight(oldMsg) + weight(msg)
      var m' := MapRemove1(bucket.as_map(), key);
      var oldMsg := bucket.as_map()[key];
      calc <= {
        WeightBucket(BucketInsert(bucket, key, msg));
        {
          assert m'[key := mergedMsg] == bucket.as_map()[key := mergedMsg];
        }
        WeightBucket(B(m'[key := mergedMsg]));
        {
          Weight_Bucket_eq_BucketMap(m'[key := mergedMsg]);
        }
        WeightBucketMap(m'[key := mergedMsg]);
        {
          WeightBucketInduct(m', key, mergedMsg);
        }
        WeightBucketMap(m') + WeightKey(key) + WeightMessage(mergedMsg);
        WeightBucketMap(m') + WeightKey(key) + WeightMessage(oldMsg) + WeightMessage(msg);
        {
          WeightBucketInduct(m', key, oldMsg);
        }
        WeightBucketMap(m'[key := oldMsg]) + WeightMessage(msg);
        {
          assert m'[key := oldMsg] == bucket.as_map();
        }
        WeightBucketMap(bucket.as_map()) + WeightMessage(msg);
        {
          Weight_BucketMap_le_Bucket(bucket);
        }
        WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg);
      }
    }
  }

  lemma WeightBucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message)
    requires WFBucketList(blist, pivots)
    requires BoundedKey(pivots, key)
    ensures WeightBucketList(BucketListInsert(blist, pivots, key, msg)) <=
    WeightBucketList(blist) + WeightKey(key) + WeightMessage(msg)
  {
    var i := Route(pivots, key);
    var bucket := blist[i];
    var bucket' := BucketInsert(bucket, key, msg);

    calc <= {
      WeightBucketList(BucketListInsert(blist, pivots, key, msg));
        { WeightBucketListReplace(blist, i, BucketInsert(bucket, key, msg)); }
      WeightBucketList(blist) - WeightBucket(bucket) + WeightBucket(BucketInsert(bucket, key, msg));
        { WeightBucketInsert(bucket, key, msg); }
      WeightBucketList(blist) + WeightKey(key) + WeightMessage(msg);
    }
  }
  
  lemma WeightKeyListAdditive(a: seq<Key>, b: seq<Key>)
  ensures WeightKeyList(a) + WeightKeyList(b) == WeightKeyList(a + b)
  {
    WeightKeyMultisetAdditive(multiset(a), multiset(b));
  }

  lemma WeightMessageListAdditive(a: seq<Message>, b: seq<Message>)
  ensures WeightMessageList(a) + WeightMessageList(b) == WeightMessageList(a + b)
  {
    WeightMessageMultisetAdditive(multiset(a), multiset(b));
  }

  lemma WeightKeyListPushFront(key: Key, keys: seq<Key>)
  ensures WeightKeyList([key] + keys)
      == WeightKey(key) + WeightKeyList(keys)
  {
    WeightKeyListAdditive([key], keys);
    WeightKeySingleton(key);
  }

  lemma WeightMessageListPushFront(msg: Message, msgs: seq<Message>)
  ensures WeightMessageList([msg] + msgs)
      == WeightMessage(msg) + WeightMessageList(msgs)
  {
    WeightMessageListAdditive([msg], msgs);
    WeightMessageSingleton(msg);
  }

  lemma WeightKeyListPushBack(keys: seq<Key>, key: Key)
  ensures WeightKeyList(keys + [key])
      == WeightKey(key) + WeightKeyList(keys)
  {
    WeightKeyListAdditive(keys, [key]);
    WeightKeySingleton(key);
  }

  lemma WeightMessageListPushBack(msgs: seq<Message>, msg: Message)
  ensures WeightMessageList(msgs + [msg])
      == WeightMessage(msg) + WeightMessageList(msgs)
  {
    WeightMessageListAdditive(msgs, [msg]);
    WeightMessageSingleton(msg);
  }

  lemma WeightBucketMapSingleton(key: Key, msg: Message)
  ensures WeightBucketMap(map[key := msg])
      == WeightKey(key) + WeightMessage(msg)
  {
    var m := map[];
    assert map[key := msg] == m[key := msg];
    calc {
      WeightBucketMap(map[key := msg]);
      WeightBucketMap(m[key := msg]);
      { WeightBucketInduct(m, key, msg); }
      WeightBucketMap(m) + WeightKey(key) + WeightMessage(msg);
      {
        assert WeightBucketMap(map[]) == 0 by { reveal_WeightBucketMap(); }
      }
      WeightKey(key) + WeightMessage(msg);
    }
  }
}
