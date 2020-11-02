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

  function {:opaque} WeightBucketMap(b: BucketMap) : (w: nat)
  {
    WeightKeyMultiset(multiset(b.Keys)) + WeightMessageMultiset(Multisets.ValueMultiset(b))
  }

/*
  lemma MergeGainsNoWeight(parent: Message, child: Message)
  ensures WeightMessage(Merge(parent, child)) <= WeightMessage(parent) + WeightMessage(child)
  {
    //var merged := Merge(parent, child);
    //if (parent.Update? && child.Define?) {
    //}
  }
  */

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

  /*function {:opaque} WeightKeySeq(keys: seq<Key>) : nat
  {
    var weights := ApplyOpaque(WeightKey, keys);
    FoldFromRight<nat, nat>(MSets.AddNat, 0, weights)
  }*/

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

/*
  lemma WeightKeyMultisetUpperBound(keys: multiset<Key>)
    ensures WeightKeyMultiset(keys) <= |keys| * (4 + KeyType.MaxLen() as nat)
  {
    if |keys| == 0 {
    } else {
      var key :| key in keys;
      var rest := keys - multiset{key};
      assert keys == rest + multiset{key};
      calc <= {
        WeightKeyMultiset(keys);
        //WeightKeyMultiset(rest + multiset{key});
        { WeightKeyMultisetAdditive(rest, multiset{key}); }
        WeightKeyMultiset(rest) + WeightKeyMultiset(multiset{key});
        { WeightKeyMultisetUpperBound(rest); }
        |rest| * (4 + KeyType.MaxLen() as nat) + WeightKeyMultiset(multiset{key});
        {
          reveal_WeightKeyMultiset();
          MSets.ApplySingleton(WeightKey, key);
          MSets.FoldSimpleSingleton<nat>(0, MSets.AddNat, WeightKey(key));
        }
        //|rest| * (4 + KeyType.MaxLen() as nat) + WeightKey(key);
        //|rest| * (4 + KeyType.MaxLen() as nat) + (4 + KeyType.MaxLen() as nat);
        |keys| * (4 + KeyType.MaxLen() as nat );
      }
    }
  }
  */
  
  /*function {:opaque} WeightMessageSeq(msgs: seq<Message>) : nat
  {
    var weights := ApplyOpaque(WeightMessage, msgs);
    FoldFromRight<nat, nat>(MSets.AddNat, 0, weights)
  }*/

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

  /*lemma WeightKeySeqList(keys: seq<Key>)
    ensures WeightKeySeq(keys) == WeightKeyList(keys)
  {
    var ws := ApplyOpaque(WeightKey, keys);
    var ws' := MSets.Apply(WeightKey, multiset(keys));
    calc {
      WeightKeySeq(keys);
      { reveal_WeightKeySeq(); }
      FoldFromRight<nat, nat>(MSets.AddNat, 0, ws);
      { MSets.natsumProperties(); }
      { MSets.FoldSeq<nat>(0, MSets.AddNat, ws); }
      MSets.FoldSimple<nat>(0, MSets.AddNat, multiset(ws));
      { MSets.ApplySeq(WeightKey, keys); }
      MSets.FoldSimple<nat>(0, MSets.AddNat, ws');
      { reveal_WeightKeyMultiset(); }
      WeightKeyList(keys);
    }
  }*/

  /*lemma WeightMessageSeqList(msgs: seq<Message>)
    ensures WeightMessageSeq(msgs) == WeightMessageList(msgs)
  {
    var ws := ApplyOpaque(WeightMessage, msgs);
    var ws' := MSets.Apply(WeightMessage, multiset(msgs));
    calc {
      WeightMessageSeq(msgs);
      { reveal_WeightMessageSeq(); }
      FoldFromRight<nat, nat>(MSets.AddNat, 0, ws);
      { MSets.natsumProperties(); }
      { MSets.FoldSeq<nat>(0, MSets.AddNat, ws); }
      MSets.FoldSimple<nat>(0, MSets.AddNat, multiset(ws));
      { MSets.ApplySeq(WeightMessage, msgs); }
      MSets.FoldSimple<nat>(0, MSets.AddNat, ws');
      { reveal_WeightMessageMultiset(); }
      WeightMessageList(msgs);
    }
  }*/

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

  lemma Weight_BucketMap_le_Bucket(b: Bucket)
  requires PreWFBucket(b)
  ensures WeightBucketMap(b.as_map()) <= WeightBucket(b)
  {
    assume false;
  }

  lemma Weight_BucketMap_eq_Bucket(b: Bucket)
  requires PreWFBucket(b)
  requires IsStrictlySorted(b.keys)
  ensures WeightBucketMap(b.as_map()) == WeightBucket(b)
  {
    assume false;
  }

  lemma Weight_Bucket_eq_BucketMap(bm: BucketMap)
  ensures WeightBucket(B(bm)) == WeightBucketMap(bm)
  {
    assume false;
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

  /*
  
  lemma WeightWellMarshalledListPointwiseLe(blist: BucketList, blist': BucketList)
    requires |blist| == |blist'|
    requires forall i | 0 <= i < |blist| :: PreWFBucket(blist[i])
    requires forall i | 0 <= i < |blist| :: PreWFBucket(blist'[i])
    requires forall i | 0 <= i < |blist| :: WeightBucket(blist'[i]) <= WeightBucket(blist[i])
    //requires forall i | 0 <= i < |blist| :: blist[i] == blist'[i] || BucketWellMarshalled(blist'[i])
    ensures WeightBucketList(blist') <= WeightBucketList(blist)
  {
    if |blist| == 0 {
    } else {
      WeightWellMarshalledListPointwiseLe(DropLast(blist), DropLast(blist'));
      assert blist == DropLast(blist) + [ Last(blist) ];
      assert blist' == DropLast(blist') + [ Last(blist') ];
      WeightBucketListConcatOne(DropLast(blist), Last(blist));
      WeightBucketListConcatOne(DropLast(blist'), Last(blist'));
    }
  }
    
  // Commonly-used filters for Image()
  function AllKeys() : iset<Key>
  {
    iset k | true
  }
  function IncludeKey(key:Key) : iset<Key>
  {
    iset k | k == key
  }
  function ExcludeKey(key:Key) : iset<Key>
  {
    iset k | k != key
  }

  // Image of bucket showing only keys in filter.
  function {:opaque} Image(bucket:Bucket, filter:iset<Key>) : (image:Bucket)
    ensures BucketWellMarshalled(image)
    ensures PreWFBucket(image)
    ensures |image.keys| == |image.msgs|
    ensures WFBucketMap(bucket.b) ==> WFBucket(image)
  {
    B(map k | k in bucket.b && k in filter :: bucket.b[k])
  }

  lemma ImageShape(b:Bucket, s:iset<Key>)
    ensures forall k :: k in b.b && k in s <==> k in Image(b, s).b.Keys
    ensures forall k :: k in Image(b,s).b ==> Image(b,s).b[k] == b.b[k];
  {
    reveal_Image();
  }

  lemma ImageMapIdentity(bucket:Bucket, s:iset<Key>)
    requires forall k :: k in bucket.b ==> k in s
    ensures bucket.b == Image(bucket, s).b
  {
    reveal_Image();
  }
  
  lemma ImageIdentity(bucket:Bucket, s:iset<Key>)
  requires PreWFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires forall k :: k in bucket.b ==> k in s
  ensures bucket == Image(bucket, s)
  {
    ImageMapIdentity(bucket, s);
    WellMarshalledBucketsEq(bucket, Image(bucket, s));
  }

  lemma ImageTrim(bucket:Bucket, s:iset<Key>, trimBucket:Bucket)
    requires forall k :: k in trimBucket.b <==> k in bucket.b && k in s
    requires forall k :: k in trimBucket.b ==> trimBucket.b[k] == bucket.b[k]
    ensures Image(bucket, s).b == trimBucket.b
  {
    ImageShape(bucket, s);
  }

  lemma ImageEquiv(a:Bucket, b:Bucket, s:iset<Key>)
    requires forall k :: k in a.b.Keys && k in s <==> k in b.b.Keys && k in s
    requires forall k :: k in a.b.Keys && k in s ==> a.b[k] == b.b[k]
    ensures Image(a, s) == Image(b, s)
  {
    reveal_Image();
  }


  lemma ImageSubset(b:Bucket, s:iset<Key>, t:iset<Key>)
    requires s <= t;
    ensures Image(Image(b, t), s) == Image(b, s)
    ensures Image(b, s).b.Keys <= Image(b, t).b.Keys
  {
    reveal_Image();
  }

  lemma ImageIntersect(b:Bucket, s:iset<Key>, t:iset<Key>)
    ensures Image(Image(b, s), t) == Image(b, s * t)
  {
    reveal_Image();
  }

  // used internally
  lemma ImageSplitsKeys(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires a !! b
    requires forall k:Key :: k in bucket.b ==> k in a + b
    ensures multiset(bucket.keys) == multiset(Image(bucket, a).keys) + multiset(Image(bucket, b).keys)
  {
    var abucket := Image(bucket, a);
    var bbucket := Image(bucket, b);
    
    calc {
      multiset(bucket.keys);
      { WellMarshalledKeyMultiset(bucket); }
      multiset(bucket.b.Keys);
      { reveal_Image(); }
      multiset(abucket.b.Keys) + multiset(bbucket.b.Keys);
      {
        WellMarshalledKeyMultiset(abucket);
        WellMarshalledKeyMultiset(bbucket);
      }
      multiset(Image(bucket, a).keys) + multiset(Image(bucket, b).keys);
    }
  }

  // used internally
  lemma ImageSplitsMessages(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires a !! b
    requires forall k:Key :: k in bucket.b ==> k in a + b
    ensures multiset(bucket.msgs) == multiset(Image(bucket, a).msgs) + multiset(Image(bucket, b).msgs)
  {
    var abucket := Image(bucket, a);
    var bbucket := Image(bucket, b);

    var fn := Multisets.ValueMultisetFn(bucket.b);
    var afn := Multisets.ValueMultisetFn(abucket.b);
    var bfn := Multisets.ValueMultisetFn(bbucket.b);
    
    calc {
      multiset(bucket.msgs);
      { WFMessageMultiset(bucket); }
      Multisets.ValueMultiset(bucket.b);
      Multisets.Apply(fn, multiset(bucket.b.Keys));
      { WellMarshalledKeyMultiset(bucket); }
      Multisets.Apply(fn, multiset(bucket.keys));
      {
        ImageSplitsKeys(bucket, a, b);
        Multisets.ApplyAdditive(fn, multiset(abucket.keys), multiset(bbucket.keys));
      }
      Multisets.Apply(fn, multiset(abucket.keys)) + Multisets.Apply(fn, multiset(bbucket.keys));
      {
        WellMarshalledKeyMultiset(abucket);
        WellMarshalledKeyMultiset(bbucket);
      }
      Multisets.Apply(fn, multiset(abucket.b.Keys)) + Multisets.Apply(fn, multiset(bbucket.b.Keys));
      {
        reveal_Image();
        Multisets.ApplyEquivalentFns(fn, afn, multiset(abucket.b.Keys));
        Multisets.ApplyEquivalentFns(fn, bfn, multiset(bbucket.b.Keys));
      }
      Multisets.ValueMultiset(abucket.b) + Multisets.ValueMultiset(bbucket.b);
      {
        WFMessageMultiset(abucket);
        WFMessageMultiset(bbucket);
      }
      multiset(abucket.msgs) + multiset(bbucket.msgs);
    }
  }

  // used internally
  lemma WeightBucketLinearInKeySet(bucket:Bucket, a:iset<Key>, b:iset<Key>)
  requires PreWFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires a !! b
  requires forall k:Key :: k in bucket.b ==> k in a + b
  ensures WeightBucket(bucket) == WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b))
  decreases |Image(bucket, a).b.Keys| + |Image(bucket, b).b.Keys|, 1
  {
    var keys := bucket.keys;
    var msgs := bucket.msgs;
    var keysweights := MSets.Apply(WeightKey, multiset(keys));
    var msgsweights := MSets.Apply(WeightMessage, multiset(msgs));

    var akeys := Image(bucket, a).keys;
    var amsgs := Image(bucket, a).msgs;
    var ab := Image(bucket, a).b;
    var akeysweights := MSets.Apply(WeightKey, multiset(akeys));
    var amsgsweights := MSets.Apply(WeightMessage, multiset(amsgs));
    
    var bkeys := Image(bucket, b).keys;
    var bmsgs := Image(bucket, b).msgs;
    var bb := Image(bucket, b).b;
    var bkeysweights := MSets.Apply(WeightKey, multiset(bkeys));
    var bmsgsweights := MSets.Apply(WeightMessage, multiset(bmsgs));

    Multisets.natsumProperties();
    
    calc {
      WeightBucket(bucket);
      // WeightKeyList(keys) + WeightMessageList(msgs);
      // WeightKeyMultiset(multiset(keys)) + WeightMessageMultiset(multiset(msgs));
      {
        reveal_WeightKeyMultiset();
        reveal_WeightMessageMultiset();
      }
      MSets.FoldSimple<nat>(0, MSets.AddNat, keysweights) + MSets.FoldSimple<nat>(0, MSets.AddNat, msgsweights);
      {
        ImageSplitsMessages(bucket, a, b);
        //assert multiset(msgs) == multiset(amsgs) + multiset(bmsgs);
        Multisets.ApplyAdditive(WeightMessage, multiset(amsgs), multiset(bmsgs));
        //assert msgsweights == amsgsweights + bmsgsweights;
        Multisets.FoldSimpleAdditive<nat>(0, MSets.AddNat, amsgsweights, bmsgsweights);
      }
        MSets.FoldSimple<nat>(0, MSets.AddNat, keysweights)
      + MSets.FoldSimple<nat>(0, MSets.AddNat, amsgsweights) + MSets.FoldSimple<nat>(0, MSets.AddNat, bmsgsweights);
      {
        ImageSplitsKeys(bucket, a, b);
        //assert multiset(keys) == multiset(akeys) + multiset(bkeys);
        Multisets.ApplyAdditive(WeightKey, multiset(akeys), multiset(bkeys));
        //assert keysweights == akeysweights + bkeysweights;
        Multisets.FoldSimpleAdditive<nat>(0, MSets.AddNat, akeysweights, bkeysweights);
      }
        MSets.FoldSimple<nat>(0, MSets.AddNat, akeysweights) + MSets.FoldSimple<nat>(0, MSets.AddNat, amsgsweights)
      + MSets.FoldSimple<nat>(0, MSets.AddNat, bkeysweights) + MSets.FoldSimple<nat>(0, MSets.AddNat, bmsgsweights);
      {
        reveal_WeightKeyMultiset();
        reveal_WeightMessageMultiset();
      }
      //   WeightKeyMultiset(multiset(akeys)) + WeightMessageMultiset(multiset(amsgs))
      // + WeightKeyMultiset(multiset(bkeys)) + WeightMessageMultiset(multiset(bmsgs));
      //   WeightKeyList(akeys) + WeightMessageList(amsgs)
      // + WeightKeyList(bkeys) + WeightMessageList(bmsgs);
      WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b));
    }
  }

  // A variant that's handy if a+b don't cover bucket.
  // used internally
  lemma WeightBucketLinearInKeySetSum(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires a!!b
    ensures WeightBucket(Image(bucket, a + b)) == WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b));
  {
    var c := a + b;
    calc {
      WeightBucket(Image(bucket, a))
        + WeightBucket(Image(bucket, b));
        { ImageSubset(bucket, b, c); }
      WeightBucket(Image(bucket, a))
        + WeightBucket(Image(Image(bucket, c), b));
        { ImageSubset(bucket, a, c); }
      WeightBucket(Image(Image(bucket, c), a))
        + WeightBucket(Image(Image(bucket, c), b));
      {
        ImageShape(bucket, c);
        WeightBucketLinearInKeySet(Image(bucket, c), a, b);
      }
      WeightBucket(Image(bucket, c));
    }
  }

  function WeightOneKey(bucket: Bucket, key: Key) : (w:int)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
  {
    if key in bucket.b
      then WeightKey(key) + WeightMessage(bucket.b[key])
      else 0
  }

  // used internally
  lemma KeyContribution(bucket: Bucket, key: Key)
    requires PreWFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    ensures WeightBucket(bucket) == WeightBucket(Image(bucket, ExcludeKey(key))) + WeightOneKey(bucket, key);
  {
    var kbucket := Image(bucket, IncludeKey(key));
    
    ImageIdentity(bucket, ExcludeKey(key) + IncludeKey(key));
    WeightBucketLinearInKeySetSum(bucket, ExcludeKey(key), IncludeKey(key));

    ImageShape(bucket, IncludeKey(key));
    if key in bucket.b {
      WFWellMarshalledBucketMapI(kbucket, 0);
      assert kbucket.keys == [key] by {
        reveal_Image();
        reveal_B();
      }
      assert kbucket == SingletonBucket(key, bucket.b[key]);
      WeightBucketSingleton(key, kbucket.b[key]);
    } else {
      WeightBucketEmpty();
      WellMarshalledKeyMultiset(kbucket);
    }
  }
  */

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

  /*
  function ILeftKeys(pivot: Key) : iset<Key> { iset k | Lexicographic_Byte_Order.lt(k, pivot) }
  function IRightKeys(pivot: Key) : iset<Key> { iset k | Lexicographic_Byte_Order.lte(pivot, k) }

  // used internally
  lemma SplitBucketImage(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    ensures SplitBucketLeft(bucket, pivot) == Image(bucket, ILeftKeys(pivot))
    ensures SplitBucketRight(bucket, pivot) == Image(bucket, IRightKeys(pivot))
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    reveal_Image();
    //ImageShape(bucket, ILeftKeys(pivot));
    //ImageShape(bucket, IRightKeys(pivot));
  }
  */

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

  /*lemma WeightSplitAtIdxBucketAdditive(bucket: Bucket, i: int)
    requires PreWFBucket(bucket)
    requires 0 <= i <= |bucket.keys|
    ensures WeightBucket(SplitBucketLeftAtIdx(bucket, i)) +
            WeightBucket(SplitBucketRightAtIdx(bucket, i)) == WeightBucket(bucket)
  {
    var l := SplitBucketLeftAtIdx(bucket, i);
    var r := SplitBucketRightAtIdx(bucket, i);
    assert bucket.keys == l.keys + r.keys
        && bucket.msgs == l.msgs + r.msgs 
    by {
      reveal_SplitBucketLeftAtIdx();
      reveal_SplitBucketRightAtIdx();
    }
    WeightKeyListAdditive(l.keys, r.keys);
    WeightMessageListAdditive(l.msgs, r.msgs);
  }*/


  /*
  lemma WeightSplitBucketAdditiveLe(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    //requires BucketWellMarshalled(bucket)
    ensures WeightBucket(SplitBucketLeft(bucket, pivot)) +
            WeightBucket(SplitBucketRight(bucket, pivot)) <= WeightBucket(bucket)
  {
    var wmbucket := Image(bucket, AllKeys());
    ImageMapIdentity(bucket, AllKeys());
    WeightWellMarshalledLe(bucket, wmbucket);
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    WeightSplitBucketAdditive(wmbucket, pivot);
  }
  */

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

/*
  lemma WeightBucketListConcatOne(left: BucketList, extra: Bucket)
    ensures WeightBucketList(left + [extra]) == WeightBucketList(left) + WeightBucket(extra)
  {
    WeightBucketListConcat(left, [extra]);
    reveal_WeightBucketList();
  }
  */

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

  /*
  function RouteRange(pivots: PivotTable, i: int) : iset<Key>
    requires WFPivots(pivots)
  {
    iset k | BoundedKey(pivots, k) && Route(pivots, k) == i
  }

  // used internally
  lemma WeightBucketListItemFlushSingletonOrEmpty(parent: Bucket, children: BucketList, pivots: PivotTable, i: int, filter:iset<Key>, key:Key)
    requires WFPivots(pivots)
    requires WFBucket(parent)
    requires BucketWellMarshalled(parent)
    requires 0 <= i < |children|
    requires WFBucket(children[i])
    requires BucketListWellMarshalled(children)
    requires forall k :: k in filter ==> k == key   // filter admits at most one key
    ensures WeightBucket(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i))
    <= WeightBucket(Image(parent, RouteRange(pivots, i) * filter))
    + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter));
  {
    reveal_Image();

    var flush := BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i);
    if key in flush.b.Keys {
      WellMarshalledBucketsEq(flush, SingletonBucket(key, flush.b[key]));
      WeightBucketSingleton(key, flush.b[key]);
    } else {
      WellMarshalledBucketsEq(flush, EmptyBucket());
      WeightBucketEmpty();
    }

    var filteredParent := Image(parent, RouteRange(pivots, i) * filter);
    if key in filteredParent.b {
      WellMarshalledBucketsEq(filteredParent, SingletonBucket(key, filteredParent.b[key]));
      WeightBucketSingleton(key, filteredParent.b[key]);
    } else {
      WellMarshalledBucketsEq(filteredParent, EmptyBucket());
      WeightBucketEmpty();
    }

    var filteredChild := Image(children[i], RouteRange(pivots, i) * filter);
    if key in filteredChild.b {
      WellMarshalledBucketsEq(filteredChild, SingletonBucket(key, filteredChild.b[key]));
      WeightBucketSingleton(key, filteredChild.b[key]);
    } else {
      WellMarshalledBucketsEq(filteredChild, EmptyBucket());
      WeightBucketEmpty();
    }

    if (key in filteredChild.b && key in filteredParent.b && key in flush.b) {
      // This is the only tricksy case, where we actually care how Merge
      // affects weights of the messages getting swapped.
      MergeGainsNoWeight(BucketGet(filteredParent, key), BucketGet(filteredChild, key));
    }
  }

  // used internally
  lemma WeightBucketFilterPartitions(bucket:Bucket, filter:iset<Key>, a:iset<Key>, b:iset<Key>)
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires a !! b
    requires filter * a + filter * b == filter;
    ensures WeightBucket(Image(bucket, filter)) ==
      WeightBucket(Image(bucket, filter * a)) + WeightBucket(Image(bucket, filter * b));
  {
    calc {
      WeightBucket(Image(bucket, filter));
        {
          ImageShape(bucket, filter);
          WeightBucketLinearInKeySet(Image(bucket, filter), a, b);
        }
      WeightBucket(Image(Image(bucket, filter), a)) + WeightBucket(Image(Image(bucket, filter), b));
        {
          ImageIntersect(bucket, filter, a);
          ImageIntersect(bucket, filter, b);
        }
      WeightBucket(Image(bucket, filter * a)) + WeightBucket(Image(bucket, filter * b));
    }
  }

  // used internally
  lemma WeightBucketListItemFlushInner(parent: Bucket, children: BucketList, pivots: PivotTable, i: int, filter:iset<Key>)
    requires WFBucket(parent)
    requires BucketWellMarshalled(parent)
    requires forall i | 0 <= i < |children| :: WFBucket(children[i])
    requires BucketListWellMarshalled(children)
    requires WFPivots(pivots)
    requires 0 <= i < |children|
    ensures
    WeightBucket(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i))
    <= WeightBucket(Image(parent, RouteRange(pivots, i) * filter)) + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter))
  decreases |Image(parent, filter).b| + |Image(children[i], filter).b|
  {
    // Pick an arbitrary key to decrease by
    // (In Lisp, "car" is the first thing in a list, "cdr" is everything else.)
    var carKey;
    if |Image(parent, filter).b| != 0 {
      carKey :| carKey in Image(parent, filter).b;
    } else if |Image(children[i], filter).b| != 0 {
      carKey :| carKey in Image(children[i], filter).b;
    } else {
      WellMarshalledBucketsEq(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), EmptyBucket());
      WeightBucketEmpty();
      return;
    }

    var carFilter := IncludeKey(carKey);
    var cdrFilter := ExcludeKey(carKey);

    // cdrFilter decreases
    if |Image(parent, filter).b| != 0 {
      forall ensures |Image(parent, filter * cdrFilter).b| < |Image(parent, filter).b|
      {
        reveal_Image();
        Sets.ProperSubsetImpliesSmallerCardinality(Image(parent, filter * cdrFilter).b.Keys, Image(parent, filter).b.Keys);
      }
      ImageSubset(children[i], filter * cdrFilter, filter);
      Sets.SetInclusionImpliesSmallerCardinality(Image(children[i], filter * cdrFilter).b.Keys, Image(children[i], filter).b.Keys);
    } else {
      ImageSubset(parent, filter * cdrFilter, filter);
      Sets.SetInclusionImpliesSmallerCardinality(Image(parent, filter * cdrFilter).b.Keys, Image(parent, filter).b.Keys);
      forall ensures |Image(children[i], filter * cdrFilter).b| < |Image(children[i], filter).b|
      {
        reveal_Image();
        Sets.ProperSubsetImpliesSmallerCardinality(Image(children[i], filter * cdrFilter).b.Keys, Image(children[i], filter).b.Keys);
      }
    }

    // The core of the proof is that the inequality holds for the carKey we chose from the parent.
    forall k | k in BucketListItemFlush(Image(parent, filter * carFilter), Image(children[i], filter * carFilter), pivots, i).b.Keys
      ensures k == carKey
    {
      reveal_Image();
    }

    calc {
      WeightBucket(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i));
        {
          WeightBucketLinearInKeySet(
            BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), carFilter, cdrFilter);
        }
      WeightBucket(Image(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), carFilter))
      + WeightBucket(Image(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), cdrFilter));
        { // push filters through Image operator & BucketListItemFlush.
          reveal_Image();
          WellMarshalledBucketsEq(
            Image(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), carFilter),
            BucketListItemFlush(Image(parent, filter * carFilter), Image(children[i], filter * carFilter), pivots, i)
          );
          WellMarshalledBucketsEq(
            Image(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), cdrFilter),
            BucketListItemFlush(Image(parent, filter * cdrFilter), Image(children[i], filter * cdrFilter), pivots, i)
          );
        }
      WeightBucket(BucketListItemFlush(Image(parent, filter * carFilter), Image(children[i], filter * carFilter), pivots, i))
      + WeightBucket(BucketListItemFlush(Image(parent, filter * cdrFilter), Image(children[i], filter * cdrFilter), pivots, i));
      <=
        { // recursion for car
          WeightBucketListItemFlushSingletonOrEmpty(parent, children, pivots, i, filter * carFilter, carKey);
          assert RouteRange(pivots, i) * (filter * carFilter) == RouteRange(pivots, i) * filter * carFilter;
          // recursion for cdr
          WeightBucketListItemFlushInner(parent, children, pivots, i, filter * cdrFilter);
          assert RouteRange(pivots, i) * (filter * cdrFilter) == RouteRange(pivots, i) * filter * cdrFilter;
        }
      WeightBucket(Image(parent, RouteRange(pivots, i) * filter * carFilter)) + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(Image(parent, RouteRange(pivots, i) * filter * cdrFilter)) + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter * cdrFilter));
      // Just rearranging terms
      WeightBucket(Image(parent, RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(Image(parent, RouteRange(pivots, i) * filter * cdrFilter))
        + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter * cdrFilter));
      { WeightBucketFilterPartitions(parent, RouteRange(pivots, i) * filter, carFilter, cdrFilter); }
      WeightBucket(Image(parent, RouteRange(pivots, i) * filter))
        + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter * cdrFilter));
      { WeightBucketFilterPartitions(children[i], RouteRange(pivots, i) * filter, carFilter, cdrFilter); }
      WeightBucket(Image(parent, RouteRange(pivots, i) * filter))
        + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter));
    }
  }

  // used internally
  lemma WeightBucketListItemFlush(parent: Bucket, children: BucketList, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  requires WFBucket(parent)
  requires BucketWellMarshalled(parent)
  requires forall i | 0 <= i < |children| :: WFBucket(children[i])
  requires BucketListWellMarshalled(children)
  ensures WeightBucket(BucketListItemFlush(parent, children[i], pivots, i))
      <= WeightBucket(Image(parent, RouteRange(pivots, i))) + WeightBucket(Image(children[i], RouteRange(pivots, i)))
  {
    WeightBucketListItemFlushInner(parent, children, pivots, i, AllKeys());
    ImageIdentity(parent, AllKeys());
    ImageIdentity(children[i], AllKeys());
    reveal_Image();
    assert Image(parent, RouteRange(pivots, i) * AllKeys()) == Image(parent, RouteRange(pivots, i));  // trigger
    assert Image(children[i], RouteRange(pivots, i) * AllKeys()) == Image(children[i], RouteRange(pivots, i));  // trigger
  }

  function RouteRanges(pivots: PivotTable, i: int) : iset<Key>
    // Keys that route to children < i
    requires WFPivots(pivots)
  {
    iset k | BoundedKey(pivots, k) && Route(pivots, k) < i
  }

  // The sequence axioms were responsible for creating a timeout in the rich
  // context where this was used; hence this ugly workaround.
  lemma SequenceSingleton<T>(s:seq<T>, i:int)
  requires 0 <= i < |s|
  ensures s[i..i+1] == [s[i]];
  {
  }

  // used internally
  lemma WMWeightBucketListFlushPartial(parent: Bucket, children: BucketList, pivots: PivotTable, items: int)
  requires WFBucketListProper(children, pivots)
  requires 0 <= items <= |children|
  requires WFBucket(parent)
  requires BucketWellMarshalled(parent)
  requires BucketListWellMarshalled(children)
  ensures WeightBucketList(BucketListFlushPartial(parent, children, pivots, items))
      <= WeightBucket(Image(parent, RouteRanges(pivots, items)))
        + WeightBucketList(children[..items])
  {
    if items == 0 {
    } else {
      calc {
        WeightBucketList(BucketListFlushPartial(parent, children, pivots, items));
          { // Break off the last element as a sublist.
            WeightBucketListConcat(BucketListFlushPartial(parent, children, pivots, items - 1),
              [BucketListItemFlush(parent, children[items - 1], pivots, items - 1)]);
          }
        WeightBucketList(BucketListFlushPartial(parent, children, pivots, items - 1))
          + WeightBucketList([BucketListItemFlush(parent, children[items - 1], pivots, items - 1)]);
          { reveal_WeightBucketList(); }  // from singleton list to bucket
        WeightBucketList(BucketListFlushPartial(parent, children, pivots, items - 1))
          + WeightBucket(BucketListItemFlush(parent, children[items - 1], pivots, items - 1));
        <=
          { WMWeightBucketListFlushPartial(parent, children, pivots, items - 1); }  // Recurse on prefix
        WeightBucket(Image(parent, RouteRanges(pivots, items - 1)))
          + WeightBucketList(children[..items - 1])
          + WeightBucket(BucketListItemFlush(parent, children[items - 1], pivots, items - 1));
        <=
          { WeightBucketListItemFlush(parent, children, pivots, items -1); }  // Flush the singleton
        WeightBucket(Image(parent, RouteRanges(pivots, items - 1)))
          + WeightBucketList(children[..items - 1])
          + WeightBucket(Image(parent, RouteRange(pivots, items - 1)))
          + WeightBucket(Image(children[items - 1], RouteRange(pivots, items - 1)));
        {  // Glue the parent halves back together
          WeightBucketLinearInKeySetSum(parent, RouteRanges(pivots, items - 1), RouteRange(pivots, items - 1));
          assert RouteRanges(pivots, items) == RouteRanges(pivots, items - 1) + RouteRange(pivots, items - 1);  // trigger
        }
        WeightBucket(Image(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items - 1])
          + WeightBucket(Image(children[items - 1], RouteRange(pivots, items - 1)));
        { // The last child bucket's RouteRange covers the whole bucket, so we can simplify.
          ImageShape(children[items - 1], RouteRange(pivots, items - 1));
          WellMarshalledBucketsEq(Image(children[items - 1], RouteRange(pivots, items - 1)), children[items-1]);
        }
        WeightBucket(Image(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items-1]) + WeightBucket(children[items-1]);
        { // pack the last bucket up into a singleton list
          SequenceSingleton(children, items-1);
          //assert children[items-1..items] == [children[items-1]]; // trigger
          reveal_WeightBucketList();
        }
        WeightBucket(Image(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items-1]) + WeightBucket(children[items-1]);
        { // and glue the children sublists back together
          WeightBucketListConcatOne(children[..items-1], children[items-1]);
          assert children[..items-1] + [children[items-1]] == children[..items]; // trigger
        }
        WeightBucket(Image(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items]);
      }
    }
  }

  // used internally
  lemma WMWeightBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable)
  requires WFBucketListProper(children, pivots)
  requires |children| == NumBuckets(pivots)
  requires WFBucket(parent)
  requires BucketWellMarshalled(parent)
  requires forall key | key in parent.b.Keys :: BoundedKey(pivots, key)
  // requires forall i | 0 <= i < |children| :: WFBucket(children[i])
  requires BucketListWellMarshalled(children)
  ensures WeightBucketList(BucketListFlush(parent, children, pivots))
      <= WeightBucket(parent) + WeightBucketList(children)
  {
    WMWeightBucketListFlushPartial(parent, children, pivots, |children|);
    forall ensures Image(parent, RouteRanges(pivots, |children|)) == parent
    {
      reveal_Image();
      WellMarshalledBucketsEq(Image(parent, RouteRanges(pivots, |children|)), parent);
    }
    assert children[..|children|] == children;  // trigger
  }

  // used
  lemma WeightBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable)
  requires WFBucketList(children, pivots)
  requires |children| == NumBuckets(pivots)
  requires WFBucket(parent)
  requires forall key | key in parent.b.Keys :: BoundedKey(pivots, key)
  //requires forall i | 0 <= i < |children| :: WFBucket(children[i])
  //requires BucketListWellMarshalled(children)
  ensures WeightBucketList(BucketListFlush(parent, children, pivots))
      <= WeightBucket(parent) + WeightBucketList(children)
  {
    var wmparent := Image(parent, AllKeys());
    var cchildren := seq(|children|, i requires 0 <= i < |children| => ClampToSlot(children[i], pivots, i));
    
    ImageMapIdentity(parent, AllKeys());
    forall i: nat | i < |children|
      ensures ClampToSlot(children[i], pivots, i) == ClampToSlot(cchildren[i], pivots, i)
      ensures WeightBucket(cchildren[i]) <= WeightBucket(children[i])
    {
      var c := ClampToSlot(children[i], pivots, i);
      var cc := ClampToSlot(cchildren[i], pivots, i);
      WellMarshalledBucketsEq(c, cc);
      WeightWellMarshalledSubsetLe(cchildren[i], children[i]);
    }

    WeightWellMarshalledLe(parent, wmparent);
    WeightWellMarshalledListPointwiseLe(children, cchildren);
    WMWeightBucketListFlush(wmparent, cchildren, pivots);
    BucketListFlushPartialDependsOnlyOnB(wmparent, cchildren, parent, children, pivots, |cchildren|);
  }
  */
  
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

  /*
  // used
  lemma WeightBucketListClearEntry(blist: BucketList, i: int)
  requires 0 <= i < |blist|
  ensures WeightBucketList(blist[i := B(map[])]) <= WeightBucketList(blist)
  {
    WeightBucketListReplace(blist, i, B(map[]));
  }
  */

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
  /*lemma WeightSplitBucketInListLe(blist: BucketList, i: int, pivot: Key)
   requires 0 <= i < |blist|
   requires WFBucket(blist[i])
   ensures WeightBucketList(SplitBucketInList(blist, i, pivot))
           <= WeightBucketList(blist)
  {
    var newblist := blist[i := B(blist[i].b)];
    calc <= {
      WeightBucketList(SplitBucketInList(blist, i, pivot));
      {
        reveal_SplitBucketInList();
        reveal_SplitBucketRight();
        reveal_SplitBucketLeft();
        reveal_replace1with2();
        assert blist[..i] == newblist[..i];
        assert blist[i+1..] == newblist[i+1..];
      }
      WeightBucketList(SplitBucketInList(newblist, i, pivot));
      { WeightSplitBucketInList(newblist, i, pivot); }
      WeightBucketList(newblist);
      {
        assert newblist == newblist[..i] + newblist[i..];
        assert newblist[i..] == newblist[i..i+1] + newblist[i+1..];
        WeightBucketListConcat(newblist[..i], newblist[i..]);
        WeightBucketListConcat(newblist[i..i+1], newblist[i+1..]);
      }
      WeightBucketList(newblist[..i]) + WeightBucketList(newblist[i..i+1]) + WeightBucketList(newblist[i+1..]);
      {
        WeightWellMarshalledLe(blist[i], newblist[i]);
        reveal_WeightBucketList();
      }
      WeightBucketList(newblist[..i]) + WeightBucketList(blist[i..i+1]) + WeightBucketList(newblist[i+1..]);
      {
        assert blist == blist[..i] + blist[i..];
        assert blist[i..] == blist[i..i+1] + blist[i+1..];
        WeightBucketListConcat(blist[..i], blist[i..]);
        WeightBucketListConcat(blist[i..i+1], blist[i+1..]);
      }
      WeightBucketList(blist);
    }
  }*/

  // used
  lemma WeightBucketListSuffix(blist: BucketList, a: int)
  requires 0 <= a <= |blist|
  ensures WeightBucketList(blist[a..]) <= WeightBucketList(blist)
  {
    WeightBucketListConcat(blist[..a], blist[a..]);
    assert blist == blist[..a] + blist[a..];
  }

  /*
  // used internally
  lemma MergedKeyMultisets(left: Bucket, right: Bucket)
    requires PreWFBucket(left)
    requires PreWFBucket(right)
    ensures multiset(MergeBuckets(left, right).keys) <= multiset(left.keys) + multiset(right.keys)
  {
    var merged := MergeBuckets(left, right);
    var fn := Multisets.ValueMultisetFn(merged.b);
    calc <= {
      multiset(merged.keys);
      { WellMarshalledKeyMultiset(merged); }
      multiset(merged.b.Keys);
      { reveal_MergeBuckets(); }
      //multiset(left.b.Keys) + multiset(right.b.Keys);
      multiset(left.keys) + multiset(right.keys);
    }
  }

  // used internally
  lemma MergedMessageMultisets(left: Bucket, right: Bucket)
    requires PreWFBucket(left)
    requires PreWFBucket(right)
    ensures multiset(MergeBuckets(left, right).msgs) <= multiset(left.msgs) + multiset(right.msgs)
  {
    var merged := MergeBuckets(left, right);
    var fn := Multisets.ValueMultisetFn(merged.b);
    calc <= {
      multiset(merged.msgs);
      { WFMessageMultiset(merged); }
      Multisets.ValueMultiset(merged.b);
      Multisets.Apply(fn, multiset(merged.b.Keys));
      {
        reveal_MergeBuckets();
        Multisets.ApplyMonotonic(fn,
                                 multiset(merged.b.Keys),
                                 multiset(left.b.Keys) + (multiset(right.b.Keys) - multiset(left.b.Keys)));
      }
      Multisets.Apply(fn, multiset(left.b.Keys) + (multiset(right.b.Keys) - multiset(left.b.Keys)));
      {
        Multisets.ApplyAdditive(fn, multiset(left.b.Keys), (multiset(right.b.Keys) - multiset(left.b.Keys)));
      }
      Multisets.Apply(fn, multiset(left.b.Keys))
        + Multisets.Apply(fn, (multiset(right.b.Keys) - multiset(left.b.Keys)));
      {
        reveal_MergeBuckets();
        Multisets.ApplyEquivalentFns(fn, Multisets.ValueMultisetFn(left.b), multiset(left.b.Keys));
      }
      Multisets.Apply(Multisets.ValueMultisetFn(left.b), multiset(left.b.Keys))
        + Multisets.Apply(fn, (multiset(right.b.Keys) - multiset(left.b.Keys)));
      {
      }
      Multisets.Apply(Multisets.ValueMultisetFn(left.b), multiset(left.b.Keys))
        + Multisets.Apply(fn, (multiset(right.b.Keys) - multiset(left.b.Keys)));
      Multisets.ValueMultiset(left.b)
        + Multisets.Apply(fn, (multiset(right.b.Keys) - multiset(left.b.Keys)));
      {
        reveal_MergeBuckets();
        Multisets.ApplyEquivalentFns(fn, Multisets.ValueMultisetFn(right.b),
                                     multiset(right.b.Keys) - multiset(left.b.Keys));
      }
      Multisets.ValueMultiset(left.b)
        + Multisets.Apply(Multisets.ValueMultisetFn(right.b), multiset(right.b.Keys) - multiset(left.b.Keys));
      {
        Multisets.ApplyMonotonic(Multisets.ValueMultisetFn(right.b),
                                 multiset(right.b.Keys) - multiset(left.b.Keys),
                                 multiset(right.b.Keys));
      }
      Multisets.ValueMultiset(left.b) + Multisets.ValueMultiset(right.b);
      {
        WFMessageMultiset(left);
        WFMessageMultiset(right);
      }
      multiset(left.msgs) + multiset(right.msgs);
    }
  }    

  // used
  lemma WeightMergeBuckets(left: Bucket, right: Bucket)
    requires PreWFBucket(left)
    requires PreWFBucket(right)
    ensures WeightBucket(MergeBuckets(left, right)) <= WeightBucket(left) + WeightBucket(right)
  {
    var merged := MergeBuckets(left, right);
    MergedKeyMultisets(left, right);
    MergedMessageMultisets(left, right);

    calc <= {
      WeightKeyMultiset(multiset(merged.keys));
      {
        assert multiset(left.keys) + multiset(right.keys) ==
          multiset(merged.keys) + ((multiset(left.keys) + multiset(right.keys)) - multiset(merged.keys));
        WeightKeyMultisetAdditive(multiset(merged.keys),
                                  (multiset(left.keys) + multiset(right.keys)) - multiset(merged.keys));
      }
      WeightKeyMultiset(multiset(left.keys) + multiset(right.keys));
      { WeightKeyMultisetAdditive(multiset(left.keys), multiset(right.keys)); }
      WeightKeyMultiset(multiset(left.keys)) + WeightKeyMultiset(multiset(right.keys));
    }
    
    calc <= {
      WeightMessageMultiset(multiset(merged.msgs));
      {
        assert multiset(left.msgs) + multiset(right.msgs) ==
          multiset(merged.msgs) + ((multiset(left.msgs) + multiset(right.msgs)) - multiset(merged.msgs));
        WeightMessageMultisetAdditive(multiset(merged.msgs),
                                     (multiset(left.msgs) + multiset(right.msgs)) - multiset(merged.msgs));
      }
      WeightMessageMultiset(multiset(left.msgs) + multiset(right.msgs));
      { WeightMessageMultisetAdditive(multiset(left.msgs), multiset(right.msgs)); }
      WeightMessageMultiset(multiset(left.msgs)) + WeightMessageMultiset(multiset(right.msgs));
    }
  }

  // used
  lemma WeightMergeBucketsInListLe(blist: BucketList, i: int, pivots: PivotTable)
  requires 0 <= i < |blist| - 1
  requires PreWFBucket(blist[i])
  requires PreWFBucket(blist[i+1])
  ensures WeightBucketList(MergeBucketsInList(blist, i)) <= WeightBucketList(blist)
  {
    var newblist := MergeBucketsInList(blist, i);
    calc <= {
      WeightBucketList(newblist);
      {
        assert newblist == newblist[..i] + newblist[i..];
        assert newblist[i..] == newblist[i..i+1] + newblist[i+1..];
        WeightBucketListConcat(newblist[..i], newblist[i..]);
        WeightBucketListConcat(newblist[i..i+1], newblist[i+1..]);
      }
      WeightBucketList(newblist[..i]) + WeightBucketList(newblist[i..i+1]) + WeightBucketList(newblist[i+1..]);
      { reveal_WeightBucketList(); }
      WeightBucketList(newblist[..i]) + WeightBucket(newblist[i]) + WeightBucketList(newblist[i+1..]);
      {
        reveal_MergeBucketsInList();
        WeightMergeBuckets(blist[i], blist[i+1]);
      }
      WeightBucketList(newblist[..i]) + WeightBucket(blist[i]) + WeightBucket(blist[i+1]) + WeightBucketList(newblist[i+1..]);
      { reveal_WeightBucketList(); }
      WeightBucketList(newblist[..i]) + WeightBucketList(blist[i..i+2]) + WeightBucketList(newblist[i+1..]);
      {
        reveal_MergeBucketsInList();
        assert blist[..i] == newblist[..i];
        assert blist[i+2..] == newblist[i+1..];
      }
      WeightBucketList(blist[..i]) + WeightBucketList(blist[i..i+2]) + WeightBucketList(blist[i+2..]);
      {
        assert blist == blist[..i] + blist[i..];
        assert blist[i..] == blist[i..i+2] + blist[i+2..];
        WeightBucketListConcat(blist[..i], blist[i..]);
        WeightBucketListConcat(blist[i..i+2], blist[i+2..]);
      }
      WeightBucketList(blist);
    }
  }

  // used internally
  lemma WeightBucketSubset(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires a<=b
    ensures WeightBucket(Image(bucket, a)) <= WeightBucket(Image(bucket, b))
  {
    calc {
      WeightBucket(Image(bucket, a));
        { ImageSubset(bucket, a, b); }
      WeightBucket(Image(Image(bucket, b), a));
      <=
      WeightBucket(Image(Image(bucket, b), a)) + WeightBucket(Image(Image(bucket, b), b-a));
        {
          ImageShape(bucket, b);
          WeightBucketLinearInKeySet(Image(bucket, b), a, b-a);
        }
      WeightBucket(Image(bucket, b));
    }
  }

  // TODO(thance): Why do we have both MergeBuckets and JoinBucketList? The
  // former is nice because it obeys the WFBucketList discipline, and can hence
  // draw tight conclusions (WeightBucketList == WeightBucketList). Can we
  // redefine JoinBucketList in terms of MergBuckets and lose some cruft?
  // used
  lemma WeightJoinBucketList(blist: BucketList)
    requires forall i | 0 <= i < |blist| :: PreWFBucket(blist[i])
    ensures WeightBucket(JoinBucketList(blist)) <= WeightBucketList(blist)
  {
    if |blist| == 0 {
    } else {
      calc <= {
        WeightBucket(JoinBucketList(blist));
        //WeightBucket(B(MapUnion(JoinBucketList(DropLast(blist)).b, Last(blist).b)));
        {
          reveal_MergeBuckets();
          reveal_MapUnion();
          WeightMergeBuckets(JoinBucketList(DropLast(blist)), Last(blist));
        }
        WeightBucket(JoinBucketList(DropLast(blist))) + WeightBucket(Last(blist));
        //WeightBucketList(DropLast(blist)) + WeightBucket(Last(blist));
        { reveal_WeightBucketList(); }
        WeightBucketList(blist);
      }
    }
  }

  // used internaly
  lemma WMWeightSplitBucketOnPivots(bucket: Bucket, pivots: PivotTable)
    requires PreWFBucket(bucket)
    requires BoundedBucket(bucket, pivots)
    requires BucketWellMarshalled(bucket)
    ensures WeightBucketList(SplitBucketOnPivots(bucket, pivots)) == WeightBucket(bucket)
    decreases |pivots|
  {
    if |pivots| == 2 {
      calc {
        WeightBucketList(SplitBucketOnPivots(bucket, pivots));
        WeightBucketList([B(bucket.b)]);
        { reveal_WeightBucketList(); }
        WeightBucket(B(bucket.b));
        { WellMarshalledBucketsEq(B(bucket.b), bucket); }
        WeightBucket(bucket);
      }
    } else {
      var piv := GetKey(pivots, NumBuckets(pivots)-1);
      var pivots' := remove(pivots, NumBuckets(pivots)-1);
      WFPivotsRemoved(pivots, NumBuckets(pivots)-1);

      var l := SplitBucketLeft(bucket, piv);
      var r := SplitBucketRight(bucket, piv);
      reveal_SplitBucketLeft();
      reveal_SplitBucketRight();

      var lKeys := iset k | k in l.b;
      var rKeys := iset k | k in r.b;
      
      calc {
        WeightBucketList(SplitBucketOnPivots(bucket, pivots));  // defn.
        WeightBucketList(SplitBucketOnPivots(l, pivots') + [r]);  // defn.
          { WeightBucketListConcatOne(SplitBucketOnPivots(l, pivots'), r); } // break off tail
        WeightBucketList(SplitBucketOnPivots(l, pivots')) + WeightBucket(r);
          { WMWeightSplitBucketOnPivots(l, pivots'); }
        WeightBucket(l) + WeightBucket(r);
          {
            ImageTrim(bucket, lKeys, l);
            ImageTrim(bucket, rKeys, r);
            WellMarshalledBucketsEq(l, Image(bucket, lKeys));
            WellMarshalledBucketsEq(r, Image(bucket, rKeys));            
          }
        WeightBucket(Image(bucket, lKeys)) + WeightBucket(Image(bucket, rKeys));
          { WeightBucketLinearInKeySetSum(bucket, lKeys, rKeys); }
        WeightBucket(Image(bucket, lKeys + rKeys));
          { ImageIdentity(bucket, lKeys + rKeys); }
        WeightBucket(bucket);
      }
    }
  }

  lemma WeightSplitBucketOnPivots(bucket: Bucket, pivots: PivotTable)
    requires PreWFBucket(bucket)
    requires WFPivots(pivots)
    requires BoundedBucket(bucket, pivots)
    ensures WeightBucketList(SplitBucketOnPivots(bucket, pivots)) <= WeightBucket(bucket)
    decreases |pivots|
  {
    var wmbucket := Image(bucket, AllKeys());
    ImageMapIdentity(bucket, AllKeys());
    WeightWellMarshalledLe(bucket, wmbucket);
    WMWeightSplitBucketOnPivots(wmbucket, pivots);
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
  }
  
  // used (in KVList)
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
  */
  
  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma NumElementsLteWeight(bucket: Bucket)
    requires PreWFBucket(bucket)
    ensures |bucket.keys| <= WeightBucket(bucket)
    decreases bucket.keys
  {
    //KeyMultisetLeWeight(multiset(bucket.keys));
    //SetCardinality(bucket.keys);
    assume false;
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

  /*
  // used internally
  lemma WMWeightBucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message)
    requires WFBucketList(blist, pivots)
    requires BoundedKey(pivots, key)
    requires BucketWellMarshalled(blist[Route(pivots, key)])
    ensures WeightBucketList(BucketListInsert(blist, pivots, key, msg)) <=
    WeightBucketList(blist) + WeightKey(key) + WeightMessage(msg)
  {
    var i := Route(pivots, key);
    var bucket := blist[i];

    var mergedMsg := Merge(msg, BucketGet(bucket, key));
    var mergedWeight := if mergedMsg != IdentityMessage() then WeightKey(key) + WeightMessage(mergedMsg) else 0;

    calc {
      WeightBucket(BucketInsert(bucket, key, msg));
        { KeyContribution(BucketInsert(bucket, key, msg), key); }
      WeightBucket(Image(BucketInsert(bucket, key, msg), ExcludeKey(key))) + WeightOneKey(BucketInsert(bucket, key, msg), key);
        {
          ImageShape(BucketInsert(bucket, key, msg), ExcludeKey(key));
          ImageShape(bucket, ExcludeKey(key));
          WellMarshalledBucketsEq(Image(BucketInsert(bucket, key, msg), ExcludeKey(key)), Image(bucket, ExcludeKey(key)));
        }
      WeightBucket(Image(bucket, ExcludeKey(key))) + WeightOneKey(BucketInsert(bucket, key, msg), key);
      WeightBucket(Image(bucket, ExcludeKey(key))) + mergedWeight;
    }

    calc {
      WeightBucketList(BucketListInsert(blist, pivots, key, msg));
        { WeightBucketListReplace(blist, i, BucketInsert(bucket, key, msg)); }
      WeightBucketList(blist) - WeightBucket(bucket) + WeightBucket(BucketInsert(bucket, key, msg));
        // Calc above
      WeightBucketList(blist) - WeightBucket(bucket) + WeightBucket(Image(bucket, ExcludeKey(key))) + mergedWeight;
        { KeyContribution(bucket, key); }
      WeightBucketList(blist) - (WeightBucket(Image(bucket, ExcludeKey(key))) + WeightOneKey(bucket, key))
        + WeightBucket(Image(bucket, ExcludeKey(key))) + mergedWeight;
      <= // terms cancel; mergedWeight definition
      WeightBucketList(blist) - WeightOneKey(bucket, key) + WeightKey(key) + WeightMessage(mergedMsg);
      <=
        { MergeGainsNoWeight(msg, BucketGet(bucket, key)); }
      WeightBucketList(blist) + WeightKey(key) + WeightMessage(msg);
    }
  }
  */

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
  
  /*
  // used
  lemma WeightBucketIntersect(bucket: Bucket, keys: set<Key>)
    requires PreWFBucket(bucket)
    ensures WeightBucket(BucketIntersect(bucket, keys)) <= WeightBucket(bucket)
  {
    var wmbucket := Image(bucket, AllKeys());
    var ikeys := iset k | k in keys;
    ImageMapIdentity(bucket, AllKeys());
    WeightWellMarshalledLe(bucket, wmbucket);

    reveal_BucketIntersect();
    ImageShape(wmbucket, ikeys);
    WellMarshalledBucketsEq(BucketIntersect(wmbucket, keys), Image(wmbucket, ikeys));
    ImageIdentity(wmbucket, AllKeys());
    WeightBucketSubset(wmbucket, ikeys, AllKeys());
  }

  // used
  lemma WeightBucketComplement(bucket: Bucket, keys: set<Key>)
    requires PreWFBucket(bucket)
    ensures WeightBucket(BucketComplement(bucket, keys)) <= WeightBucket(bucket)
  {
    var wmbucket := Image(bucket, AllKeys());
    var ikeys := iset k | k !in keys;
    ImageMapIdentity(bucket, AllKeys());
    WeightWellMarshalledLe(bucket, wmbucket);

    reveal_BucketComplement();
    ImageShape(wmbucket, ikeys);
    WellMarshalledBucketsEq(BucketComplement(wmbucket, keys), Image(wmbucket, ikeys));
    ImageIdentity(wmbucket, AllKeys());
    WeightBucketSubset(wmbucket, ikeys, AllKeys());
  }
  */

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
    assume false;
  }
}
