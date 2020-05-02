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
  import opened PivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage`Internal
  import ValueType`Internal
  import opened Maps
  import opened Sequences
  import opened BucketsLib
  import opened NativeTypes
  import opened KeyType
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

  lemma MergeGainsNoWeight(parent: Message, child: Message)
  ensures WeightMessage(Merge(parent, child)) <= WeightMessage(parent) + WeightMessage(child)
  {
    //var merged := Merge(parent, child);
    //if (parent.Update? && child.Define?) {
    //}
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

  function {:opaque} ChooseKey(bucket: Bucket) : (key : Key)
  requires |bucket.b| > 0
  ensures key in bucket.b
  {
    var key :| key in bucket.b;
    key
  }

  function {:opaque} Choose<A> (things: multiset<A>) : (result: A)
    requires 0 < |things|
    ensures result in things
  {
    var thing :| thing in things;
    thing
  }
  
  function {:opaque} WeightKeyMultiset(keys: multiset<Key>) : (result: nat)
    ensures |keys| == 0 ==> result == 0
  {
    var weights := MSets.Apply(WeightKey, keys);
    assert |keys| == 0 ==> |weights| == 0;
    MSets.FoldSimple<nat>(0, (x, y) => x + y, weights)
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
    MSets.FoldSimpleAdditive<nat>(0, (x, y) => x + y, weights1, weights2);
    reveal_WeightKeyMultiset();
  }
  
  function {:opaque} WeightMessageMultiset(msgs: multiset<Message>) : (result: nat)
    ensures |msgs| == 0 ==> result == 0
  {
    var weights := MSets.Apply(WeightMessage, msgs);
    assert |msgs| == 0 ==> |weights| == 0;
    MSets.FoldSimple<nat>(0, (x, y) => x + y, weights)
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
    MSets.FoldSimpleAdditive<nat>(0, (x, y) => x + y, weights1, weights2);
    reveal_WeightMessageMultiset();
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

  lemma WeightBucketEmpty()
  ensures WeightBucket(B(map[])) == 0
  {
  }

  lemma WeightKeySingleton(key: Key)
    ensures WeightKeyMultiset(multiset{key}) == WeightKey(key)
  {
    MSets.ApplySingleton(WeightKey, key);
    MSets.FoldSimpleSingleton<nat>(0, (x, y) => x + y, WeightKey(key));
    reveal_WeightKeyMultiset();
  }
  
  lemma WeightMessageSingleton(msg: Message)
    ensures WeightMessageMultiset(multiset{msg}) == WeightMessage(msg)
  {
    MSets.ApplySingleton(WeightMessage, msg);
    MSets.FoldSimpleSingleton<nat>(0, (x, y) => x + y, WeightMessage(msg));
    reveal_WeightMessageMultiset();
  }

  // TODO(robj): wonky interface -- we should just pass key and msg
  lemma WeightBucketSingleton(key:Key, msg: Message)
    ensures WeightBucket(SingletonBucket(key, msg))
    == WeightKey(key) + WeightMessage(msg);
  {
    WeightKeySingleton(key);
    WeightMessageSingleton(msg);
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
  requires WFBucket(bucket)
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

  lemma ImageSingleton(b:Bucket, k:Key)
    requires WFBucket(b)
    requires k in b.b
    ensures Image(b, iset {k}).b.Keys == {k}
    ensures Image(b, iset {k}).b[k] == b.b[k]
    ensures Image(b, iset {k}).keys == [k]
    ensures Image(b, iset {k}).msgs == [ b.b[k] ]
  {
    reveal_Image();
    reveal_IsStrictlySorted();
    var im := Image(b, iset {k});
    if 1 < |im.keys| {
      assert im.keys[0] != im.keys[1];
      assert im.keys[0] in im.b.Keys;
      assert im.keys[1] in im.b.Keys;
      assert false;
    }
    WFWellMarshalledBucketMap(im, k);
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

  lemma ImageSplitsKeys(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires WFBucket(bucket)
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
  
  lemma ImageSplitsMessages(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires WFBucket(bucket)
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
      { WellMarshalledMessageMultiset(bucket); }
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
        WellMarshalledMessageMultiset(abucket);
        WellMarshalledMessageMultiset(bbucket);
      }
      multiset(abucket.msgs) + multiset(bbucket.msgs);
    }
  }
  
  lemma WeightBucketLinearInKeySet(bucket:Bucket, a:iset<Key>, b:iset<Key>)
  requires WFBucket(bucket)
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
      MSets.FoldSimple<nat>(0, (x, y) => x + y, keysweights) + MSets.FoldSimple<nat>(0, (x, y) => x + y, msgsweights);
      {
        ImageSplitsMessages(bucket, a, b);
        //assert multiset(msgs) == multiset(amsgs) + multiset(bmsgs);
        Multisets.ApplyAdditive(WeightMessage, multiset(amsgs), multiset(bmsgs));
        //assert msgsweights == amsgsweights + bmsgsweights;
        Multisets.FoldSimpleAdditive<nat>(0, (x, y) => x + y, amsgsweights, bmsgsweights);
      }
        MSets.FoldSimple<nat>(0, (x, y) => x + y, keysweights)
      + MSets.FoldSimple<nat>(0, (x, y) => x + y, amsgsweights) + MSets.FoldSimple<nat>(0, (x, y) => x + y, bmsgsweights);
      {
        ImageSplitsKeys(bucket, a, b);
        //assert multiset(keys) == multiset(akeys) + multiset(bkeys);
        Multisets.ApplyAdditive(WeightKey, multiset(akeys), multiset(bkeys));
        //assert keysweights == akeysweights + bkeysweights;
        Multisets.FoldSimpleAdditive<nat>(0, (x, y) => x + y, akeysweights, bkeysweights);
      }
        MSets.FoldSimple<nat>(0, (x, y) => x + y, akeysweights) + MSets.FoldSimple<nat>(0, (x, y) => x + y, amsgsweights)
      + MSets.FoldSimple<nat>(0, (x, y) => x + y, bkeysweights) + MSets.FoldSimple<nat>(0, (x, y) => x + y, bmsgsweights);
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
  lemma WeightBucketLinearInKeySetSum(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires WFBucket(bucket)
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
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
  {
    if key in bucket.b
      then WeightKey(key) + WeightMessage(bucket.b[key])
      else 0
  }

  lemma KeyContribution(bucket: Bucket, key: Key)
    requires WFBucket(bucket)
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

  lemma WeightBucketInduct(bucket: Bucket, key: Key, msg: Message)
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    requires key !in bucket.b
    requires msg != IdentityMessage()
    ensures WeightBucket(B(bucket.b[key := msg])) == WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)
  {
    var newbucket := B(bucket.b[key := msg]);
    calc {
      WeightBucket(newbucket);
      { KeyContribution(newbucket, key); }
      WeightBucket(Image(newbucket, ExcludeKey(key))) + WeightOneKey(newbucket, key);
      WeightBucket(Image(newbucket, ExcludeKey(key))) + WeightKey(key) + WeightMessage(msg);
      {
        ImageIdentity(bucket, ExcludeKey(key));
        ImageEquiv(bucket, newbucket, ExcludeKey(key));
      }
      WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg);
    }
  }

  function ILeftKeys(pivot: Key) : iset<Key> { iset k | Keyspace.lt(k, pivot) }
  function IRightKeys(pivot: Key) : iset<Key> { iset k | Keyspace.lte(pivot, k) }

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

  lemma WeightSplitBucketLeft(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    ensures WeightBucket(SplitBucketLeft(bucket, pivot)) <= WeightBucket(bucket)
  {
    SplitBucketImage(bucket, pivot);
    WeightBucketLinearInKeySet(bucket, ILeftKeys(pivot), AllKeys() - ILeftKeys(pivot));
  }

  lemma WeightSplitBucketRight(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    ensures WeightBucket(SplitBucketRight(bucket, pivot)) <= WeightBucket(bucket)
  {
    SplitBucketImage(bucket, pivot);
    WeightBucketLinearInKeySet(bucket, AllKeys() - IRightKeys(pivot), IRightKeys(pivot));
  }

  lemma WeightSplitBucketAdditive(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    ensures WeightBucket(SplitBucketLeft(bucket, pivot)) +
            WeightBucket(SplitBucketRight(bucket, pivot)) == WeightBucket(bucket)
  {
    SplitBucketImage(bucket, pivot);
    WeightBucketLinearInKeySet(bucket, ILeftKeys(pivot), IRightKeys(pivot));
  }

  lemma WeightSplitBucketAdditiveLe(bucket: Bucket, pivot: Key)
    requires WFBucket(bucket)
    requires BucketWellMarshalled(bucket)
    ensures WeightBucket(SplitBucketLeft(bucket, pivot)) +
            WeightBucket(SplitBucketRight(bucket, pivot)) <= WeightBucket(bucket)
  {
    WeightSplitBucketAdditive(bucket, pivot);
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

  lemma WeightBucketListConcatOne(left: BucketList, extra: Bucket)
    ensures WeightBucketList(left + [extra]) == WeightBucketList(left) + WeightBucket(extra)
  {
    WeightBucketListConcat(left, [extra]);
    reveal_WeightBucketList();
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

  lemma WeightSplitBucketListLeft(blist: BucketList, pivots: seq<Key>, cLeft: int, key: Key)
    requires SplitBucketListLeft.requires(blist, pivots, cLeft, key)
    requires BucketWellMarshalled(blist[cLeft])
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

  lemma WeightSplitBucketListRight(blist: BucketList, pivots: seq<Key>, cRight: int, key: Key)
    requires SplitBucketListRight.requires(blist, pivots, cRight, key)
    requires BucketWellMarshalled(blist[cRight])
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

  function RouteRange(pivots: PivotTable, i: int) : iset<Key>
    requires WFPivots(pivots)
  {
    iset k | Route(pivots, k) == i
  }

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
    iset k | Route(pivots, k) < i
  }

  // The sequence axioms were responsible for creating a timeout in the rich
  // context where this was used; hence this ugly workaround.
  lemma SequenceSingleton<T>(s:seq<T>, i:int)
  requires 0 <= i < |s|
  ensures s[i..i+1] == [s[i]];
  {
  }

  lemma WeightBucketListFlushPartial(parent: Bucket, children: BucketList, pivots: PivotTable, items: int)
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
          { WeightBucketListFlushPartial(parent, children, pivots, items - 1); }  // Recurse on prefix
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

  lemma WeightBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable)
  requires WFBucketListProper(children, pivots)
  requires |children| == NumBuckets(pivots)
  requires WFBucket(parent)
  requires BucketWellMarshalled(parent)
  //requires forall i | 0 <= i < |children| :: WFBucket(children[i])
  requires BucketListWellMarshalled(children)
  ensures WeightBucketList(BucketListFlush(parent, children, pivots))
      <= WeightBucket(parent) + WeightBucketList(children)
  {
    WeightBucketListFlushPartial(parent, children, pivots, |children|);
    forall ensures Image(parent, RouteRanges(pivots, |children|)) == parent
    {
      reveal_Image();
      WellMarshalledBucketsEq(Image(parent, RouteRanges(pivots, |children|)), parent);
    }
    assert children[..|children|] == children;  // trigger
  }

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

  lemma WeightBucketListShrinkEntry(blist: BucketList, i: int, bucket: Bucket)
  requires 0 <= i < |blist|
  requires WeightBucket(bucket) <= WeightBucket(blist[i])
  ensures WeightBucketList(blist[i := bucket]) <= WeightBucketList(blist)
  {
    WeightBucketListReplace(blist, i, bucket);
  }

  lemma WeightBucketListClearEntry(blist: BucketList, i: int)
  requires 0 <= i < |blist|
  ensures WeightBucketList(blist[i := B(map[])]) <= WeightBucketList(blist)
  {
    WeightBucketListReplace(blist, i, B(map[]));
  }

  // Analogous to WeightBucketListReplace, except we're changing the size of the subsequence in the middle.
  lemma WeightSplitBucketInList(blist: BucketList, i: int, pivot: Key)
    requires 0 <= i < |blist|
    requires WFBucket(blist[i])
    requires BucketWellMarshalled(blist[i])
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

  lemma WeightSplitBucketInListLe(blist: BucketList, i: int, pivot: Key)
  requires 0 <= i < |blist|
  ensures WeightBucketList(SplitBucketInList(blist, i, pivot))
      <= WeightBucketList(blist)
  {
    assume false;
  }

  lemma WeightBucketListSuffix(blist: BucketList, a: int)
  requires 0 <= a <= |blist|
  ensures WeightBucketList(blist[a..]) <= WeightBucketList(blist)
  {
    WeightBucketListConcat(blist[..a], blist[a..]);
    assert blist == blist[..a] + blist[a..];
  }

  // TODO move this to BucketsLib?
  lemma MergeUndoesSplit(blist:BucketList, pivots:PivotTable, i:int)
  requires 0 <= i < |blist| - 1
  requires WFBucketListProper(blist, pivots)
  requires BucketWellMarshalled(blist[i])
  requires BucketWellMarshalled(blist[i+1])
  ensures SplitBucketInList(MergeBucketsInList(blist, i), i, pivots[i]) == blist;
  {
    var merged := MergeBucketsInList(blist, i);
    var mbucket := MergeBuckets(blist[i], blist[i+1]);

    calc {
      SplitBucketInList(merged, i, pivots[i]);
        { reveal_SplitBucketInList(); }
      replace1with2(merged, SplitBucketLeft(merged[i], pivots[i]), SplitBucketRight(merged[i], pivots[i]), i);
        { reveal_replace1with2(); }
      merged[..i] + [SplitBucketLeft(merged[i], pivots[i]), SplitBucketRight(merged[i], pivots[i])] + merged[i+1..];
        { reveal_replace2with1(); }
        { reveal_MergeBucketsInList(); }
      blist[..i] + [SplitBucketLeft(mbucket, pivots[i]), SplitBucketRight(mbucket, pivots[i])] + blist[i+2..];
        {
          reveal_MergeBuckets();
          reveal_Image();
          SplitBucketImage(mbucket, pivots[i]);
          WellMarshalledBucketsEq(SplitBucketLeft(mbucket, pivots[i]), blist[i]);
          WellMarshalledBucketsEq(SplitBucketRight(mbucket, pivots[i]), blist[i+1]);
        }
      blist[..i] + [blist[i], blist[i+1]] + blist[i+2..];
      blist;
    }
  }

  // Undoes WeightSplitBucketInList
  lemma WeightMergeBucketsInList(blist: BucketList, i: int, pivots: PivotTable)
    requires 0 <= i < |blist| - 1
    requires WFBucketListProper(blist, pivots)
    requires BucketWellMarshalled(blist[i])
    requires BucketWellMarshalled(blist[i+1])
    ensures WeightBucketList(MergeBucketsInList(blist, i)) == WeightBucketList(blist)
  {
    MergeUndoesSplit(blist, pivots, i);
    reveal_MergeBucketsInList();
    WeightSplitBucketInList(MergeBucketsInList(blist, i), i, pivots[i]);
  }

  lemma WeightMergeBucketsInListLe(blist: BucketList, i: int, pivots: PivotTable)
  requires 0 <= i < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures WeightBucketList(MergeBucketsInList(blist, i)) <= WeightBucketList(blist)
  {
    assume false;
  }

  lemma WeightBucketSubset(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires WFBucketMap(bucket.b)
    requires BucketWellMarshalled(bucket)
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

  lemma WeightBucketMapUnion(x:Bucket, xKeys:iset<Key>, y:Bucket, yKeys:iset<Key>)
    requires WFBucketMap(x.b)
    requires WFBucketMap(y.b)
    requires BucketWellMarshalled(x)
    requires BucketWellMarshalled(y)
    requires xKeys == iset k | k in x.b.Keys;
    requires yKeys == iset k | k !in x.b.Keys;
    ensures WeightBucket(B(MapUnion(x.b, y.b))) == WeightBucket(Image(x, xKeys)) + WeightBucket(Image(y, yKeys))
  {
    calc {
      WeightBucket(B(MapUnion(x.b, y.b)));
        { reveal_MapUnion(); }
      WeightBucket(B(MapUnionPreferA(x.b, y.b)));
        {
          ImageIdentity(B(MapUnionPreferA(x.b, y.b)), xKeys + yKeys);
        }
      WeightBucket(Image(B(MapUnionPreferA(x.b, y.b)), xKeys + yKeys));
        { WeightBucketLinearInKeySetSum(B(MapUnionPreferA(x.b, y.b)), xKeys, yKeys); }
      WeightBucket(Image(B(MapUnionPreferA(x.b, y.b)), xKeys)) + WeightBucket(Image(B(MapUnionPreferA(x.b, y.b)), yKeys));
      {
        ImageEquiv(x, B(MapUnionPreferA(x.b, y.b)), xKeys);
        ImageEquiv(y, B(MapUnionPreferA(x.b, y.b)), yKeys);
      }
      WeightBucket(Image(x, xKeys)) + WeightBucket(Image(y, yKeys));
    }
  }

  // TODO(thance): Why do we have both MergeBuckets and JoinBucketList? The
  // former is nice because it obeys the WFBucketList discipline, and can hence
  // draw tight conclusions (WeightBucketList == WeightBucketList). Can we
  // redefine JoinBucketList in terms of MergBuckets and lose some cruft?
  lemma WeightJoinBucketList(blist: BucketList)
  ensures WeightBucket(JoinBucketList(blist)) <= WeightBucketList(blist)
  {
    assume false;
    if |blist| == 0 {
      assert WeightBucket(JoinBucketList(blist)) == 0;  // delete
      // assert JoinBucketList(blist) == map[];
      reveal_WeightBucketList();
      assert WeightBucketList(blist) == 0;  // delete
    } else {
      var subKeys := iset k | k in JoinBucketList(DropLast(blist)).b.Keys;
      var lastKeys := AllKeys() - subKeys;
      calc {
        WeightBucket(JoinBucketList(blist));
        WeightBucket(B(MapUnion(JoinBucketList(DropLast(blist)).b, Last(blist).b)));
          { WeightBucketMapUnion(JoinBucketList(DropLast(blist)), subKeys, Last(blist), lastKeys); }
        WeightBucket(Image(JoinBucketList(DropLast(blist)), subKeys))
          + WeightBucket(Image(Last(blist), lastKeys));
        <=
          { WeightBucketSubset(Last(blist), lastKeys, AllKeys()); }
        WeightBucket(Image(JoinBucketList(DropLast(blist)), subKeys)) + WeightBucket(Image(Last(blist), AllKeys()));
          { // subKeys doesn't reduce the subList, and AllKeys() doesn't reduce Last(blist)
            ImageIdentity(Last(blist), AllKeys());
            ImageIdentity(JoinBucketList(DropLast(blist)), subKeys);
          }
        WeightBucket(JoinBucketList(DropLast(blist))) + WeightBucket(Last(blist));
        <=
          { WeightJoinBucketList(DropLast(blist)); }  // recurse
        WeightBucketList(DropLast(blist)) + WeightBucket(Last(blist));
          { // Stitch blist back together.
            WeightBucketListConcatOne(DropLast(blist), Last(blist));
            assert DropLast(blist) + [Last(blist)] == blist; // trigger
          }
        WeightBucketList(blist);
      }
    }
  }

  lemma WeightSplitBucketOnPivots(bucket: Bucket, pivots: seq<Key>)
  requires BucketWellMarshalled(bucket)
  ensures WeightBucketList(SplitBucketOnPivots(bucket, pivots)) == WeightBucket(bucket)
  decreases |pivots|
  {
    assume false;
    if |pivots| == 0 {
      reveal_WeightBucketList();
      calc {
        WeightBucketList(SplitBucketOnPivots(bucket, pivots));
        WeightBucket(bucket);
      }
    } else {
      var l := map key | key in bucket.b && Keyspace.lt(key, Last(pivots)) :: bucket.b[key];
      var r := map key | key in bucket.b && Keyspace.lte(Last(pivots), key) :: bucket.b[key];
      var lKeys := iset k | k in l;
      var rKeys := iset k | k in r;

      calc {
        WeightBucketList(SplitBucketOnPivots(bucket, pivots));  // defn.
        WeightBucketList(SplitBucketOnPivots(B(l), DropLast(pivots)) + [B(r)]);
          { WeightBucketListConcatOne(SplitBucketOnPivots(B(l), DropLast(pivots)), B(r)); } // break off tail
        WeightBucketList(SplitBucketOnPivots(B(l), DropLast(pivots))) + WeightBucket(B(r));
          { WeightSplitBucketOnPivots(B(l), DropLast(pivots)); }
        WeightBucket(B(l)) + WeightBucket(B(r));
          {
            ImageTrim(bucket, lKeys, B(l));
            ImageTrim(bucket, rKeys, B(r));
          }
        WeightBucket(Image(bucket, lKeys)) + WeightBucket(Image(bucket, rKeys));
          { WeightBucketLinearInKeySetSum(bucket, lKeys, rKeys); }
        WeightBucket(Image(bucket, lKeys + rKeys));
          { ImageIdentity(bucket, lKeys + rKeys); }
        WeightBucket(bucket);
      }
    }
  }

  lemma LenLeWeightInner(bucket: Bucket, filter:iset<Key>)
  requires BucketWellMarshalled(bucket)
  ensures |Image(bucket, filter).b| <= WeightBucket(Image(bucket, filter))
  decreases |Image(bucket, filter).b|
  {
    if |Image(bucket, filter).b| == 0 {
    } else {
      var key :| key in Image(bucket, filter).b;
      var others := filter - IncludeKey(key);

      ImageShape(bucket, IncludeKey(key));
      ImageShape(bucket, filter);
      assert |Image(bucket, filter).b| == |Image(bucket, filter).b.Keys|;
      assert |Image(bucket, IncludeKey(key)).b| == |Image(bucket, IncludeKey(key)).b.Keys|;
      assert |Image(bucket, others).b| == |Image(bucket, others).b.Keys|;

      calc {
        |Image(bucket, filter).b|;
          {
            reveal_Image();
            assert Image(bucket, filter).b.Keys == Image(bucket, IncludeKey(key)).b.Keys + Image(bucket, others).b.Keys;  // trigger
          }
        |Image(bucket, IncludeKey(key)).b| + |Image(bucket, others).b|;
        <=
          { assert Image(bucket, IncludeKey(key)).b.Keys == {key}; }
        WeightKey(key) + WeightMessage(bucket.b[key]) + |Image(bucket, others).b|;
          { WeightBucketSingleton(key, bucket.b[key]); } // break key out of bucket
        WeightBucket(Image(bucket, IncludeKey(key))) + |Image(bucket, others).b|;
        <=
          { // recurse
            reveal_Image();
            assert Image(bucket, others).b.Keys == Image(bucket, filter).b.Keys - {key};
            LenLeWeightInner(bucket, others);
          }
        WeightBucket(Image(bucket, IncludeKey(key))) + WeightBucket(Image(bucket, others));
          { // reassemble
            WeightBucketLinearInKeySet(Image(bucket, filter), IncludeKey(key), others);
            ImageSubset(bucket, IncludeKey(key), filter);
            ImageSubset(bucket, others, filter);
          }
        WeightBucket(Image(bucket, filter));
      }
    }
  }

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma LenLeWeight(bucket: Bucket)
  requires BucketWellMarshalled(bucket)
  ensures |bucket.b| <= WeightBucket(bucket)
  {
    LenLeWeightInner(bucket, AllKeys());
    ImageIdentity(bucket, AllKeys());
  }

  lemma WeightBucketListOneEmpty()
  ensures WeightBucketList([B(map[])]) == 0
  {
    reveal_WeightBucketList();
    WeightBucketEmpty();
  }

  lemma WeightBucketPut(bucket: Bucket, key: Key, msg: Message)
  requires BucketWellMarshalled(bucket)
  ensures WeightBucket(B(bucket.b[key := msg])) <=
      WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)
  {
    calc {
      WeightBucket(B(bucket.b[key := msg]));
        { KeyContribution(B(bucket.b[key := msg]), key); }
      WeightBucket(Image(B(bucket.b[key := msg]), ExcludeKey(key))) + WeightKey(key) + WeightMessage(msg);
        { ImageShape(B(bucket.b[key := msg]), ExcludeKey(key));
          ImageShape(bucket, ExcludeKey(key));
          assert Image(B(bucket.b[key := msg]), ExcludeKey(key)) == Image(bucket, ExcludeKey(key));
        }
      WeightBucket(Image(bucket, ExcludeKey(key))) + WeightKey(key) + WeightMessage(msg);
      <=
      WeightBucket(Image(bucket, ExcludeKey(key))) + (if key in bucket.b then WeightKey(key) + WeightMessage(bucket.b[key]) else 0)
        + WeightKey(key) + WeightMessage(msg);
        { KeyContribution(bucket, key); }
      WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg);
    }
  }

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

  lemma WeightBucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message)
  requires WFBucketList(blist, pivots)
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
          assert Image(BucketInsert(bucket, key, msg), ExcludeKey(key)) == Image(bucket, ExcludeKey(key)); // trigger
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

  lemma WeightBucketIntersect(bucket: Bucket, keys: set<Key>)
  requires BucketWellMarshalled(bucket)
  ensures WeightBucket(BucketIntersect(bucket, keys)) <= WeightBucket(bucket)
  {
    var ikeys := iset k | k in keys;
    reveal_BucketIntersect();
    ImageShape(bucket, ikeys);
    assert BucketIntersect(bucket, keys) == Image(bucket, ikeys);
    ImageIdentity(bucket, AllKeys());
    WeightBucketSubset(bucket, ikeys, AllKeys());
  }

  lemma WeightBucketComplement(bucket: Bucket, keys: set<Key>)
  requires BucketWellMarshalled(bucket)
  ensures WeightBucket(BucketComplement(bucket, keys)) <= WeightBucket(bucket)
  {
    var ikeys := iset k | k !in keys;
    reveal_BucketComplement();
    ImageShape(bucket, ikeys);
    assert BucketComplement(bucket, keys) == Image(bucket, ikeys);
    ImageIdentity(bucket, AllKeys());
    WeightBucketSubset(bucket, ikeys, AllKeys());
  }

  lemma WeightMessageBound(msg: Message)
  ensures WeightMessage(msg) <= 4 + 1024
  { }
}
