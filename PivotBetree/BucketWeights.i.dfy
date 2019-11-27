include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/BucketsLib.i.dfy"
//
// Assigning weights to buckets guides the flushing algorithm to decide
// which child to push messages towards. TODO(thance): help!
//

module BucketWeights {
  import Sets
  import opened PivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import ValueWithDefault`Internal
  import opened Maps
  import opened Sequences
  import opened BucketsLib
  import opened NativeTypes

  function WeightKey(key: Key) : (w:int)
  ensures w >= 0
  {
    8 + |key|
  }
 
  function WeightKeySeq(keys: seq<Key>) : (w:int)
  ensures w >= 0
  {
    if |keys| == 0 then 0 else WeightKeySeq(DropLast(keys)) + WeightKey(Last(keys))
  }

  function WeightMessage(msg: Message) : (w:int)
  ensures w >= 0
  {
    match msg {
      case Define(value) => 8 + ValueWithDefault.Len(value)
      case Update(delta) => 0
    }
  }

  lemma MergeGainsNoWeight(parent: Message, child: Message)
  ensures WeightMessage(Merge(parent, child)) <= WeightMessage(parent) + WeightMessage(child)
  {
    var merged := Merge(parent, child);
    if (parent.Update? && child.Define?) {
      assume ValueWithDefault.Len(ApplyDelta(parent.delta, child.value))
        <= WeightMessage(parent) + ValueWithDefault.Len(child.value);
    }
  }

  function method WeightKeyUint64(key: Key) : (w:uint64)
  ensures w as int == WeightKey(key)
  {
    8 + |key| as uint64
  }

  function method WeightMessageUint64(msg: Message) : (w:uint64)
  ensures w as int == WeightMessage(msg)
  {
    match msg {
      case Define(value) => 8 + |value| as uint64
      case Update(delta) => 0
    }
  }

  function WeightMessageSeq(msgs: seq<Message>) : (w:int)
  ensures w >= 0
  {
    if |msgs| == 0 then 0 else WeightMessageSeq(DropLast(msgs)) + WeightMessage(Last(msgs))
  }

  function {:opaque} ChooseKey(bucket: Bucket) : (key : Key)
  requires |bucket| > 0
  ensures key in bucket
  {
    var key :| key in bucket;
    key
  }

  function {:opaque} WeightBucket(bucket: Bucket) : (w:int)
  ensures w >= 0
  ensures |bucket|==0 ==> WeightBucket(bucket) == 0
  {
    if |bucket| == 0 then 0 else (
      var key := ChooseKey(bucket);
      var msg := bucket[key];
      WeightBucket(MapRemove1(bucket, key)) + WeightKey(key) + WeightMessage(msg)
    )
  }

  function {:opaque} WeightBucketList(buckets: BucketList) : (w:int)
  ensures w >= 0
  {
    if |buckets| == 0 then 0 else (
      WeightBucketList(DropLast(buckets)) + WeightBucket(Last(buckets))
    )
  }

  function {:opaque} Image(b:Bucket, s:set<Key>) : (image:Bucket)
  requires s <= b.Keys
  ensures |Image(b, s)| == |s|
  // ensures forall k :: k in image ==> k in s
  // The ensures above isn't implicated in profiling, but seems to overtrigger
  // MapType0Select somewhere else, quite badly.
  {
    var m := map k | k in s :: b[k];
    assert m.Keys == s;
    m
  }

  function {:opaque} IImage(b:Bucket, s:iset<Key>) : (image:Bucket)
//    ensures image.Keys <= b.Keys
// Even this subset relation is a timeout source. (This must be the cause of
// timeout on branch hard-to-trace-map-timeout)
  {
    map k | k in b && k in s :: b[k]
  }

  lemma IImageShape(b:Bucket, s:iset<Key>)
    ensures forall k :: k in b && k in s <==> k in IImage(b, s).Keys
    ensures forall k :: k in IImage(b,s) ==> IImage(b,s)[k] == b[k];
  {
    reveal_IImage();
  }

  lemma IImageSingleton(b:Bucket, k:Key)
    requires k in b;
    ensures IImage(b, iset {k}).Keys == {k};
    ensures IImage(b, iset {k})[k] == b[k];
  {
    reveal_IImage();
  }

  // TODO reorder s <= t
  lemma IImageSubset(b:Bucket, s:iset<Key>, t:iset<Key>)
    requires s <= t;
    ensures IImage(IImage(b, t), s) == IImage(b, s)
    ensures IImage(b, s).Keys <= IImage(b, t).Keys
  {
    reveal_IImage();
  }

  lemma IImageIntersect(b:Bucket, s:iset<Key>, t:iset<Key>)
    ensures IImage(IImage(b, s), t) == IImage(b, s * t)
  {
    reveal_IImage();
  }

  lemma MapRemoveVsIImage(bucket:Bucket, ibk:iset<Key>, key:Key)
  requires forall k :: k in bucket.Keys ==> k in ibk
  ensures MapRemove1(bucket, key) == IImage(bucket, ibk - iset{key})
  {
    reveal_MapRemove1();
    reveal_IImage();
  }

  lemma WeightBucketSingleton(bucket:Bucket, key:Key)
  requires bucket.Keys == {key};
  ensures WeightBucket(bucket) == WeightKey(key) + WeightMessage(bucket[key]);
  {
    reveal_WeightBucket();
  }

  lemma WeightBucketLinearInKeySetInner(bucket:Bucket, a:iset<Key>, b:iset<Key>)
  requires a !! b
  requires forall k:Key :: k in bucket ==> k in a + b // a,b partition bucket
  requires IImage(bucket, a).Keys != {} // So we can decrease
  requires IImage(bucket, b).Keys != {} // So we can decrease
  requires |bucket| > 0 // So we can ChooseKey
  requires ChooseKey(bucket) in a
  ensures WeightBucket(bucket) == WeightBucket(IImage(bucket, a)) + WeightBucket(IImage(bucket, b))
  decreases |IImage(bucket, a).Keys| + |IImage(bucket, b).Keys|, 0
  {
    var key := ChooseKey(bucket);
    var msg := bucket[key];
    var residual := WeightKey(key) + WeightMessage(msg);

    calc {
      WeightBucket(IImage(bucket, a));
        {
          var A := IImage(bucket, a);
          var B := IImage(A, a-iset{key});
          IImageSubset(bucket, a-iset{key}, a);
          IImageShape(bucket, a-iset{key});
          IImageShape(bucket, a);
          Sets.ProperSubsetImpliesSmallerCardinality(B.Keys, A.Keys);

          IImageShape(A, iset{key});
          Sets.SetInclusionImpliesSmallerCardinality(IImage(A, iset{key}).Keys, {key});
          IImageShape(bucket, b);
          var kb :| kb in IImage(bucket, b).Keys;
          Sets.SetInclusionImpliesSmallerCardinality({kb}, IImage(bucket, b).Keys);

          IWeightBucketLinearInKeySet(A, a-iset{key}, iset{key});
        }
      WeightBucket(IImage(IImage(bucket, a), a-iset{key})) + WeightBucket(IImage(IImage(bucket, a), iset{key}));
        {
          IImageSubset(bucket, a-iset{key}, a);
          IImageSubset(bucket, iset{key}, a);
        }
      WeightBucket(IImage(bucket, a-iset{key})) + WeightBucket(IImage(bucket, iset{key}));
        {
          IImageSingleton(bucket, key);
          WeightBucketSingleton(IImage(bucket, iset{key}), key);
          assert IImage(bucket, iset{key})[key] == bucket[key];
          assert WeightBucket(IImage(bucket, iset{key})) == WeightKey(key) + WeightMessage(bucket[key]);
        }
      WeightBucket(IImage(bucket, a-iset{key})) + residual;
    }
    calc {
      WeightBucket(bucket);
        { reveal_WeightBucket(); }
      WeightBucket(MapRemove1(bucket, key)) + residual;
        { MapRemoveVsIImage(bucket, a+b, key); }
      WeightBucket(IImage(bucket, (a+b)-iset{key}) )+ residual;
        { assert a+b-iset{key} == (a-iset{key})+b; }  // OSBERVE trigger
      WeightBucket(IImage(bucket, (a-iset{key})+b)) + residual;
        {
          var A := IImage(bucket, (a-iset{key})+b);
          var B := IImage(A, a-iset{key});
          IImageSubset(bucket, a-iset{key}, (a-iset{key})+b);
          IImageShape(bucket, a-iset{key});
          IImageShape(bucket, a);
          Sets.ProperSubsetImpliesSmallerCardinality(B.Keys, IImage(bucket, a).Keys);

          IImageSubset(bucket, b, (a-iset{key})+b);
          Sets.SetInclusionImpliesSmallerCardinality(
            IImage(IImage(bucket, (a-iset{key})+b), b).Keys, IImage(bucket, b).Keys);

          IImageShape(bucket, (a-iset{key})+b); // propagate partition precondition
          IWeightBucketLinearInKeySet(IImage(bucket, (a-iset{key})+b), a-iset{key}, b);
        }
      WeightBucket(IImage(IImage(bucket, (a-iset{key})+b), a-iset{key})) + WeightBucket(IImage(IImage(bucket, (a-iset{key})+b), b)) + residual;
        { 
          IImageSubset(bucket, a-iset{key}, (a-iset{key})+b);
          IImageSubset(bucket, b, (a-iset{key})+b);
        }
      WeightBucket(IImage(bucket, a-iset{key})) + WeightBucket(IImage(bucket, b)) + residual;
        // upper calc
      WeightBucket(IImage(bucket, a)) + WeightBucket(IImage(bucket, b));
    }
  }

  lemma IWeightBucketLinearInKeySet(bucket:Bucket, a:iset<Key>, b:iset<Key>)
  requires a !! b
  requires forall k:Key :: k in bucket ==> k in a + b
  ensures WeightBucket(bucket) == WeightBucket(IImage(bucket, a)) + WeightBucket(IImage(bucket, b))
  decreases |IImage(bucket, a).Keys| + |IImage(bucket, b).Keys|, 1
  {
    IImageShape(bucket, a);
    IImageShape(bucket, b);
    WeightBucketEmpty();
    if |bucket| == 0 {
    } else if IImage(bucket, a).Keys=={} {
      assert bucket == IImage(bucket, b);  // trigger
    } else if IImage(bucket, b).Keys=={} {
      assert bucket == IImage(bucket, a);  // trigger
    } else {
      if ChooseKey(bucket) in a {
        WeightBucketLinearInKeySetInner(bucket, a, b);
      } else {
        WeightBucketLinearInKeySetInner(bucket, b, a);
      }
    }
  }

  // A variant that's handy for peeling off extra IImage wrappers.
  lemma WeightBucketLinearVariant(bucket:Bucket, a:iset<Key>, b:iset<Key>)
    requires a!!b
    ensures WeightBucket(IImage(bucket, a + b)) == WeightBucket(IImage(bucket, a)) + WeightBucket(IImage(bucket, b));
  {
    var c := a + b;
    calc {
      WeightBucket(IImage(bucket, a))
        + WeightBucket(IImage(bucket, b));
        { IImageSubset(bucket, b, c); }
      WeightBucket(IImage(bucket, a))
        + WeightBucket(IImage(IImage(bucket, c), b));
        { IImageSubset(bucket, a, c); }
      WeightBucket(IImage(IImage(bucket, c), a))
        + WeightBucket(IImage(IImage(bucket, c), b));
      {
        IImageShape(bucket, c);
        IWeightBucketLinearInKeySet(IImage(bucket, c), a, b);
      }
      WeightBucket(IImage(bucket, c));
    }
  }

  lemma ImageVsIImage(bucket:Bucket, a:set<Key>)
    requires a <= bucket.Keys
    ensures Image(bucket, a) == IImage(bucket, iset k | k in a)
  {
    reveal_Image();
    reveal_IImage();
  }

  // The raw WeightBucket definition is really difficult to work with. This
  // lemma is a much nicer foundation to work with.
  lemma WeightBucketLinearInKeySet(bucket:Bucket, a:set<Key>, b:set<Key>)
  requires a !! b
  requires a + b == bucket.Keys
  ensures WeightBucket(bucket) == WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b))
  decreases |bucket|, 1
  {
    IWeightBucketLinearInKeySet(bucket, iset k | k in a, iset k | k in b);
    ImageVsIImage(bucket, a);
    ImageVsIImage(bucket, b);
  }

  lemma WeightBucketInduct(bucket: Bucket, key: Key, msg: Message)
  requires key !in bucket
  ensures WeightBucket(bucket[key := msg]) == WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)
  {
    var update := map [ key := msg ];
    var rest := bucket.Keys - {key};

    reveal_Image();
    WeightBucketLinearInKeySet(bucket[key := msg], {key}, rest);
    assert Image(bucket[key := msg], {key}) == update;  // trigger
    assert Image(bucket[key := msg], rest) == bucket; // trigger
    WeightBucketSingleton(Image(update, {key}), key);
  }

  lemma SplitBucketLeftImage(bucket: Bucket, pivot: Key, leftKeys:set<Key>)
  requires leftKeys == set k | k in bucket && Keyspace.lt(k, pivot)
  ensures SplitBucketLeft(bucket, pivot) == Image(bucket, leftKeys)
  {
    reveal_Image();
    reveal_SplitBucketLeft();
  }

  lemma SplitBucketRightImage(bucket: Bucket, pivot: Key, rightKeys:set<Key>)
  requires rightKeys == set k | k in bucket && Keyspace.lte(pivot, k)
  ensures SplitBucketRight(bucket, pivot) == Image(bucket, rightKeys)
  {
    reveal_Image();
    reveal_SplitBucketRight();
  }

  lemma WeightSplitBucketLeft(bucket: Bucket, pivot: Key)
  ensures WeightBucket(SplitBucketLeft(bucket, pivot)) <= WeightBucket(bucket)
  {
    var leftKeys := set k | k in bucket && Keyspace.lt(k, pivot);
    var rightKeys := bucket.Keys - leftKeys;
    reveal_SplitBucketLeft();
    reveal_Image();
    assert SplitBucketLeft(bucket, pivot) == Image(bucket, leftKeys); // trigger.
    WeightBucketLinearInKeySet(bucket, leftKeys, rightKeys);
  }

  lemma WeightSplitBucketRight(bucket: Bucket, pivot: Key)
  ensures WeightBucket(SplitBucketRight(bucket, pivot)) <= WeightBucket(bucket)
  {
    var rightKeys := set k | k in bucket && Keyspace.lte(pivot, k);
    var leftKeys := bucket.Keys - rightKeys;
    SplitBucketRightImage(bucket, pivot, rightKeys);
    WeightBucketLinearInKeySet(bucket, leftKeys, rightKeys);
  }

  lemma WeightSplitBucketAdditive(bucket: Bucket, pivot: Key)
  ensures WeightBucket(SplitBucketLeft(bucket, pivot)) +
          WeightBucket(SplitBucketRight(bucket, pivot)) == WeightBucket(bucket)
  {
    var leftKeys := set k | k in bucket && Keyspace.lt(k, pivot);
    forall ensures SplitBucketLeft(bucket, pivot) == Image(bucket, leftKeys)
    {
      reveal_Image();
      reveal_SplitBucketLeft();
    }

    var rightKeys := set k | k in bucket && Keyspace.lte(pivot, k);
    SplitBucketRightImage(bucket, pivot, rightKeys);
    assert SplitBucketRight(bucket, pivot) == Image(bucket, rightKeys); // trigger.

    var notLeftKeys := bucket.Keys - leftKeys;
    assert notLeftKeys == rightKeys;

    WeightBucketLinearInKeySet(bucket, leftKeys, rightKeys);
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

  lemma FreakinSetExtensionality<T>(a:set<T>, b:set<T>)
    requires forall e :: e in a ==> e in b;
    requires forall e :: e in b ==> e in a;
    ensures a == b;
  {
  }

  lemma WeightBucketFilterPartitions(bucket:Bucket, filter:iset<Key>, a:iset<Key>, b:iset<Key>)
    requires a !! b
    requires filter * a + filter * b == filter;
    ensures WeightBucket(IImage(bucket, filter)) ==
      WeightBucket(IImage(bucket, filter * a)) + WeightBucket(IImage(bucket, filter * b));
  {
    calc {
      WeightBucket(IImage(bucket, filter));
        {
          IImageShape(bucket, filter);
          IWeightBucketLinearInKeySet(IImage(bucket, filter), a, b);
        }
      WeightBucket(IImage(IImage(bucket, filter), a)) + WeightBucket(IImage(IImage(bucket, filter), b));
        {
          IImageIntersect(bucket, filter, a);
          IImageIntersect(bucket, filter, b);
        }
      WeightBucket(IImage(bucket, filter * a)) + WeightBucket(IImage(bucket, filter * b));
    }
  }

  lemma SetPartition<T>(B:set<T>, f:T->bool, fa:T->bool, fb:T->bool)
    requires forall e:T :: f(e) == (fa(e) || fb(e))
    ensures (set e | e in B && f(e)) == (set e | e in B && fa(e)) + (set e | e in B && fb(e))
  {
  }

  lemma WeightBucketListItemFlushSingletonOrEmpty(parent: Bucket, children: BucketList, pivots: PivotTable, i: int, filter:iset<Key>, key:Key)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  requires forall k :: k in filter ==> k == key   // filter admits at most one key
  ensures WeightBucket(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i))
    <= WeightBucket(IImage(parent, RouteRange(pivots, i) * filter))
       + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter));
  {
    reveal_IImage();

    var flush := BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i);
    if key in flush.Keys {
      WeightBucketSingleton(flush, key);
    } else {
      WeightBucketEmpty();
      assert flush == map[];
    }

    var filteredParent := IImage(parent, RouteRange(pivots, i) * filter);
    if key in filteredParent {
      WeightBucketSingleton(filteredParent, key);
    } else {
      WeightBucketEmpty();
    }

    var filteredChild := IImage(children[i], RouteRange(pivots, i) * filter);
    if key in filteredChild {
      WeightBucketSingleton(filteredChild, key);
    } else {
      WeightBucketEmpty();
    }

    if (key in filteredChild && key in filteredParent && key in flush) {
      // This is the only tricksy case, where we actually care how Merge
      // affects weights of the messages getting swapped.
      MergeGainsNoWeight(BucketGet(filteredParent, key), BucketGet(filteredChild, key));
    }
  }

  lemma WeightBucketListItemFlushInner(parent: Bucket, children: BucketList, pivots: PivotTable, i: int, filter:iset<Key>)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  ensures
    WeightBucket(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i))
      <= WeightBucket(IImage(parent, RouteRange(pivots, i) * filter)) + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter))
  decreases |IImage(parent, filter)| + |IImage(children[i], filter)|
  {
    // Pick an arbitrary key to decrease by
    // (In Lisp, "car" is the first thing in a list, "cdr" is everything else.)
    var carKey;
    if |IImage(parent, filter)| != 0 {
      carKey :| carKey in IImage(parent, filter);
    } else if |IImage(children[i], filter)| != 0 {
      carKey :| carKey in IImage(children[i], filter);
    } else {
      return;
    }

    var carFilter := iset {carKey};
    var cdrFilter := iset k | k != carKey;

    // cdrFilter decreases
    if |IImage(parent, filter)| != 0 {
      forall ensures |IImage(parent, filter * cdrFilter)| < |IImage(parent, filter)|
      {
        reveal_IImage();
        Sets.ProperSubsetImpliesSmallerCardinality(IImage(parent, filter * cdrFilter).Keys, IImage(parent, filter).Keys);
      }
      IImageSubset(children[i], filter * cdrFilter, filter);
      Sets.SetInclusionImpliesSmallerCardinality(IImage(children[i], filter * cdrFilter).Keys, IImage(children[i], filter).Keys);
    } else {
      IImageSubset(parent, filter * cdrFilter, filter);
      Sets.SetInclusionImpliesSmallerCardinality(IImage(parent, filter * cdrFilter).Keys, IImage(parent, filter).Keys);
      forall ensures |IImage(children[i], filter * cdrFilter)| < |IImage(children[i], filter)|
      {
        reveal_IImage();
        Sets.ProperSubsetImpliesSmallerCardinality(IImage(children[i], filter * cdrFilter).Keys, IImage(children[i], filter).Keys);
      }
    }

    // The core of the proof is that the inequality holds for the carKey we
    // chose from the parent.
    forall k | k in BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i).Keys
      ensures k == carKey
    {
      reveal_IImage();
    }

    calc {
      WeightBucket(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i));
        {
          IWeightBucketLinearInKeySet(
            BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i), carFilter, cdrFilter);
        }
      WeightBucket(IImage(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i), carFilter))
      + WeightBucket(IImage(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i), cdrFilter));
        { // push filters through IImage operator & BucketListItemFlush.
          reveal_IImage();
          assert IImage(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i), carFilter)
            == BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i);
          assert IImage(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i), cdrFilter)
            == BucketListItemFlush(IImage(parent, filter * cdrFilter), IImage(children[i], filter * cdrFilter), pivots, i);
        }
      WeightBucket(BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i))
      + WeightBucket(BucketListItemFlush(IImage(parent, filter * cdrFilter), IImage(children[i], filter * cdrFilter), pivots, i));
      <=
        { // recursion for car
          WeightBucketListItemFlushSingletonOrEmpty(parent, children, pivots, i, filter * carFilter, carKey);
          assert RouteRange(pivots, i) * (filter * carFilter) == RouteRange(pivots, i) * filter * carFilter;
          // recursion for cdr
          WeightBucketListItemFlushInner(parent, children, pivots, i, filter * cdrFilter);
          assert RouteRange(pivots, i) * (filter * cdrFilter) == RouteRange(pivots, i) * filter * cdrFilter;
        }
      WeightBucket(IImage(parent, RouteRange(pivots, i) * filter * carFilter)) + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(IImage(parent, RouteRange(pivots, i) * filter * cdrFilter)) + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * cdrFilter));
      // Just rearranging terms
      WeightBucket(IImage(parent, RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(IImage(parent, RouteRange(pivots, i) * filter * cdrFilter))
        + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * cdrFilter));
      { WeightBucketFilterPartitions(parent, RouteRange(pivots, i) * filter, carFilter, cdrFilter); }
      WeightBucket(IImage(parent, RouteRange(pivots, i) * filter))
        + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * carFilter))
        + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * cdrFilter));
      { WeightBucketFilterPartitions(children[i], RouteRange(pivots, i) * filter, carFilter, cdrFilter); }
      WeightBucket(IImage(parent, RouteRange(pivots, i) * filter))
        + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter));
    }
  }

  lemma WeightBucketListItemFlush(parent: Bucket, children: BucketList, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  ensures WeightBucket(BucketListItemFlush(parent, children[i], pivots, i))
      <= WeightBucket(IImage(parent, RouteRange(pivots, i))) + WeightBucket(IImage(children[i], RouteRange(pivots, i)))
  {
    var noFilter := iset k | true;
    WeightBucketListItemFlushInner(parent, children, pivots, i, noFilter);
    reveal_IImage();
    assert IImage(parent, noFilter) == parent;  // trigger
    assert IImage(children[i], noFilter) == children[i];  // trigger
    assert IImage(parent, RouteRange(pivots, i) * noFilter) == IImage(parent, RouteRange(pivots, i));  // trigger
    assert IImage(children[i], RouteRange(pivots, i) * noFilter) == IImage(children[i], RouteRange(pivots, i));  // trigger
  }

  function RouteRanges(pivots: PivotTable, i: int) : iset<Key>
    // Keys that route to children < i
    requires WFPivots(pivots)
  {
    iset k | Route(pivots, k) < i
  }

  lemma WeightBucketListFlushPartial(parent: Bucket, children: BucketList, pivots: PivotTable, items: int)
  requires WFBucketList(children, pivots)
  requires 0 <= items <= |children|
  ensures WeightBucketList(BucketListFlushPartial(parent, children, pivots, items))
      <= WeightBucket(IImage(parent, RouteRanges(pivots, items)))
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
        WeightBucket(IImage(parent, RouteRanges(pivots, items - 1)))
          + WeightBucketList(children[..items - 1])
          + WeightBucket(BucketListItemFlush(parent, children[items - 1], pivots, items - 1));
        <=
          { WeightBucketListItemFlush(parent, children, pivots, items -1); }  // Flush the singleton
        WeightBucket(IImage(parent, RouteRanges(pivots, items - 1)))
          + WeightBucketList(children[..items - 1])
          + WeightBucket(IImage(parent, RouteRange(pivots, items - 1)))
          + WeightBucket(IImage(children[items - 1], RouteRange(pivots, items - 1)));
        {  // Glue the parent halves back together
          WeightBucketLinearVariant(parent, RouteRanges(pivots, items - 1), RouteRange(pivots, items - 1));
          assert RouteRanges(pivots, items) == RouteRanges(pivots, items - 1) + RouteRange(pivots, items - 1);  // trigger
        }
        WeightBucket(IImage(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items - 1])
          + WeightBucket(IImage(children[items - 1], RouteRange(pivots, items - 1)));
        { // The last child bucket's RouteRange covers the whole bucket, so we can simplify.
          IImageShape(children[items - 1], RouteRange(pivots, items - 1));
          assert IImage(children[items - 1], RouteRange(pivots, items - 1)) == children[items-1]; // trigger
        }
        WeightBucket(IImage(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items-1]) + WeightBucket(children[items-1]);
        { // pack the last bucket up into a singleton list
          assert children[items-1..items] == [children[items-1]]; // trigger
          reveal_WeightBucketList();
        }
        WeightBucket(IImage(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items-1]) + WeightBucket(children[items-1]);
        { // and glue the children sublists back together
          WeightBucketListConcatOne(children[..items-1], children[items-1]);
          assert children[..items-1] + [children[items-1]] == children[..items]; // trigger
        }
        WeightBucket(IImage(parent, RouteRanges(pivots, items)))
          + WeightBucketList(children[..items]);
      }
    }
  }

  lemma WeightBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable)
  requires WFBucketList(children, pivots)
  requires |children| == NumBuckets(pivots)
  ensures WeightBucketList(BucketListFlush(parent, children, pivots))
      <= WeightBucket(parent) + WeightBucketList(children)
  {
    WeightBucketListFlushPartial(parent, children, pivots, |children|);
    forall ensures IImage(parent, RouteRanges(pivots, |children|)) == parent
    {
      reveal_IImage();
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
  ensures WeightBucketList(blist[i := map[]]) <= WeightBucketList(blist)
  {
    WeightBucketListReplace(blist, i, map[]);
  }

  // Analogous to WeightBucketListReplace, except we're changing the size of the thing in the middle.
  lemma WeightSplitBucketInList(blist: BucketList, i: int, pivot: Key)
  requires 0 <= i < |blist|
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

  lemma WeightBucketListSuffix(blist: BucketList, a: int)
  requires 0 <= a <= |blist|
  ensures WeightBucketList(blist[a..]) <= WeightBucketList(blist)
  {
    WeightBucketListConcat(blist[..a], blist[a..]);
    assert blist == blist[..a] + blist[a..];
  }

  lemma MergeUndoesSplit(blist:BucketList, pivots:PivotTable, i:int)
  requires 0 <= i < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures SplitBucketInList(MergeBucketsInList(blist, i), i, pivots[i]) == blist;
  {
    var merged := MergeBucketsInList(blist, i);
    var mbucket := MergeBuckets(blist[i], blist[i+1]);

    reveal_MergeBucketsInList();
    reveal_replace2with1();
    reveal_MergeBuckets();
    reveal_Image();
    var leftKeys := set k | k in mbucket && Keyspace.lt(k, pivots[i]);
    SplitBucketLeftImage(mbucket, pivots[i], leftKeys);
    var rightKeys := set k | k in mbucket && Keyspace.lte(pivots[i], k);
    SplitBucketRightImage(mbucket, pivots[i], rightKeys);

    assert SplitBucketLeft(mbucket, pivots[i]) == blist[i];
    assert SplitBucketRight(mbucket, pivots[i]) == blist[i+1];

    calc {
      SplitBucketInList(merged, i, pivots[i]);
        { reveal_SplitBucketInList(); }
      replace1with2(merged, SplitBucketLeft(merged[i], pivots[i]), SplitBucketRight(merged[i], pivots[i]), i);
        { reveal_replace1with2(); }
      merged[..i] + [SplitBucketLeft(merged[i], pivots[i]), SplitBucketRight(merged[i], pivots[i])] + merged[i+1..];
      blist[..i] + [SplitBucketLeft(mbucket, pivots[i]), SplitBucketRight(mbucket, pivots[i])] + blist[i+2..];
      blist[..i] + [blist[i], blist[i+1]] + blist[i+2..];
      blist;
    }
  }

  // Undoes WeightSplitBucketInList
  lemma WeightMergeBucketsInList(blist: BucketList, i: int, pivots: PivotTable)
  requires 0 <= i < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures WeightBucketList(MergeBucketsInList(blist, i)) == WeightBucketList(blist)
  {
    MergeUndoesSplit(blist, pivots, i);
    WeightSplitBucketInList(MergeBucketsInList(blist, i), i, pivots[i]);
  }

  lemma WeightJoinBucketList(blist: BucketList)
  ensures WeightBucket(JoinBucketList(blist)) <= WeightBucketList(blist)
  { }

  lemma WeightSplitBucketOnPivots(bucket: Bucket, pivots: seq<Key>)
  ensures WeightBucketList(SplitBucketOnPivots(bucket, pivots)) == WeightBucket(bucket)
  { }

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma LenLeWeight(bucket: Bucket)
  ensures |bucket| <= WeightBucket(bucket)
  { }

  lemma WeightBucketEmpty()
  ensures WeightBucket(map[]) == 0
  {
    reveal_WeightBucket();
  }

  lemma WeightBucketListOneEmpty()
  ensures WeightBucketList([map[]]) == 0
  { }

  lemma WeightBucketPut(bucket: Bucket, key: Key, msg: Message)
  ensures WeightBucket(bucket[key := msg]) <=
      WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)
  { }

  lemma WeightBucketLeBucketList(blist: BucketList, i: int)
  requires 0 <= i < |blist|
  ensures WeightBucket(blist[i]) <= WeightBucketList(blist)
  { }

  lemma WeightBucketListInsert(blist: BucketList, pivots: PivotTable, key: Key, msg: Message)
  requires WFBucketList(blist, pivots)
  ensures WeightBucketList(BucketListInsert(blist, pivots, key, msg)) <=
      WeightBucketList(blist) + WeightKey(key) + WeightMessage(msg)
  { }

  lemma WeightBucketIntersect(bucket: Bucket, keys: set<Key>)
  ensures WeightBucket(BucketIntersect(bucket, keys)) <= WeightBucket(bucket)
  { }

  lemma WeightBucketComplement(bucket: Bucket, keys: set<Key>)
  ensures WeightBucket(BucketComplement(bucket, keys)) <= WeightBucket(bucket)
  { }

  lemma WeightMessageBound(msg: Message)
  ensures WeightMessage(msg) <= 8 + 1024
  { }
}
