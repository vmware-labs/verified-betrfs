include "../PivotBetree/BucketsLib.i.dfy"
//
// Assigning weights to buckets guides the flushing algorithm to decide
// which child to push messages towards. TODO(thance): help!
//

module BucketWeights {
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
  ensures forall k :: k in image ==> k in s
  // The ensures above isn't implicated in profiling, but seems to overtrigger
  // MapType0Select somewhere else, quite badly.
  {
    var m := map k | k in s :: b[k];
    assert m.Keys == s;
    m
  }

  lemma MapRemoveVsImage(bbig:Bucket, bsmall:Bucket, key:Key)
  requires bsmall == MapRemove1(bbig, key)
  ensures Image(bbig, bbig.Keys - {key}) == bsmall;
  {
    reveal_MapRemove1();
  }

  lemma WeightBucketSingleton(bucket:Bucket, key:Key)
  requires bucket.Keys == {key};
  ensures WeightBucket(bucket) == WeightKey(key) + WeightMessage(bucket[key]);
  {
    reveal_WeightBucket();
  }

  lemma WeightBucketLinearInKeySetInner(bucket:Bucket, a:set<Key>, b:set<Key>)
  requires a !! b
  requires a + b == bucket.Keys
  requires |a| > 0  // So we can decrease |bucket|
  requires |b| > 0
  requires |bucket| > 0 // So we can ChooseKey
  requires ChooseKey(bucket) in a
  ensures WeightBucket(bucket) == WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b))
  decreases |bucket|, 0
  {
    var key := ChooseKey(bucket);
    var msg := bucket[key];
    var residual := WeightKey(key) + WeightMessage(msg);

    calc {
      WeightBucket(Image(bucket, a));
        { WeightBucketLinearInKeySet(Image(bucket, a), a-{key}, {key}); }
      WeightBucket(Image(Image(bucket, a), a-{key})) + WeightBucket(Image(Image(bucket, a), {key}));
        {
          assert Image(Image(bucket, a), a-{key}) == Image(bucket, a-{key});  // OBSERVE trigger
          assert Image(Image(bucket, a), {key}) == Image(bucket, {key});  // OBSERVE trigger
        }
      WeightBucket(Image(bucket, a-{key})) + WeightBucket(Image(bucket, {key}));
        { WeightBucketSingleton(Image(bucket, {key}), key); }
      WeightBucket(Image(bucket, a-{key})) + residual;
    }
    calc {
      WeightBucket(bucket);
        { reveal_WeightBucket(); }
      WeightBucket(MapRemove1(bucket, key)) + residual;
        { MapRemoveVsImage(bucket, Image(bucket, (a+b)-{key}), key); }
      WeightBucket(Image(bucket, (a+b)-{key}) )+ residual;
        { assert a+b-{key} == (a-{key})+b; }  // OSBERVE trigger
      WeightBucket(Image(bucket, (a-{key})+b)) + residual;
        { WeightBucketLinearInKeySet(Image(bucket, (a-{key})+b), a-{key}, b); }
      WeightBucket(Image(Image(bucket, (a-{key})+b), a-{key})) + WeightBucket(Image(Image(bucket, (a-{key})+b), b)) + residual;
        { 
          assert Image(Image(bucket, (a-{key})+b), a-{key}) == Image(bucket, a-{key});  // OBSERVE trigger
          assert Image(Image(bucket, (a-{key})+b), b) == Image(bucket, b);  // OBSERVE trigger
        }
      WeightBucket(Image(bucket, a-{key})) + WeightBucket(Image(bucket, b)) + residual;
        // upper calc
      WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b));
    }
  }

  // The raw WeightBucket definition is really difficult to work with. This
  // lemma is a much nicer foundation to work with.
  lemma WeightBucketLinearInKeySet(bucket:Bucket, a:set<Key>, b:set<Key>)
  requires a !! b
  requires a + b == bucket.Keys
  ensures WeightBucket(bucket) == WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b))
  decreases |bucket|, 1
  {
    if |bucket| == 0 {
    } else if a=={} {
      assert bucket == Image(bucket, b);  // trigger
    } else if b=={} {
      assert bucket == Image(bucket, a);  // trigger
    } else {
      if ChooseKey(bucket) in a {
        WeightBucketLinearInKeySetInner(bucket, a, b);
      } else {
        WeightBucketLinearInKeySetInner(bucket, b, a);
      }
    }
  }

  lemma WeightBucketInduct(bucket: Bucket, key: Key, msg: Message)
  requires key !in bucket
  ensures WeightBucket(bucket[key := msg]) == WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)
  {
    var update := map [ key := msg ];
    var rest := bucket.Keys - {key};

    WeightBucketLinearInKeySet(bucket[key := msg], {key}, rest);
    assert Image(bucket[key := msg], {key}) == update;  // trigger
    assert Image(bucket[key := msg], rest) == bucket; // trigger
    WeightBucketSingleton(Image(update, {key}), key);
  }

  lemma SplitBucketLeftImage(bucket: Bucket, pivot: Key, leftKeys:set<Key>)
  requires leftKeys == set k | k in bucket && Keyspace.lt(k, pivot)
  ensures SplitBucketLeft(bucket, pivot) == Image(bucket, leftKeys)
  {
    reveal_SplitBucketLeft();
  }

  lemma SplitBucketRightImage(bucket: Bucket, pivot: Key, rightKeys:set<Key>)
  requires rightKeys == set k | k in bucket && Keyspace.lte(pivot, k)
  ensures SplitBucketRight(bucket, pivot) == Image(bucket, rightKeys)
  {
    reveal_SplitBucketRight();
  }

  lemma WeightSplitBucketLeft(bucket: Bucket, pivot: Key)
  ensures WeightBucket(SplitBucketLeft(bucket, pivot)) <= WeightBucket(bucket)
  {
    var leftKeys := set k | k in bucket && Keyspace.lt(k, pivot);
    var rightKeys := bucket.Keys - leftKeys;
    reveal_SplitBucketLeft();
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
    { reveal_SplitBucketLeft(); }

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

  function {:opaque} KeySetForRoute(parent: Bucket, pivots: PivotTable, i: int) : (ks:set<Key>)
    ensures forall k :: k in parent.Keys && Route(pivots, k) == i <==> k in ks
  {
    set k | k in parent.Keys && Route(pivots, k) == i
  }

  lemma EmptyBucketListItemFlush(parent: Bucket, child: Bucket, pivots: PivotTable, i: int)
    requires |Image(parent, KeySetForRoute(parent, pivots, i))| == 0
    ensures |BucketListItemFlush(parent, child, pivots, i)| == 0
  {
    forall key | key in (child.Keys + parent.Keys) && Route(pivots, key) == i
      ensures key in Image(parent, KeySetForRoute(parent, pivots, i))
    {
    }
  }

  lemma WeightBucketListItemFlush(parent: Bucket, children: BucketList, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  // A tighter bound we'll need later...
  ensures WeightBucket(BucketListItemFlush(parent, children[i], pivots, i))
      <= WeightBucket(Image(parent, KeySetForRoute(parent, pivots, i))) + WeightBucket(children[i])
  // ...gives this one easily:
  ensures WeightBucket(BucketListItemFlush(parent, children[i], pivots, i))
      <= WeightBucket(parent) + WeightBucket(children[i])
  {
    var childKeys := KeySetForRoute(parent, pivots, i);
    if |Image(parent, childKeys)| == 0 {
      calc {
        WeightBucket(BucketListItemFlush(parent, children[i], pivots, i));
          { EmptyBucketListItemFlush(parent, children[i], pivots, i); }
        0;
        <=
        WeightBucket(children[i]);
        WeightBucket(Image(parent, childKeys)) + WeightBucket(children[i]);
      }
    } else {
      // Pick a key to decrease parent by
      var extraKey :| extraKey in Image(parent, childKeys);
      var subparent := MapRemove1(parent, extraKey);
      assert extraKey in parent;
      assert |subparent| < |parent|;
      var subChildKeys := childKeys - { extraKey };
      calc {
        WeightBucket(BucketListItemFlush(parent, children[i], pivots, i));
        //here
        WeightBucket(BucketListItemFlush(subparent, children[i], pivots, i));
        <=
          { WeightBucketListItemFlush(subparent, children, pivots, i); }
          // here`:3
        WeightBucket(Image(subparent, subChildKeys)) + WeightBucket(children[i]);
        WeightBucket(Image(parent, childKeys)) + WeightBucket(children[i]);
      }
    }
    assert WeightBucket(Image(parent, KeySetForRoute(parent, pivots, i))) <= WeightBucket(parent);
  }

  lemma WeightBucketListFlush(parent: Bucket, children: BucketList, pivots: PivotTable)
  requires WFPivots(pivots)
  ensures WeightBucketList(BucketListFlush(parent, children, pivots))
      <= WeightBucket(parent) + WeightBucketList(children)
  {
    calc {
      WeightBucketList(BucketListFlush(parent, children, pivots));
      WeightBucketList(BucketListFlush(parent, children, pivots));

    }
  }

  lemma WeightBucketListShrinkEntry(blist: BucketList, i: int, bucket: Bucket)
  requires 0 <= i < |blist|
  requires WeightBucket(bucket) <= WeightBucket(blist[i])
  ensures WeightBucketList(blist[i := bucket]) <= WeightBucketList(blist)
  { }

  lemma WeightBucketListClearEntry(blist: BucketList, i: int)
  requires 0 <= i < |blist|
  ensures WeightBucketList(blist[i := map[]]) <= WeightBucketList(blist)
  { }

  lemma WeightSplitBucketInList(blist: BucketList, slot: int, pivot: Key)
  requires 0 <= slot < |blist|
  ensures WeightBucketList(SplitBucketInList(blist, slot, pivot))
      == WeightBucketList(blist)
  { }

  lemma WeightBucketListSuffix(blist: BucketList, a: int)
  requires 0 <= a <= |blist|
  ensures WeightBucketList(blist[a..]) <= WeightBucketList(blist)
  { }

  lemma WeightMergeBucketsInList(blist: BucketList, slot: int, pivots: PivotTable)
  requires 0 <= slot < |blist| - 1
  requires WFBucketList(blist, pivots)
  ensures WeightBucketList(MergeBucketsInList(blist, slot)) == WeightBucketList(blist)
  { }

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
