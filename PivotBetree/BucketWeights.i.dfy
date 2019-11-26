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

  lemma MergeGainsNoWeight(parent: Message, child: Message)
  ensures WeightMessage(Merge(parent, child)) <= WeightMessage(parent) + WeightMessage(child)
  {
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

  lemma MapRemoveVsImage(bbig:Bucket, bsmall:Bucket, key:Key)
  requires bsmall == MapRemove1(bbig, key)
  ensures Image(bbig, bbig.Keys - {key}) == bsmall;
  {
    reveal_MapRemove1();
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
  requires forall k:Key :: k in bucket ==> k in a + b
  requires exists k :: k in a // So we can decrease |bucket|
  requires exists k :: k in b // So we can decrease |bucket|
  requires |bucket| > 0 // So we can ChooseKey
  requires ChooseKey(bucket) in a
  ensures WeightBucket(bucket) == WeightBucket(IImage(bucket, a)) + WeightBucket(IImage(bucket, b))
  decreases |bucket|, 0
  {
    var key := ChooseKey(bucket);
    var msg := bucket[key];
    var residual := WeightKey(key) + WeightMessage(msg);

    calc {
      WeightBucket(IImage(bucket, a));
        { IWeightBucketLinearInKeySet(IImage(bucket, a), a-iset{key}, iset{key}); }
      WeightBucket(IImage(IImage(bucket, a), a-iset{key})) + WeightBucket(IImage(IImage(bucket, a), iset{key}));
        {
          reveal_IImage();
          assert IImage(IImage(bucket, a), a-iset{key}) == IImage(bucket, a-iset{key});  // OBSERVE trigger
          assert IImage(IImage(bucket, a), iset{key}) == IImage(bucket, iset{key});  // OBSERVE trigger
        }
      WeightBucket(IImage(bucket, a-iset{key})) + WeightBucket(IImage(bucket, iset{key}));
        { reveal_IImage(); WeightBucketSingleton(IImage(bucket, iset{key}), key); }
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
        { IWeightBucketLinearInKeySet(IImage(bucket, (a-iset{key})+b), a-iset{key}, b); }
      WeightBucket(IImage(IImage(bucket, (a-iset{key})+b), a-iset{key})) + WeightBucket(IImage(IImage(bucket, (a-iset{key})+b), b)) + residual;
        { 
          reveal_IImage();
          assert IImage(IImage(bucket, (a-iset{key})+b), a-iset{key}) == IImage(bucket, a-iset{key});  // OBSERVE trigger
          assert IImage(IImage(bucket, (a-iset{key})+b), b) == IImage(bucket, b);  // OBSERVE trigger
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
  decreases |bucket|, 1
  {
    if |bucket| == 0 {
    } else if a==iset{} {
      assert bucket == IImage(bucket, b);  // trigger
    } else if b==iset{} {
      assert bucket == IImage(bucket, a);  // trigger
    } else {
      if ChooseKey(bucket) in a {
//        WeightBucketLinearInKeySetInner(bucket, a, b);
      } else {
 //       WeightBucketLinearInKeySetInner(bucket, b, a);
      }
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
//        WeightBucketLinearInKeySetInner(bucket, a, b);
      } else {
 //       WeightBucketLinearInKeySetInner(bucket, b, a);
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

  function RouteRange(pivots: PivotTable, i: int) : iset<Key>
  {
    iset k | Route(pivots, k) == i
  }

  function toIset<T>(s:set<T>) : iset<T>
  {
     iset e | e in s
  }

  function {:opaque} IImage(b:Bucket, s:iset<Key>) : (image:Bucket)
    ensures image.Keys <= b.Keys
    ensures toIset(image.Keys) <= s
  {
    map k | k in b && k in s :: b[k]
  }

  function fIntersect<T>(s:set<T>, t:iset<T>) : set<T>
  {
    set e | e in s && e in t
  }

  lemma EmptyBucketListItemFlush(parent: Bucket, child: Bucket, pivots: PivotTable, i: int)
    requires |IImage(parent, RouteRange(pivots, i))| == 0
    ensures |BucketListItemFlush(parent, child, pivots, i)| == 0
  {
    forall key | key in (child.Keys + parent.Keys) && Route(pivots, key) == i
      ensures key in IImage(parent, RouteRange(pivots, i))
    {
    }
  }

  lemma SetCardinality<T>(a:set<T>, b:set<T>)
    requires a < b
    ensures |a| < |b|
  {
  }

  lemma FreakinSetExtensionality<T>(a:set<T>, b:set<T>)
    requires forall e :: e in a ==> e in b;
    requires forall e :: e in b ==> e in a;
    ensures a == b;
  {
  }

  // Flipping back and forth between iset and set here is a pain.
  lemma SetMunging(bucket:Bucket, fa:iset<Key>, fb:iset<Key>)
  ensures fIntersect(bucket.Keys, fa * fb) <= IImage(bucket, fa).Keys;
  ensures Image(IImage(bucket, fa), fIntersect(bucket.Keys, fa * fb)) == IImage(bucket, fa * fb)
  {
    reveal_IImage();
    reveal_Image();
  }

  lemma WeightBucketFilterPartitions(bucket:Bucket, filter:iset<Key>, a:iset<Key>, b:iset<Key>)
    ensures WeightBucket(IImage(bucket, filter)) ==
      WeightBucket(IImage(bucket, filter * a)) + WeightBucket(IImage(bucket, filter * b));
    requires a !! b
    requires filter * a + filter * b == filter;
  {
    reveal_IImage();
    WeightBucketLinearInKeySet(IImage(bucket, filter),
      fIntersect(bucket.Keys, filter * a), fIntersect(bucket.Keys, filter * b));
    SetMunging(bucket, filter, a);
    SetMunging(bucket, filter, b);
  }

  lemma SetPartition<T>(B:set<T>, f:T->bool, fa:T->bool, fb:T->bool)
    requires forall e:T :: f(e) == (fa(e) || fb(e))
    ensures (set e | e in B && f(e)) == (set e | e in B && fa(e)) + (set e | e in B && fb(e))
  {
  }

  lemma WeightBucketListItemFlushSingletonOrEmpty(parent: Bucket, children: BucketList, pivots: PivotTable, i: int, filter:iset<Key>, key:Key)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  requires forall k :: k in filter ==> k == key
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
  decreases |IImage(parent, filter)|
  {
    if |IImage(parent, filter)| == 0 {
      calc {
        WeightBucket(BucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i));
          { EmptyBucketListItemFlush(IImage(parent, filter), IImage(children[i], filter), pivots, i); }
        0;
        <=
        WeightBucket(IImage(parent, RouteRange(pivots, i) * filter))
          + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter));
      }
    } else {
      // Pick an arbitrary key to decrease parent by
      // (In Lisp, "car" is the first thing in a list, "cdr" is everything else.)
      var carKey :| carKey in IImage(parent, filter);
      var carFilter := iset {carKey};
      var cdrFilter := iset k | k != carKey;

      // The core of the proof is that the inequality holds for the carKey we
      // chose from the parent.
      forall k | k in BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i).Keys
        ensures k == carKey
      {
        reveal_IImage();
      }

//      if (carKey !in BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i)) {
//        // That could work either because carKey doesn't actually end up in the
//        // flush output (WeightBucketEmpty())...
//        calc {
//          WeightBucket(BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i));
//            { WeightBucketEmpty(); }
//          0;
//          <=
//          WeightBucket(IImage(parent, RouteRange(pivots, i) * filter * carFilter)) + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * carFilter));
//        }
//      } else {
//        // Or we
//        assert BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i).Keys == {carKey};
//        calc {
//          WeightBucket(BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i));
//            { WeightBucketSingleton(BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i), carKey); }
//          WeightKey(carKey) + WeightMessage(BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i)[carKey]);
//          <=
//          WeightKey(carKey) + WeightMessage(parent[carKey])
//            + WeightKey(carKey) + WeightMessage(children[i][carKey]);
//            { WeightBucketSingleton(children[i], carKey); }
//          WeightKey(carKey) + WeightMessage(parent[carKey])
//            + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * carFilter));
//            { WeightBucketSingleton(IImage(parent, RouteRange(pivots, i) * filter * carFilter), carKey); }
//          WeightBucket(IImage(parent, RouteRange(pivots, i) * filter * carFilter))
//            + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * carFilter));
//        }
//      }
//      if |IImage(parent, filter)| == 1 {
//        // carFilter is a no-op.
//        forall ensures IImage(parent, filter * carFilter) == IImage(parent, filter) {
//          reveal_IImage();
//          forall k | k in IImage(parent, filter).Keys ensures k in IImage(parent, filter * carFilter).Keys {
//            if (k != carKey) {
//              SetCardinality({k}, IImage(parent, filter).Keys);
//              assert false;
//            }
//          }
//        }
//        forall k | k in BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i)
//          ensures k in IImage(parent, RouteRange(pivots, i) * filter * carFilter)
//        {
//          var childKeys := IImage(children[i], filter * carFilter).Keys;
//          var parentKeys := IImage(parent, filter * carFilter).Keys;
//          assert k in childKeys + parentKeys;
//          assert k in parentKeys;
//          assert k in carFilter;
//        }
//
//        calc {
//          WeightBucket(BucketListItemFlush(IImage(parent, filter * carFilter), IImage(children[i], filter * carFilter), pivots, i));
//          { reveal_IImage(); }
//          WeightBucket(IImage(parent, RouteRange(pivots, i) * filter * carFilter)) + WeightBucket(IImage(children[i], RouteRange(pivots, i) * filter * carFilter));
//        }
//      } else {
//        // carFilter decreases
//        forall ensures |IImage(parent, filter * carFilter)| < |IImage(parent, filter)|
//        {
//          reveal_IImage();
//          if (forall cdrKey :: !(cdrKey in cdrFilter && cdrKey in IImage(parent, filter).Keys)) {
//            // proof by contradiction: cdrFilter must include something, or else we're in the ||==1 case.
//            assert IImage(parent, filter).Keys == IImage(parent, filter * carFilter).Keys + IImage(parent, filter * cdrFilter).Keys;
//            assert IImage(parent, filter * carFilter).Keys == {carKey};
//            assert |IImage(parent, filter * cdrFilter).Keys| == 0;
//            assert |IImage(parent, filter)| == |IImage(parent, filter * carFilter)| == 1;
//            assert false;
//          }
//          var cdrKey :| cdrKey in cdrFilter && cdrKey in IImage(parent, filter).Keys;
//          SetCardinality(IImage(parent, filter * carFilter).Keys, IImage(parent, filter).Keys);
//        }
//        WeightBucketListItemFlushInner(parent, children, pivots, i, filter * carFilter);  // recursion car
//        assert RouteRange(pivots, i) * (filter * carFilter) == RouteRange(pivots, i) * filter * carFilter;
//      }

      // cdrFilter decreases
      forall ensures |IImage(parent, filter * cdrFilter)| < |IImage(parent, filter)|
      {
        reveal_IImage();
        SetCardinality(IImage(parent, filter * cdrFilter).Keys, IImage(parent, filter).Keys);
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
  }

  lemma WeightBucketListItemFlush(parent: Bucket, children: BucketList, pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  ensures WeightBucket(BucketListItemFlush(parent, children[i], pivots, i))
      <= WeightBucket(parent) + WeightBucket(children[i])
  {
    calc {
      WeightBucket(BucketListItemFlush(parent, children[i], pivots, i));
      <=
      WeightBucket(parent) + WeightBucket(children[i]);
    }
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
