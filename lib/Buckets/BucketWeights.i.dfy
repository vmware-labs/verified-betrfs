include "../Base/Sets.i.dfy"
include "BucketsLib.i.dfy"
//
// Assigning weights to buckets guides the flushing algorithm to decide
// which child to push messages towards. TODO(thance): help!
//

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

  function WeightKey(key: Key) : (w:int)
  ensures w >= 0
  {
    4 + |key|
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

  function WeightMessageSeq(msgs: seq<Message>) : (w:int)
  ensures w >= 0
  {
    if |msgs| == 0 then 0 else WeightMessageSeq(DropLast(msgs)) + WeightMessage(Last(msgs))
  }

  function {:opaque} ChooseKey(bucket: Bucket) : (key : Key)
  requires |bucket.b| > 0
  ensures key in bucket.b
  {
    var key :| key in bucket.b;
    key
  }

  // TODO we need to rewrite this in terms of the bucket sequences
  // not the map.
  function {:opaque} WeightBucket(bucket: Bucket) : (w:int)
  ensures w >= 0
  ensures |bucket.b| == 0 ==> WeightBucket(bucket) == 0
  decreases bucket.b
  {
    if |bucket.b| == 0 then 0 else (
      var key := ChooseKey(bucket);
      var msg := bucket.b[key];
      WeightBucket(B(MapRemove1(bucket.b, key))) + WeightKey(key) + WeightMessage(msg)
    )
  }

  function {:opaque} WeightBucketList(buckets: BucketList) : (w:int)
  ensures w >= 0
  {
    if |buckets| == 0 then 0 else (
      WeightBucketList(DropLast(buckets)) +
          WeightBucket(Last(buckets))
    )
  }

  lemma WeightBucketEmpty()
  ensures WeightBucket(B(map[])) == 0
  {
    reveal_WeightBucket();
  }

  lemma WeightBucketSingleton(bucket:Bucket, key:Key)
  requires BucketWellMarshalled(bucket)
  requires bucket.b.Keys == {key};
  ensures WeightBucket(bucket) == WeightKey(key) + WeightMessage(bucket.b[key]);
  {
    reveal_WeightBucket();
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
  requires BucketWellMarshalled(bucket)
  ensures BucketWellMarshalled(image)
//    ensures image.Keys <= bucket.Keys
// Even this subset relation is a timeout source. (This must be the cause of
// timeout on branch hard-to-trace-map-timeout)
  {
    B(map k | k in bucket.b && k in filter :: bucket.b[k])
  }

  lemma ImageShape(b:Bucket, s:iset<Key>)
    requires BucketWellMarshalled(b)
    ensures forall k :: k in b.b && k in s <==> k in Image(b, s).b.Keys
    ensures forall k :: k in Image(b,s).b ==> Image(b,s).b[k] == b.b[k];
  {
    reveal_Image();
  }

  lemma ImageIdentity(bucket:Bucket, s:iset<Key>)
  requires BucketWellMarshalled(bucket)
  requires forall k :: k in bucket.b ==> k in s
  ensures bucket == Image(bucket, s)
  {
    assume false;
    ImageShape(bucket, s);
  }

  lemma ImageTrim(bucket:Bucket, s:iset<Key>, trimBucket:Bucket)
  requires BucketWellMarshalled(bucket)
  requires BucketWellMarshalled(trimBucket)
  requires forall k :: k in trimBucket.b <==> k in bucket.b && k in s
  requires forall k :: k in trimBucket.b ==> trimBucket.b[k] == bucket.b[k]
  ensures Image(bucket, s).b == trimBucket.b
  {
    ImageShape(bucket, s);
  }

  lemma ImageEquiv(a:Bucket, b:Bucket, s:iset<Key>)
  requires BucketWellMarshalled(a)
  requires BucketWellMarshalled(b)
  requires forall k :: k in a.b.Keys && k in s <==> k in b.b.Keys && k in s
  requires forall k :: k in a.b.Keys && k in s ==> a.b[k] == b.b[k]
  ensures Image(a, s) == Image(b, s)
  {
    reveal_Image();
  }

  lemma ImageSingleton(b:Bucket, k:Key)
    requires BucketWellMarshalled(b)
    requires k in b.b;
    ensures Image(b, iset {k}).b.Keys == {k};
    ensures Image(b, iset {k}).b[k] == b.b[k];
  {
    reveal_Image();
  }

  lemma ImageSubset(b:Bucket, s:iset<Key>, t:iset<Key>)
    requires BucketWellMarshalled(b)
    requires s <= t;
    ensures Image(Image(b, t), s) == Image(b, s)
    ensures Image(b, s).b.Keys <= Image(b, t).b.Keys
  {
    reveal_Image();
  }

  lemma ImageIntersect(b:Bucket, s:iset<Key>, t:iset<Key>)
    requires BucketWellMarshalled(b)
    ensures Image(Image(b, s), t) == Image(b, s * t)
  {
    reveal_Image();
  }

  lemma MapRemoveVsImage(bucket:Bucket, ibk:iset<Key>, key:Key)
  requires BucketWellMarshalled(bucket)
  requires forall k :: k in bucket.b.Keys ==> k in ibk
  ensures MapRemove1(bucket.b, key) == Image(bucket, ibk - iset{key}).b
  {
    reveal_MapRemove1();
    reveal_Image();
  }

  lemma WeightBucketLinearInKeySetInner(bucket:Bucket, a:iset<Key>, b:iset<Key>)
  requires a !! b
  requires BucketWellMarshalled(bucket)
  requires forall k:Key :: k in bucket.b ==> k in a + b // a,b partition bucket
  requires Image(bucket, a).b.Keys != {} // So we can decrease
  requires Image(bucket, b).b.Keys != {} // So we can decrease
  requires |bucket.b| > 0 // So we can ChooseKey
  requires ChooseKey(bucket) in a
  ensures WeightBucket(bucket) == WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b))
  decreases |Image(bucket, a).b.Keys| + |Image(bucket, b).b.Keys|, 0
  {
    assume false;
    var key := ChooseKey(bucket);
    var msg := bucket.b[key];
    var residual := WeightKey(key) + WeightMessage(msg);

    calc {
      WeightBucket(Image(bucket, a));
        {
          var A := Image(bucket, a);
          var B := Image(A, a-iset{key});
          ImageSubset(bucket, a-iset{key}, a);
          ImageShape(bucket, a-iset{key});
          ImageShape(bucket, a);
          Sets.ProperSubsetImpliesSmallerCardinality(B.b.Keys, A.b.Keys);

          ImageShape(A, iset{key});
          Sets.SetInclusionImpliesSmallerCardinality(Image(A, iset{key}).b.Keys, {key});
          ImageShape(bucket, b);
          var kb :| kb in Image(bucket, b).b.Keys;
          Sets.SetInclusionImpliesSmallerCardinality({kb}, Image(bucket, b).b.Keys);

          WeightBucketLinearInKeySet(A, a-iset{key}, iset{key});
        }
      WeightBucket(Image(Image(bucket, a), a-iset{key})) + WeightBucket(Image(Image(bucket, a), iset{key}));
        {
          ImageSubset(bucket, a-iset{key}, a);
          ImageSubset(bucket, iset{key}, a);
        }
      WeightBucket(Image(bucket, a-iset{key})) + WeightBucket(Image(bucket, iset{key}));
        {
          ImageSingleton(bucket, key);
          WeightBucketSingleton(Image(bucket, iset{key}), key);
          assert Image(bucket, iset{key}).b[key] == bucket.b[key];
          assert WeightBucket(Image(bucket, iset{key})) == WeightKey(key) + WeightMessage(bucket.b[key]);
        }
      WeightBucket(Image(bucket, a-iset{key})) + residual;
    }
    calc {
      WeightBucket(bucket);
        { reveal_WeightBucket(); }
      WeightBucket(B(MapRemove1(bucket.b, key))) + residual;
        { MapRemoveVsImage(bucket, a+b, key); }
      WeightBucket(Image(bucket, (a+b)-iset{key})) + residual;
        { assert a+b-iset{key} == (a-iset{key})+b; }  // OSBERVE trigger
      WeightBucket(Image(bucket, (a-iset{key})+b)) + residual;
        {
          var A := Image(bucket, (a-iset{key})+b);
          var B := Image(A, a-iset{key});
          ImageSubset(bucket, a-iset{key}, (a-iset{key})+b);
          ImageShape(bucket, a-iset{key});
          ImageShape(bucket, a);
          Sets.ProperSubsetImpliesSmallerCardinality(B.b.Keys, Image(bucket, a).b.Keys);

          ImageSubset(bucket, b, (a-iset{key})+b);
          Sets.SetInclusionImpliesSmallerCardinality(
            Image(Image(bucket, (a-iset{key})+b), b).b.Keys, Image(bucket, b).b.Keys);

          ImageShape(bucket, (a-iset{key})+b); // propagate partition precondition
          WeightBucketLinearInKeySet(Image(bucket, (a-iset{key})+b), a-iset{key}, b);
        }
      WeightBucket(Image(Image(bucket, (a-iset{key})+b), a-iset{key})) + WeightBucket(Image(Image(bucket, (a-iset{key})+b), b)) + residual;
        { 
          ImageSubset(bucket, a-iset{key}, (a-iset{key})+b);
          ImageSubset(bucket, b, (a-iset{key})+b);
        }
      WeightBucket(Image(bucket, a-iset{key})) + WeightBucket(Image(bucket, b)) + residual;
        // upper calc
      WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b));
    }
  }

  lemma WeightBucketLinearInKeySet(bucket:Bucket, a:iset<Key>, b:iset<Key>)
  requires a !! b
  requires BucketWellMarshalled(bucket)
  requires forall k:Key :: k in bucket.b ==> k in a + b
  ensures WeightBucket(bucket) == WeightBucket(Image(bucket, a)) + WeightBucket(Image(bucket, b))
  decreases |Image(bucket, a).b.Keys| + |Image(bucket, b).b.Keys|, 1
  {
    assume false;
    ImageShape(bucket, a);
    ImageShape(bucket, b);
    WeightBucketEmpty();
    if |bucket.b| == 0 {
    } else if Image(bucket, a).b.Keys=={} {
      assert bucket == Image(bucket, b);  // trigger
    } else if Image(bucket, b).b.Keys=={} {
      assert bucket == Image(bucket, a);  // trigger
    } else {
      if ChooseKey(bucket) in a {
        WeightBucketLinearInKeySetInner(bucket, a, b);
      } else {
        WeightBucketLinearInKeySetInner(bucket, b, a);
      }
    }
  }

  // A variant that's handy if a+b don't cover bucket.
  lemma WeightBucketLinearInKeySetSum(bucket:Bucket, a:iset<Key>, b:iset<Key>)
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
  requires BucketWellMarshalled(bucket)
  {
    if key in bucket.b
      then WeightKey(key) + WeightMessage(bucket.b[key])
      else 0
  }

  lemma KeyContribution(bucket: Bucket, key: Key)
    requires BucketWellMarshalled(bucket)
    ensures WeightBucket(bucket) == WeightBucket(Image(bucket, ExcludeKey(key))) + WeightOneKey(bucket, key);
  {
    ImageIdentity(bucket, ExcludeKey(key) + IncludeKey(key));
    WeightBucketLinearInKeySetSum(bucket, ExcludeKey(key), IncludeKey(key));

    ImageShape(bucket, IncludeKey(key));
    if key in bucket.b {
      WeightBucketSingleton(Image(bucket, IncludeKey(key)), key);
    } else {
      WeightBucketEmpty();
    }
  }

  lemma WeightBucketInduct(bucket: Bucket, key: Key, msg: Message)
  requires BucketWellMarshalled(bucket)
  requires key !in bucket.b
  ensures WeightBucket(B(bucket.b[key := msg])) == WeightBucket(bucket) + WeightKey(key) + WeightMessage(msg)
  {
    assume false;
    KeyContribution(B(bucket.b[key := msg]), key);
    ImageShape(B(bucket.b[key := msg]), ExcludeKey(key));
    assert bucket == Image(B(bucket.b[key := msg]), ExcludeKey(key));
  }

  function ILeftKeys(pivot: Key) : iset<Key> { iset k | Keyspace.lt(k, pivot) }
  function IRightKeys(pivot: Key) : iset<Key> { iset k | Keyspace.lte(pivot, k) }

  lemma SplitBucketImage(bucket: Bucket, pivot: Key)
  requires BucketWellMarshalled(bucket)
  ensures SplitBucketLeft(bucket, pivot) == Image(bucket, ILeftKeys(pivot))
  ensures SplitBucketRight(bucket, pivot) == Image(bucket, IRightKeys(pivot))
  {
    assume false;
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    ImageShape(bucket, ILeftKeys(pivot));
    ImageShape(bucket, IRightKeys(pivot));
  }

  lemma WeightSplitBucketLeft(bucket: Bucket, pivot: Key)
  requires BucketWellMarshalled(bucket)
  ensures WeightBucket(SplitBucketLeft(bucket, pivot)) <= WeightBucket(bucket)
  {
    SplitBucketImage(bucket, pivot);
    WeightBucketLinearInKeySet(bucket, ILeftKeys(pivot), AllKeys() - ILeftKeys(pivot));
  }

  lemma WeightSplitBucketRight(bucket: Bucket, pivot: Key)
  requires BucketWellMarshalled(bucket)
  ensures WeightBucket(SplitBucketRight(bucket, pivot)) <= WeightBucket(bucket)
  {
    SplitBucketImage(bucket, pivot);
    WeightBucketLinearInKeySet(bucket, AllKeys() - IRightKeys(pivot), IRightKeys(pivot));
  }

  lemma WeightSplitBucketAdditive(bucket: Bucket, pivot: Key)
  requires BucketWellMarshalled(bucket)
  ensures WeightBucket(SplitBucketLeft(bucket, pivot)) +
          WeightBucket(SplitBucketRight(bucket, pivot)) == WeightBucket(bucket)
  {
    SplitBucketImage(bucket, pivot);
    WeightBucketLinearInKeySet(bucket, ILeftKeys(pivot), IRightKeys(pivot));
  }

  lemma WeightSplitBucketAdditiveLe(bucket: Bucket, pivot: Key)
  ensures WeightBucket(SplitBucketLeft(bucket, pivot)) +
          WeightBucket(SplitBucketRight(bucket, pivot)) <= WeightBucket(bucket)
  {
    assume false;
  }

  lemma WeightBucketList2(a: Bucket, b: Bucket)
  requires BucketWellMarshalled(a)
  requires BucketWellMarshalled(b)
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
  requires BucketWellMarshalled(extra)
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
    assume false;
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
    assume false;
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
  requires BucketWellMarshalled(parent)
  requires BucketListWellMarshalled(children)
  requires 0 <= i < |children|
  requires forall k :: k in filter ==> k == key   // filter admits at most one key
  ensures WeightBucket(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i))
    <= WeightBucket(Image(parent, RouteRange(pivots, i) * filter))
       + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter));
  {
    reveal_Image();

    var flush := BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i);
    if key in flush.b.Keys {
      WeightBucketSingleton(flush, key);
    } else {
      WeightBucketEmpty();
      assert flush.b == map[];
    }

    var filteredParent := Image(parent, RouteRange(pivots, i) * filter);
    if key in filteredParent.b {
      WeightBucketSingleton(filteredParent, key);
    } else {
      WeightBucketEmpty();
    }

    var filteredChild := Image(children[i], RouteRange(pivots, i) * filter);
    if key in filteredChild.b {
      WeightBucketSingleton(filteredChild, key);
    } else {
      WeightBucketEmpty();
    }

    if (key in filteredChild.b && key in filteredParent.b && key in flush.b) {
      // This is the only tricksy case, where we actually care how Merge
      // affects weights of the messages getting swapped.
      MergeGainsNoWeight(BucketGet(filteredParent, key), BucketGet(filteredChild, key));
    }
  }

  lemma WeightBucketFilterPartitions(bucket:Bucket, filter:iset<Key>, a:iset<Key>, b:iset<Key>)
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
  requires BucketWellMarshalled(parent)
  requires BucketListWellMarshalled(children)
  requires WFPivots(pivots)
  requires 0 <= i < |children|
  ensures
    WeightBucket(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i))
      <= WeightBucket(Image(parent, RouteRange(pivots, i) * filter)) + WeightBucket(Image(children[i], RouteRange(pivots, i) * filter))
  decreases |Image(parent, filter).b| + |Image(children[i], filter).b|
  {
    assume false;
    // Pick an arbitrary key to decrease by
    // (In Lisp, "car" is the first thing in a list, "cdr" is everything else.)
    var carKey;
    if |Image(parent, filter).b| != 0 {
      carKey :| carKey in Image(parent, filter).b;
    } else if |Image(children[i], filter).b| != 0 {
      carKey :| carKey in Image(children[i], filter).b;
    } else {
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
          assert Image(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), carFilter)
            == BucketListItemFlush(Image(parent, filter * carFilter), Image(children[i], filter * carFilter), pivots, i);
          assert Image(BucketListItemFlush(Image(parent, filter), Image(children[i], filter), pivots, i), cdrFilter)
            == BucketListItemFlush(Image(parent, filter * cdrFilter), Image(children[i], filter * cdrFilter), pivots, i);
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
  requires BucketWellMarshalled(parent)
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
  requires BucketWellMarshalled(parent)
  requires BucketListWellMarshalled(children)
  ensures WeightBucketList(BucketListFlushPartial(parent, children, pivots, items))
      <= WeightBucket(Image(parent, RouteRanges(pivots, items)))
        + WeightBucketList(children[..items])
  {
    assume false;
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
          assert Image(children[items - 1], RouteRange(pivots, items - 1)) == children[items-1]; // trigger
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
  requires WFBucketList(children, pivots)
  requires |children| == NumBuckets(pivots)
  requires BucketWellMarshalled(parent)
  requires BucketListWellMarshalled(children)
  ensures WeightBucketList(BucketListFlush(parent, children, pivots))
      <= WeightBucket(parent) + WeightBucketList(children)
  {
    assume false;
    WeightBucketListFlushPartial(parent, children, pivots, |children|);
    forall ensures Image(parent, RouteRanges(pivots, |children|)) == parent
    {
      reveal_Image();
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
  requires BucketListWellMarshalled(blist)
  ensures SplitBucketInList(MergeBucketsInList(blist, i), i, pivots[i]) == blist;
  {
    assume false;
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
          assert SplitBucketLeft(mbucket, pivots[i]) == blist[i];
          assert SplitBucketRight(mbucket, pivots[i]) == blist[i+1];
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
    assume false;
    MergeUndoesSplit(blist, pivots, i);
    WeightSplitBucketInList(MergeBucketsInList(blist, i), i, pivots[i]);
  }

  lemma WeightBucketSubset(bucket:Bucket, a:iset<Key>, b:iset<Key>)
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
  requires BucketListWellMarshalled(blist)
  ensures WeightBucket(JoinBucketList(blist)) <= WeightBucketList(blist)
  {
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
          { WeightBucketSingleton(Image(bucket, IncludeKey(key)), key); } // break key out of bucket
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
    assume false;
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
  requires WFBucketListProper(blist, pivots)
  requires BucketWellMarshalled(blist[Route(pivots, key)])
  ensures WeightBucketList(BucketListInsert(blist, pivots, key, msg)) <=
      WeightBucketList(blist) + WeightKey(key) + WeightMessage(msg)
  {
    assume false;
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
    assume false;
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
    assume false;
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
