include "../lib/Buckets/BucketIteratorModel.i.dfy"
//
// A mathematical description of bucket generators.
// It's like an iterator, but it doesn't directly refer to an actual bucket.
// The bucket may be implicit.
//

module BucketGeneratorModel {
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Sequences
  import opened BucketIteratorModel
  import opened BucketMaps
  import opened KeyType
  import UI

  datatype Generator =
    | BasicGenerator(
        bucket: Bucket,
        it: Iterator
      )
    | ComposeGenerator(
        top: Generator,
        bot: Generator,
        next: IteratorOutput
      )

  predicate WF(g: Generator)
  {
    && (g.BasicGenerator? ==> (
      && WFBucket(g.bucket)
      && WFIter(g.bucket, g.it)
    ))
    && (g.ComposeGenerator? ==> (
      && WF(g.top)
      && WF(g.bot)
    ))
  }

  predicate WM(g: Generator)
  {
    && (g.BasicGenerator? ==> (
      && BucketWellMarshalled(g.bucket)
    ))
    && (g.ComposeGenerator? ==> (
      && WM(g.top)
      && WM(g.bot)
    ))
  }

  function GenLeft(g: Generator) : (next : IteratorOutput)
  {
    match g {
      case BasicGenerator(bucket, it) => (
        g.it.next
      )
      case ComposeGenerator(top, bot, next) => (
        g.next
      )
    }
  }

  function {:opaque} BasicGenPop(g: Generator) : (g' : Generator)
  requires WF(g)
  requires GenLeft(g).Next?
  requires g.BasicGenerator?
  decreases g, 0
  ensures WF(g')
  {
    BasicGenerator(
      g.bucket,
      IterInc(g.bucket, g.it))
  }

  function {:opaque} MergeGenPop(g: Generator) : (g' : Generator)
  requires WF(g)
  requires GenLeft(g).Next?
  requires g.ComposeGenerator?
  decreases g, 0
  ensures WF(g')
  {
    var top := g.top;
    var bot := g.bot;
    if GenLeft(top).Next? && GenLeft(bot).Next?
        && GenLeft(top).key == GenLeft(bot).key then (
      ComposeGenerator(
        GenPop(top),
        GenPop(bot),
        Next(GenLeft(top).key,
            Merge(GenLeft(top).msg, GenLeft(bot).msg)))
    ) else if GenLeft(top).Next?
        && (GenLeft(bot).Next? ==> lt(GenLeft(top).key, GenLeft(bot).key)) then (
      ComposeGenerator(
        GenPop(top),
        bot,
        GenLeft(top))
    ) else if GenLeft(bot).Next? then (
      ComposeGenerator(
        top,
        GenPop(bot),
        GenLeft(bot))
    ) else (
      ComposeGenerator(
        top,
        bot,
        Done)
    )
  }

  function {:opaque} GenPop(g: Generator) : (g' : Generator)
  requires WF(g)
  requires GenLeft(g).Next?
  decreases g, 1
  ensures WF(g')
  {
    match g {
      case BasicGenerator(bucket, it) => (
        BasicGenPop(g)
      )
      case ComposeGenerator(top, bot, next) => (
        MergeGenPop(g)
      )
    }
  }

  function {:opaque} GenCompose(top: Generator, bot: Generator) : (g' : Generator)
  requires WF(top)
  requires WF(bot)
  ensures WF(g')
  {
    // Yeah this is basically duplicated with the above, but when I tried to factor
    // it out, I ran into weird interactions with decreases clauses.

    if GenLeft(top).Next? && GenLeft(bot).Next?
        && GenLeft(top).key == GenLeft(bot).key then (
      ComposeGenerator(
        GenPop(top),
        GenPop(bot),
        Next(GenLeft(top).key,
            Merge(GenLeft(top).msg, GenLeft(bot).msg)))
    ) else if GenLeft(top).Next?
        && (GenLeft(bot).Next? ==> lt(GenLeft(top).key, GenLeft(bot).key)) then (
      ComposeGenerator(
        GenPop(top),
        bot,
        GenLeft(top))
    ) else if GenLeft(bot).Next? then (
      ComposeGenerator(
        top,
        GenPop(bot),
        GenLeft(bot))
    ) else (
      ComposeGenerator(
        top,
        bot,
        Done)
    )
  }

  function {:opaque} GenFromBucketWithLowerBound(bucket: Bucket, start: UI.RangeStart) : (g : Generator)
  requires WFBucket(bucket)
  ensures WF(g)
  {
    var it := match start {
      case SExclusive(key) => IterFindFirstGt(bucket, key)
      case SInclusive(key) => IterFindFirstGte(bucket, key)
      case NegativeInf => IterStart(bucket)
    };
    BasicGenerator(bucket, it)
  }

  function {:opaque} GenFromBucketStackWithLowerBound(buckets: seq<Bucket>, start: UI.RangeStart) : (g : Generator)
  requires |buckets| >= 1
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  decreases |buckets|
  ensures WF(g)
  {
    if |buckets| == 1 then (
      GenFromBucketWithLowerBound(buckets[0], start)
    ) else (
      GenCompose(
        GenFromBucketStackWithLowerBound(DropLast(buckets), start),
        GenFromBucketStackWithLowerBound([Last(buckets)], start)
      )
    )
  }

  // Characterizing what the generators return

  predicate {:opaque} Monotonic(g: Generator)
  {
    g.ComposeGenerator? ==> (
      && (g.next.Next? && GenLeft(g.top).Next? ==> lt(g.next.key, GenLeft(g.top).key))
      && (g.next.Next? && GenLeft(g.bot).Next? ==> lt(g.next.key, GenLeft(g.bot).key))
      && (g.next.Done? ==> GenLeft(g.top).Done?)
      && (g.next.Done? ==> GenLeft(g.bot).Done?)
      && Monotonic(g.top)
      && Monotonic(g.bot)
    )
  }

  function {:opaque} BucketOf(g: Generator) : BucketMap
  requires WF(g)
  {
    match g {
      case BasicGenerator(bucket, it) =>
        if it.next.Done? then map[]
        else map k | k in bucket.as_map() && lte(it.next.key, k) :: bucket.as_map()[k]
      case ComposeGenerator(top, bot, next) =>
        if next.Done? then map[]
        else Compose(BucketOf(top), BucketOf(bot))[next.key := next.msg]
    }
  }

  // like reveal_BucketOf but only takes a single argument
  lemma reveal_BucketOf_for_Merge(g: Generator)
  requires WF(g)
  ensures g.ComposeGenerator? && g.next.Done? ==> BucketOf(g) == map[]
  ensures g.ComposeGenerator? && g.next.Next? ==> BucketOf(g) ==
        Compose(BucketOf(g.top), BucketOf(g.bot))[g.next.key := g.next.msg]
  {
    reveal_BucketOf();
  }

  predicate YieldsSortedBucket(g: Generator, b: BucketMap)
  {
    && WF(g)
    && WM(g)
    && Monotonic(g)
    && BucketOf(g) == b
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

  lemma GenLeftIsMinimum(g: Generator)
  requires WM(g)
  requires WF(g)
  requires Monotonic(g)
  ensures GenLeft(g).Done? ==> BucketOf(g) == map[]
  ensures GenLeft(g).Next? ==> minimumKey(BucketOf(g).Keys) == Some(GenLeft(g).key)
  ensures GenLeft(g).Next? ==> BucketOf(g)[GenLeft(g).key] == GenLeft(g).msg
  {
    reveal_BucketOf();
    if GenLeft(g).Next? {
      if g.ComposeGenerator? {
        reveal_Compose();
        assert Monotonic(g.top) by { reveal_Monotonic(); }
        assert Monotonic(g.bot) by { reveal_Monotonic(); }
        GenLeftIsMinimum(g.top);
        GenLeftIsMinimum(g.bot);
        assert GenLeft(g).key in BucketOf(g);
        assert forall k | k in BucketOf(g) :: lte(GenLeft(g).key, k) by {
          reveal_Monotonic();
        }
        assert minimumKey(BucketOf(g).Keys) == Some(GenLeft(g).key);
      } else {
        assert GenLeft(g).key in BucketOf(g);
        assert forall k | k in BucketOf(g) :: lte(GenLeft(g).key, k);
        assert minimumKey(BucketOf(g).Keys) == Some(GenLeft(g).key);
      }
    }
  }

  lemma GenPopIsRemove(g: Generator)
  requires WM(g)
  requires WF(g)
  requires Monotonic(g)
  requires GenLeft(g).Next?
  ensures |BucketOf(g).Keys| >= 1
  ensures YieldsSortedBucket(GenPop(g),
      MapRemove1(BucketOf(g), Keyspace.minimum(BucketOf(g).Keys)))
  {
    reveal_BucketOf();
    var g' := GenPop(g);

    GenLeftIsMinimum(g);
    reveal_GenPop();

    if g.BasicGenerator? {
      reveal_BasicGenPop();
      IterIncKeyGreater(g.bucket, g.it);

      var b1 := BucketOf(g');
      var b2 := MapRemove1(BucketOf(g), minimum(BucketOf(g).Keys));
      forall k | k in b1 ensures k in b2 && b1[k] == b2[k]
      {
      }
      forall k | k in b2 ensures k in b1
      {
        noKeyBetweenIterAndIterInc(g.bucket, g.it, k);
      }
      assert b1 == b2;

      assert Monotonic(GenPop(g)) by { reveal_Monotonic(); }
    } else {
      assert g.ComposeGenerator?;
      reveal_Compose();
      reveal_MergeGenPop();

      assert Monotonic(g.top) by { reveal_Monotonic(); }
      assert Monotonic(g.bot) by { reveal_Monotonic(); }
      GenLeftIsMinimum(g.top);
      GenLeftIsMinimum(g.bot);

      if (GenLeft(g.top).Next?) {
        GenPopIsRemove(g.top);
        assert GenLeft(g.top).key in BucketOf(g.top).Keys;
      }
      if (GenLeft(g.bot).Next?) {
        GenPopIsRemove(g.bot);
        assert GenLeft(g.bot).key in BucketOf(g.bot).Keys;
      }

      assert Monotonic(GenPop(g)) by {
        reveal_Monotonic();
      }

      assert GenPop(g).ComposeGenerator?;
      calc {
        BucketOf(GenPop(g));
        {
          assert
            && (g.next.Next? && GenLeft(g.top).Next? ==> lt(g.next.key, GenLeft(g.top).key))
            && (g.next.Next? && GenLeft(g.bot).Next? ==> lt(g.next.key, GenLeft(g.bot).key)) by {
            reveal_Monotonic();
          }
        }
        MapRemove1(BucketOf(g), minimum(BucketOf(g).Keys));
      }
      assert YieldsSortedBucket(GenPop(g),
        MapRemove1(BucketOf(g), minimum(BucketOf(g).Keys)));
    }
  }

  lemma GenComposeIsMonotonic(top: Generator, bot: Generator)
  requires WF(top)
  requires WF(bot)
  requires WM(top)
  requires WM(bot)
  requires Monotonic(top)
  requires Monotonic(bot)
  ensures Monotonic(GenCompose(top, bot))
  {
    GenLeftIsMinimum(top);
    GenLeftIsMinimum(bot);
    reveal_BucketOf();

    reveal_GenCompose();
    if (GenLeft(top).Next?) {
      GenPopIsRemove(top);
      assert GenLeft(top).key in BucketOf(top).Keys;
    }
    if (GenLeft(bot).Next?) {
      GenPopIsRemove(bot);
      assert GenLeft(bot).key in BucketOf(bot).Keys;
    }
    assert Monotonic(GenCompose(top, bot)) by {
      reveal_Monotonic();
    }
  }

  lemma GenComposeIsCompose(top: Generator, bot: Generator)
  requires WF(top)
  requires WF(bot)
  requires WM(top)
  requires WM(bot)
  requires Monotonic(top)
  requires Monotonic(bot)
  ensures YieldsSortedBucket(GenCompose(top, bot), Compose(BucketOf(top), BucketOf(bot)))
  {
    var g := GenCompose(top, bot);

    GenComposeIsMonotonic(top, bot);
    reveal_Compose();
    reveal_GenCompose();

    GenLeftIsMinimum(top);
    GenLeftIsMinimum(bot);

    if (GenLeft(top).Next?) {
      GenPopIsRemove(top);
    }
    if (GenLeft(bot).Next?) {
      GenPopIsRemove(bot);
    }

    // Calling reveal_BucketOf() causes a trigger-loop for some reason
    reveal_BucketOf_for_Merge(g);

    /*if GenLeft(top).Next? && GenLeft(bot).Next?
        && GenLeft(top).key == GenLeft(bot).key {
      assert BucketOf(g)
          == Compose(BucketOf(top), BucketOf(bot));
    } else if GenLeft(top).Next?
        && (GenLeft(bot).Next? ==> Keyspace.lt(GenLeft(top).key, GenLeft(bot).key)) {
      assert BucketOf(g)
          == Compose(BucketOf(GenPop(top)), BucketOf(bot))
                [GenLeft(top).key := GenLeft(top).msg]
          == Compose(MapRemove1(BucketOf(top), GenLeft(top).key), BucketOf(bot))
                [GenLeft(top).key := GenLeft(top).msg]
          == Compose(BucketOf(top), BucketOf(bot));
    } else if GenLeft(bot).Next? {
      assert BucketOf(g)
          == Compose(BucketOf(top), MapRemove1(BucketOf(bot), GenLeft(bot).key))
                [GenLeft(bot).key := GenLeft(bot).msg]
          == Compose(BucketOf(top), BucketOf(bot));
    } else {
      assert BucketOf(g)
          == map[]
          == Compose(BucketOf(top), BucketOf(bot));
    }*/
  }

  lemma GenFromBucketWithLowerBoundYieldsClampStart(bucket: Bucket, start: UI.RangeStart)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  ensures var g := GenFromBucketWithLowerBound(bucket, start);
      YieldsSortedBucket(g, ClampStart(bucket.as_map(), start))
  {
    reveal_GenFromBucketWithLowerBound();
    reveal_ClampStart();
    reveal_BucketOf();

    var g := GenFromBucketWithLowerBound(bucket, start);
    var b1 := BucketOf(g);
    var b2 := ClampStart(bucket.as_map(), start);

    forall k | k in b2 ensures k in b1
    {
      match start {
        case SExclusive(key) => {
          noKeyBetweenIterFindFirstGt(bucket, key, k);
        }
        case SInclusive(key) => {
          noKeyBetweenIterFindFirstGte(bucket, key, k);
        }
        case NegativeInf => {
          noKeyBeforeIterStart(bucket, k);
        }
      }
    }

    assert YieldsSortedBucket(g, ClampStart(bucket.as_map(), start)) by {
      reveal_Monotonic();
    }
  }

  lemma GenFromBucketStackWithLowerBoundYieldsComposeSeq(buckets: seq<Bucket>, start: UI.RangeStart)
  requires |buckets| >= 1
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  requires BucketListWellMarshalled(buckets)
  ensures var g := GenFromBucketStackWithLowerBound(buckets, start);
      && YieldsSortedBucket(g, ClampStart(ComposeSeq(MapsOfBucketList(buckets)), start))
  decreases |buckets|
  {
    reveal_GenFromBucketStackWithLowerBound();
    var g := GenFromBucketStackWithLowerBound(buckets, start);
    if |buckets| == 1 {
      assert BucketWellMarshalled(buckets[0]);
      reveal_GenFromBucketWithLowerBound();
      assert WM(g);

      ComposeSeq1(buckets[0].as_map());
      assert [buckets[0]] == buckets;
      assert WFBucket(buckets[0]);
      /*assert WFBucket(ComposeSeq([buckets[0].as_map()])) by {
        reveal_ComposeSeq();
        reveal_Compose();
      }*/
      GenFromBucketWithLowerBoundYieldsClampStart(buckets[0], start);
      //WellMarshalledBucketsEq(ComposeSeq([buckets[0]]), buckets[0]);
      assert MapsOfBucketList(buckets) == [buckets[0].as_map()];
    } else {
      var g1 := GenFromBucketStackWithLowerBound(DropLast(buckets), start);
      var g2 := GenFromBucketStackWithLowerBound([Last(buckets)], start);
      assert WM(g1);
      assert WM(g2) by { GenFromBucketStackWithLowerBoundYieldsComposeSeq([Last(buckets)], start); }
      GenComposeIsCompose(g1, g2);
      var bucketMaps := MapsOfBucketList(buckets);
      calc {
        BucketOf(g);
          { GenComposeIsCompose(g1, g2); }
        Compose(BucketOf(g1), BucketOf(g2));
          {
            GenFromBucketStackWithLowerBoundYieldsComposeSeq(DropLast(buckets), start);
            GenFromBucketStackWithLowerBoundYieldsComposeSeq([Last(buckets)], start);
            reveal_Compose();
          }
        Compose(
          ClampStart(ComposeSeq(MapsOfBucketList(DropLast(buckets))), start), 
          ClampStart(ComposeSeq(MapsOfBucketList([Last(buckets)])), start));
        {
            assert MapsOfBucketList([Last(buckets)]) == [Last(bucketMaps)];
            assert MapsOfBucketList(DropLast(buckets)) == DropLast(bucketMaps);
        }
        Compose(
          ClampStart(ComposeSeq(DropLast(bucketMaps)), start), 
          ClampStart(ComposeSeq([Last(bucketMaps)]), start));
          {
            reveal_Compose();
            reveal_ClampStart();
          }
        ClampStart(Compose(ComposeSeq(DropLast(bucketMaps)), ComposeSeq([Last(bucketMaps)])), start);
          {
            ComposeSeqAdditive(DropLast(bucketMaps), [Last(bucketMaps)]);
            reveal_ClampStart();
          }
        ClampStart(ComposeSeq(DropLast(bucketMaps) + [Last(bucketMaps)]), start);
          { assert DropLast(bucketMaps) + [Last(bucketMaps)] == bucketMaps; }
        ClampStart(ComposeSeq(bucketMaps), start);
      }
    }
  }

  ////// For termination

  function {:opaque} decreaser(g: Generator) : nat
  requires WF(g)
  {
    match g {
      case BasicGenerator(bucket, it) => (
        it.decreaser
      )
      case ComposeGenerator(top, bot, next) => (
        decreaser(top) + decreaser(bot) + (if next.Next? then 1 else 0)
      )
    }
  }

  lemma lemmaDecreaserDecreases(g: Generator)
  requires WF(g)
  ensures GenLeft(g).Next? ==> decreaser(GenPop(g)) < decreaser(g)
  {
    reveal_GenPop();
    reveal_MergeGenPop();
    reveal_BasicGenPop();
    reveal_decreaser();
    if g.ComposeGenerator? {
      lemmaDecreaserDecreases(g.top);
      lemmaDecreaserDecreases(g.bot);
    }
  }
}
