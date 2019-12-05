include "BucketIterator.i.dfy"
//
// A mathematical description of bucket generators.
// It's like an iterator, but it doesn't directly refer to an actual bucket.
// The bucket may be implicit.
//

module BucketGenerator {
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences
  import opened BucketIterator
  import UI

  datatype Generator =
    | BasicGenerator(
        bucket: Bucket,
        it: Iterator
      )
    | MergeGenerator(
        top: Generator,
        bot: Generator,
        next: IteratorOutput
      )

  predicate WF(g: Generator)
  {
    && (g.BasicGenerator? ==> (
      && WFIter(g.bucket, g.it)
    ))
    && (g.MergeGenerator? ==> (
      && WF(g.top)
      && WF(g.bot)
    ))
  }

  function GenLeft(g: Generator) : (next : IteratorOutput)
  {
    match g {
      case BasicGenerator(bucket, it) => (
        g.it.next
      )
      case MergeGenerator(top, bot, next) => (
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
  requires g.MergeGenerator?
  decreases g, 0
  ensures WF(g')
  {
    var top := g.top;
    var bot := g.bot;
    if GenLeft(top).Next? && GenLeft(bot).Next?
        && GenLeft(top).key == GenLeft(bot).key then (
      MergeGenerator(
        GenPop(top),
        GenPop(bot),
        Next(GenLeft(top).key,
            Merge(GenLeft(top).msg, GenLeft(bot).msg)))
    ) else if GenLeft(top).Next?
        && (GenLeft(bot).Next? ==> Keyspace.lt(GenLeft(top).key, GenLeft(bot).key)) then (
      MergeGenerator(
        GenPop(top),
        bot,
        GenLeft(top))
    ) else if GenLeft(bot).Next? then (
      MergeGenerator(
        top,
        GenPop(bot),
        GenLeft(bot))
    ) else (
      MergeGenerator(
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
      case MergeGenerator(top, bot, next) => (
        MergeGenPop(g)
      )
    }
  }

  function {:opaque} GenLump(top: Generator, bot: Generator) : (g' : Generator)
  requires WF(top)
  requires WF(bot)
  ensures WF(g')
  {
    // Yeah this is basically duplicated with the above, but when I tried to factor
    // it out, I ran into weird interactions with decreases clauses.

    if GenLeft(top).Next? && GenLeft(bot).Next?
        && GenLeft(top).key == GenLeft(bot).key then (
      MergeGenerator(
        GenPop(top),
        GenPop(bot),
        Next(GenLeft(top).key,
            Merge(GenLeft(top).msg, GenLeft(bot).msg)))
    ) else if GenLeft(top).Next?
        && (GenLeft(bot).Next? ==> Keyspace.lt(GenLeft(top).key, GenLeft(bot).key)) then (
      MergeGenerator(
        GenPop(top),
        bot,
        GenLeft(top))
    ) else if GenLeft(bot).Next? then (
      MergeGenerator(
        top,
        GenPop(bot),
        GenLeft(bot))
    ) else (
      MergeGenerator(
        top,
        bot,
        Done)
    )
  }

  function {:opaque} GenFromBucketWithLowerBound(bucket: Bucket, start: UI.RangeStart) : (g : Generator)
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
  ensures WF(g)
  {
    if |buckets| == 1 then (
      GenFromBucketWithLowerBound(buckets[0], start)
    ) else (
      var mid := |buckets| / 2;
      GenLump(
        GenFromBucketStackWithLowerBound(buckets[..mid], start),
        GenFromBucketStackWithLowerBound(buckets[mid..], start)
      )
    )
  }

  // Characterizing what the generators return

  protected predicate Monotonic(g: Generator)
  {
    g.MergeGenerator? ==> (
      && (g.next.Next? && GenLeft(g.top).Next? ==> Keyspace.lt(g.next.key, GenLeft(g.top).key))
      && (g.next.Next? && GenLeft(g.bot).Next? ==> Keyspace.lt(g.next.key, GenLeft(g.bot).key))
      && (g.next.Done? ==> GenLeft(g.top).Done?)
      && (g.next.Done? ==> GenLeft(g.bot).Done?)
      && Monotonic(g.top)
      && Monotonic(g.bot)
    )
  }

  function {:opaque} BucketOf(g: Generator) : Bucket
  {
    match g {
      case BasicGenerator(bucket, it) =>
        if it.next.Done? then map[]
        else map k | k in bucket && Keyspace.lte(it.next.key, k) :: bucket[k]
      case MergeGenerator(top, bot, next) =>
        if next.Done? then map[]
        else Lump(BucketOf(top), BucketOf(bot))[next.key := next.msg]
    }
  }

  lemma reveal_BucketOf_for_Merge(g: Generator)
  ensures g.MergeGenerator? && g.next.Done? ==> BucketOf(g) == map[]
  ensures g.MergeGenerator? && g.next.Next? ==> BucketOf(g) ==
        Lump(BucketOf(g.top), BucketOf(g.bot))[g.next.key := g.next.msg]
  {
    reveal_BucketOf();
  }

  predicate YieldsSortedBucket(g: Generator, b: Bucket)
  {
    && WF(g)
    && Monotonic(g)
    && BucketOf(g) == b
  }

  lemma GenLeftIsMinimum(g: Generator)
  requires WF(g)
  requires Monotonic(g)
  ensures GenLeft(g).Done? ==> BucketOf(g) == map[]
  ensures GenLeft(g).Next? ==> Keyspace.minimumOpt(BucketOf(g).Keys) == Some(GenLeft(g).key)
  ensures GenLeft(g).Next? ==> BucketOf(g)[GenLeft(g).key] == GenLeft(g).msg
  {
    reveal_BucketOf();
    if GenLeft(g).Next? {
      if g.MergeGenerator? {
        reveal_Lump();
        GenLeftIsMinimum(g.top);
        GenLeftIsMinimum(g.bot);
        assert GenLeft(g).key in BucketOf(g);
        assert forall k | k in BucketOf(g) :: Keyspace.lte(GenLeft(g).key, k);
        assert Keyspace.minimumOpt(BucketOf(g).Keys) == Some(GenLeft(g).key);
      } else {
        assert GenLeft(g).key in BucketOf(g);
        assert forall k | k in BucketOf(g) :: Keyspace.lte(GenLeft(g).key, k);
        assert Keyspace.minimumOpt(BucketOf(g).Keys) == Some(GenLeft(g).key);
      }
    }
  }

  lemma GenPopIsRemove(g: Generator)
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
      var b2 := MapRemove1(BucketOf(g), Keyspace.minimum(BucketOf(g).Keys));
      forall k | k in b1 ensures k in b2 && b1[k] == b2[k]
      {
      }
      forall k | k in b2 ensures k in b1
      {
        noKeyBetweenIterAndIterInc(g.bucket, g.it, k);
      }
      assert b1 == b2;
    } else {
      reveal_Lump();
      reveal_MergeGenPop();

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
      assert YieldsSortedBucket(GenPop(g),
        MapRemove1(BucketOf(g), Keyspace.minimum(BucketOf(g).Keys)));
    }
  }

  lemma GenLumpIsMonotonic(top: Generator, bot: Generator)
  requires WF(top)
  requires WF(bot)
  requires Monotonic(top)
  requires Monotonic(bot)
  ensures Monotonic(GenLump(top, bot))
  {
    GenLeftIsMinimum(top);
    GenLeftIsMinimum(bot);
    reveal_BucketOf();

    reveal_GenLump();
    if (GenLeft(top).Next?) {
      GenPopIsRemove(top);
      assert GenLeft(top).key in BucketOf(top).Keys;
    }
    if (GenLeft(bot).Next?) {
      GenPopIsRemove(bot);
      assert GenLeft(bot).key in BucketOf(bot).Keys;
    }
  }

  lemma GenLumpIsLump(top: Generator, bot: Generator)
  requires WF(top)
  requires WF(bot)
  requires Monotonic(top)
  requires Monotonic(bot)
  ensures YieldsSortedBucket(GenLump(top, bot), Lump(BucketOf(top), BucketOf(bot)))
  {
    var g := GenLump(top, bot);

    GenLumpIsMonotonic(top, bot);
    reveal_Lump();
    reveal_GenLump();

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
          == Lump(BucketOf(top), BucketOf(bot));
    } else if GenLeft(top).Next?
        && (GenLeft(bot).Next? ==> Keyspace.lt(GenLeft(top).key, GenLeft(bot).key)) {
      assert BucketOf(g)
          == Lump(BucketOf(GenPop(top)), BucketOf(bot))
                [GenLeft(top).key := GenLeft(top).msg]
          == Lump(MapRemove1(BucketOf(top), GenLeft(top).key), BucketOf(bot))
                [GenLeft(top).key := GenLeft(top).msg]
          == Lump(BucketOf(top), BucketOf(bot));
    } else if GenLeft(bot).Next? {
      assert BucketOf(g)
          == Lump(BucketOf(top), MapRemove1(BucketOf(bot), GenLeft(bot).key))
                [GenLeft(bot).key := GenLeft(bot).msg]
          == Lump(BucketOf(top), BucketOf(bot));
    } else {
      assert BucketOf(g)
          == map[]
          == Lump(BucketOf(top), BucketOf(bot));
    }*/
  }

  lemma GenFromBucketWithLowerBoundYieldsClampStart(bucket: Bucket, start: UI.RangeStart)
  ensures var g := GenFromBucketWithLowerBound(bucket, start);
      YieldsSortedBucket(g, ClampStart(bucket, start))
  {
    reveal_GenFromBucketWithLowerBound();
    reveal_ClampStart();
    reveal_BucketOf();

    var g := GenFromBucketWithLowerBound(bucket, start);
    var b1 := BucketOf(g);
    var b2 := ClampStart(bucket, start);

    //forall k | k in b1 ensures k in b2 && b2[k] == b1[k]
    //{
    //}

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
  }

  lemma GenFromBucketStackWithLowerBoundYieldsLumpSeq(buckets: seq<Bucket>, start: UI.RangeStart)
  requires |buckets| >= 1
  ensures var g := GenFromBucketStackWithLowerBound(buckets, start);
      YieldsSortedBucket(g, ClampStart(LumpSeq(buckets), start))
  {
    reveal_GenFromBucketStackWithLowerBound();
    var g := GenFromBucketStackWithLowerBound(buckets, start);
    if |buckets| == 1 {
      LumpSeq1(buckets[0]);
      assert [buckets[0]] == buckets;
      GenFromBucketWithLowerBoundYieldsClampStart(buckets[0], start);
    } else {
      var mid := |buckets| / 2;
      var g1 := GenFromBucketStackWithLowerBound(buckets[..mid], start);
      var g2 := GenFromBucketStackWithLowerBound(buckets[mid..], start);
      GenLumpIsLump(g1, g2);
      calc {
        BucketOf(g);
          { GenLumpIsLump(g1, g2); }
        Lump(BucketOf(g1), BucketOf(g2));
          {
            GenFromBucketStackWithLowerBoundYieldsLumpSeq(buckets[..mid], start);
            GenFromBucketStackWithLowerBoundYieldsLumpSeq(buckets[mid..], start);
          }
        Lump(
          ClampStart(LumpSeq(buckets[..mid]), start), 
          ClampStart(LumpSeq(buckets[mid..]), start));
          {
            reveal_Lump();
            reveal_ClampStart();
          }
        ClampStart(Lump(LumpSeq(buckets[..mid]), LumpSeq(buckets[mid..])), start);
          { LumpSeqAdditive(buckets[..mid], buckets[mid..]); }
        ClampStart(LumpSeq(buckets[..mid] + buckets[mid..]), start);
          { assert buckets[..mid] + buckets[mid..] == buckets; }
        ClampStart(LumpSeq(buckets), start);
      }
    }
  }
}
