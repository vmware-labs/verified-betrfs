include "KVList.i.dfy"
include "KVListPartialFlush.i.dfy"

module KMTable {
  import KVList
  import KVListPartialFlush
  import opened ValueMessage`Internal
  import opened Lexicographic_Byte_Order
  import opened Sequences
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened Bounds
  import opened BucketWeights
  import opened NativeTypes
  import Native
  import Pivots = PivotsLib

  type Key = Element
  type Kvl = KVList.Kvl

  datatype KMT = KMT(kvl: Kvl, weight: uint64)

	export S provides WF, I, ISeq, flush, Flush, partialFlush, partialFlushRes, PartialFlush, Query, splitLeft, SplitLeft, splitRight, SplitRight, splitKMTInList, SplitKMTInList, join, Join, splitOnPivots, SplitOnPivots, KMT, computeWeightKMTSeq, computeWeightKMT, kmtOfSeq, kmtOfSeqRes, KmtOfSeq, Empty, WFImpliesWFBucket, Islice, Isuffix, IPopBack, IPopFront,
	    BucketsLib, ValueMessage, Options, NativeTypes, BucketWeights, Pivots, Bounds, Lexicographic_Byte_Order
	    reveals Key
	export Internal reveals *
	export extends S

  predicate WF(kmt: KMT)
  {
    && KVList.WF(kmt.kvl)
    && kmt.weight as int == WeightBucket(KVList.I(kmt.kvl))
  }

  function I(kmt: KMT) : Bucket
  requires WF(kmt)
  {
    KVList.I(kmt.kvl)
  }

  function {:opaque} ISeq(kmts: seq<KMT>) : (s : seq<Bucket>)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures |s| == |kmts|
  ensures forall i | 0 <= i < |kmts| :: s[i] == I(kmts[i])
  {
    if |kmts| == 0 then [] else ISeq(DropLast(kmts)) + [I(Last(kmts))]
  }

  function toKmt(kvl: Kvl) : KMT
  requires KVList.WF(kvl)
  requires WeightBucket(KVList.I(kvl)) < 0x1_0000_0000_0000_0000
  {
    KMT(kvl, WeightBucket(KVList.I(kvl)) as uint64)
  }

  function toKmtSeq(kvls: seq<Kvl>) : (kmts : seq<KMT>)
  requires forall i | 0 <= i < |kvls| :: KVList.WF(kvls[i])
  requires forall i | 0 <= i < |kvls| :: WeightBucket(KVList.I(kvls[i])) < 0x1_0000_0000_0000_0000
  ensures |kvls| == |kmts|
  ensures forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |kmts| :: kvls[i] == kmts[i].kvl
  {
    if |kvls| == 0 then [] else toKmtSeq(DropLast(kvls)) + [toKmt(Last(kvls))]
  }

  function toKvlSeq(kmts: seq<KMT>) : (kvls: seq<Kvl>)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |kvls| :: KVList.WF(kvls[i])
  ensures |kvls| == |kmts|
  ensures forall i | 0 <= i < |kmts| :: kvls[i] == kmts[i].kvl
  {
    if |kmts| == 0 then [] else toKvlSeq(DropLast(kmts)) + [Last(kmts).kvl]
  }

  lemma seqLemmaToKvl(kmts: seq<KMT>)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq(kmts) == KVList.ISeq(toKvlSeq(kmts))

  lemma seqLemmaToKMT(kvls: seq<Kvl>)
  requires toKmtSeq.requires(kvls)
  ensures ISeq(toKmtSeq(kvls)) == KVList.ISeq(kvls)

  lemma weightsInSeq(kvls: seq<Kvl>)
  requires forall i | 0 <= i < |kvls| :: KVList.WF(kvls[i])
  requires WeightBucketList(KVList.ISeq(kvls)) < 0x1_0000_0000_0000_0000
  ensures forall i | 0 <= i < |kvls| :: WeightBucket(KVList.I(kvls[i])) < 0x1_0000_0000_0000_0000

  method ToKmt(kvl: Kvl) returns (kmt : KMT)
  requires toKmt.requires(kvl)
  ensures kmt == toKmt(kvl)
  {
    var w := KVList.computeWeightKvl(kvl);
    kmt := KMT(kvl, w);
  }

  method ToKmtSeq(kvls: seq<Kvl>) returns (kmts : seq<KMT>)
  requires toKmtSeq.requires(kvls)
  ensures kmts == toKmtSeq(kvls)
  {
    assume false;
    var ar := new KMT[|kvls| as uint64];
    var j: uint64 := 0;
    while j < |kvls| as uint64 {
      ar[j] := ToKmt(kvls[j]);
      j := j + 1;
    }
    kmts := ar[..];
  }

  method ToKvlSeq(kmts: seq<KMT>) returns (kvls: seq<Kvl>)
  requires toKvlSeq.requires(kmts)
  ensures kvls == toKvlSeq(kmts)
  {
    assume false;
    var ar := new Kvl[|kmts| as uint64];
    var j: uint64 := 0;
    while j < |kmts| as uint64 {
      ar[j] := kmts[j].kvl;
      j := j + 1;
    }
    kvls := ar[..];
  }

  function flush(parent: KMT, children: seq<KMT>, pivots: seq<Key>) : (newChildren : seq<KMT>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires WFBucketList(ISeq(children), pivots)
  requires |pivots| + 1 == |children|
  requires WeightBucket(I(parent)) + WeightBucketList(ISeq(children)) < 0x8000_0000_0000_0000
  requires |children| < 0x1_0000_0000_0000_0000
  ensures forall i | 0 <= i < |newChildren| :: WF(newChildren[i])
  ensures ISeq(newChildren) == BucketListFlush(I(parent), ISeq(children), pivots)
  {
    KVList.flushRes(parent.kvl, toKvlSeq(children), pivots);
    WeightBucketListFlush(I(parent), ISeq(children), pivots);
    seqLemmaToKvl(children);
    weightsInSeq(KVList.flush(parent.kvl, toKvlSeq(children), pivots));

    toKmtSeq(KVList.flush(parent.kvl, toKvlSeq(children), pivots))
  }

  method Flush(parent: KMT, children: seq<KMT>, pivots: seq<Key>) returns (newChildren : seq<KMT>)
  requires flush.requires(parent, children, pivots)
  ensures newChildren == flush(parent, children, pivots)
  {
    KVList.flushRes(parent.kvl, toKvlSeq(children), pivots);
    WeightBucketListFlush(I(parent), ISeq(children), pivots);
    seqLemmaToKvl(children);
    weightsInSeq(KVList.flush(parent.kvl, toKvlSeq(children), pivots));

    forall i | 0 <= i < |children| ensures |children[i].kvl.keys| + |parent.kvl.keys| < 0x8000_0000_0000_0000
    {
      KVList.lenKeysLeWeight(children[i].kvl);
      KVList.lenKeysLeWeight(parent.kvl);
      WeightBucketLeBucketList(ISeq(children), i);
    }

    var kvlChildren := ToKvlSeq(children);
    var f := KVList.Flush(parent.kvl, kvlChildren, pivots);
    newChildren := ToKmtSeq(f);
  }

  lemma partialFlushRes_(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  requires KVList.WF(parent)
  requires Pivots.WFPivots(pivots)
  requires forall i | 0 <= i < |children| :: KVList.WF(children[i])
  requires |pivots| + 1 == |children|
  requires WeightBucketList(KVList.ISeq(children)) <= MaxTotalBucketWeight()
  ensures var (newParent, newChildren) := KVListPartialFlush.partialFlush(parent, children, pivots);
      && KVList.WF(newParent)
      && (forall i | 0 <= i < |newChildren| :: KVList.WF(newChildren[i]))
      && WeightBucket(KVList.I(newParent)) <= WeightBucket(KVList.I(parent))
      && WeightBucketList(KVList.ISeq(newChildren)) <= MaxTotalBucketWeight()
  {
    var _ := KVListPartialFlush.partialFlushRes(parent, children, pivots);
  }

  function partialFlush(parent: KMT, children: seq<KMT>, pivots: seq<Key>) : (KMT, seq<KMT>)
  requires WF(parent)
  requires Pivots.WFPivots(pivots)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  requires |children| <= MaxNumChildren()
  requires WeightBucket(I(parent)) <= MaxTotalBucketWeight()
  requires WeightBucketList(ISeq(children)) <= MaxTotalBucketWeight()
  {
    seqLemmaToKvl(children);
    partialFlushRes_(parent.kvl, toKvlSeq(children), pivots);
    WeightBucketListFlush(I(parent), ISeq(children), pivots);

    var (kvlNewParent, kvlNewChildren) := KVListPartialFlush.partialFlush(parent.kvl, toKvlSeq(children), pivots);

    weightsInSeq(kvlNewChildren);

    (toKmt(kvlNewParent), toKmtSeq(kvlNewChildren))
  }

  lemma partialFlushRes(parent: KMT, children: seq<KMT>, pivots: seq<Key>)
  returns (flushedKeys: set<Key>)
  requires partialFlush.requires(parent, children, pivots);
  ensures var (newParent, newChildren) := partialFlush(parent, children, pivots);
      && WF(newParent)
      && (forall i | 0 <= i < |newChildren| :: WF(newChildren[i]))
      && I(newParent) == BucketComplement(I(parent), flushedKeys)
      && ISeq(newChildren) == BucketListFlush(BucketIntersect(I(parent), flushedKeys), ISeq(children), pivots)
      && WeightBucket(I(newParent)) <= WeightBucket(I(parent))
      && WeightBucketList(ISeq(newChildren)) <= MaxTotalBucketWeight()
  {
    seqLemmaToKvl(children);
    partialFlushRes_(parent.kvl, toKvlSeq(children), pivots);
    WeightBucketListFlush(I(parent), ISeq(children), pivots);

    flushedKeys := KVListPartialFlush.partialFlushRes(parent.kvl, toKvlSeq(children), pivots);
  }

  method PartialFlush(parent: KMT, children: seq<KMT>, pivots: seq<Key>)
  returns (newParent: KMT, newChildren: seq<KMT>)
  requires partialFlush.requires(parent, children, pivots);
  ensures (newParent, newChildren) == partialFlush(parent, children, pivots)
  {
    seqLemmaToKvl(children);
    partialFlushRes_(parent.kvl, toKvlSeq(children), pivots);
    WeightBucketListFlush(I(parent), ISeq(children), pivots);

    var kvlChildren := ToKvlSeq(children);
    var kvlNewParent, kvlNewChildren := KVListPartialFlush.PartialFlush(parent.kvl, kvlChildren, pivots);

    weightsInSeq(kvlNewChildren);

    newParent := ToKmt(kvlNewParent);
    newChildren := ToKmtSeq(kvlNewChildren);
  }

  method Query(kmt: KMT, key: Key) returns (m: Option<Message>)
  requires WF(kmt)
  ensures m.None? ==> key !in I(kmt)
  ensures m.Some? ==> key in I(kmt) && I(kmt)[key] == m.value
  {
    KVList.lenKeysLeWeightOver8(kmt.kvl);
    m := KVList.Query(kmt.kvl, key);
  }

  function splitLeft(kmt: KMT, pivot: Key) : (left : KMT)
  requires WF(kmt)
  ensures WF(left)
  ensures I(left) == SplitBucketLeft(I(kmt), pivot)
  ensures left == splitLeft(kmt, pivot)
  {
    KVList.splitLeftCorrect(kmt.kvl, pivot);
    WeightSplitBucketLeft(I(kmt), pivot);
    toKmt(KVList.splitLeft(kmt.kvl, pivot))
  }

  method SplitLeft(kmt: KMT, pivot: Key) returns (left : KMT)
  requires splitLeft.requires(kmt, pivot)
  ensures left == splitLeft(kmt, pivot)
  {
    KVList.splitLeftCorrect(kmt.kvl, pivot);
    WeightSplitBucketLeft(I(kmt), pivot);
    KVList.lenKeysLeWeightOver8(kmt.kvl);
    var kvlLeft := KVList.SplitLeft(kmt.kvl, pivot);
    left := ToKmt(kvlLeft);
  }

  function splitRight(kmt: KMT, pivot: Key) : (right : KMT)
  requires WF(kmt)
  ensures WF(right)
  ensures I(right) == SplitBucketRight(I(kmt), pivot)
  ensures right == splitRight(kmt, pivot)
  {
    KVList.splitRightCorrect(kmt.kvl, pivot);
    WeightSplitBucketRight(I(kmt), pivot);
    toKmt(KVList.splitRight(kmt.kvl, pivot))
  }

  method SplitRight(kmt: KMT, pivot: Key) returns (right : KMT)
  requires splitRight.requires(kmt, pivot)
  ensures right == splitRight(kmt, pivot)
  {
    KVList.splitRightCorrect(kmt.kvl, pivot);
    WeightSplitBucketRight(I(kmt), pivot);
    KVList.lenKeysLeWeightOver8(kmt.kvl);
    var kvlRight := KVList.SplitRight(kmt.kvl, pivot);
    right := ToKmt(kvlRight);
  }

  lemma splitSmallBucket(buckets: seq<KMT>, slot: uint64, pivot: Key)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot as int < |buckets|
  ensures
    var kvls := KVList.splitKvlInList(toKvlSeq(buckets), slot as int, pivot);
    && (forall i | 0 <= i < |kvls| :: KVList.WF(kvls[i]))
    && (forall i | 0 <= i < |kvls| :: WeightBucket(KVList.I(kvls[i])) < 0x1_0000_0000_0000_0000)

  function splitKMTInList(buckets: seq<KMT>, slot: uint64, pivot: Key) : (buckets' : seq<KMT>)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot as int < |buckets|
  ensures |buckets'| == |buckets| + 1
  ensures (forall i | 0 <= i < |buckets'| :: WF(buckets'[i]))
  ensures (ISeq(buckets') == SplitBucketInList(ISeq(buckets), slot as int, pivot))
  {
    KVList.splitKvlInListCorrect(toKvlSeq(buckets), slot as int, pivot);
    seqLemmaToKvl(buckets);
    splitSmallBucket(buckets, slot, pivot);

    toKmtSeq(KVList.splitKvlInList(toKvlSeq(buckets), slot as int, pivot))
  }

  method SplitKMTInList(buckets: seq<KMT>, slot: uint64, pivot: Key) returns (buckets' : seq<KMT>)
  requires splitKMTInList.requires(buckets, slot, pivot)
  ensures buckets' == splitKMTInList(buckets, slot, pivot)
  {
    KVList.splitKvlInListCorrect(toKvlSeq(buckets), slot as int, pivot);
    seqLemmaToKvl(buckets);
    splitSmallBucket(buckets, slot, pivot);
    
    var kvlBuckets := ToKvlSeq(buckets);
    KVList.lenKeysLeWeightOver8(kvlBuckets[slot]);
    var kvlBuckets' := KVList.SplitKvlInList(kvlBuckets, slot as int, pivot);
    buckets' := ToKmtSeq(kvlBuckets');
  }

  function join(kmts: seq<KMT>, pivots: seq<Key>) : (kmt: KMT)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  requires WFBucketList(ISeq(kmts), pivots)
  requires WeightBucketList(ISeq(kmts)) <= MaxTotalBucketWeight()
  requires |kmts| < 0x8000_0000
  ensures WF(kmt)
  ensures I(kmt) == JoinBucketList(ISeq(kmts))
  {
    KVList.joinEqJoinBucketList(toKvlSeq(kmts), pivots);
    seqLemmaToKvl(kmts);
    WeightJoinBucketList(ISeq(kmts));
    toKmt(KVList.join(toKvlSeq(kmts)))
  }

  method Join(kmts: seq<KMT>, ghost pivots: seq<Key>)
  returns (kmt: KMT)
  requires join.requires(kmts, pivots)
  ensures kmt == join(kmts, pivots)
  {
    KVList.joinEqJoinBucketList(toKvlSeq(kmts), pivots);
    seqLemmaToKvl(kmts);
    WeightJoinBucketList(ISeq(kmts));
    
    var kvls := ToKvlSeq(kmts);

    forall i | 0 <= i < |kvls| ensures |kvls[i].keys| < 0x1_0000_0000
    {
      WeightBucketLeBucketList(ISeq(kmts), i);
      KVList.lenKeysLeWeightOver8(kvls[i]);
    }

    var kvl := KVList.Join(kvls, pivots);
    kmt := ToKmt(kvl);
  }

  lemma splitResultSmall(kmt: KMT, pivots: seq<Key>)
  requires WF(kmt)
  requires Pivots.WFPivots(pivots)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  ensures
    var kvls := KVList.splitOnPivots(kmt.kvl, pivots);
    && (forall i | 0 <= i < |kvls| :: KVList.WF(kvls[i]))
    && (forall i | 0 <= i < |kvls| :: WeightBucket(KVList.I(kvls[i])) < 0x1_0000_0000_0000_0000)

  function splitOnPivots(kmt: KMT, pivots: seq<Key>)
  : (kmts : seq<KMT>)
  requires WF(kmt)
  requires Pivots.WFPivots(pivots)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  ensures forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq(kmts) == SplitBucketOnPivots(I(kmt), pivots)
  ensures |kmts| == |pivots| + 1
  {
    WeightSplitBucketOnPivots(I(kmt), pivots);
    splitResultSmall(kmt, pivots);

    toKmtSeq(KVList.splitOnPivots(kmt.kvl, pivots))
  }

  method SplitOnPivots(kmt: KMT, pivots: seq<Key>)
  returns (kmts : seq<KMT>)
  requires splitOnPivots.requires(kmt, pivots)
  ensures kmts == splitOnPivots(kmt, pivots)
  {
    WeightSplitBucketOnPivots(I(kmt), pivots);
    KVList.lenKeysLeWeightOver8(kmt.kvl);
    splitResultSmall(kmt, pivots);

    var kvls := KVList.SplitOnPivots(kmt.kvl, pivots);
    kmts := ToKmtSeq(kvls);
  }

  method computeWeightKMT(kmt: KMT)
  returns (weight: uint64)
  requires WF(kmt)
  requires WeightBucket(I(kmt)) < 0x1_0000_0000_0000_0000
  ensures weight as int == WeightBucket(I(kmt))
  {
    weight := kmt.weight;
  }

  method computeWeightKMTSeq(kmts: seq<KMT>)
  returns (weight: uint64)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  requires WeightBucketList(ISeq(kmts)) < 0x1_0000_0000_0000_0000
  ensures weight as int == WeightBucketList(ISeq(kmts))
  {
    assume false;
    var j: uint64 := 0;
    var total: uint64 := 0;
    while j < |kmts| as uint64
    {
      var w := kmts[j].weight;
      total := total + w;
      j := j + 1;
    }
    weight := total;
  }

  lemma Islice(kmts: seq<KMT>, a: int, b: int)
  requires 0 <= a <= b <= |kmts|
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |kmts[a..b]| :: WF(kmts[a..b][i])
  ensures ISeq(kmts[a..b]) == ISeq(kmts)[a..b]
  {
    if b == |kmts| {
      if (a == b) {
      } else {
        Islice(DropLast(kmts), a, b - 1);
      }
    } else {
      Islice(DropLast(kmts), a, b);
    }
  }

  lemma Isuffix(kmts: seq<KMT>, a: int)
  requires 0 <= a <= |kmts|
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |kmts[a..]| :: WF(kmts[a..][i])
  ensures ISeq(kmts[a..]) == ISeq(kmts)[a..]
  {
    Islice(kmts, a, |kmts|);
  }

  lemma IPopFront(kmt: KMT, kmts: seq<KMT>)
  requires WF(kmt)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq([kmt] + kmts) == [I(kmt)] + ISeq(kmts)
  {
    if |kmts| == 0 {
    } else {
      IPopFront(kmt, DropLast(kmts));
    }
  }

  lemma IPopBack(kmts: seq<KMT>, kmt: KMT)
  requires WF(kmt)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq(kmts + [kmt]) == ISeq(kmts) + [I(kmt)]
  {
    reveal_ISeq();
  }

  lemma Ireplace1with2(kmts: seq<KMT>, kmt1: KMT, kmt2: KMT, slot: int)
  requires WF(kmt1)
  requires WF(kmt2)
  requires 0 <= slot < |kmts|
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |replace1with2(kmts, kmt1, kmt2, slot)| :: WF(replace1with2(kmts, kmt1, kmt2, slot)[i])
  ensures ISeq(replace1with2(kmts, kmt1, kmt2, slot)) == replace1with2(ISeq(kmts), I(kmt1), I(kmt2), slot)
  {
    forall i | 0 <= i < |replace1with2(kmts, kmt1, kmt2, slot)|
    ensures WF(replace1with2(kmts, kmt1, kmt2, slot)[i])
    {
      if i < slot {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmts[i];
      }
      if i == slot {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmt1;
      }
      if i == slot + 1 {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmt2;
      }
      if i > slot + 1 {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmts[i-1];
      }
    }

    if slot == |kmts|-1 {
    } else {
      Ireplace1with2(DropLast(kmts), kmt1, kmt2, slot);
    }

    reveal_replace1with2();
  }

  function kmtOfSeq(s: seq<(Key, Message)>) : (kmt: KMT)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures WF(kmt)

  lemma kmtOfSeqRes(s: seq<(Key, Message)>, m: map<Key, Message>)
  requires |s| < 0x1_0000_0000_0000_0000
  requires SortedSeqForMap(s, m)
  ensures WF(kmtOfSeq(s))
  ensures I(kmtOfSeq(s)) == m

  method KmtOfSeq(s: seq<(Key, Message)>, ghost m: map<Key, Message>) returns (kmt: KMT)
  requires SortedSeqForMap(s, m)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures kmt == kmtOfSeq(s)
  {
    assume false;

    var keys := new Key[|s| as uint64];
    var defaultMessage := IdentityMessage();
    var values := new Message[|s| as uint64]((i) => defaultMessage);
    var weight := 0;

    var i := 0;
    while i < |s| as uint64
    {
      keys[i] := s[i].0;
      values[i] := s[i].1;
      weight := weight + WeightKey(keys[i]) as uint64 + WeightMessage(values[i]) as uint64;
      i := i + 1;
    }

    kmt := KMT(KVList.Kvl(keys[..], values[..]), weight);
  }

  function method Empty() : (kmt: KMT)
  ensures WF(kmt)
  ensures I(kmt) == map[]
  {
    WeightBucketEmpty();
    KMT(KVList.Empty(), 0)
  }

  lemma WFImpliesWFBucket(kmt: KMT)
  requires WF(kmt)
  ensures WFBucket(I(kmt))
  {
    KVList.WFImpliesWFBucket(kmt.kvl);
  }
}
