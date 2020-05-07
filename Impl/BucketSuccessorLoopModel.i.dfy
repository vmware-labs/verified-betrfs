include "BucketGeneratorModel.i.dfy"

module BucketSuccessorLoopModel {
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences
  import opened BucketIteratorModel
  import opened BucketGeneratorModel
  import UI
  import opened KeyType

  // A straightforward loop using the generator machinery

  function {:opaque} ProcessGenerator(
      g: Generator,
      maxToFind: int,
      upTo: Option<Key>,
      results: seq<UI.SuccResult>) : UI.SuccResultList
  requires WF(g)
  requires |results| < maxToFind
  decreases decreaser(g)
  {
    lemmaDecreaserDecreases(g);

    var next := GenLeft(g);
    if next.Next? && (upTo.Some? ==> Keyspace.lt(next.key, upTo.value)) then (
      var v := Merge(next.msg, DefineDefault()).value;
      if v != DefaultValue() then (
        var results' := results + [UI.SuccResult(next.key, v)];
        if |results'| < maxToFind then (
          var g' := GenPop(g);
          ProcessGenerator(g', maxToFind, upTo, results')
        ) else (
          UI.SuccResultList(results', UI.EInclusive(next.key))
        )
      ) else (
        var g' := GenPop(g);
        ProcessGenerator(g', maxToFind, upTo, results)
      )
    ) else (
      UI.SuccResultList(results,
          if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf)
    )
  }

  function {:opaque} GetSuccessorInBucketStack(
      buckets: seq<Bucket>,
      maxToFind: int,
      start: UI.RangeStart,
      upTo: Option<Key>) : UI.SuccResultList
  requires |buckets| >= 1
  requires maxToFind >= 1
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  {
    var g := GenFromBucketStackWithLowerBound(buckets, start);
    ProcessGenerator(g, maxToFind, upTo, [])
  }

  // Lemmas and stuff

  predicate ProcessInv(
      bucket: Bucket,
      left: Bucket,
      right: Bucket,
      g: Generator,
      maxToFind: int,
      upTo: Option<Key>,
      results: seq<UI.SuccResult>)
  {
    && results == SortedSeqOfKeyValueMap(KeyValueMapOfBucket(left))
    && YieldsSortedBucket(g, right)
    && (forall l, r | l in left.b && r in right.b :: Keyspace.lt(l, r))
    && (upTo.Some? ==> forall l | l in left.b :: Keyspace.lt(l, upTo.value))
    && MapUnionPreferA(left.b, right.b) == bucket.b
    && |results| < maxToFind
  }

  lemma ProcessGeneratorResult(
      bucket: Bucket,
      left: Bucket,
      right: Bucket,
      g: Generator,
      maxToFind: int,
      upTo: Option<Key>,
      results: seq<UI.SuccResult>)
  requires ProcessInv(bucket, left, right, g, maxToFind, upTo, results)
  requires BucketWellMarshalled(bucket)
  requires BucketWellMarshalled(left)
  requires BucketWellMarshalled(right)
  ensures var r := ProcessGenerator(g, maxToFind, upTo, results);
      && r.results == SortedSeqOfKeyValueMap(
          KeyValueMapOfBucket(
            ClampEnd(bucket, r.end)))
      && (upTo.Some? ==> !MS.UpperBound(upTo.value, r.end))
      && (|r.results| == 0 ==>
          r.end == (if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf))
  decreases decreaser(g)
  {
    reveal_ProcessGenerator();
    reveal_SortedSeqOfKeyValueMap();
    reveal_KeyValueMapOfBucket();
    reveal_ClampEnd();

    lemmaDecreaserDecreases(g);

    var next := GenLeft(g);
    GenLeftIsMinimum(g);

    if next.Next? && (upTo.Some? ==> Keyspace.lt(next.key, upTo.value)) {
      var v := Merge(next.msg, DefineDefault()).value;

      GenPopIsRemove(g);

      var left' := B(left.b[next.key := next.msg]);
      var right' := B(MapRemove1(right.b, next.key));

      if v != DefaultValue() {
        var results' := results + [UI.SuccResult(next.key, v)];

        assert forall k | k in KeyValueMapOfBucket(left').Keys :: Keyspace.lte(k, next.key);
        assert next.key in KeyValueMapOfBucket(left').Keys;
        assert next.key == Keyspace.maximum(KeyValueMapOfBucket(left').Keys);
        assert MapRemove1(KeyValueMapOfBucket(left'), Keyspace.maximum(KeyValueMapOfBucket(left').Keys)) == KeyValueMapOfBucket(left);
        assert results' == SortedSeqOfKeyValueMap(KeyValueMapOfBucket(left'));

        if |results'| < maxToFind {
          var g' := GenPop(g);
          ProcessGeneratorResult(bucket, left', right', g', maxToFind, upTo, results');
        } else {
          WellMarshalledBucketsEq(left', ClampEnd(bucket, UI.EInclusive(next.key)));
          assert left' == ClampEnd(bucket, UI.EInclusive(next.key));
          //var r := UI.SuccResultList(results', UI.EInclusive(next.key));
        }
      } else {
        assert KeyValueMapOfBucket(left') == KeyValueMapOfBucket(left);
        assert results == SortedSeqOfKeyValueMap(KeyValueMapOfBucket(left'));

        var g' := GenPop(g);
        ProcessGeneratorResult(bucket, left', right', g', maxToFind, upTo, results);
      }
    } else {
      var ce := ClampEnd(bucket, 
          if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf);
      assert left.b == ce.b;
      //var r := UI.SuccResultList(results,
      //    if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf);
    }
  }

  lemma InRangeImpliesNonEmpty(start: UI.RangeStart, key: Key, end: UI.RangeEnd)
  requires MS.InRange(start, key, end)
  ensures MS.NonEmptyRange(start, end)
  {
    assert start.SInclusive? ==> Keyspace.lte(start.key, key);
    assert start.SExclusive? ==> Keyspace.lt(start.key, key);
    assert end.EInclusive? ==> Keyspace.lte(key, end.key);
    assert end.EExclusive? ==> Keyspace.lt(key, end.key);
  }

  lemma GetSuccessorInBucketStackResult(
      buckets: seq<Bucket>,
      maxToFind: int,
      start: UI.RangeStart,
      upTo: Option<Key>)
  requires |buckets| >= 1
  requires maxToFind >= 1
  requires BucketListWellMarshalled(buckets)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  requires upTo.Some? && (start.SInclusive? || start.SExclusive?) ==>
      Keyspace.lt(start.key, upTo.value)
  ensures var r := GetSuccessorInBucketStack(buckets, maxToFind, start, upTo);
    && r.results ==
        SortedSeqOfKeyValueMap(
          KeyValueMapOfBucket(
            ClampRange(ComposeSeq(buckets), start, r.end)))
    && (upTo.Some? ==> !MS.UpperBound(upTo.value, r.end))
    && MS.NonEmptyRange(start, r.end)
  {
    reveal_GetSuccessorInBucketStack();
    var g := GenFromBucketStackWithLowerBound(buckets, start);
    GenFromBucketStackWithLowerBoundYieldsComposeSeq(buckets, start);
    var bucket := BucketOf(g);
    reveal_KeyValueMapOfBucket();
    reveal_SortedSeqOfKeyValueMap();
    ProcessGeneratorResult(bucket, B(map[]), bucket, g, maxToFind, upTo, []);
    var r := ProcessGenerator(g, maxToFind, upTo, []);
    assert r == GetSuccessorInBucketStack(buckets, maxToFind, start, upTo);

    reveal_ClampRange();
    reveal_ClampStart();
    reveal_ClampEnd();
    assert ClampRange(ComposeSeq(buckets), start, r.end)
        == ClampEnd(ClampStart(ComposeSeq(buckets), start), r.end);

    /*assert bucket == ClampStart(ComposeSeq(buckets), start);

    assert r.results
        == SortedSeqOfKeyValueMap(
             KeyValueMapOfBucket(
               ClampEnd(bucket, r.end)))
        == SortedSeqOfKeyValueMap(
             KeyValueMapOfBucket(
               ClampRange(ComposeSeq(buckets), start, r.end)));*/

    if |r.results| == 0 {
      // In this case, the r.end will be upTo
      assert MS.NonEmptyRange(start, r.end);
    } else {
      // There's at least 1 result, so the range has to be non-empty
      SortedSeqOfKeyValueMaps(KeyValueMapOfBucket(
               ClampRange(ComposeSeq(buckets), start, r.end)), 0);
      assert r.results[0].key in ClampRange(ComposeSeq(buckets), start, r.end).b;
      assert MS.InRange(start, r.results[0].key, r.end);
      InRangeImpliesNonEmpty(start, r.results[0].key, r.end);
    }
  }
}
