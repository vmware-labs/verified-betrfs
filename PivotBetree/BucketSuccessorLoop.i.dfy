include "BucketGenerator.i.dfy"

module BucketSuccessorLoop {
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences
  import opened BucketIterator
  import opened BucketGenerator
  import UI

  // A straightforward loop using the generator machinery

  function {:opaque} ProcessGenerator(
      g: Generator,
      maxToFind: int,
      upTo: Option<Key>,
      results: seq<UI.SuccResult>) : UI.SuccResultList
  requires WF(g)
  requires |results| < maxToFind
  {
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
    && (forall l, r | l in left && r in right :: Keyspace.lt(l, r))
    && (upTo.Some? ==> forall l | l in left :: Keyspace.lt(l, upTo.value))
    && MapUnionPreferA(left, right) == bucket
    && |results| < maxToFind
  }

  lemma ProcessGeneratorPreserves(
      bucket: Bucket,
      left: Bucket,
      right: Bucket,
      g: Generator,
      maxToFind: int,
      upTo: Option<Key>,
      results: seq<UI.SuccResult>)
  requires ProcessInv(bucket, left, right, g, maxToFind, upTo, results)
  ensures var r := ProcessGenerator(g, maxToFind, upTo, results);
      && r.results == SortedSeqOfKeyValueMap(
          KeyValueMapOfBucket(
            ClampEnd(bucket, r.end)))
      && (upTo.Some? ==> !MS.UpperBound(upTo.value, r.end))
  {
    reveal_ProcessGenerator();
    reveal_SortedSeqOfKeyValueMap();
    reveal_KeyValueMapOfBucket();
    reveal_ClampEnd();

    var next := GenLeft(g);
    GenLeftIsMinimum(g);

    if next.Next? && (upTo.Some? ==> Keyspace.lt(next.key, upTo.value)) {
      var v := Merge(next.msg, DefineDefault()).value;

      GenPopIsRemove(g);

      var left' := left[next.key := next.msg];
      var right' := MapRemove1(right, next.key);
      assert forall k | k in left' :: Keyspace.lte(k, next.key);
      assert next.key == Keyspace.maximum(left'.Keys);
      assert MapRemove1(left', Keyspace.maximum(left'.Keys)) == left;

      if v != DefaultValue() {
        var results' := results + [UI.SuccResult(next.key, v)];

        assert forall k | k in KeyValueMapOfBucket(left').Keys :: Keyspace.lte(k, next.key);
        assert next.key in KeyValueMapOfBucket(left').Keys;
        assert next.key == Keyspace.maximum(KeyValueMapOfBucket(left').Keys);
        assert MapRemove1(KeyValueMapOfBucket(left'), Keyspace.maximum(KeyValueMapOfBucket(left').Keys)) == KeyValueMapOfBucket(left);
        assert results' == SortedSeqOfKeyValueMap(KeyValueMapOfBucket(left'));

        if |results'| < maxToFind {
          var g' := GenPop(g);
          ProcessGeneratorPreserves(bucket, left', right', g', maxToFind, upTo, results');
        } else {
          assert left' == ClampEnd(bucket, UI.EInclusive(next.key));
          //var r := UI.SuccResultList(results', UI.EInclusive(next.key));
        }
      } else {
        assert KeyValueMapOfBucket(left') == KeyValueMapOfBucket(left);
        assert results == SortedSeqOfKeyValueMap(KeyValueMapOfBucket(left'));

        var g' := GenPop(g);
        ProcessGeneratorPreserves(bucket, left', right', g', maxToFind, upTo, results);
      }
    } else {
      assert left == ClampEnd(bucket, 
          if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf);
      //var r := UI.SuccResultList(results,
      //    if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf);
    }
  }
}
