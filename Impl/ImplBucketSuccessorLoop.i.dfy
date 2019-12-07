include "../PivotBetree/BucketSuccessorLoop.i.dfy"
include "ImplBucketGenerator.i.dfy"

module ImplBucketSuccessorLoop {
  import opened MutableBucket
  import opened ImplBucketGenerator
  import opened NativeTypes
  import opened Options
  import BucketSuccessorLoop
  import BucketGenerator
  import opened Lexicographic_Byte_Order
  import opened ValueMessage

  method GetSuccessorInBucketStack(
      buckets: seq<MutBucket>,
      maxToFind: uint64,
      start: UI.RangeStart,
      upTo: Option<Key>)
  returns (res : UI.SuccResultList)
  requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
  requires |buckets| >= 1
  requires maxToFind >= 1
  ensures res == BucketSuccessorLoop.GetSuccessorInBucketStack(
      MutBucket.ISeq(buckets), maxToFind as int, start, upTo)
  {
    BucketSuccessorLoop.reveal_GetSuccessorInBucketStack();
    BucketSuccessorLoop.reveal_ProcessGenerator();

    var g := Generator.GenFromBucketStackWithLowerBound(buckets, start);
    var results := new UI.SuccResult[maxToFind];
    var results_len: uint64 := 0;

    while true
    invariant g.Inv()
    invariant forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    invariant fresh(g.Repr)
    invariant results !in g.Repr
    invariant results !in g.ReadOnlyRepr
    invariant 0 <= results_len < maxToFind
    invariant BucketSuccessorLoop.GetSuccessorInBucketStack(MutBucket.ISeq(buckets), maxToFind as int, start, upTo) == BucketSuccessorLoop.ProcessGenerator(g.I(), maxToFind as int, upTo, results[..results_len])
    decreases BucketGenerator.decreaser(g.I())
    {
      //MutBucket.AllocatedReprSeq(buckets);
      BucketGenerator.lemmaDecreaserDecreases(g.I());

      //ghost var old_g := g.I();
      ghost var old_results := results[..results_len];
      ghost var old_buckets := MutBucket.ISeq(buckets);

      var next := g.GenLeft();

      var okay := next.Next?;
      if okay && upTo.Some? {
        var c := cmp(next.key, upTo.value);
        if c >= 0 {
          okay := false;
        }
      }
      assert okay == (next.Next? && (upTo.Some? ==> lt(next.key, upTo.value)));

      if okay {
        var v := Merge(next.msg, DefineDefault()).value;
        if v != DefaultValue() {
          results[results_len] := UI.SuccResult(next.key, v);
          results_len := results_len + 1;

          assert results[..results_len] == old_results + [UI.SuccResult(next.key, v)];
          assert results_len as int == |results[..results_len]|;

          if results_len < maxToFind {
            g.GenPop();

            //ghost var new_results := old_results + [UI.SuccResult(next.key, v)];
            assert MutBucket.ISeq(buckets) == old_buckets;
            //assert BucketSuccessorLoop.GetSuccessorInBucketStack(MutBucket.ISeq(buckets), maxToFind as int, start, upTo)
            //    == BucketSuccessorLoop.GetSuccessorInBucketStack(old_buckets, maxToFind as int, start, upTo)
            //    == BucketSuccessorLoop.ProcessGenerator(old_g, maxToFind as int, upTo, old_results)
            //    == BucketSuccessorLoop.ProcessGenerator(BucketGenerator.GenPop(old_g), maxToFind as int, upTo, new_results)
            //    == BucketSuccessorLoop.ProcessGenerator(g.I(), maxToFind as int, upTo, results[..results_len]);
          } else {
            return UI.SuccResultList(results[..results_len], UI.EInclusive(next.key));
          }
        } else {
          g.GenPop();

          assert MutBucket.ISeq(buckets) == old_buckets;
          //assert BucketSuccessorLoop.GetSuccessorInBucketStack(MutBucket.ISeq(buckets), maxToFind as int, start, upTo) == BucketSuccessorLoop.ProcessGenerator(g.I(), maxToFind as int, upTo, results[..results_len]);
        }
      } else {
        return UI.SuccResultList(results[..results_len],
            if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf);
      }
    }
  }
}
