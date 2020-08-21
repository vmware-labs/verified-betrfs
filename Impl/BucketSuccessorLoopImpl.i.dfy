include "BucketSuccessorLoopModel.i.dfy"
include "BucketGeneratorImpl.i.dfy"

module BucketSuccessorLoopImpl {
  import opened BucketsLib
  import opened BucketImpl
  import opened BucketGeneratorImpl
  import opened NativeTypes
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened Options
  import BucketSuccessorLoopModel
  import BucketGeneratorModel
  import opened Lexicographic_Byte_Order_Impl
  import opened ValueMessage
  import opened KeyType

  method GetSuccessorInBucketStack(
      linear g': Generator,
      ghost buckets: seq<Bucket>,
      maxToFind: uint64,
      start: UI.RangeStart,
      upTo: Option<Key>)
  returns (res : UI.SuccResultList)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  requires |buckets| >= 1
  requires |buckets| < 0x1_0000_0000_0000_0000
  requires g'.Inv() && g'.I() == BucketGeneratorModel.GenFromBucketStackWithLowerBound(buckets, start)
  requires maxToFind >= 1
  ensures res == BucketSuccessorLoopModel.GetSuccessorInBucketStack(
      buckets, maxToFind as int, start, upTo)
  {
    BucketSuccessorLoopModel.reveal_GetSuccessorInBucketStack();
    BucketSuccessorLoopModel.reveal_ProcessGenerator();
    linear var g := g';
    
    var results := new UI.SuccResult[maxToFind];
    var results_len: uint64 := 0;
    var done := false;

    while !done
    invariant g.Inv()
    invariant forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
    invariant 0 <= results_len <= maxToFind
    invariant !done ==> results_len < maxToFind
    invariant !done ==> BucketSuccessorLoopModel.GetSuccessorInBucketStack(buckets, maxToFind as int, start, upTo) 
        == BucketSuccessorLoopModel.ProcessGenerator(g.I(), maxToFind as int, upTo, results[..results_len])
    invariant done ==> res == BucketSuccessorLoopModel.GetSuccessorInBucketStack(
                buckets, maxToFind as int, start, upTo)
    decreases !done, BucketGeneratorModel.decreaser(g.I())
    {
      BucketGeneratorModel.lemmaDecreaserDecreases(g.I());

      ghost var old_results := results[..results_len];

      var next := g.GenLeft();

      var okay := next.Next?;
      if okay && upTo.Some? {
        var c := cmp(next.key, upTo.value);
        if c >= 0 {
          okay := false;
        }
      }
      assert okay == (next.Next? && (upTo.Some? ==> Ord.lt(next.key, upTo.value)));

      if okay {
        var v := Merge(next.msg, DefineDefault()).value;
        if v != DefaultValue() {
          results[results_len] := UI.SuccResult(next.key, v);
          results_len := results_len + 1;

          assert results[..results_len] == old_results + [UI.SuccResult(next.key, v)];
          assert results_len as int == |results[..results_len]|;

          if results_len < maxToFind {
            inout g.GenPop();
          } else {
            done := true;
            res := UI.SuccResultList(results[..results_len], UI.EInclusive(next.key));
          }
        } else {
          inout g.GenPop();
        }
      } else {
        done := true;
        res := UI.SuccResultList(results[..results_len],
            if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf);
      }
    }
    g.Free();
  }
}
