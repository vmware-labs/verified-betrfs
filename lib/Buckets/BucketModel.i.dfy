include "BucketsLib.i.dfy"
include "PivotsLib.i.dfy"
include "BucketWeights.i.dfy"
include "../Base/Message.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/total_order.i.dfy"
include "../../MapSpec/UI.s.dfy"
include "../../MapSpec/MapSpec.s.dfy"
include "../../PivotBetree/Bounds.i.dfy"

module BucketModel {
  import opened BucketsLib
  import opened BucketWeights
  import PivotsLib
  import opened Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Maps
  import opened Sequences
  import opened KeyType
  import opened Options
  import UI
  import MS = MapSpec
  import opened Bounds

  datatype singleMergeResult =
      MergeCompleted(bot: Bucket, slack: nat)
    | SlackExhausted(bot: Bucket, end: nat, slack: nat)

  function mergeToOneChild(top: Bucket, from: nat, to: nat, bot: Bucket, slack: nat) : (result: singleMergeResult)
    requires WFBucket(top)
    requires BucketWellMarshalled(top)
    requires from <= to < |top.keys|
    requires WFBucket(bot)
    requires BucketWellMarshalled(bot)
  {
    assume false;
    MergeCompleted(bot, 0)
  }
    

  datatype partialFlushResult = partialFlushResult(newParent: Bucket, newChildren: seq<Bucket>, flushedKeys: set<Key>)

  function {:opaque} partialFlush(parent: Bucket, children: seq<Bucket>, pivots: seq<Key>) : (res: partialFlushResult)
    requires WFBucket(parent)
    requires PivotsLib.WFPivots(pivots)
    requires |pivots| + 1 == |children|
    requires WeightBucketList(children) <= MaxTotalBucketWeight()
    requires forall i | 0 <= i < |children| :: WFBucket(children[i])
    requires BucketWellMarshalled(parent)
    requires BucketListWellMarshalled(children)
    ensures WFBucket(res.newParent)
    ensures (forall i | 0 <= i < |res.newChildren| :: WFBucket(res.newChildren[i]))
    ensures res.newParent == BucketComplement(parent, res.flushedKeys)
    ensures res.newChildren == BucketListFlush(BucketIntersect(parent, res.flushedKeys), children, pivots)
    ensures WeightBucket(res.newParent) <= WeightBucket(parent)
    ensures WeightBucketList(res.newChildren) <= MaxTotalBucketWeight()
  {
    assume false;
    partialFlushResult(parent, [], {}) // FIXME
  }
}
