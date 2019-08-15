include "ImplState.i.dfy"

module Bounds {
  import IS = ImplState
  import BT = PivotBetreeSpec
  import opened BucketList

  function BlockSize() : int { 8 * 1024 * 1024 }

  function MaxNumChildren() : int { 32 }
  function MaxTotalBucketWeight() : int { 8355784 }

  function MaxCacheSize() : int { 70 }

  // Minimum weight a bucket needs to have before we consider flushing it.
  function FlushTriggerWeight() : int { MaxTotalBucketWeight() / 8 }

  function WeightBucket(bucket: Bucket) : int
  function WeightBucketList(bucket: BucketList) : int

  predicate NodeInBounds(node: BT.G.Node)
  {
    && |node.buckets| <= MaxNumChildren()
    && WeightBucketList(node.buckets) <= MaxTotalBucketWeight()
  }
}
