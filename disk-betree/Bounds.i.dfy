include "../lib/NativeTypes.s.dfy"

module Bounds {
  import opened NativeTypes

  function method BlockSizeUint64() : uint64 { 8 * 1024 * 1024 }

  function method MaxNumChildrenUint64() : uint64 { 32 }
  function method MaxTotalBucketWeightUint64() : uint64 { 8067784 }

  function method MaxCacheSizeUint64() : uint64 { 200 }

  // Minimum weight a bucket needs to have before we consider flushing it.
  function method FlushTriggerWeightUint64() : uint64 { MaxTotalBucketWeightUint64() / 8 }



  function BlockSize() : int { BlockSizeUint64() as int }

  function MaxNumChildren() : int { MaxNumChildrenUint64() as int }
  function MaxTotalBucketWeight() : int { MaxTotalBucketWeightUint64() as int }

  function MaxCacheSize() : int { MaxCacheSizeUint64() as int }

  // Minimum weight a bucket needs to have before we consider flushing it.
  function FlushTriggerWeight() : int { FlushTriggerWeightUint64() as int }
}
