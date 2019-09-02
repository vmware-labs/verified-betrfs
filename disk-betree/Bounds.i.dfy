module Bounds {
  function method BlockSize() : int { 8 * 1024 * 1024 }

  function method MaxNumChildren() : int { 32 }
  function method MaxTotalBucketWeight() : int { 8067784 }

  function method MaxCacheSize() : int { 200 }

  // Minimum weight a bucket needs to have before we consider flushing it.
  function method FlushTriggerWeight() : int { MaxTotalBucketWeight() / 8 }
}
