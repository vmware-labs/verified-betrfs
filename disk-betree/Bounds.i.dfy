module Bounds {
  function BlockSize() : int { 8 * 1024 * 1024 }

  function MaxNumChildren() : int { 32 }
  function MaxTotalBucketWeight() : int { 8355784 }

  function MaxCacheSize() : int { 70 }

  // Minimum weight a bucket needs to have before we consider flushing it.
  function FlushTriggerWeight() : int { MaxTotalBucketWeight() / 8 }
}
