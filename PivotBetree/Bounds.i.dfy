include "../lib/Base/NativeTypes.s.dfy"
include "../lib/Base/KeyType.s.dfy"
//
// Defines bounds on various abstract quantities, such as the number
// of children of a node.
//

module Bounds {
  import opened NativeTypes
  import opened KeyType

  function method IndirectionTableBlockSizeUint64() : uint64 { 8*1024*1024 }
  function method NodeBlockSizeUint64() : uint64 { 98304 }
  function method MinNodeBlockIndexUint64() : uint64 { 86 }

  //function method MaxTotalBucketWeightUint64() : uint64 { 8356168 }
  //function method MaxCacheSizeUint64() : uint64 { 200 }
  function method MaxTotalBucketWeightUint64() : uint64 { 64220 }
  function method MaxCacheSizeUint64() : uint64 { 25600 }

  function method MaxNumChildrenUint64() : uint64 { 32 }

  // Minimum weight a bucket needs to have before we consider flushing it.
  function method FlushTriggerWeightUint64() : uint64 { MaxTotalBucketWeightUint64() / 8 }

  function method NumBlocksUint64() : uint64 { 0x1_0000 }

  function method IndirectionTableMaxSizeUint64() : uint64 { 0x1_0000_0000 }

  function IndirectionTableBlockSize() : int { IndirectionTableBlockSizeUint64() as int }
  function NodeBlockSize() : int { NodeBlockSizeUint64() as int }
  function MinNodeBlockIndex() : int { MinNodeBlockIndexUint64() as int }
  function MaxNumChildren() : int { MaxNumChildrenUint64() as int }
  function MaxTotalBucketWeight() : int { MaxTotalBucketWeightUint64() as int }
  function MaxCacheSize() : int { MaxCacheSizeUint64() as int }
  function FlushTriggerWeight() : int { FlushTriggerWeightUint64() as int }
  function NumBlocks() : int { NumBlocksUint64() as int }
  function IndirectionTableMaxSize() : int { IndirectionTableMaxSizeUint64() as int }

  lemma lemma_node_sector_doesnt_overlap_indirection_table()
  ensures NodeBlockSize() * MinNodeBlockIndex()
       >= IndirectionTableBlockSize()
  {
  }

  lemma lemma_node_fits_in_block()
  ensures 32 // checksum
    + 8 // sector case
    + (4 + (MaxNumChildren()-1)*(4 + KeyType.MaxLen() as int)) // pivot array
    + (8 + MaxNumChildren() * 8) // children array
    + 8 // number of buckets
    + MaxNumChildren() * (4 + 4) // length of each bucket
    + MaxTotalBucketWeight()
    <= NodeBlockSize()
  {
  }
}
