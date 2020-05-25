include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/KeyType.s.dfy"
//
// Defines bounds on various abstract quantities, such as the number
// of children of a node.
//

module Bounds {
  import opened NativeTypes
  import opened KeyType

  function method NodeBlockSizeUint64() : uint64 { 2*1024*1024 }

  // TODO(jonh): We should partition the disk, in byte units, into regions,
  // and then address each region in its native block size with 0-based indexing.
  function method MinNodeBlockIndexUint64() : uint64
  {
    (2 * SuperblockSizeUint64()
      + DiskNumJournalBlocksUint64() * JournalBlockSizeUint64()
      + 2 * (IndirectionTableBlockSizeUint64())
      + NodeBlockSizeUint64() - 1)
    / NodeBlockSizeUint64()
  }

  // This is the configuration constraint for MinNodeBlockIndexUint64, so you can
  // "make build/PivotBetree/Bounds.i.verified" as a quick way to sanity-check
  // without running a complete system verification.
  lemma SanityCheckMinNodeBlockIndexUint64()
    ensures (MinNodeBlockIndexUint64() as int) * (NodeBlockSizeUint64() as int)
      >= 2*SuperblockSize() + (DiskNumJournalBlocksUint64() as int) * JournalBlockSize() + 2 * (IndirectionTableBlockSizeUint64() as int)
  {
  }

  // Disk layout goes: 2 Superblocks, Journal, 2 Indirection tables, nodes
  function method SuperblockSizeUint64() : uint64 { 4096 }  // Bytes

  function method JournalBlockSizeUint64() : uint64 { 4096 } // Bytes
  function method DiskNumJournalBlocksUint64() : uint64 { 64*1024 /* 512MB */ } // JournalBlockSize() blocks

  function method IndirectionTableBlockSizeUint64() : uint64 { 24*1024*1024 } // Bytes

  function method LargestBlockSizeOfAnyTypeUint64() : (size:uint64)
    ensures IndirectionTableBlockSizeUint64() <= size
    ensures NodeBlockSizeUint64() <= size
    // Superblock?
    // Journal?
  {
    IndirectionTableBlockSizeUint64()
  }


  function method MaxTotalBucketWeightUint64() : uint64 { 2*1024*1024-65536 }
  function method MaxCacheSizeUint64() : uint64 { 100 }

  function method MaxNumChildrenUint64() : uint64 { 8 }

  // Minimum weight a bucket needs to have before we consider flushing it.
  function method FlushTriggerWeightUint64() : uint64 { MaxTotalBucketWeightUint64() / 8 }

  function method NumBlocksUint64() : uint64 { 0x10_0000 }

  function method IndirectionTableMaxSizeUint64() : uint64 { 0x1_0000_0000 }

  function SuperblockSize() : int { SuperblockSizeUint64() as int }  // Bytes
  function IndirectionTableBlockSize() : int { IndirectionTableBlockSizeUint64() as int }
  function NodeBlockSize() : int { NodeBlockSizeUint64() as int }
  function MinNodeBlockIndex() : int { MinNodeBlockIndexUint64() as int }
  function MaxNumChildren() : int { MaxNumChildrenUint64() as int }
  function MaxTotalBucketWeight() : int { MaxTotalBucketWeightUint64() as int }
  function MaxCacheSize() : int { MaxCacheSizeUint64() as int }
  function FlushTriggerWeight() : int { FlushTriggerWeightUint64() as int }
  function NumBlocks() : int { NumBlocksUint64() as int }
  function IndirectionTableMaxSize() : int { IndirectionTableMaxSizeUint64() as int }
  function JournalBlockSize() : int { JournalBlockSizeUint64() as int } // Bytes
  function DiskNumJournalBlocks() : int { DiskNumJournalBlocksUint64() as int }

  lemma lemma_node_sector_doesnt_overlap_indirection_table()
  ensures NodeBlockSize() * MinNodeBlockIndex()
       >= 2 * 4096 + DiskNumJournalBlocks() * 4096
          + 2 * IndirectionTableBlockSize()
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
