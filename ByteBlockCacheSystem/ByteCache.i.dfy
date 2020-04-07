include "../BlockCacheSystem/BlockJournalCache.i.dfy"
include "InterpretationDiskOps.i.dfy"

//
// Wraps a BetreeBlockCache (which does I/O in high-level Node sectors) into
// a state machine that is an AsyncDiskMachine: a client of a disk that does
// I/O in bytes.
//
// You (or past Jon) might ask: why do we refine Betree and BlockCache mostly
// separately, but join them up at the Pivot level, even though we still have
// a layer of refinement (pivot->byte) to go? The answer is that we never have
// a "byte betree block cache" in memory; we want our program to manipulate
// cooked data structures, not have to unmarshall every time we inspect a block
// of bytes from the cache. We want the parsing step to be specific to the
// memory->disk boundary, rather than having a refinement layer that eliminates
// the Pivot Node data structure entirely.
//

module ByteCache refines AsyncDiskMachine {
  import BJC = BlockJournalCache

  import opened InterpretationDiskOps

  type Constants = BJC.Constants
  type Variables = BJC.Variables
  
  predicate Init(k: Constants, s: Variables)
  {
    BJC.Init(k, s)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    && (dop.ReqReadOp? ==> ValidDiskOp(dop))
    && (dop.ReqWriteOp? ==> ValidDiskOp(dop))
    && (dop.ReqWrite2Op? ==> ValidDiskOp(dop))
    && (ValidDiskOp(dop) ==>
      BJC.Next(k, s, s', uiop, IDiskOp(dop)))
    && (!ValidDiskOp(dop) ==> s == s')
  }
}
