// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

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

  type Variables = BJC.Variables
  
  predicate Init(s: Variables)
  {
    BJC.Init(s)
  }

  predicate Next(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    && (dop.ReqReadOp? ==> ValidDiskOp(dop))
    && (dop.ReqWriteOp? ==> ValidDiskOp(dop))
    && (dop.ReqWrite2Op? ==> ValidDiskOp(dop))
    && (ValidDiskOp(dop) ==>
      BJC.Next(s, s', uiop, IDiskOp(dop)))
    && (!ValidDiskOp(dop) ==> s == s')
  }
}
