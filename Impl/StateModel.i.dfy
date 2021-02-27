// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

// include "../PivotBetree/PivotBetreeSpec.i.dfy"
// include "../lib/Base/Message.i.dfy"
// include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
// include "../lib/Base/Option.s.dfy"
// include "../BlockCacheSystem/BetreeCache.i.dfy"
// include "../lib/Lang/NativeTypes.s.dfy"
// include "../lib/DataStructures/LruModel.i.dfy"
// include "../lib/DataStructures/MutableMapModel.i.dfy"
// include "../lib/DataStructures/BitmapModel.i.dfy"
// include "BlockAllocatorModel.i.dfy"
// include "IndirectionTableModel.i.dfy"
// include "CommitterModel.i.dfy"
// include "../BlockCacheSystem/BlockJournalDisk.i.dfy"
include "../BlockCacheSystem/BlockJournalCache.i.dfy"
// include "../ByteBlockCacheSystem/ByteCache.i.dfy"
// include "DiskOpModel.i.dfy"
include "CommitterImpl.i.dfy"
include "StateBCModel.i.dfy"
//
// This file represents immutability's last stand.
// It is the highest-fidelity representation of the implementation
// that can be represented with immutable datatypes.
//
// For example, it has a model of the root bucket which does not exist in
// BlockCache.  It also represents indirection table as a map to pairs, rather
// than two maps, because real, mutable implementation uses a map to pairs.
//

module StateModel {
  import BJC = BlockJournalCache
  import opened CommitterImpl
  import opened StateBCModel

  // type Node = BT.G.Node  
  // type IndirectionTable = IndirectionTableModel.IndirectionTable

  datatype Variables = Variables(
    bc: BCVariables,
    jc: Committer)

  predicate WFVars(s: Variables)
  {
    && WFBCVars(s.bc)
    && s.jc.WF()
  }

  function IVars(vars: Variables) : BJC.Variables
  requires WFVars(vars)
  {
    BJC.Variables(IBlockCache(vars.bc), vars.jc.I())
  }

  function I(s: Variables) : BJC.Variables
  requires WFVars(s)
  {
    IVars(s)
  }

  predicate Inv(s: Variables)
  {
    && WFVars(s)
    && BCInv(s.bc)
    && s.jc.Inv()
    && BJC.Inv(I(s))
  }
}
