// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CoordinationSystem.i.dfy"
include "../CoordinationLayer/CoordinationSystem.i.dfy"
// include "CoordinationJournal.i.dfy"
// include "CoordinationBetree.i.dfy"

module CoordinationSystemRefinement {
  import AllocJournal = AllocationJournal
  import AllocBetree = AllocationBetree

  import AbstractJournal
  import AbstractMap
  import opened CoordinationJournal
  import opened CoordinationBetree
  import opened CoordinationSystemMod
  import AbstractSystem = CoordinationSystem
//   import opened Options
//   import opened MapRemove_s
//   import opened CrashTolerantMapSpecMod
//   import opened MsgHistoryMod
//   import opened KeyType
//   import opened ValueMessage
//   import opened TotalKMMapMod
//   import opened LSNMod
//   import opened CoordinationJournal
//   import opened CoordinationBetree

  predicate Inv(v: Variables)
  {
    && true
  }

  
  // Place holders:
  // 1. alloc journal refines to abstract journal
  // 2. coordination alloc journal refines to crash tolerant abstract journal
  // 3. alloc betree conditionally refines to abstract map
  // 4. coordination alloc betree conditionally refines to crash tolerant abstract map


// }
