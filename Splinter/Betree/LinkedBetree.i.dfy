// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Journal/GenericDisk.i.dfy"


module LinkedBetree
{
  import opened Options
  import opened KeyType
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Buffers
  import GenericDisk
  import opened BoundedPivotsLib

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(linkedBetree: LinkedBetree)
    | InternalLabel()


  datatype BetreeNode = Nil | BetreeNode(
    buffers: BufferStack,  // Should buffer stack also be linked via pointers?
    pivotTable: PivotTable,
    children: seq<Pointer>)
  {}


  datatype DiskView = DiskView(seqEnd: LSN, entries: map<Address, BetreeNode>) 
  {}
  
  
  datatype LinkedBetree = LinkedBetree(
    root: Pointer,
    diskView: DiskView
  ) {}


}
