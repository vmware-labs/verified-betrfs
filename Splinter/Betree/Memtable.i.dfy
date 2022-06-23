// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../CoordinationLayer/MsgHistory.i.dfy"
include "Buffers.i.dfy"

module MemtableMod
{
  import opened KeyType
  import opened ValueMessage
  import opened LSNMod
  import opened MsgHistoryMod
  import opened Buffers

  datatype Memtable = Memtable(buffer: Buffer, seqEnd: LSN)
  {
    function ApplyPut(km: KeyedMessage) : Memtable
    {
      Memtable(Buffer(buffer.mapp[km.key := Merge(km.message, Query(km.key))]), seqEnd+1)
    }

    function ApplyPuts(puts: MsgHistory) : Memtable
      requires puts.WF()
      requires puts.seqStart == seqEnd
      decreases puts.Len()
    {
      if puts.IsEmpty() then this
      else ApplyPuts(puts.DiscardRecent(puts.seqEnd-1)).ApplyPut(puts.msgs[puts.seqEnd-1])
    }

    function Query(key: Key) : Message
    {
      buffer.Query(key)
    }

    // Drain out the contents (into the StampedBetree), but remember the seqEnd
    function Drain() : Memtable
    {
      EmptyMemtable(seqEnd)
    }

    predicate IsEmpty()
    {
      buffer.mapp.Keys == {}
    }
  }

  function EmptyMemtable(lsn: LSN) : Memtable
  {
    Memtable(Buffer(map[]), lsn)
  }
}
