// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../CoordinationLayer/MsgHistory.i.dfy"

module MemtableMod
{
  import opened KeyType
  import opened ValueMessage
  import opened LSNMod
  import opened MsgHistoryMod

  datatype Memtable = Memtable(mapp: map<Key, Message>, seqEnd: LSN)
  {
    function Get(key: Key) : Message
    {
      if key in mapp then mapp[key] else Update(NopDelta())
    }

    function ApplyPut(km: KeyedMessage) : Memtable
    {
      Memtable(mapp[km.key := Merge(km.message, Get(km.key))], seqEnd+1)
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
      if key in mapp then mapp[key] else Update(NopDelta())
    }

    // Drain out the contents (into the StampedBetree), but remember the seqEnd
    function Drain() : Memtable
    {
      EmptyMemtable(seqEnd)
    }
  }

  function EmptyMemtable(lsn: LSN) : Memtable
  {
    Memtable(map[], lsn)
  }
}
