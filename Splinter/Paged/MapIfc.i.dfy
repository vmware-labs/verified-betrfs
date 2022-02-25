// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "StampedMap.i.dfy"
include "MsgHistory.i.dfy"

abstract module MapIfc {
  import opened TotalKMMapMod
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened ValueMessage
  import opened KeyType
  import opened LSNMod

  type Map(==,!new)

  predicate WF(mapp: Map)

  function I(mapp: Map) : (out: StampedMap)

  // "Accessors" that are restricted ways we expect coordination implementation
  // to need to inspect the map (efficiently)

  function Mkfs() : (out: Map)
    ensures WF(out)
    ensures I(out) == StampedMapMod.Empty()

  // The LSNs (exclusive) whose effect this map represents
  function SeqEnd(mapp: Map) : (out: LSN)
    requires WF(mapp)
    ensures out == I(mapp).seqEnd

  function ApplyPuts(mapp: Map, puts: MsgHistory) : (out: Map)
    requires WF(mapp)
    requires puts.WF()
    requires puts.CanFollow(SeqEnd(mapp))
    ensures WF(out)
    ensures I(out) == MapPlusHistory(I(mapp), puts)

  function Query(mapp: Map, key: Key) : (out: Value)
    requires WF(mapp)
    ensures
      assert TotalKMMapMod.AnyKey(key); // trigger to deref mi
      out == I(mapp).mi[key].value
}
