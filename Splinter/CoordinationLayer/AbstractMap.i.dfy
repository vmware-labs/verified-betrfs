// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "StampedMap.i.dfy"
include "MsgHistory.i.dfy"
include "LSNMod.i.dfy"

module AbstractMap {
  import opened ValueMessage
  import opened KeyType
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened LSNMod

  datatype Variables = Variables(sm: StampedMap)
  {
    function SeqEnd(): LSN
    {
      sm.seqEnd
    }
  }

  // Should I do this as a predicate step with no enabling conditions?
  function LoadMap(persistentMap: StampedMap) : Variables
  {
    Variables(persistentMap)
  }

  predicate Query(v: Variables, v': Variables, key: Key, value: Value)
  {
    && assert TotalKMMapMod.AnyKey(key);
    && value == v.sm.mi[key].value
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, puts: MsgHistory)
  {
    && puts.WF()
    && puts.CanFollow(v.SeqEnd())
    && v'.sm == MapPlusHistory(v.sm, puts)
  }

  predicate FreezeAs(v: Variables, v': Variables, sm: StampedMap)
  {
    && sm == v.sm
    && v' == v
  }
}
