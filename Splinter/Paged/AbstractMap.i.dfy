// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "MapIfc.i.dfy"

module AbstractMap refines MapIfc {
  type Map = StampedMap

  predicate WF(mapp: Map) {
    true
  }

  function I(mapp: Map) : (out: StampedMap)
  { mapp }

  function Mkfs() : (out: Map)
    // ensures WF(out)
    // ensures I(out) == StampedMapMod.Empty()
  {
    StampedMapMod.Empty()
  }

  function SeqEnd(mapp: Map) : (out: LSN)
    // requires WF(mapp)
    // ensures out == I(mapp).seqEnd
  {
    mapp.seqEnd
  }

  function ApplyPuts(mapp: Map, puts: MsgHistory) : (out: Map)
    // requires WF(mapp)
    // requires puts.WF()
    // requires puts.CanFollow(SeqEnd(mapp))
    // ensures WF(out)
    // ensures I(out) == MapPlusHistory(I(mapp), puts)
  {
    MapPlusHistory(mapp, puts)
  }

  function Query(mapp: Map, key: Key) : (out: Value)
    // requires WF(mapp)
    // ensures assert TotalKMMapMod.AnyKey(key); out == I(mapp).mi[key].value
  {
    assert TotalKMMapMod.AnyKey(key);
    mapp.mi[key].value
  }
}
