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

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(stampedMap: StampedMap)
    | InternalLabel()

  datatype Variables = Variables(stampedMap: StampedMap)

  // private:
  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryLabel?
    && lbl.endLsn == v.stampedMap.seqEnd
    && assert TotalKMMapMod.AnyKey(lbl.key);
    && lbl.value == v.stampedMap.mi[lbl.key].value
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && lbl.puts.WF()
    && lbl.puts.CanFollow(v.stampedMap.seqEnd)
    && v'.stampedMap == MapPlusHistory(v.stampedMap, lbl.puts)
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryEndLsnLabel?
    && lbl.endLsn == v.stampedMap.seqEnd
    && v' == v
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.FreezeAsLabel?
    && lbl.stampedMap == v.stampedMap
    && v' == v
  }

  // public:
  predicate Init(v: Variables, persistentMap: StampedMap)
  {
    v == Variables(persistentMap)
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    match lbl {
      case QueryLabel(_, _, _) => Query(v, v', lbl)
      case PutLabel(_) => Put(v, v', lbl)
      case QueryEndLsnLabel(_) => QueryEndLsn(v, v', lbl)
      case FreezeAsLabel(_) => FreezeAs(v, v', lbl)
      case InternalLabel() => v == v'
    }
  }
}
