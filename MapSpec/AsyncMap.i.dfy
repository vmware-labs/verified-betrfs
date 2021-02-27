// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "MapSpec.s.dfy"
include "../lib/Base/Maps.i.dfy"

module AsyncMapSpec {
  import MapSpec
  import opened ValueType
  import opened KeyType
  import opened Maps
  
  import UI

  datatype Variables = Variables(
      dict: MapSpec.Variables,
      queries: map<int, Value>)

  datatype Step =
      | QueryBeginStep(key: Key)
      | QueryEndStep(result: Value)
      | QueryStep(key: Key, result: Value)
      | WriteStep(key: Key, new_value: Value)
      | SuccStep(start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd)
      | StutterStep

  predicate Init(s: Variables)
  {
    && MapSpec.Init(s.dict)
    && s.queries == map[]
  }

  predicate QueryBegin(s: Variables, s': Variables, uiop: UI.Op, key: Key)
  {
    && uiop.GetBeginOp?
    && uiop.key == key
    && s'.dict == s.dict
    && uiop.id !in s.queries
    && MapSpec.WF(s.dict)
    && s'.queries == s.queries[uiop.id := s.dict.view[key]]
  }

  predicate QueryEnd(s: Variables, s': Variables, uiop: UI.Op, result: Value)
  {
    && uiop.GetEndOp?
    && uiop.value == result
    && s'.dict == s.dict
    && uiop.id in s.queries
    && s'.queries == MapRemove1(s.queries, uiop.id)
    && result == s.queries[uiop.id]
  }

  predicate Query(s: Variables, s': Variables, uiop: UI.Op, key: Key, result: Value)
  {
    && s'.queries == s.queries
    && MapSpec.Query(s.dict, s'.dict, uiop, key, result)
  }

  predicate Write(s: Variables, s': Variables, uiop: UI.Op, key: Key, new_value: Value)
  {
    && s'.queries == s.queries
    && MapSpec.Write(s.dict, s'.dict, uiop, key, new_value)
  }

  predicate Succ(s: Variables, s': Variables, uiop: UI.Op,
      start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd)
  {
    && s'.queries == s.queries
    && MapSpec.Succ(s.dict, s'.dict, uiop, start, results, end)
  }

  predicate NextStep(s:Variables, s':Variables, uiop: UI.Op, step:Step)
  {
    match step {
      case QueryBeginStep(key) => QueryBegin(s, s', uiop, key)
      case QueryEndStep(result) => QueryEnd(s, s', uiop, result)
      case QueryStep(key, result) => Query(s, s', uiop, key, result)
      case WriteStep(key, new_value) => Write(s, s', uiop, key, new_value)
      case SuccStep(start, results, end) => Succ(s, s', uiop, start, results, end)
      case StutterStep() => s == s'
    }
  }

  predicate Next(s:Variables, s':Variables, uiop: UI.Op)
  {
    exists step :: NextStep(s, s', uiop, step)
  }
}
