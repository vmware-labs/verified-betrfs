// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/sequences.i.dfy"
include "../../lib/Base/Maps.i.dfy"

module ConcurrentMap {
  import opened Sequences
  import opened Maps
  import opened Options

  type Key = int
  type Value(!new,==)

  datatype Req =
      | ReqQuery(key: Key)
      | ReqInsert(key: Key, value: Value)

  datatype Variables = Variables(
      m: map<Key, Value>,
      threads: map<nat, Req>
  )

  datatype Step =
    | InsertStartStep(tid: nat, key:Key, value:Value)
    | InsertEndStep(tid:nat)
    | QueryStartStep(tid: nat, key:Key)
    | QueryEndStep(tid:nat, res: Option<Value>)
    | NoOpStep

  predicate InsertStart(s: Variables, s': Variables, tid: nat, key: Key, value: Value)
  {
    && s'.m == s.m
    && tid !in s.threads
    && s'.threads == s.threads[tid := ReqInsert(key, value)]
  }

  predicate InsertEnd(s: Variables, s': Variables, tid: nat)
  {
    && tid in s.threads
    && s.threads[tid].ReqInsert?
    && var key := s.threads[tid].key;
    && var value := s.threads[tid].value;
    && s'.m == s.m[key := value]
    && s'.threads == MapRemove1(s.threads, tid)
  }

  predicate QueryStart(s: Variables, s': Variables, tid: nat, key: Key)
  {
    && s'.m == s.m
    && tid !in s.threads
    && s'.threads == s.threads[tid := ReqQuery(key)]
  }

  predicate QueryEnd(s: Variables, s': Variables, tid: nat, res: Option<Value>)
  {
    && tid in s.threads
    && s.threads[tid].ReqQuery?
    && var key := s.threads[tid].key;
    && s'.m == s.m
    && s'.threads == MapRemove1(s.threads, tid)
    && (res.None? ==> key !in s.m)
    && (res.Some? ==> key in s.m && s.m[key] == res.value)
  }

  predicate NextStep(s:Variables, s':Variables, step:Step)
  {
    match step {
      case InsertStartStep(tid, key, value) => InsertStart(s, s', tid, key, value)
      case InsertEndStep(tid) => InsertEnd(s, s', tid)
      case QueryStartStep(tid, key) => QueryStart(s, s', tid, key)
      case QueryEndStep(tid, value) => QueryEnd(s, s', tid, value)
      case NoOpStep => s' == s
    }
  }

  predicate Next(s:Variables, s':Variables) {
    exists step:Step :: NextStep(s, s', step)
  }
}
