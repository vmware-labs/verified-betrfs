// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "../lib/Lang/System/SeqComparison.s.dfy"
include "../MapSpec/UI.s.dfy"
include "../MapSpec/UIStateMachine.s.dfy"

// Basic dictionary state machine.

module MapSpec refines UIStateMachine {
  import opened ValueType
  import opened KeyType
  import SeqComparison
  import Options

  import UI

  // Users must provide a definition of EmptyValue
  function EmptyValue() : Value {
    ValueType.DefaultValue()
  }

  type View = imap<Key, Value>
  datatype Variables = Variables(ghost view:View)

  predicate ViewComplete(view:View)
  {
    forall k :: k in view
  }

  predicate WF(s:Variables)
  {
    && ViewComplete(s.view)
  }

  // Dafny black magic: This name is here to give EmptyMap's forall something to
  // trigger on. (Eliminates a /!\ Warning.)
  predicate InDomain(k:Key)
  {
    true
  }

  function EmptyMap() : (zmap : imap<Key,Value>)
      ensures ViewComplete(zmap)
  {
    imap k | InDomain(k) :: EmptyValue()
  }

  predicate Init(s:Variables)
      ensures Init(s) ==> WF(s)
  {
    s == Variables(EmptyMap())
  }

  // Can collapse key and result; use the ones that came in uiop for free.
  predicate Query(s:Variables, s':Variables, uiop: UIOp, key:Key, result:Value)
  {
    && uiop == UI.GetOp(key, result)
    && WF(s)
    && result == s.view[key]
    && s' == s
  }

  predicate LowerBound(start: UI.RangeStart, key: Key)
  {
    && (start.SInclusive? ==> SeqComparison.lte(start.key, key))
    && (start.SExclusive? ==> SeqComparison.lt(start.key, key))
  }

  predicate UpperBound(key: Key, end: UI.RangeEnd)
  {
    && (end.EInclusive? ==> SeqComparison.lte(key, end.key))
    && (end.EExclusive? ==> SeqComparison.lt(key, end.key))
  }

  predicate InRange(start: UI.RangeStart, key: Key, end: UI.RangeEnd)
  {
    && LowerBound(start, key)
    && UpperBound(key, end)
  }

  predicate NonEmptyRange(start: UI.RangeStart, end: UI.RangeEnd)
  {
    || start.NegativeInf?
    || end.PositiveInf?
    || (start.SInclusive? && end.EInclusive? && SeqComparison.lte(start.key, end.key))
    || SeqComparison.lt(start.key, end.key)
  }

  predicate Succ(s: Variables, s': Variables, uiop: UIOp,
      start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd)
  {
    && uiop == UI.SuccOp(start, results, end)
    && WF(s)
    && s' == s
    && NonEmptyRange(start, end)
    && (forall i | 0 <= i < |results| :: s.view[results[i].key] == results[i].value)
    && (forall i | 0 <= i < |results| :: results[i].value != EmptyValue())
    && (forall i | 0 <= i < |results| :: InRange(start, results[i].key, end))
    && (forall i, j | 0 <= i < j < |results| :: SeqComparison.lt(results[i].key, results[j].key))
    && (forall key | InRange(start, key, end) && s.view[key] != EmptyValue() ::
        exists i :: 0 <= i < |results| && results[i].key == key)
  }

  predicate Write(s:Variables, s':Variables, uiop: UIOp, key:Key, new_value:Value)
      ensures Write(s, s', uiop, key, new_value) ==> WF(s')
  {
    && uiop == UI.PutOp(key, new_value)
    && WF(s)
    && WF(s')
    && s'.view == s.view[key := new_value]
  }

  predicate Stutter(s:Variables, s':Variables, uiop: UIOp)
  {
    && uiop.NoOp?
    && s' == s
  }

  // uiop should be in here, too.
  datatype Step =
      | QueryStep(key: Key, result: Value)
      | WriteStep(key: Key, new_value: Value)
      | SuccStep(start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd)
      | StutterStep

  predicate NextStep(s:Variables, s':Variables, uiop: UIOp, step:Step)
  {
    match step {
      case QueryStep(key, result) => Query(s, s', uiop, key, result)
      case WriteStep(key, new_value) => Write(s, s', uiop, key, new_value)
      case SuccStep(start, results, end) => Succ(s, s', uiop, start, results, end)
      case StutterStep() => Stutter(s, s', uiop)
    }
  }

  predicate Next(s:Variables, s':Variables, uiop: UIOp)
  {
    exists step :: NextStep(s, s', uiop, step)
  }

  predicate Inv(s:Variables)
  {
    WF(s)
  }

  lemma InitImpliesInv(s: Variables)
  {
  }

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UIOp)
  {
  }
}
