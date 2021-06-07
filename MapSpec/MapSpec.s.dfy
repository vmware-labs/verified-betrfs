// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
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
    && NonEmptyRange(start, end)
    && (forall i | 0 <= i < |results| :: s.view[results[i].key] == results[i].value)
    && (forall i | 0 <= i < |results| :: results[i].value != EmptyValue())
    && (forall i | 0 <= i < |results| :: InRange(start, results[i].key, end))
    && (forall i, j | 0 <= i < j < |results| :: SeqComparison.lt(results[i].key, results[j].key))
    && (forall key | InRange(start, key, end) && s.view[key] != EmptyValue() ::
        exists i :: 0 <= i < |results| && results[i].key == key)
    && s' == s
  }

  predicate Write(s:Variables, s':Variables, uiop: UIOp, key:Key, new_value:Value)
      ensures Write(s, s', uiop, key, new_value) ==> WF(s')
  {
    && uiop == UI.PutOp(key, new_value)
    && WF(s)
    && WF(s')
    && s'.view == s.view[key := new_value]
  }

  function CloneView(view: imap<Key, Value>, new_to_old:imap<Key, Key>): imap<Key, Value>
  requires ViewComplete(view)
  {
    imap k :: if k in new_to_old then view[new_to_old[k]] else view[k]
  }

  function ApplyCloneView(view: imap<Key, Value>, new_to_old:imap<Key, Key>): imap<Key, Value>
  {
    imap k :: if k in new_to_old && new_to_old[k] in view then view[new_to_old[k]] 
      else (if k in view then view[k] else EmptyValue())
  }

  predicate KeyHasPrefix(key: Key, prefix: Key)
  {
    && |prefix| <= |key|
    && key[..|prefix|] == prefix
  }

  function fromkey(k: Key, to: Key, from: Key) : Key 
  requires KeyHasPrefix(k, to)
  {
    assume |from + k[|to|..]| <= 1024;
    from + k[|to|..]
  }

  // from = old, to = new
  function CloneMap(from: Key, to: Key) : (m: imap<Key, Key>)
  {
    imap k | KeyHasPrefix(k, to) :: fromkey(k, to, from)
  }

  // predicate CloneMapFollowsUIOp(uiop: UIOp, new_to_old:imap<Key, Key>)
  // {
  //   && uiop.CloneOp?
  //   && (forall k | k in new_to_old ::
  //     && KeyHasPrefix(k, uiop.to)
  //     && KeyHasPrefix(new_to_old[k], uiop.from)
  //   )
  // }

  // clone(k, k') => k's content is k
  // old = k, new = k' 
  predicate Clone(s:Variables, s':Variables, uiop: UIOp, new_to_old:imap<Key, Key>)
  {
    && uiop.CloneOp?
    && new_to_old == CloneMap(uiop.from, uiop.to)
    && WF(s)
    && WF(s')
    && s'.view == CloneView(s.view, new_to_old)
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
      | CloneStep(new_to_old: imap<Key, Key>) // map from key to key
      | SuccStep(start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd)
      | StutterStep

  predicate NextStep(s:Variables, s':Variables, uiop: UIOp, step:Step)
  {
    match step {
      case QueryStep(key, result) => Query(s, s', uiop, key, result)
      case WriteStep(key, new_value) => Write(s, s', uiop, key, new_value)
      case CloneStep(new_to_old) => Clone(s, s', uiop, new_to_old)
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
