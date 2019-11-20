include "../lib/Base/Option.s.dfy"
include "../lib/Base/SeqComparison.s.dfy"
include "UI.s.dfy"
include "UIStateMachine.s.dfy"

module MapSpec refines UIStateMachine {
  import V = ValueWithDefault
  import K = KeyType
  import SeqComparison

  import UI
  type Key = K.Key
  type Value = V.Value

  // Users must provide a definition of EmptyValue
  function EmptyValue() : Value {
    V.DefaultValue()
  }

  datatype Constants = Constants()
  type View = imap<Key, Value>
  datatype Variables = Variables(view:View)

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

  predicate Init(k:Constants, s:Variables)
      ensures Init(k, s) ==> WF(s)
  {
    s == Variables(EmptyMap())
  }

  // Can collapse key and result; use the ones that came in uiop for free.
  predicate Query(k:Constants, s:Variables, s':Variables, uiop: UIOp, key:Key, result:Value)
  {
    && uiop == UI.GetOp(key, result)
    && WF(s)
    && result == s.view[key]
    && s' == s
  }

  predicate Succ(k: Constants, s: Variables, s': Variables, uiop: UIOp, key: Key, succKey: Key, succValue: Value)
  {
    && uiop == UI.SuccOp(key, succKey, succValue)
    && WF(s)
    && s' == s
    && succValue != EmptyValue()
    && s.view[succKey] == succValue
    && (forall k | (SeqComparison.lt(key, k) && SeqComparison.lt(k, succKey)
        && k in s.view) :: s.view[k] == EmptyValue())
  }

  predicate Write(k:Constants, s:Variables, s':Variables, uiop: UIOp, key:Key, new_value:Value)
      ensures Write(k, s, s', uiop, key, new_value) ==> WF(s')
  {
    && uiop == UI.PutOp(key, new_value)
    && WF(s)
    && WF(s')
    && s'.view == s.view[key := new_value]
  }

  predicate Stutter(k:Constants, s:Variables, s':Variables, uiop: UIOp)
  {
    && uiop.NoOp?
    && s' == s
  }

  // uiop should be in here, too.
  datatype Step =
      | QueryStep(key: Key, result: Value)
      | WriteStep(key: Key, new_value: Value)
      | SuccStep(key: Key, succKey: Key, succValue: Value)
      | StutterStep

  predicate NextStep(k:Constants, s:Variables, s':Variables, uiop: UIOp, step:Step)
  {
    match step {
      case QueryStep(key, result) => Query(k, s, s', uiop, key, result)
      case WriteStep(key, new_value) => Write(k, s, s', uiop, key, new_value)
      case SuccStep(key, succKey, succValue) => Succ(k, s, s', uiop, key, succKey, succValue)
      case StutterStep() => Stutter(k, s, s', uiop)
    }
  }

  predicate Next(k:Constants, s:Variables, s':Variables, uiop: UIOp)
  {
    exists step :: NextStep(k, s, s', uiop, step)
  }

  predicate Inv(k:Constants, s:Variables)
  {
    WF(s)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
  {
  }
}
