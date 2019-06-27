include "../tla-tree/MissingLibrary.dfy"
include "../lib/total_order.dfy"

module UI {
  import Keyspace = Total_Order
  type Key = Keyspace.Element

  datatype Op<Value> =
    | NoOp
    | GetOp(key: Key, value: Value)
    | PutOp(key: Key, value: Value)
    | CrashOp
}

module MapSpec {
  import opened MissingLibrary

  import UI = UI
  import Keyspace = UI.Keyspace
  type Key = Keyspace.Element

  // Users must provide a definition of EmptyValue
  function EmptyValue<Value>() : Value

  datatype Constants = Constants()
  type View<Value> = imap<Key, Value>
  datatype Variables<Value> = Variables(view:View<Value>)

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

  function EmptyMap<Value>() : (zmap : imap<Key,Value>)
      ensures ViewComplete(zmap)
  {
      imap k | InDomain(k) :: EmptyValue()
  }

  predicate Init(k:Constants, s:Variables)
      ensures Init(k, s) ==> WF(s)
  {
      s == Variables(EmptyMap())
  }

  predicate Query<Value>(k:Constants, s:Variables, s':Variables, uiop: UI.Op, key:Key, result:Value)
  {
      && uiop == UI.GetOp(key, result)
      && WF(s)
      && result == s.view[key]
      && s' == s
  }

  predicate Write<Value>(k:Constants, s:Variables, s':Variables, uiop: UI.Op, key:Key, new_value:Value)
      ensures Write(k, s, s', uiop, key, new_value) ==> WF(s')
  {
      && uiop == UI.PutOp(key, new_value)
      && WF(s)
      && WF(s')
      && s'.view == s.view[key := new_value]
  }

  predicate Stutter(k:Constants, s:Variables, s':Variables, uiop: UI.Op)
  {
      && uiop.NoOp?
      && s' == s
  }

  datatype Step<Value> =
      | QueryStep(key:Key, result:Value)
      | WriteStep(key:Key, new_value:Value)
      | StutterStep

  predicate NextStep(k:Constants, s:Variables, s':Variables, uiop: UI.Op, step:Step)
  {
      match step {
          case QueryStep(key, result) => Query(k, s, s', uiop, key, result)
          case WriteStep(key, new_value) => Write(k, s, s', uiop, key, new_value)
          case StutterStep() => Stutter(k, s, s', uiop)
      }
  }

  predicate Next<Value(!new)>(k:Constants, s:Variables, s':Variables, uiop: UI.Op)
  {
      exists step :: NextStep<Value>(k, s, s', uiop, step)
  }

  predicate Inv(k:Constants, s:Variables) { WF(s) }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
  {
  }
}
