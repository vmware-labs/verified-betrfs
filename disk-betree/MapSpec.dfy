include "../tla-tree/MissingLibrary.dfy"
include "../lib/total_order.dfy"
include "../lib/NativeTypes.dfy"

module ValueWithDefault {
  import NativeTypes

  type Value(==,!new) = seq<NativeTypes.byte>
	function method DefaultValue() : Value { [] }

	export S provides Value, DefaultValue
	export Internal reveals *
	export extends S
}

module UI {
  //import Keyspace = Total_Order
  import Keyspace = Lexicographic_Byte_Order

  import V = ValueWithDefault
  type Key = Keyspace.Element
  type Value = V.Value

  datatype Op =
    | NoOp
    | GetOp(key: Key, value: Value)
    | PutOp(key: Key, value: Value)
}

module MapSpec {
  import opened MissingLibrary
  import V = ValueWithDefault

  import UI = UI
  import Keyspace = UI.Keyspace
  type Key = Keyspace.Element
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

  predicate Query(k:Constants, s:Variables, s':Variables, uiop: UI.Op, key:Key, result:Value)
  {
      && uiop == UI.GetOp(key, result)
      && WF(s)
      && result == s.view[key]
      && s' == s
  }

  predicate Write(k:Constants, s:Variables, s':Variables, uiop: UI.Op, key:Key, new_value:Value)
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

  datatype Step =
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

  predicate Next(k:Constants, s:Variables, s':Variables, uiop: UI.Op)
  {
      exists step :: NextStep(k, s, s', uiop, step)
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
