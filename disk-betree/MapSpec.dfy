include "../tla-tree/MissingLibrary.dfy"
include "../lib/total_order.dfy"

module MapSpec {
import opened MissingLibrary

import Keyspace = Total_Order
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

predicate Query<Value>(k:Constants, s:Variables, s':Variables, key:Key, result:Value)
{
    && WF(s)
    && result == s.view[key]
    && s' == s
}

predicate Write<Value>(k:Constants, s:Variables, s':Variables, key:Key, new_value:Value)
    ensures Write(k, s, s', key, new_value) ==> WF(s')
{
    && WF(s)
    && WF(s')
    && s'.view == s.view[key := new_value]
}

predicate Stutter(k:Constants, s:Variables, s':Variables)
{
    s' == s
}

datatype Step<Value> =
    | QueryStep(key:Key, result:Value)
    | WriteStep(key:Key, new_value:Value)
    | StutterStep

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
{
    match step {
        case QueryStep(key, result) => Query(k, s, s', key, result)
        case WriteStep(key, new_value) => Write(k, s, s', key, new_value)
        case StutterStep() => Stutter(k, s, s')
    }
}

predicate Next<Value(!new)>(k:Constants, s:Variables, s':Variables)
{
    exists step :: NextStep<Value>(k, s, s', step)
}

predicate Inv(k:Constants, s:Variables) { WF(s) }

lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
{
}

lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  ensures Inv(k, s')
{
}

}
