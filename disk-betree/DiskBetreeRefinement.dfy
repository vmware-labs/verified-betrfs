include "DiskBetree.dfy"
include "MapSpec.dfy"
include "DiskBetreeInv.dfy"

abstract module DiskBetreeRefinement {
  import opened DBI : DiskBetreeInv

  import BC = DBI.DB.BC

  type Node<Value> = DB.Node<Value>
  type Key = DB.Key
  type Lookup<Value> = DB.Lookup<Value>
    
  datatype LookupResult<Value> = LookupResult(lookup: Lookup, result: Value)
  
  function GetLookup<Value>(k: DB.Constants, view: BC.View<Node>, key: Key) : LookupResult
    requires KeyHasSatisfyingLookup(k, view, key);
  {
    var lookup, value :| DB.IsSatisfyingLookup(k, view, key, value, lookup);
    LookupResult(lookup, value)
  }

  function GetValue<Value>(k: DB.Constants, view: BC.View<Node>, key: Key) : Value
    requires KeyHasSatisfyingLookup(k, view, key);
  {
    GetLookup(k, view, key).result
  }

  function IView<Value>(k: DB.Constants, view: BC.View<Node>) : imap<Key, Value>
    requires forall key :: KeyHasSatisfyingLookup(k, view, key);
  {
    imap key | DB.MS.InDomain(key) :: GetValue(k, view, key)
  }
  
  function Ik(k: DB.Constants) : DB.MS.Constants {
    DB.MS.Constants()
  }
  
  function I(k: DB.Constants, s: DB.Variables) : DB.MS.Variables
    requires Inv(k, s)
  {
    DB.MS.Variables(IView(k, BC.ViewOf(k.bck, s.bcv)))
  }

  lemma BetreeRefinesMapInit(k: DB.Constants, s: DB.Variables)
    requires DB.Init(k, s)
    ensures Inv(k, s)
    ensures DB.MS.Init(Ik(k), I(k, s))
  {
    InitImpliesInv(k, s);
  }

  lemma BetreeRefinesMapNextStep(k: DB.Constants, s: DB.Variables, s':DB.Variables, step: DB.Step)
    requires Inv(k, s)
    requires DB.NextStep(k, s, s', step)
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
    
  lemma BetreeRefinesMapNext(k: DB.Constants, s: DB.Variables, s':DB.Variables)
    requires Inv(k, s)
    requires DB.Next(k, s, s')
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
  {
    NextPreservesInvariant(k, s, s');
    var step :| DB.NextStep(k, s, s', step);
    BetreeRefinesMapNextStep(k, s, s', step);
  }
}
