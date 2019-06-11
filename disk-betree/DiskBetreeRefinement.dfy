include "DiskBetree.dfy"
include "MapSpec.dfy"
include "DiskBetreeInv.dfy"

abstract module DiskBetreeRefinement {
  import opened DiskBetreeInv

  type Key = DB.Key
  type Lookup<Value> = DB.Lookup<Value>
    
  datatype LookupResult<Value> = LookupResult(lookup: Lookup, result: Value)
  
  function GetLookup<Value>(k: DB.Constants, s: DB.Variables, key: Key) : LookupResult
    requires DB.KeyHasSatisfyingLookup(k, s, key);
  {
    var lookup, value :| DB.IsSatisfyingLookup(k, s, key, value, lookup);
    LookupResult(lookup, value)
  }

  function GetValue<Value>(k: DB.Constants, s: DB.Variables, key: Key) : Value
    requires DB.KeyHasSatisfyingLookup(k, s, key);
  {
    GetLookup(k, s, key).result
  }
  
  function Ik(k: DB.Constants) : DB.MS.Constants {
    DB.MS.Constants()
  }
  
  function I(k: DB.Constants, s: DB.Variables) : DB.MS.Variables
    requires Inv(k, s)
  {
    DB.MS.Variables(imap key | DB.MS.InDomain(key) :: GetValue(k, s, key))
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
