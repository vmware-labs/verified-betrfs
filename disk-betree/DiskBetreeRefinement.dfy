include "DiskBetree.dfy"
include "MapSpec.dfy"
  
abstract module DiskBetreeRefinement {
  import opened DiskBetree

  /// Invariants
  
  predicate KeyHasSatisfyingLookup<Value(!new)>(k: Constants, s: Variables, key: Key)
  {
    exists lookup, value :: IsSatisfyingLookup(k, s, key, value, lookup)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(k, s, key)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    assert forall key :: MS.InDomain(key) ==> IsSatisfyingLookup(k, s, key, MS.EmptyValue(), [Layer(BC.Root(k.bcc), EmptyNode(), [Insertion(MS.EmptyValue())])]);
  }
  
  // Refinement proof

  datatype Pair<S,T> = Pair(first: S, second: T)
  
  function GetLookup<Value>(k: Constants, s: Variables, key: Key) : Pair<Lookup, Value>
    requires KeyHasSatisfyingLookup(k, s, key);
  {
    var lookup, value :| IsSatisfyingLookup(k, s, key, value, lookup);
    Pair(lookup, value)
  }

  function GetValue<Value>(k: Constants, s: Variables, key: Key) : Value
    requires KeyHasSatisfyingLookup(k, s, key);
  {
    GetLookup(k, s, key).second
  }
  
  function Ik(k: Constants) : MS.Constants {
    MS.Constants()
  }
  
  function I(k: Constants, s: Variables) : MS.Variables
    requires Inv(k, s)
  {
    MS.Variables(imap key | MS.InDomain(key) :: GetValue(k, s, key))
  }

  lemma BetreeRefinesMapInit(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
    ensures MS.Init(Ik(k), I(k, s))
  {
    InitImpliesInv(k, s);
  }

  lemma BetreeRefinesMapNext(k: Constants, s: Variables, s':Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures MS.Next(Ik(k), I(k, s), I(k, s'))
  {
  }
}
