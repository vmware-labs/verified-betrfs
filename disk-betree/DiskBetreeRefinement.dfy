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

  lemma EquivalentLookupsImplInterpsEqual(k: DB.Constants, s: DB.Variables, s': DB.Variables)
  requires Inv(k, s);
  requires Inv(k, s');
  requires EquivalentLookups(k, s, s');
  ensures I(k, s) == I(k, s');
  {
    forall key
    ensures IView(k, BC.ViewOf(k.bck, s.bcv))[key]
         == IView(k, BC.ViewOf(k.bck, s'.bcv))[key];
    {
      var view := BC.ViewOf(k.bck, s.bcv);
      var view' := BC.ViewOf(k.bck, s'.bcv);

      var res := GetLookup(k, view, key);
      var res' := GetLookup(k, view', key);
      var value := res.result;
      var lookup := res.lookup;
      var value' := res'.result;
      var lookup' := res'.lookup;

      assert DB.IsSatisfyingLookup(k, view, key, value, lookup);
      // Follows from EquivalentLookup:
      var lookup'' :| DB.IsSatisfyingLookup(k, view, key, value', lookup'');
      CantEquivocate(k, s, key, value, value', lookup, lookup'');
      assert value == value';
    }
    assert IView(k, BC.ViewOf(k.bck, s.bcv))
        == IView(k, BC.ViewOf(k.bck, s'.bcv));
  }

  lemma QueryStepRefinesMap<Value>(k: DB.Constants, s: DB.Variables, s': DB.Variables, key: Key, value: Value, lookup: Lookup)
    requires Inv(k, s)
    requires DB.Query(k, s, s', key, value, lookup)
    requires Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
  
  lemma InsertMessageStepRefinesMap<Value>(k: DB.Constants, s: DB.Variables, s': DB.Variables, key: Key, msg: DB.BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires DB.InsertMessage(k, s, s', key, msg, oldroot)
    requires Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))

  lemma FlushStepRefinesMap<Value>(k: DB.Constants, s: DB.Variables, s': DB.Variables,
                                           parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference)
    requires Inv(k, s)
    requires DB.Flush(k, s, s', parentref, parent, childref, child, newchildref)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), DB.MS.StutterStep)
  {
    FlushEquivalentLookups(k, s, s', parentref, parent, childref, child, newchildref);
    EquivalentLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma GrowStepRefinesMap<Value>(k: DB.Constants, s: DB.Variables, s': DB.Variables, oldroot: Node, newchildref: BC.Reference)
    requires Inv(k, s)
    requires DB.Grow(k, s, s', oldroot, newchildref)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), DB.MS.StutterStep)
  {
    GrowEquivalentLookups(k, s, s', oldroot, newchildref);
    EquivalentLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma BetreeRefinesMapNextStep(k: DB.Constants, s: DB.Variables, s':DB.Variables, step: DB.Step)
    requires Inv(k, s)
    requires DB.NextStep(k, s, s', step)
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
  {
    NextPreservesInvariant(k, s, s');
    match step {
      case QueryStep(key, value, lookup) => QueryStepRefinesMap(k, s, s', key, value, lookup);
      case InsertMessageStep(key, value, oldroot) => InsertMessageStepRefinesMap(k, s, s', key, value, oldroot);
      case FlushStep(parentref, parent, childref, child, newchildref) => FlushStepRefinesMap(k, s, s', parentref, parent, childref, child, newchildref);
      case GrowStep(oldroot, newchildref) => GrowStepRefinesMap(k, s, s', oldroot, newchildref);
    }
  }
    
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
