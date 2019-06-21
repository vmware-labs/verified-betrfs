include "DiskBetree.dfy"
include "MapSpec.dfy"
include "DiskBetreeInv.dfy"

module DiskBetreeRefinement {
  import opened DBI = DiskBetreeInv
  import opened G = BetreeGraph

  type Lookup = DB.Lookup
    
  datatype LookupResult = LookupResult(lookup: Lookup, result: Value)
  
  function GetLookup(k: DB.Constants, view: DB.BI.View, key: Key) : LookupResult
    requires KeyHasSatisfyingLookup(k, view, key);
  {
    var lookup, value :| DB.IsSatisfyingLookup(k, view, key, value, lookup);
    LookupResult(lookup, value)
  }

  function GetValue(k: DB.Constants, view: DB.BI.View, key: Key) : Value
    requires KeyHasSatisfyingLookup(k, view, key);
  {
    GetLookup(k, view, key).result
  }

  function IView(k: DB.Constants, view: DB.BI.View) : imap<Key, Value>
    requires forall key | DB.MS.InDomain(key) :: KeyHasSatisfyingLookup(k, view, key);
  {
    imap key | DB.MS.InDomain(key) :: GetValue(k, view, key)
  }
  
  function Ik(k: DB.Constants) : DB.MS.Constants {
    DB.MS.Constants()
  }
  
  function I(k: DB.Constants, s: DB.Variables) : DB.MS.Variables<Value>
    requires Inv(k, s)
  {
    DB.MS.Variables(IView(k, s.bcv.view))
  }

  lemma BetreeRefinesMapInit(k: DB.Constants, s: DB.Variables)
    requires DB.Init(k, s)
    ensures Inv(k, s)
    ensures DB.MS.Init(Ik(k), I(k, s))
  {
    InitImpliesInv(k, s);

    forall key | DB.MS.InDomain(key)
    ensures KeyHasSatisfyingLookup(k, s.bcv.view, key)
    ensures key in IView(k, s.bcv.view)
    ensures IView(k, s.bcv.view)[key] == DB.MS.EmptyValue()
    {
      /*
      assert (forall key | DB.MS.InDomain(key) :: KeyHasSatisfyingLookup(k, s.bcv.view, key));
      assert KeyHasSatisfyingLookup(k, s.bcv.view, key);
      assert key in (imap key | DB.MS.InDomain(key) :: GetValue(k, s.bcv.view, key));
      assert IView(k, s.bcv.view) == (imap key | DB.MS.InDomain(key) :: GetValue(k, s.bcv.view, key));
      */
      var lookupResult := GetLookup(k, s.bcv.view, key);
      var lookup := lookupResult.lookup;
      var value := lookupResult.result;
      //assert DB.IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
      assert DB.TotalLog(lookup, key) == [Insertion(DB.MS.EmptyValue())];
      //assert value == DB.MS.EmptyValue();
      //assert GetValue(k, s.bcv.view, key) == DB.MS.EmptyValue();
    }
  }

  lemma EquivalentLookupsImplInterpsEqual(k: DB.Constants, s: DB.Variables, s': DB.Variables)
  requires Inv(k, s);
  requires Inv(k, s');
  requires EquivalentLookups(k, s, s');
  ensures I(k, s) == I(k, s');
  {
    forall key
    ensures IView(k, s.bcv.view)[key]
         == IView(k, s'.bcv.view)[key];
    {
      var view := s.bcv.view;
      var view' := s'.bcv.view;

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
    assert IView(k, s.bcv.view)
        == IView(k, s'.bcv.view);
  }

  lemma EquivalentLookupsWithPutImplInterpsPut(k: DB.Constants, s: DB.Variables, s': DB.Variables, key: Key, value: Value)
  requires Inv(k, s);
  requires Inv(k, s');
  requires EquivalentLookupsWithPut(k, s, s', key, value);
  ensures IView(k, s'.bcv.view) == IView(k, s.bcv.view)[key := value];
  {
    var view := s.bcv.view;
    var view' := s'.bcv.view;

    forall key' | DB.MS.InDomain(key')
    ensures IView(k, s'.bcv.view)[key'] == IView(k, s.bcv.view)[key := value][key'];
    {
      if (key' == key) {
        var res := GetLookup(k, view', key);
        var value' := res.result;
        var lookup' := res.lookup;
        assert DB.IsSatisfyingLookup(k, view', key, value', lookup');
        var lookup :| DB.IsSatisfyingLookup(k, view', key, value, lookup);
        CantEquivocate(k, s', key, value, value', lookup, lookup');
        assert IView(k, view')[key] == value;
      } else {
        var res := GetLookup(k, view, key');
        var res' := GetLookup(k, view', key');
        var value := res.result;
        var lookup := res.lookup;
        var value' := res'.result;
        var lookup' := res'.lookup;

        assert DB.IsSatisfyingLookup(k, view, key', value, lookup);
        // Follows from EquivalentLookupWithPut:
        var lookup'' :| DB.IsSatisfyingLookup(k, view, key', value', lookup'');
        CantEquivocate(k, s, key', value, value', lookup, lookup'');
        assert value == value';
      }
    }
  }

  lemma QueryStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, key: Key, value: Value, lookup: Lookup)
    requires Inv(k, s)
    requires DB.Query(k, s, s', key, value, lookup)
    requires Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
  
  lemma InsertMessageStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires DB.BetreeSpec.InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    requires Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
  {
    var value := msg.value;

    // TODO show this:
    // (InsertMessageStepRefinesMap does half of it)
    assert EquivalentLookupsWithPut(k, s, s', key, value);
    
    EquivalentLookupsWithPutImplInterpsPut(k, s, s', key, value);
    assert DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), DB.MS.WriteStep(key, value));
  }

  lemma FlushStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables,
                                           parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference)
    requires Inv(k, s)
    requires DB.BetreeSpec.Flush(k.bck, s.bcv, s'.bcv, parentref, parent, childref, child, newchildref)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), DB.MS.StutterStep)
  {
    FlushEquivalentLookups(k, s, s', parentref, parent, childref, child, newchildref);
    EquivalentLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma GrowStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, oldroot: Node, newchildref: Reference)
    requires Inv(k, s)
    requires DB.BetreeSpec.Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), DB.MS.StutterStep)
  {
    GrowEquivalentLookups(k, s, s', oldroot, newchildref);
    EquivalentLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma SplitStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, fusion: DB.BetreeSpec.NodeFusion)
    requires Inv(k, s)
    requires DB.BetreeSpec.Split(k.bck, s.bcv, s'.bcv, fusion)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), DB.MS.StutterStep)
  {
    SplitEquivalentLookups(k, s, s', fusion);
    EquivalentLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma BetreeRefinesMapNextStep(k: DB.Constants, s: DB.Variables, s':DB.Variables, step: DB.Step)
    requires Inv(k, s)
    requires DB.NextStep(k, s, s', step)
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
  {
    NextPreservesInv(k, s, s');
    match step {
      case QueryStep(key, value, lookup) => QueryStepRefinesMap(k, s, s', key, value, lookup);
      case InsertMessageStep(key, value, oldroot) => InsertMessageStepRefinesMap(k, s, s', key, value, oldroot);
      case FlushStep(parentref, parent, childref, child, newchildref) => FlushStepRefinesMap(k, s, s', parentref, parent, childref, child, newchildref);
      case GrowStep(oldroot, newchildref) => GrowStepRefinesMap(k, s, s', oldroot, newchildref);
      case SplitStep(fusion) => SplitStepRefinesMap(k, s, s', fusion);
    }
  }
    
  lemma BetreeRefinesMapNext(k: DB.Constants, s: DB.Variables, s':DB.Variables)
    requires Inv(k, s)
    requires DB.Next(k, s, s')
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'))
  {
    NextPreservesInv(k, s, s');
    var step :| DB.NextStep(k, s, s', step);
    BetreeRefinesMapNextStep(k, s, s', step);
  }
}
