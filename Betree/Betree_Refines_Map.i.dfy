include "../Betree/Betree.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/BetreeInv.i.dfy"
//
// Refinement proof from Betree to Map.
//

module Betree_Refines_Map {
  import MS = MapSpec
  import opened DBI = BetreeInv
  import opened G = BetreeGraph
  import opened BetreeSpec`Internal
  import ValueMessage`Internal
  import opened Maps
  import opened ValueType
  import opened KeyType
  import UI
  import SeqComparison

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
    requires forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(k, view, key);
  {
    imap key | MS.InDomain(key) :: GetValue(k, view, key)
  }
  
  function Ik(k: DB.Constants) : MS.Constants {
    MS.Constants()
  }
  
  function I(k: DB.Constants, s: DB.Variables) : MS.Variables
    requires Inv(k, s)
  {
    MS.Variables(IView(k, s.bcv.view))
  }

  lemma RefinesInit(k: DB.Constants, s: DB.Variables)
    requires DB.Init(k, s)
    ensures Inv(k, s)
    ensures MS.Init(Ik(k), I(k, s))
  {
    InitImpliesInv(k, s);

    forall key | MS.InDomain(key)
    ensures KeyHasSatisfyingLookup(k, s.bcv.view, key)
    ensures key in IView(k, s.bcv.view)
    ensures IView(k, s.bcv.view)[key] == MS.EmptyMap()[key]
    {
      var l := GetLookup(k, s.bcv.view, key);
      var lookup := l.lookup;
      var value := l.result;
      assert InterpretLookup(lookup, key) == G.M.Define(G.M.DefaultValue()); // observe
      /*
      assert value == G.M.DefaultValue();
      assert GetValue(k, s.bcv.view, key)
          == value
          == MS.EmptyValue();
      assert IView(k, s.bcv.view)[key] == MS.EmptyValue();
      assert MS.EmptyMap()[key] == MS.EmptyValue();
      */
    }
    //assert IView(k, s.bcv.view) == MS.EmptyMap();
    //assert I(k, s) == MS.Variables(MS.EmptyMap());
  }

  lemma PreservesLookupsRev(k: DB.Constants, s: DB.Variables, s': DB.Variables)
  requires Inv(k, s);
  requires Inv(k, s');
  requires PreservesLookups(k, s, s');
  ensures PreservesLookups(k, s', s);
  {
    forall lookup', key, value' | DB.IsSatisfyingLookup(k, s'.bcv.view, key, value', lookup')
      ensures exists lookup :: DB.IsSatisfyingLookup(k, s.bcv.view, key, value', lookup)
    {
      assert KeyHasSatisfyingLookup(k, s.bcv.view, key);
      var lookup, value :| DB.IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
      var lookup'2 :| DB.IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'2);
      CantEquivocate(k, s', key, value, value', lookup'2, lookup');
      assert DB.IsSatisfyingLookup(k, s.bcv.view, key, value', lookup);
    }
  }

  lemma PreservesLookupsImplInterpsEqual(k: DB.Constants, s: DB.Variables, s': DB.Variables)
  requires Inv(k, s);
  requires Inv(k, s');
  requires PreservesLookups(k, s, s');
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
      PreservesLookupsRev(k, s, s');
      var lookup'' :| DB.IsSatisfyingLookup(k, view, key, value', lookup'');
      CantEquivocate(k, s, key, value, value', lookup, lookup'');
      assert value == value';
    }
    assert IView(k, s.bcv.view)
        == IView(k, s'.bcv.view);
  }

  lemma PreservesLookupsRevExcept(k: DB.Constants, s: DB.Variables, s': DB.Variables, except: Key)
  requires Inv(k, s);
  requires Inv(k, s');
  requires PreservesLookupsExcept(k, s, s', except);
  ensures PreservesLookupsExcept(k, s', s, except);
  {
    forall lookup', key, value' | key != except && DB.IsSatisfyingLookup(k, s'.bcv.view, key, value', lookup')
      ensures exists lookup :: DB.IsSatisfyingLookup(k, s.bcv.view, key, value', lookup)
    {
      assert KeyHasSatisfyingLookup(k, s.bcv.view, key);
      var lookup, value :| DB.IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
      var lookup'2 :| DB.IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'2);
      CantEquivocate(k, s', key, value, value', lookup'2, lookup');
      assert DB.IsSatisfyingLookup(k, s.bcv.view, key, value', lookup);
    }
  }


  lemma PreservesLookupsPutImplInterpsPut(k: DB.Constants, s: DB.Variables, s': DB.Variables, key: Key, value: Value)
  requires Inv(k, s);
  requires Inv(k, s');
  requires PreservesLookupsPut(k, s, s', key, value);
  ensures IView(k, s'.bcv.view) == IView(k, s.bcv.view)[key := value];
  {
    var view := s.bcv.view;
    var view' := s'.bcv.view;

    forall key' | MS.InDomain(key')
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
        PreservesLookupsRevExcept(k, s, s', key);
        var lookup'' :| DB.IsSatisfyingLookup(k, view, key', value', lookup'');
        CantEquivocate(k, s, key', value, value', lookup, lookup'');
        assert value == value';
      }
    }
  }

  lemma LookupImpliesMap(k: DB.Constants, s: DB.Variables, key: Key, value: Value, lookup: Lookup)
  requires Inv(k, s)
  requires LookupKeyValue(lookup, key, value)
  requires DB.BI.Reads(k.bck, s.bcv, lookup)
  ensures I(k, s).view[key] == value
  {
    var lookupResult := GetLookup(k, s.bcv.view, key);
    var lookup' := lookupResult.lookup;
    var value' := lookupResult.result;

    forall i | 0 <= i < |lookup|
    ensures IMapsTo(s.bcv.view, lookup[i].ref, lookup[i].node)
    {
      assert DB.BI.ReadStep(k.bck, s.bcv, lookup[i]);
    }
    CantEquivocate(k, s, key, value, value', lookup, lookup');
  }

  lemma QueryStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UI.Op, key: Key, value: Value, lookup: Lookup)
    requires Inv(k, s)
    requires BetreeStepUI(BetreeQuery(LookupQuery(key, value, lookup)), uiop)
    requires DBI.Query(k.bck, s.bcv, s'.bcv, key, value, lookup)
    requires Inv(k, s')
    ensures MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.QueryStep(key, value))
  {
    LookupImpliesMap(k, s, key, value, lookup);
  }

  lemma SuccQueryStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UI.Op, start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd, lookup: Lookup)
    requires Inv(k, s)
    requires BetreeStepUI(BetreeSuccQuery(SuccQuery(start, results, end, lookup)), uiop)
    requires DBI.SuccQuery(k.bck, s.bcv, s'.bcv, start, results, end, lookup)
    requires Inv(k, s')
    ensures MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.SuccStep(start, results, end))
  {
    forall i | 0 <= i < |results|
    ensures I(k, s).view[results[i].key] == results[i].value
    {
      LookupImpliesMap(k, s, results[i].key, results[i].value, lookup);
    }

    forall key | MS.InRange(start, key, end) && I(k, s).view[key] != MS.EmptyValue()
    ensures exists i :: 0 <= i < |results| && results[i].key == key
    {
      if (!(exists i :: 0 <= i < |results| && results[i].key == key)) {
        LookupImpliesMap(k, s, key, MS.EmptyValue(), lookup);
      }
    }

    assert MS.Succ(Ik(k), I(k,s), I(k,s'), uiop, start, results, end);
  }
  
  lemma InsertMessageStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UI.Op, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires BetreeStepUI(BetreeInsert(MessageInsertion(key, msg, oldroot)), uiop)
    requires DBI.InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    requires Inv(k, s')
    ensures MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var value := msg.value;

    InsertMessagePreservesLookupsPut(k, s, s', key, msg, oldroot);
    
    PreservesLookupsPutImplInterpsPut(k, s, s', key, value);
    assert MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.WriteStep(key, value));
  }

  lemma FlushStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UI.Op, flush:NodeFlush)
    requires Inv(k, s)
    requires uiop.NoOp?
    requires DBI.Flush(k.bck, s.bcv, s'.bcv, flush)
    requires Inv(k, s')
    ensures MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.StutterStep)
  {
    FlushPreservesLookups(k, s, s', flush);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma GrowStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UI.Op, oldroot: Node, newchildref: Reference)
    requires Inv(k, s)
    requires uiop.NoOp?
    requires DBI.Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
    requires Inv(k, s')
    ensures MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.StutterStep)
  {
    GrowPreservesLookups(k, s, s', oldroot, newchildref);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

//~  lemma RedirectStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UI.Op, redirect: DB.BetreeSpec.Redirect)
//~    requires Inv(k, s)
//~    requires uiop.NoOp?
//~    requires DBI.Redirect(k.bck, s.bcv, s'.bcv, redirect)
//~    requires Inv(k, s')
//~    ensures MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.StutterStep)
//~  {
//~    RedirectPreservesLookups(k, s, s', redirect);
//~    PreservesLookupsImplInterpsEqual(k, s, s');
//~    assert I(k, s) == I(k, s');
//~  }

  lemma RedirectRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UI.Op, r: DB.BetreeSpec.Redirect)
    requires Inv(k, s)
    requires uiop.NoOp?
    requires DBI.Redirect(k.bck, s.bcv, s'.bcv, r)
    requires Inv(k, s')
    ensures MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.StutterStep)
  {
    RedirectPreservesLookups(k, s, s', r);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma BetreeStepRefinesMap(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UI.Op, betreeStep: DBI.BetreeSpec.BetreeStep)
    requires Inv(k, s)
    requires BetreeStepUI(betreeStep, uiop)
    requires DB.NextStep(k, s, s', uiop, DB.BetreeStep(betreeStep))
    ensures Inv(k, s')
    ensures MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    NextPreservesInv(k, s, s', uiop);
    match betreeStep {
      case BetreeQuery(q) => QueryStepRefinesMap(k, s, s', uiop, q.key, q.value, q.lookup);
      case BetreeSuccQuery(q) => SuccQueryStepRefinesMap(k, s, s', uiop, q.start, q.results, q.end, q.lookup);
      case BetreeInsert(ins) => InsertMessageStepRefinesMap(k, s, s', uiop, ins.key, ins.msg, ins.oldroot);
      case BetreeFlush(flush) => FlushStepRefinesMap(k, s, s', uiop, flush);
      case BetreeGrow(growth) => GrowStepRefinesMap(k, s, s', uiop, growth.oldroot, growth.newchildref);
      case BetreeRedirect(r) => RedirectRefinesMap(k, s, s', uiop, r);
    }
  }

  lemma GCStepRefinesMap(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UI.Op, refs: iset<DB.BI.Reference>)
    requires Inv(k, s)
    requires DB.NextStep(k, s, s', uiop, DB.GCStep(refs))
    requires Inv(k, s')
    ensures MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.StutterStep)
  {
    GCStepPreservesLookups(k, s, s', refs);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma RefinesNextStep(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UI.Op, step: DB.Step)
    requires Inv(k, s)
    requires DB.NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
    ensures MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    NextPreservesInv(k, s, s', uiop);
    match step {
      case BetreeStep(betreeStep) => BetreeStepRefinesMap(k, s, s', uiop, betreeStep);
      case GCStep(refs) => GCStepRefinesMap(k, s, s', uiop, refs);
      case StutterStep() => {
        assert MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, MS.StutterStep);
      }
    }
  }
    
  lemma RefinesNext(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UI.Op)
    requires Inv(k, s)
    requires DB.Next(k, s, s', uiop)
    ensures Inv(k, s')
    ensures MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    NextPreservesInv(k, s, s', uiop);
    var step :| DB.NextStep(k, s, s', uiop, step);
    RefinesNextStep(k, s, s', uiop, step);
  }
}
