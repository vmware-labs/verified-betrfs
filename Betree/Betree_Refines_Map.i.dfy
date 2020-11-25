include "../Betree/Betree.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/BetreeInv.i.dfy"
//
// Refinement proof from Betree to Map.
//

module Betree_Refines_Map {
  import MS = MapSpec
  import opened Betree
  import opened BetreeInv
  import opened G = BetreeGraph
  import opened BetreeSpec`Internal
  import ValueMessage`Internal
  import opened Maps
  import opened ValueType
  import opened KeyType
  import UI
  import SeqComparison

  datatype LookupResult = LookupResult(lookup: Lookup, result: Value)
  
  function GetLookup(view: Betree.BI.View, key: Key, start: Reference) : LookupResult
    requires KeyHasSatisfyingLookup(view, key, start)
  {
    var lookup: Lookup, value :|
        BetreeInv.IsSatisfyingLookupFrom(view, key, value, lookup, start);
    LookupResult(lookup, value)
  }

  function GetValue(view: Betree.BI.View, key: Key) : Value
    requires KeyHasSatisfyingLookup(view, key, Root());
  {
    GetLookup(view, key, Root()).result
  }

  function IView(view: Betree.BI.View) : imap<Key, Value>
    requires forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(view, key, Root());
  {
    imap key | MS.InDomain(key) :: GetValue(view, key)
  }
  
  function I(s: Betree.Variables) : MS.Variables
    requires Inv(s)
  {
    MS.Variables(IView(s.bcv.view))
  }

  lemma RefinesInit(s: Betree.Variables)
    requires Betree.Init(s)
    ensures Inv(s)
    ensures MS.Init(I(s))
  {
    InitImpliesInv(s);

    forall key | MS.InDomain(key)
    ensures KeyHasSatisfyingLookup(s.bcv.view, key, Root())
    ensures key in IView(s.bcv.view)
    ensures IView(s.bcv.view)[key] == MS.EmptyMap()[key]
    {
      var l := GetLookup(s.bcv.view, key, Root());
      var lookup := l.lookup;
      var value := l.result;
      assert InterpretLookup(lookup, key) == G.M.Define(G.M.DefaultValue()); // observe
      /*
      assert value == G.M.DefaultValue();
      assert GetValue(s.bcv.view, key)
          == value
          == MS.EmptyValue();
      assert IView(s.bcv.view)[key] == MS.EmptyValue();
      assert MS.EmptyMap()[key] == MS.EmptyValue();
      */
    }
    //assert IView(s.bcv.view) == MS.EmptyMap();
    //assert I(s) == MS.Variables(MS.EmptyMap());
  }

  lemma PreservesLookupsRev(s: Betree.Variables, s': Betree.Variables)
  requires Inv(s);
  requires Inv(s');
  requires PreservesLookups(s, s', Root());
  ensures PreservesLookups(s', s, Root());
  {
    forall lookup': Lookup, key, value' | BetreeInv.IsSatisfyingLookupFrom(s'.bcv.view, key, value', lookup', Root())
      ensures exists lookup: Lookup :: BetreeInv.IsSatisfyingLookupFrom(s.bcv.view, key, value', lookup, Root())
    {
      assert KeyHasSatisfyingLookup(s.bcv.view, key, Root());
      var lookup: Lookup, value :| BetreeInv.IsSatisfyingLookupFrom(
          s.bcv.view, key, value, lookup, Root());
      var lookup'2: Lookup :| BetreeInv.IsSatisfyingLookupFrom(
          s'.bcv.view, key, value, lookup'2, Root());
      CantEquivocate(s', key, value, value', lookup'2, lookup');
      assert BetreeInv.IsSatisfyingLookupFrom(s.bcv.view, key, value', lookup, Root());
    }
  }

  lemma PreservesLookupsImplInterpsEqual(s: Betree.Variables, s': Betree.Variables)
  requires Inv(s);
  requires Inv(s');
  requires PreservesLookups(s, s', Root());
  ensures I(s) == I(s');
  {
    forall key
    ensures IView(s.bcv.view)[key]
         == IView(s'.bcv.view)[key];
    {
      var view := s.bcv.view;
      var view' := s'.bcv.view;

      var res := GetLookup(view, key, Root());
      var res' := GetLookup(view', key, Root());
      var value := res.result;
      var lookup := res.lookup;
      var value' := res'.result;
      var lookup' := res'.lookup;

      assert BetreeInv.IsSatisfyingLookupFrom(view, key, value, lookup, Root());
      PreservesLookupsRev(s, s');
      var lookup'' :| BetreeInv.IsSatisfyingLookupFrom(view, key, value', lookup'', Root());
      CantEquivocate(s, key, value, value', lookup, lookup'');
      assert value == value';
    }
    assert IView(s.bcv.view)
        == IView(s'.bcv.view);
  }

  lemma PreservesLookupsRevExcept(s: Betree.Variables, s': Betree.Variables, except: Key)
  requires Inv(s);
  requires Inv(s');
  requires PreservesLookupsExcept(s, s', Root(), except);
  ensures PreservesLookupsExcept(s', s, Root(), except);
  {
    forall lookup', key, value' | key != except && BetreeInv.IsSatisfyingLookupFrom(s'.bcv.view, key, value', lookup', Root())
      ensures exists lookup :: BetreeInv.IsSatisfyingLookupFrom(s.bcv.view, key, value', lookup, Root())
    {
      assert KeyHasSatisfyingLookup(s.bcv.view, key, Root());
      var lookup, value :| BetreeInv.IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, Root());
      var lookup'2 :| BetreeInv.IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup'2, Root());
      CantEquivocate(s', key, value, value', lookup'2, lookup');
      assert BetreeInv.IsSatisfyingLookupFrom(s.bcv.view, key, value', lookup, Root());
    }
  }


  lemma PreservesLookupsPutImplInterpsPut(s: Betree.Variables, s': Betree.Variables, key: Key, value: Value)
  requires Inv(s);
  requires Inv(s');
  requires PreservesLookupsPut(s, s', key, value);
  ensures IView(s'.bcv.view) == IView(s.bcv.view)[key := value];
  {
    var view := s.bcv.view;
    var view' := s'.bcv.view;

    forall key' | MS.InDomain(key')
    ensures IView(s'.bcv.view)[key'] == IView(s.bcv.view)[key := value][key'];
    {
      if (key' == key) {
        var res := GetLookup(view', key, Root());
        var value' := res.result;
        var lookup' := res.lookup;
        assert BetreeInv.IsSatisfyingLookupFrom(view', key, value', lookup', Root());
        var lookup :| BetreeInv.IsSatisfyingLookupFrom(view', key, value, lookup, Root());
        CantEquivocate(s', key, value, value', lookup, lookup');
        assert IView(view')[key] == value;
      } else {
        var res := GetLookup(view, key', Root());
        var res' := GetLookup(view', key', Root());
        var value := res.result;
        var lookup := res.lookup;
        var value' := res'.result;
        var lookup' := res'.lookup;

        assert BetreeInv.IsSatisfyingLookupFrom(view, key', value, lookup, Root());
        PreservesLookupsRevExcept(s, s', key);
        var lookup'' :| BetreeInv.IsSatisfyingLookupFrom(view, key', value', lookup'', Root());
        CantEquivocate(s, key', value, value', lookup, lookup'');
        assert value == value';
      }
    }
  }

  lemma LookupImpliesMap(s: Betree.Variables, key: Key, value: Value, lookup: Lookup)
  requires Inv(s)
  requires LookupKeyValue(lookup, key, value)
  requires Betree.BI.Reads(s.bcv, lookup)
  ensures I(s).view[key] == value
  {
    var lookupResult := GetLookup(s.bcv.view, key, Root());
    var lookup' := lookupResult.lookup;
    var value' := lookupResult.result;

    forall i | 0 <= i < |lookup|
    ensures IMapsTo(s.bcv.view, lookup[i].ref, lookup[i].node)
    {
      assert Betree.BI.ReadStep(s.bcv, lookup[i]);
    }
    CantEquivocate(s, key, value, value', lookup, lookup');
  }

  lemma QueryStepRefinesMap(s: Betree.Variables, s': Betree.Variables, uiop: UI.Op, key: Key, value: Value, lookup: Lookup)
    requires Inv(s)
    requires BetreeStepUI(BetreeQuery(LookupQuery(key, value, lookup)), uiop)
    requires BetreeInv.Query(s.bcv, s'.bcv, key, value, lookup)
    requires Inv(s')
    ensures MS.NextStep(I(s), I(s'), uiop, MS.QueryStep(key, value))
  {
    LookupImpliesMap(s, key, value, lookup);
  }

  lemma SuccQueryStepRefinesMap(s: Betree.Variables, s': Betree.Variables, uiop: UI.Op, start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd, lookup: Lookup)
    requires Inv(s)
    requires BetreeStepUI(BetreeSuccQuery(SuccQuery(start, results, end, lookup)), uiop)
    requires BetreeInv.SuccQuery(s.bcv, s'.bcv, start, results, end, lookup)
    requires Inv(s')
    ensures MS.NextStep(I(s), I(s'), uiop, MS.SuccStep(start, results, end))
  {
    forall i | 0 <= i < |results|
    ensures I(s).view[results[i].key] == results[i].value
    {
      LookupImpliesMap(s, results[i].key, results[i].value, lookup);
    }

    forall key | MS.InRange(start, key, end) && I(s).view[key] != MS.EmptyValue()
    ensures exists i :: 0 <= i < |results| && results[i].key == key
    {
      if (!(exists i :: 0 <= i < |results| && results[i].key == key)) {
        LookupImpliesMap(s, key, MS.EmptyValue(), lookup);
      }
    }

    assert MS.Succ(I(s), I(s'), uiop, start, results, end);
  }
  
  lemma InsertMessageStepRefinesMap(s: Betree.Variables, s': Betree.Variables, uiop: UI.Op, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(s)
    requires BetreeStepUI(BetreeInsert(MessageInsertion(key, msg, oldroot)), uiop)
    requires BetreeInv.InsertMessage(s.bcv, s'.bcv, key, msg, oldroot)
    requires Inv(s')
    ensures MS.Next(I(s), I(s'), uiop)
  {
    var value := msg.value;

    InsertMessagePreservesLookupsPut(s, s', key, msg, oldroot);
    
    PreservesLookupsPutImplInterpsPut(s, s', key, value);
    assert MS.NextStep(I(s), I(s'), uiop, MS.WriteStep(key, value));
  }

  lemma FlushStepRefinesMap(s: Betree.Variables, s': Betree.Variables, uiop: UI.Op, flush:NodeFlush)
    requires Inv(s)
    requires uiop.NoOp?
    requires BetreeInv.Flush(s.bcv, s'.bcv, flush)
    requires Inv(s')
    ensures MS.NextStep(I(s), I(s'), uiop, MS.StutterStep)
  {
    FlushPreservesLookups(s, s', Root(), flush);
    PreservesLookupsImplInterpsEqual(s, s');
    assert I(s) == I(s');
  }

  lemma GrowStepRefinesMap(s: Betree.Variables, s': Betree.Variables, uiop: UI.Op, oldroot: Node, newchildref: Reference)
    requires Inv(s)
    requires uiop.NoOp?
    requires BetreeInv.Grow(s.bcv, s'.bcv, oldroot, newchildref)
    requires Inv(s')
    ensures MS.NextStep(I(s), I(s'), uiop, MS.StutterStep)
  {
    GrowPreservesLookups(s, s', Root(), oldroot, newchildref);
    PreservesLookupsImplInterpsEqual(s, s');
    assert I(s) == I(s');
  }


  lemma RedirectRefinesMap(s: Betree.Variables, s': Betree.Variables, uiop: UI.Op, r: Betree.BetreeSpec.Redirect)
    requires Inv(s)
    requires uiop.NoOp?
    requires BetreeInv.Redirect(s.bcv, s'.bcv, r)
    requires Inv(s')
    ensures MS.NextStep(I(s), I(s'), uiop, MS.StutterStep)
  {
    RedirectPreservesLookups(s, s', Root(), r);
    PreservesLookupsImplInterpsEqual(s, s');
    assert I(s) == I(s');
  }

  lemma BetreeStepRefinesMap(s: Betree.Variables, s':Betree.Variables, uiop: UI.Op, betreeStep: BetreeInv.BetreeSpec.BetreeStep)
    requires Inv(s)
    requires BetreeStepUI(betreeStep, uiop)
    requires Betree.NextStep(s, s', uiop, Betree.BetreeStep(betreeStep))
    ensures Inv(s')
    ensures MS.Next(I(s), I(s'), uiop)
  {
    NextPreservesInv(s, s', uiop);
    match betreeStep {
      case BetreeQuery(q) => QueryStepRefinesMap(s, s', uiop, q.key, q.value, q.lookup);
      case BetreeSuccQuery(q) => SuccQueryStepRefinesMap(s, s', uiop, q.start, q.results, q.end, q.lookup);
      case BetreeInsert(ins) => InsertMessageStepRefinesMap(s, s', uiop, ins.key, ins.msg, ins.oldroot);
      case BetreeFlush(flush) => FlushStepRefinesMap(s, s', uiop, flush);
      case BetreeGrow(growth) => GrowStepRefinesMap(s, s', uiop, growth.oldroot, growth.newchildref);
      case BetreeRedirect(r) => RedirectRefinesMap(s, s', uiop, r);
    }
  }

  lemma GCStepRefinesMap(s: Betree.Variables, s':Betree.Variables, uiop: UI.Op, refs: iset<Betree.BI.Reference>)
    requires Inv(s)
    requires Betree.NextStep(s, s', uiop, Betree.GCStep(refs))
    requires Inv(s')
    ensures MS.NextStep(I(s), I(s'), uiop, MS.StutterStep)
  {
    GCStepPreservesLookups(s, s', Root(), refs);
    PreservesLookupsImplInterpsEqual(s, s');
    assert I(s) == I(s');
  }

  lemma RefinesNextStep(s: Betree.Variables, s':Betree.Variables, uiop: UI.Op, step: Betree.Step)
    requires Inv(s)
    requires Betree.NextStep(s, s', uiop, step)
    ensures Inv(s')
    ensures MS.Next(I(s), I(s'), uiop)
  {
    NextPreservesInv(s, s', uiop);
    match step {
      case BetreeStep(betreeStep) => BetreeStepRefinesMap(s, s', uiop, betreeStep);
      case GCStep(refs) => GCStepRefinesMap(s, s', uiop, refs);
      case StutterStep() => {
        assert MS.NextStep(I(s), I(s'), uiop, MS.StutterStep);
      }
    }
  }
    
  lemma RefinesNext(s: Betree.Variables, s':Betree.Variables, uiop: UI.Op)
    requires Inv(s)
    requires Betree.Next(s, s', uiop)
    ensures Inv(s')
    ensures MS.Next(I(s), I(s'), uiop)
  {
    NextPreservesInv(s, s', uiop);
    var step :| Betree.NextStep(s, s', uiop, step);
    RefinesNextStep(s, s', uiop, step);
  }
}
