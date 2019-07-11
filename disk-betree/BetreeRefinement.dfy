include "Betree.dfy"
include "MapSpec.dfy"
include "BetreeInv.dfy"

abstract module BetreeRefinement {
  import opened DBI = BetreeInv
  import opened G = BetreeGraph
  import opened BetreeSpec`Internal
  import ValueMessage`Internal
  import opened Maps

  type UIOp = DB.MS.UI.Op
    
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
  
  function I(k: DB.Constants, s: DB.Variables) : DB.MS.Variables
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
        PreservesLookupsRevExcept(k, s, s', key);
        var lookup'' :| DB.IsSatisfyingLookup(k, view, key', value', lookup'');
        CantEquivocate(k, s, key', value, value', lookup, lookup'');
        assert value == value';
      }
    }
  }

  lemma QueryStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UIOp, key: Key, value: Value, lookup: Lookup)
    requires Inv(k, s)
    requires BetreeStepUI(BetreeQuery(LookupQuery(key, value, lookup)), uiop)
    requires DBI.Query(k.bck, s.bcv, s'.bcv, key, value, lookup)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.QueryStep(key, value))
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
  
  lemma InsertMessageStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UIOp, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires BetreeStepUI(BetreeInsert(MessageInsertion(key, msg, oldroot)), uiop)
    requires DBI.InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    requires Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var value := msg.value;

    InsertMessagePreservesLookupsPut(k, s, s', key, msg, oldroot);
    
    PreservesLookupsPutImplInterpsPut(k, s, s', key, value);
    assert DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.WriteStep(key, value));
  }

  lemma FlushStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UIOp,
                                           parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, movedKeys: iset<Key>)
    requires Inv(k, s)
    requires uiop.NoOp?
    requires DBI.Flush(k.bck, s.bcv, s'.bcv, parentref, parent, childref, child, newchildref, movedKeys)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.StutterStep)
  {
    FlushPreservesLookups(k, s, s', parentref, parent, childref, child, newchildref, movedKeys);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma GrowStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UIOp, oldroot: Node, newchildref: Reference)
    requires Inv(k, s)
    requires uiop.NoOp?
    requires DBI.Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.StutterStep)
  {
    GrowPreservesLookups(k, s, s', oldroot, newchildref);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma RedirectStepRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UIOp, redirect: DB.BetreeSpec.Redirect)
    requires Inv(k, s)
    requires uiop.NoOp?
    requires DBI.Redirect(k.bck, s.bcv, s'.bcv, redirect)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.StutterStep)
  {
    RedirectPreservesLookups(k, s, s', redirect);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma RedirectRefinesMap(k: DB.Constants, s: DB.Variables, s': DB.Variables, uiop: UIOp, r: DB.BetreeSpec.Redirect)
    requires Inv(k, s)
    requires uiop.NoOp?
    requires DBI.Redirect(k.bck, s.bcv, s'.bcv, r)
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.StutterStep)
  {
    RedirectPreservesLookups(k, s, s', r);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma BetreeStepRefinesMap(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UIOp, betreeStep: DBI.BetreeSpec.BetreeStep)
    requires Inv(k, s)
    requires BetreeStepUI(betreeStep, uiop)
    requires DB.NextStep(k, s, s', uiop, DB.BetreeStep(betreeStep))
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    NextPreservesInv(k, s, s', uiop);
    match betreeStep {
      case BetreeQuery(q) => QueryStepRefinesMap(k, s, s', uiop, q.key, q.value, q.lookup);
      case BetreeInsert(ins) => InsertMessageStepRefinesMap(k, s, s', uiop, ins.key, ins.msg, ins.oldroot);
      case BetreeFlush(flush) => FlushStepRefinesMap(k, s, s', uiop, flush.parentref, flush.parent, flush.childref, flush.child, flush.newchildref, flush.movedKeys);
      case BetreeGrow(growth) => GrowStepRefinesMap(k, s, s', uiop, growth.oldroot, growth.newchildref);
      case BetreeRedirect(r) => RedirectRefinesMap(k, s, s', uiop, r);
    }
  }

  lemma GCStepRefinesMap(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UIOp, refs: iset<DB.BI.Reference>)
    requires Inv(k, s)
    requires DB.NextStep(k, s, s', uiop, DB.GCStep(refs))
    requires Inv(k, s')
    ensures DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.StutterStep)
  {
    GCStepPreservesLookups(k, s, s', refs);
    PreservesLookupsImplInterpsEqual(k, s, s');
    assert I(k, s) == I(k, s');
  }

  lemma BetreeRefinesMapNextStep(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UIOp, step: DB.Step)
    requires Inv(k, s)
    requires DB.NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    NextPreservesInv(k, s, s', uiop);
    match step {
      case BetreeStep(betreeStep) => BetreeStepRefinesMap(k, s, s', uiop, betreeStep);
      case GCStep(refs) => GCStepRefinesMap(k, s, s', uiop, refs);
      case StutterStep() => {
        assert DB.MS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, DB.MS.StutterStep);
      }
    }
  }
    
  lemma BetreeRefinesMapNext(k: DB.Constants, s: DB.Variables, s':DB.Variables, uiop: UIOp)
    requires Inv(k, s)
    requires DB.Next(k, s, s', uiop)
    ensures Inv(k, s')
    ensures DB.MS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    NextPreservesInv(k, s, s', uiop);
    var step :| DB.NextStep(k, s, s', uiop, step);
    BetreeRefinesMapNextStep(k, s, s', uiop, step);
  }
}
