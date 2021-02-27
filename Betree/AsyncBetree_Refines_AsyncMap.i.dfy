// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "AsyncBetree.i.dfy"
include "../MapSpec/AsyncMap.i.dfy"
include "BetreeInv.i.dfy"
include "Betree_Refines_Map.i.dfy"

module AsyncBetree_Refines_AsyncMap {
  import AM = AsyncMapSpec
  import MS = MapSpec
  import opened AB = AsyncBetree
  import Betree_Refines_Map
  import Betree
  import opened QueryStates
  import opened ValueType
  import opened KeyType
  import opened BetreeGraph

  function QueryAnswer(betree: Betree.Variables, query: QueryState) : Value
  requires QueryInv(betree, query)
  {
    match query {
      case InProgress(key, delta, ref) => (
        G.M.ApplyDelta(delta,
            Betree_Refines_Map.GetLookup(betree.bcv.view, query.key, ref).result)
      )
      case Finished(key, answer) => answer
    }
  }

  function IQueries(s: Variables) : map<int, Value>
  requires forall id | id in s.queries :: QueryInv(s.betree, s.queries[id])
  {
    map id | id in s.queries :: QueryAnswer(s.betree, s.queries[id])
  }

  function I(s: Variables) : AM.Variables
  requires Inv(s)
  {
    AM.Variables(
      Betree_Refines_Map.I(s.betree),
      IQueries(s)
    )
  }

  lemma RefinesInit(s: Variables)
    requires Init(s)
    ensures Inv(s)
    ensures AM.Init(I(s))
  {
    Betree_Refines_Map.RefinesInit(s.betree);
  }

  lemma RefinesQueryBeginStep(s: Variables, s':Variables, uiop: UI.Op)
  requires Inv(s)
  requires QueryBegin(s, s', uiop)
  requires Inv(s')
  ensures AM.Next(I(s), I(s'), uiop)
  {
    var qs := InProgress(uiop.key, G.M.NopDelta(), Root());
    assert QueryAnswer(s.betree, qs) == I(s).dict.view[qs.key];
    assert AM.NextStep(I(s), I(s'), uiop, AM.QueryBeginStep(qs.key));
  }

  lemma RefinesQueryEndStep(s: Variables, s':Variables, uiop: UI.Op)
  requires Inv(s)
  requires QueryEnd(s, s', uiop)
  requires Inv(s')
  ensures AM.Next(I(s), I(s'), uiop)
  {
    var qs := s.queries[uiop.id];
    assert AM.NextStep(I(s), I(s'), uiop, AM.QueryEndStep(qs.answer));
  }

  lemma RefinesQueryAdvanceStep(s: Variables, s':Variables,
      uiop: UI.Op, id: int, descent: QueryDescent)
  requires Inv(s)
  requires QueryAdvance(s, s', uiop, id, descent)
  requires Inv(s')
  ensures AM.Next(I(s), I(s'), uiop)
  {
    var res := Betree_Refines_Map.GetLookup(s.betree.bcv.view,
        descent.query.key, descent.query.ref);
    var lookup := res.lookup;
    var value := res.result;

    var lookup2, value2 := QueryAdvanceChangesLookup(s.betree, descent, lookup, value);

    if descent.query'.InProgress? {
      var res' := Betree_Refines_Map.GetLookup(s'.betree.bcv.view,
          descent.query'.key, descent.query'.ref);
      var lookup' := res'.lookup;
      var value' := res'.result;

      BetreeInv.CantEquivocate(s.betree, descent.query.key, value', value2, lookup', lookup2);
    }

    assert QueryAnswer(s.betree, descent.query)
        == QueryAnswer(s.betree, descent.query');
    assert AM.NextStep(I(s), I(s'), uiop, AM.StutterStep);
  }

  lemma BasicStepPreservesIQuery(betree: Betree.Variables, betree': Betree.Variables,
      uiop: UI.Op, step: Betree.Step, qs: QueryState)
  requires BetreeInv.Inv(betree)
  requires Betree.NextStep(betree, betree', uiop, step)
  requires QueryInv(betree, qs)
  requires qs.InProgress?
  requires (step.BetreeStep? && step.step.BetreeInsert? ==> qs.ref != Root())
  requires (step.GCStep? ==> qs.ref !in step.refs)
  ensures QueryInv(betree', qs)
  ensures QueryAnswer(betree, qs) == QueryAnswer(betree', qs)
  {
    match step {
      case BetreeStep(betreeStep) => {
        match betreeStep {
          case BetreeQuery(q) => {
          }
          case BetreeSuccQuery(sq) => {
          }
          case BetreeInsert(ins) => {
            assert qs.ref != Root();
            BetreeInv.InsertMessagePreservesNonrootLookups(
                betree, betree', ins.key, ins.msg, ins.oldroot, qs.ref);
          }
          case BetreeFlush(flush) => {
            BetreeInv.FlushPreservesLookups(betree, betree', qs.ref, flush);
          }
          case BetreeGrow(growth) => {
            BetreeInv.GrowPreservesLookups(
                betree, betree', qs.ref, growth.oldroot, growth.newchildref);
          }
          case BetreeRedirect(redirect) => {
            BetreeInv.RedirectPreservesLookups(betree, betree', qs.ref, redirect);
          }
        }
      }
      case GCStep(refs) => {
        BetreeInv.GCStepPreservesLookups(betree, betree', qs.ref, refs);
      }
      case StutterStep => {
      }
    }

    var res := Betree_Refines_Map.GetLookup(betree.bcv.view, qs.key, qs.ref);
    var lookup := res.lookup;
    var value := res.result;

    var res' := Betree_Refines_Map.GetLookup(betree'.bcv.view, qs.key, qs.ref);
    var lookup' := res'.lookup;
    var value' := res'.result;

    var lookup2 :|
      BetreeInv.IsSatisfyingLookupFrom(betree'.bcv.view, qs.key, value, lookup2, qs.ref);

    BetreeInv.CantEquivocate(betree', qs.key, value', value, lookup', lookup2);
  }

  lemma RefinesNextStep(s: Variables, s':Variables, uiop: UI.Op, step: Step)
    requires Inv(s)
    requires NextStep(s, s', uiop, step)
    ensures Inv(s')
    ensures AM.Next(I(s), I(s'), uiop)
  {
    NextPreservesInv(s, s', uiop);
    match step {
      case BasicStep(betreeStep) => {
        Betree_Refines_Map.RefinesNextStep(s.betree, s'.betree, uiop, betreeStep);
        assert s.queries == s'.queries;

        forall id | id in s.queries
        ensures QueryAnswer(s.betree, s.queries[id])
             == QueryAnswer(s'.betree, s.queries[id])
        {
          if s.queries[id].InProgress? {
            BasicStepPreservesIQuery(s.betree, s'.betree, uiop, betreeStep, s.queries[id]);
          }
        }
        assert IQueries(s) == IQueries(s');

        var mapstep :| MS.NextStep(
            Betree_Refines_Map.I(s.betree),
            Betree_Refines_Map.I(s'.betree),
            uiop, mapstep);
        match mapstep {
          case QueryStep(key, result) => {
            assert AM.NextStep(I(s), I(s'), uiop, AM.QueryStep(key, result));
          }
          case WriteStep(key, new_value) => {
            assert AM.NextStep(I(s), I(s'), uiop, AM.WriteStep(key, new_value));
          }
          case SuccStep(start, results, end) => {
            assert AM.NextStep(I(s), I(s'), uiop, AM.SuccStep(start, results, end));
          }
          case StutterStep() => {
            assert AM.NextStep(I(s), I(s'), uiop, AM.StutterStep);
          }
        }
      }
      case QueryBeginStep => {
        RefinesQueryBeginStep(s, s', uiop);
      }
      case QueryEndStep => {
        RefinesQueryEndStep(s, s', uiop);
      }
      case QueryAdvanceStep(id, qd) => {
        RefinesQueryAdvanceStep(s, s', uiop, id, qd);
      }
      case StutterStep => {
        assert AM.NextStep(I(s), I(s'), uiop, AM.StutterStep);
      }
    }
  }
    
  lemma RefinesNext(s: Variables, s':Variables, uiop: UI.Op)
    requires Inv(s)
    requires Next(s, s', uiop)
    ensures Inv(s')
    ensures AM.Next(I(s), I(s'), uiop)
  {
    NextPreservesInv(s, s', uiop);
    var step :| NextStep(s, s', uiop, step);
    RefinesNextStep(s, s', uiop, step);
  }
}
