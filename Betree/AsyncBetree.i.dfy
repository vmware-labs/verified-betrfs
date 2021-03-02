// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "QueryState.i.dfy"
include "Betree.i.dfy"
include "BetreeInv.i.dfy"

module AsyncBetree {
  import opened G = BetreeGraph
  import Betree
  import opened QueryStates
  import opened BetreeSpec`Internal
  import opened Maps
  import opened ValueType
  import opened KeyType
  import BetreeInv
  import BI = BetreeBlockInterface
  import UI
  
  datatype Variables = Variables(
      betree: Betree.Variables,
      queries: map<int, QueryState>)

  predicate Init(s: Variables)
  {
    && Betree.Init(s.betree)
    && s.queries == map[]
  }

  datatype Step =
    | BasicStep(betreeStep: Betree.Step)
    | QueryBeginStep
    | QueryEndStep
    | QueryAdvanceStep(ghost id: int, descent: QueryDescent)
    | StutterStep

  predicate AvoidsQueries(ref: Reference, queries: map<int, QueryState>)
  {
    forall q | q in queries.Values && q.InProgress? :: ref != q.ref
  }

  predicate Basic(s: Variables, s': Variables, uiop: UI.Op, betreeStep: Betree.Step)
  {
    && s'.queries == s.queries
    && Betree.NextStep(s.betree, s'.betree, uiop, betreeStep)
    && (betreeStep.BetreeStep? && betreeStep.step.BetreeInsert?
        ==> AvoidsQueries(Root(), s.queries))
    && (betreeStep.GCStep? ==> forall r | r in betreeStep.refs :: AvoidsQueries(r, s.queries))
  }

  predicate QueryBegin(s: Variables, s': Variables, uiop: UI.Op)
  {
    && uiop.GetBeginOp?
    && uiop.id !in s.queries
    && s'.betree == s.betree
    && s'.queries == s.queries[uiop.id :=
        InProgress(uiop.key, G.M.NopDelta(), Root())]
  }

  predicate QueryEnd(s: Variables, s': Variables, uiop: UI.Op)
  {
    && uiop.GetEndOp?
    && uiop.id in s.queries
    && s'.betree == s.betree
    && s'.queries == MapRemove1(s.queries, uiop.id)
    && s.queries[uiop.id].Finished?
    && uiop.value == s.queries[uiop.id].answer
  }

  predicate QueryAdvance(s: Variables, s': Variables, uiop: UI.Op, id: int, qd: QueryDescent)
  {
    && s'.betree == s.betree
    && id in s.queries
    && id in s'.queries
    && ValidQueryDescent(qd)
    && qd.query == s.queries[id] 
    && qd.query' == s'.queries[id] 
    && s'.queries == s.queries[id := qd.query']
    && BI.Reads(s.betree.bcv, QueryDescentReads(qd))
  }

  predicate NextStep(s: Variables, s': Variables, uiop: UI.Op, step: Step)
  {
    match step {
      case BasicStep(betreeStep) => Basic(s, s', uiop, betreeStep)
      case QueryBeginStep => QueryBegin(s, s', uiop)
      case QueryEndStep => QueryEnd(s, s', uiop)
      case QueryAdvanceStep(id, qd) => QueryAdvance(s, s', uiop, id, qd)
      case StutterStep => s == s' && uiop.NoOp?
    }
  }

  predicate Next(s: Variables, s': Variables, uiop: UI.Op)
  {
    exists step :: NextStep(s, s', uiop, step)
  }

  predicate QueryInv(betree: Betree.Variables, qs: QueryState)
  {
    qs.InProgress? ==>
      BetreeInv.KeyHasSatisfyingLookup(betree.bcv.view, qs.key, qs.ref)
  }

  predicate Inv(s: Variables)
  {
    && BetreeInv.Inv(s.betree)
    && (forall id | id in s.queries :: QueryInv(s.betree, s.queries[id]))
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
    BetreeInv.InitImpliesInv(s.betree);
  }

  lemma BasicStepPreservesQueryInv(betree: Betree.Variables, betree': Betree.Variables,
      uiop: UI.Op, step: Betree.Step, qs: QueryState)
  requires BetreeInv.Inv(betree)
  requires Betree.NextStep(betree, betree', uiop, step)
  requires QueryInv(betree, qs)
  requires qs.InProgress?
  requires (step.BetreeStep? && step.step.BetreeInsert? ==> qs.ref != Root())
  requires (step.GCStep? ==> qs.ref !in step.refs)
  ensures QueryInv(betree', qs)
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
  }

  lemma QueryAdvanceChangesLookup(betree: Betree.Variables, qd: QueryDescent, lookup: Lookup, value: Value)
  returns (lookup': Lookup, value': Value)
  requires BetreeInv.Inv(betree)
  requires QueryInv(betree, qd.query)
  requires ValidQueryDescent(qd)
  requires BI.Reads(betree.bcv, QueryDescentReads(qd))
  requires |lookup| > 0
  requires lookup[0].ref == qd.query.ref
  requires BetreeInv.IsSatisfyingLookup(betree.bcv.view, qd.query.key, value, lookup)
  ensures qd.query'.InProgress? ==>
      && |lookup'| > 0
      && lookup'[0].ref == qd.query'.ref
      && BetreeInv.IsSatisfyingLookup(betree.bcv.view, qd.query'.key, value', lookup')
      && G.M.ApplyDelta(qd.query.delta, value)
          == G.M.ApplyDelta(qd.query'.delta, value')
  ensures qd.query'.Finished? ==>
      && G.M.ApplyDelta(qd.query.delta, value)
          == qd.query'.answer
  {
    lookup' := lookup[1..];
    var l0 := [lookup[0]];
    assert l0 + lookup' == lookup; 
    BetreeInv.InterpretLookupAdditive(l0, lookup', qd.query.key);

    if qd.query'.InProgress? {
      if |lookup| == 1 {
        // Can't have this case: if this is the last node in the lookup,
        // then we would have gone to the Finished state instead.
        assert betree.bcv.view[qd.query.ref].buffer[qd.query.key].Define?;
        assert false;
      }

      assert |lookup| >= 2;

      var m' := InterpretLookup(lookup', qd.query.key);
      assert m'.Define?;
      value' := m'.value;

      assert LookupFollowsChildRefAtLayer(qd.query.key, lookup, 0);

      forall idx | 0 <= idx < |lookup'| - 1
      ensures LookupFollowsChildRefAtLayer(qd.query'.key, lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(qd.query'.key, lookup, idx+1);
        assert lookup'[idx] == lookup[idx+1];
        assert lookup'[idx+1] == lookup[idx+2];
      }

      G.M.ApplyIsAssociative(qd.query.delta, 
          betree.bcv.view[qd.query.ref].buffer[qd.query.key].delta,
          value');
    } else {
    }
  }

  lemma QueryAdvancePreservesInv(betree: Betree.Variables, qd: QueryDescent)
  requires BetreeInv.Inv(betree)
  requires QueryInv(betree, qd.query)
  requires ValidQueryDescent(qd)
  requires BI.Reads(betree.bcv, QueryDescentReads(qd))
  ensures QueryInv(betree, qd.query')
  {
    var lookup: Lookup, value :|
      && BetreeInv.IsSatisfyingLookup(betree.bcv.view, qd.query.key, value, lookup)
      && lookup[0].ref == qd.query.ref;
    var lookup', value' := QueryAdvanceChangesLookup(betree, qd, lookup, value);
  }
 
  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires Next(s, s', uiop)
  ensures Inv(s')
  {
    var step :| NextStep(s, s', uiop, step);

    match step {
      case BasicStep(betreeStep) => {
        BetreeInv.NextStepPreservesInvariant(s.betree, s'.betree, uiop, betreeStep);
        forall id | id in s'.queries ensures QueryInv(s'.betree, s'.queries[id])
        {
          if s.queries[id].InProgress? {
            BasicStepPreservesQueryInv(s.betree, s'.betree, uiop, betreeStep, s.queries[id]);
          }
        }
        assert Inv(s');
      }
      case QueryBeginStep => {
        assert Inv(s');
      }
      case QueryEndStep => {
        assert Inv(s');
      }
      case QueryAdvanceStep(id, qd) => {
        QueryAdvancePreservesInv(s.betree, qd);
        assert Inv(s');
      }
      case StutterStep => {
        assert Inv(s');
      }
    }
  }


/*
  lemma QueryBeginStepPreservesInvariant(s: Variables, s': Variables, uiop: UI.Op, query: LookupQuery)
    requires Inv(s)
    requires QueryBegin(s, s', uiop, query)
    ensures Inv(s')
  {
    var qs := InProgress(uiop.key, G.M.NopDelta(), Root(), query.value);

    forall i | 0 <= i < |query.lookup|
    ensures IMapsTo(s.bcv.view, query.lookup[i].ref, query.lookup[i].node)
    {
      assert BI.ReadStep(s.bcv, query.lookup[i]);
    }

    assert IsSatisfyingLookup(s.bcv.view, qs.key, qs.answer, query.lookup);
    assert QueryStateInv(s.bcv, qs);
  }

  lemma QueryEndStepPreservesInvariant(s: Variables, s': Variables, uiop: UI.Op)
    requires Inv(s)
    requires QueryEnd(s, s', uiop)
    ensures Inv(s')
  {
  }
*/
}
