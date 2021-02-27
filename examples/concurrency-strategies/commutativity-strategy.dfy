// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "spec.s.dfy"

module Concrete {
  import Abstract
  import opened Options

  datatype Well = Well(stones: nat)

  datatype Thread = Thread(lockHeld: nat, victim:nat)
    // Thread's goal is to find a well containing victim stones, and add a stone to it.

  type Board = seq<Well>

  datatype State = State(board:Board, threads:map<int, Thread>)

  function View(board:Board, i:nat) : (v:seq<nat>)
    requires 0 <= i <= |board|
    ensures |v| == |board| - i
    ensures forall j | 0<=j<|v| :: v[j] == board[j+i].stones
    decreases |board| - i
  {
    if i < |board| then
      [board[i].stones] + View(board, i+1)
    else
      []
  }
 
  function {:opaque} MapRemove1<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures forall j :: j in m && j != k ==> j in m'
    ensures forall j :: j in m' ==> j in m && j != k
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures k in m ==> |m'| == |m| - 1
    ensures k !in m ==> |m'| == |m|
  {
    var m' := map j | j in m && j != k :: m[j];
    assert m'.Keys == m.Keys - {k};
    m'
  }

  predicate Init(s: State) {
    && (forall i | 0 <= i < |s.board| :: s.board[i].stones == 0)  // not necessary, just feels right
    && s.threads == map[]
  }

  predicate LockFree(s: State, lockId:nat) {
    forall t: Thread | t in s.threads.Values :: t.lockHeld != lockId
  }

  predicate Start(s: State, s':State, victim:nat, tid: int, ui:Abstract.UI) {
    var newThread := Thread(0, victim);
    && LockFree(s, 0)
    && s'.board == s.board
    && tid !in s.threads
    && s'.threads == s.threads[tid := newThread]
    && ui == None
    && s'.board == s.board
  }

  predicate Advance(s: State, s':State, tid: int, ui:Abstract.UI) {
    && tid in s.threads
    && var t := s.threads[tid];
    && var nextLock := t.lockHeld + 1;
    && 0 <= t.lockHeld < |s.board|
    && if s.board[t.lockHeld].stones == t.victim then
      // yay we found it!
      && s'.board == s.board[t.lockHeld := s.board[t.lockHeld].(stones := t.victim + 1)]
      // we're done! exit the runnable queue
      && s'.threads == MapRemove1(s.threads, tid)
      && ui == Some(Abstract.DonateOp(t.victim, Some(t.lockHeld)))
    else if |s.board| <= nextLock then
      // Ran off end of list without finding victim.
      && s'.board == s.board
      // we're done! exit the runnable queue
      && s'.threads == MapRemove1(s.threads, tid)
      && ui == Some(Abstract.DonateOp(t.victim, None))
    else
      && LockFree(s, nextLock)
      && var t' := Thread(nextLock, t.victim);
      && s'.board == s.board
      && s'.threads == s.threads[tid := t']
      && ui == None
  }

  predicate Next(s:State, s':State, tid: int, ui:Abstract.UI) {
    || (exists victim :: Start(s, s', victim, tid, ui))
    || Advance(s, s', tid, ui)
  }

  predicate LocksDistinct(s: State, tid1: int, tid2: int)
  {
    tid1 in s.threads && tid2 in s.threads && tid1 != tid2 ==>
        s.threads[tid1].lockHeld != s.threads[tid2].lockHeld
  }

  predicate Inv(s: State)
  {
    && (forall tid1, tid2 :: LocksDistinct(s, tid1, tid2))
  }

  lemma InitImpliesInv(s: State)
  requires Init(s)
  ensures Inv(s)
  {
  }

  lemma NextPreservesInv(s: State, s': State, tid: int, ui: Abstract.UI)
  requires Inv(s)
  requires Next(s, s', tid, ui)
  ensures Inv(s')
  {
    forall tid1, tid2
    ensures LocksDistinct(s', tid1, tid2)
    {
      assert LocksDistinct(s, tid1, tid2);
    }
  }
}

module ConcreteOrdered {
  import Concrete
  import Abstract
  import opened Options

  datatype Lock = HasLock(lock: int)
                | NotStarted
                | Done

  datatype LockTrans = LockTrans(from: Lock, to: Lock)

  predicate lt_less(a: LockTrans, b: LockTrans)
  {
    && (a.from.HasLock? && b.from.HasLock? ==> a.from.lock < b.from.lock)
    && (a.from.HasLock? && b.to.HasLock? ==> a.from.lock < b.to.lock)
    && (a.to.HasLock? && b.from.HasLock? ==> a.to.lock < b.from.lock)
    && (a.to.HasLock? && b.to.HasLock? ==> a.to.lock < b.to.lock)
  }

  predicate Next(s: Concrete.State, s': Concrete.State, tid: int,
      ui:Abstract.UI, lt: LockTrans)
  {
    && Concrete.Next(s, s', tid, ui)
    && (lt.from ==
      if tid in s.threads
        then HasLock(s.threads[tid].lockHeld)
        else NotStarted
    )
    && (lt.to ==
      if tid in s'.threads
        then HasLock(s'.threads[tid].lockHeld)
        else Done
    )
  }

  lemma Commute(s: Concrete.State, s1: Concrete.State, s12: Concrete.State,
      tid1: int, ui1: Abstract.UI, lt1: LockTrans,
      tid2: int, ui2: Abstract.UI, lt2: LockTrans)
  returns (s2: Concrete.State)
  requires Concrete.Inv(s)
  requires Concrete.Inv(s1)
  requires Concrete.Inv(s12)
  requires Next(s, s1, tid1, ui1, lt1)
  requires Next(s1, s12, tid2, ui2, lt2)
  requires lt_less(lt1, lt2)
  requires tid1 != tid2
  ensures Next(s, s2, tid2, ui2, lt2)
  ensures Next(s2, s12, tid1, ui1, lt1)
  {
    assert Concrete.LocksDistinct(s, tid1, tid2);

    if Concrete.Advance(s1, s12, tid2, ui2) {
      var t := s.threads[tid2];
      assert t == s1.threads[tid2];
      assert s.board[t.lockHeld] == s1.board[t.lockHeld];

      var nextLock := t.lockHeld + 1;
      if s.board[t.lockHeld].stones == t.victim {
        // yay we found it!
        var board := s.board[t.lockHeld := s.board[t.lockHeld].(stones := t.victim + 1)];
        var threads := Concrete.MapRemove1(s.threads, tid2);
        s2 := Concrete.State(board, threads);

        assert ui2.Some?;
        assert ui2.value.victim == t.victim;
        assert ui2.value.outidx == Some(t.lockHeld);
        assert Concrete.Advance(s, s2, tid2, ui2);
        assert Next(s, s2, tid2, ui2, lt2);
      } else if |s.board| <= nextLock {
        var board := s.board;
        var threads := Concrete.MapRemove1(s.threads, tid2);
        s2 := Concrete.State(board, threads);

        assert Next(s, s2, tid2, ui2, lt2);
      } else {
        var t' := Concrete.Thread(nextLock, t.victim);
        var board := s.board;
        var threads := s.threads[tid2 := t'];
        s2 := Concrete.State(board, threads);

        assert Concrete.LockFree(s1, nextLock);
        assert lt2.to == HasLock(nextLock);
        forall id | id in s.threads
        ensures s.threads[id].lockHeld != nextLock
        {
          if id == tid1 {
            assert s.threads[id].lockHeld != nextLock;
          } else {
            assert s.threads[id].lockHeld
                == s1.threads[id].lockHeld;
            assert s.threads[id].lockHeld != nextLock;
          }
        }
        assert Concrete.LockFree(s, nextLock);

        assert Concrete.Advance(s, s2, tid2, ui2);
        assert Next(s, s2, tid2, ui2, lt2);
      }
    } else {
      var victim :| Concrete.Start(s1, s12, victim, tid2, ui2);
      var board := s.board;
      var newThread := Concrete.Thread(0, victim);
      var threads := s.threads[tid2 := newThread];
      s2 := Concrete.State(board, threads);

      forall id | id in s.threads
      ensures s.threads[id].lockHeld != 0
      {
        if id == tid1 {
          assert s.threads[id].lockHeld != 0;
        } else {
          assert s.threads[id].lockHeld
              == s1.threads[id].lockHeld;
          assert s.threads[id].lockHeld != 0;
        }
      }

      assert Concrete.Start(s, s2, victim, tid2, ui2);
      assert Next(s, s2, tid2, ui2, lt2);
    }

    if Concrete.Advance(s, s1, tid1, ui1) {
      assert Concrete.Advance(s2, s12, tid1, ui1);
      assert Next(s2, s12, tid1, ui1, lt1);
    } else {
      var victim :| Concrete.Start(s, s1, victim, tid1, ui1);
      assert Concrete.Start(s2, s12, victim, tid1, ui1);
      assert Next(s2, s12, tid1, ui1, lt1);
    }
  }
}

module TheoremProof {
  import Abstract
  import Concrete
  import ConcreteOrdered

  datatype Edge = Edge(
      ui: Abstract.UI,
      tid: int
  )

  datatype Trace = Behavior(
      states: seq<Concrete.State>,
      edges: seq<Edge>
  )

  datatype SEdge = SEdge(
      ui: Abstract.UI,
      lt: ConcreteOrdered.LockTrans,
      tid: int,
      order: int
  )

  datatype SState = SState(
    state: Concrete.State,
    thread_map: map<int, int>,
    largest_so_far: int
  )

  datatype STrace = STrace(
    states: seq<SState>,
    edges: seq<SEdge>
  )

  predicate ThreadMapUpdate(s: SState, s': SState, tid: int, order: int)
  {
    if tid in s.state.threads then (
      if tid in s'.state.threads then (
        && s'.thread_map == s.thread_map
        && s'.largest_so_far == s.largest_so_far
        && tid in s.thread_map
        && order == s.thread_map[tid]
      ) else (
        && s'.thread_map == Concrete.MapRemove1(s.thread_map, tid)
        && s'.largest_so_far == s.largest_so_far
        && tid in s.thread_map
        && order == s.thread_map[tid]
      )
    ) else (
      if tid in s'.state.threads then (
        && s'.thread_map == s.thread_map[tid := s.largest_so_far + 1]
        && s'.largest_so_far == s.largest_so_far + 1
        && order == s.largest_so_far + 1
      ) else (
        && s'.thread_map == s.thread_map
        && s'.largest_so_far == s.largest_so_far + 1
        && order == s.largest_so_far + 1
      )
    )
  }

  predicate WFSTraceAt(trace: STrace, i: int)
  requires 0 <= i < |trace.edges|
  requires i+1 < |trace.states|
  {
    && ConcreteOrdered.Next(
      trace.states[i].state,
      trace.states[i+1].state, 
      trace.edges[i].tid,
      trace.edges[i].ui,
      trace.edges[i].lt
    )
    && ThreadMapUpdate(
      trace.states[i],
      trace.states[i+1],
      trace.edges[i].tid,
      trace.edges[i].order
    )
  }

  predicate WFSTrace(trace: STrace)
  {
    && |trace.states| == |trace.edges| + 1
    && Concrete.Init(trace.states[0].state)
    && (forall i | 0 <= i < |trace.edges| :: WFSTraceAt(trace, i))
    && trace.states[0].thread_map == map[]
  }

  lemma inv_at(trace: STrace, i: int)
  requires WFSTrace(trace)
  requires 0 <= i < |trace.states|
  ensures Concrete.Inv(trace.states[i].state)
  {
    if (i == 0) {
      Concrete.InitImpliesInv(trace.states[0].state);
    } else {
      inv_at(trace, i-1);
      assert WFSTraceAt(trace, i-1);
      Concrete.NextPreservesInv(
          trace.states[i-1].state,
          trace.states[i].state,
          trace.edges[i-1].tid,
          trace.edges[i-1].ui);
    }
  }

  lemma le_largest_so_far(trace: STrace, i: int, tid: int)
  requires WFSTrace(trace)
  requires 0 <= i < |trace.states|
  requires tid in trace.states[i].thread_map
  ensures trace.states[i].thread_map[tid] <= trace.states[i].largest_so_far
  {
    if i == 0 {
    } else {
      assert WFSTraceAt(trace, i-1);
      if tid in trace.states[i-1].thread_map {
        le_largest_so_far(trace, i-1, tid);
      } else {
      }
    }
  }

  lemma order_le_largest_so_far(trace: STrace, i: int)
  requires WFSTrace(trace)
  requires 0 <= i < |trace.edges|
  ensures trace.edges[i].order <= trace.states[i+1].largest_so_far
  {
    var tid := trace.edges[i].tid;
    assert WFSTraceAt(trace, i);
    if tid in trace.states[i].thread_map {
      le_largest_so_far(trace, i, tid);
    } else {
    }
  }

  lemma lock_order(trace: STrace, i: int, tid1: int, tid2: int)
  requires WFSTrace(trace)
  requires 0 <= i < |trace.edges| - 1
  requires tid1 in trace.states[i].thread_map
  requires tid2 in trace.states[i].thread_map
  requires trace.states[i].thread_map[tid1]
         > trace.states[i].thread_map[tid2]
  requires tid1 in trace.states[i].state.threads
  requires tid2 in trace.states[i].state.threads
  ensures trace.states[i].state.threads[tid1].lockHeld
         < trace.states[i].state.threads[tid2].lockHeld;
  {
    assert WFSTraceAt(trace, i);
    assert i > 0;
    assert WFSTraceAt(trace, i-1);
    if (trace.edges[i-1].tid == tid1) {
      if tid1 in trace.states[i-1].state.threads {
        lock_order(trace, i-1, tid1, tid2);

        assert trace.states[i].state.threads[tid1].lockHeld
             < trace.states[i].state.threads[tid2].lockHeld;
      } else {
        assert trace.states[i].state.threads[tid1].lockHeld
             < trace.states[i].state.threads[tid2].lockHeld;
      }
    } else if (trace.edges[i-1].tid == tid2) {
      le_largest_so_far(trace, i-1, tid1);
      assert trace.states[i-1].thread_map[tid1] <= trace.states[i].largest_so_far;

      assert tid2 in trace.states[i-1].thread_map;

      lock_order(trace, i-1, tid1, tid2);
      assert trace.states[i].state.threads[tid1].lockHeld
           < trace.states[i].state.threads[tid2].lockHeld;
    } else {
      lock_order(trace, i-1, tid1, tid2);
      assert trace.states[i].state.threads[tid1].lockHeld
           < trace.states[i].state.threads[tid2].lockHeld;
    }
  }

  lemma lt_less_at(trace: STrace, i: int)
  requires WFSTrace(trace)
  requires 0 <= i < |trace.edges| - 1
  requires trace.edges[i].order > trace.edges[i+1].order
  ensures ConcreteOrdered.lt_less(trace.edges[i].lt, trace.edges[i+1].lt);
  {
    var tid1 := trace.edges[i].tid;
    var tid2 := trace.edges[i+1].tid;
    assert WFSTraceAt(trace, i);
    assert WFSTraceAt(trace, i+1);

    order_le_largest_so_far(trace, i);
    assert trace.edges[i].order <= trace.states[i+1].largest_so_far;
    assert tid2 in trace.states[i+1].thread_map;

    assert tid1 != tid2; /* by {
      if tid1 == tid2 {
        assert tid1 in trace.states[i].thread_map;
        assert tid1 in trace.states[i+1].thread_map;
        assert trace.edges[i].order
            == trace.states[i].thread_map[tid1]
            == trace.states[i+1].thread_map[tid1]
            == trace.edges[i+1].order;
      }
    }*/

    if (tid2 in trace.states[i].state.threads) {
      assert trace.states[i].state.threads[tid2]
          == trace.states[i+1].state.threads[tid2];
    }

    if (tid1 in trace.states[i].state.threads) {
      lock_order(trace, i, tid1, tid2);
      assert trace.states[i].state.threads[tid1].lockHeld
           < trace.states[i].state.threads[tid2].lockHeld;
      if (tid1 in trace.states[i+1].state.threads) {
        assert trace.states[i].state.threads[tid1].lockHeld + 1
            != trace.states[i].state.threads[tid2].lockHeld;
      }
    } else {
      assert 0
           < trace.states[i].state.threads[tid2].lockHeld;
    }
  }

  lemma do_commute(trace: STrace, i: int) returns (trace': STrace)
  requires WFSTrace(trace)
  requires 0 <= i < |trace.edges| - 1
  requires trace.edges[i].order > trace.edges[i+1].order
  ensures WFSTrace(trace')
  {
    inv_at(trace, i);
    inv_at(trace, i+1);
    inv_at(trace, i+2);
    assert WFSTraceAt(trace, i);
    assert WFSTraceAt(trace, i+1);
    lt_less_at(trace, i);
    var s' := ConcreteOrdered.Commute(
        trace.states[i].state,
        trace.states[i+1].state,
        trace.states[i+2].state,
        trace.edges[i].tid,
        trace.edges[i].ui,
        trace.edges[i].lt,
        trace.edges[i+1].tid,
        trace.edges[i+1].ui,
        trace.edges[i+1].lt);

    var s := trace.states[i];
    var state';
    var tid := trace.edges[i+1].tid;
    if tid in s.state.threads {
      if tid in s'.threads {
        state' := SState(s', s.thread_map, s.largest_so_far);
      } else {
        state' := SState(
          s',
          Concrete.MapRemove1(s.thread_map, tid),
          s.largest_so_far);
      }
    } else {
      if tid in s'.threads {
        state' := SState(
          s',
          s.thread_map[tid := s.largest_so_far + 1],
          s.largest_so_far + 1);
      } else {
        state' := SState(
          s',
          s.thread_map,
          s.largest_so_far + 1);
      }
    }
    assert ThreadMapUpdate(trace.states[i], state', 
            trace.edges[i+1].tid, trace.edges[i+1].order);
    var states' := trace.states[i+1 := state'];
    var edges' := trace.edges
        [i := trace.edges[i+1]]
        [i+1 := trace.edges[i]];

    trace' := STrace(states', edges');

    forall i | 0 <= i < |trace'.edges| ensures WFSTraceAt(trace', i)
    {
      assert WFSTraceAt(trace, i);
    }
  }

  /*lemma Correctness(b:Behavior<Concrete.State>, I:CState->AState)
    requires Reachable(b, Concrete.Init, Concrete.Next)
    ensures var ab := Interpret(b, I); Reachable(ab, Abstract.Init, Abstract.Next)
  {
    var ab := Interpret(b, I);

    if (b is in the good TLA order) {
      call the tla refinement proof
    } else {
      pick an index very carefully:
        - terminates
        - can satisfy ind. hyp.
      var b' := swap(b, idx)
      assert Reachable(b', Concrete.Init, Concrete.Next);
 
      var ab' := Interpret(b', I);  // required by spec
      Correctness(b', I);
      assert Reachable(ab', Abstract.Init, Abstract.Next);


      assert Reachable(ab, Abstract.Init, Abstract.Next);
    }
  }*/
  

}
