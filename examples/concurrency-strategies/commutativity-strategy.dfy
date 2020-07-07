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
    else if LockFree(s, nextLock) then
      var t' := Thread(nextLock, t.victim);
      && s'.board == s.board
      && s'.threads == s.threads[tid := t']
      && ui == None
    else
      // Need to advance, but waiting on a lock
      && s' == s
      && ui == None
  }

  predicate Next(s:State, s':State, tid: int, ui:Abstract.UI) {
    || (exists victim :: Start(s, s', victim, tid, ui))
    || Advance(s, s', tid, ui)
  }
}

module ConcreteOrdered {
  import Concrete
  import Abstract
  import opened Options

  datatype Variables = Variables(
      state: Concrete.State,
      orders: map<int, int>
  )

  predicate Next(s: Variables, s': Variables, tid: int, ui:Abstract.UI, my_rank: int)
  {
    && Concrete.Next(s.state, s'.state, tid, ui)
    && (tid !in s.state.threads && tid in s'.state.threads ==>
      s'.orders == s.orders[tid := my_rank]
    )
    && (tid in s.state.threads && tid !in s'.state.threads ==>
      && s'.orders == Concrete.MapRemove1(s.orders, tid)
    )
    && (tid !in s.state.threads && tid !in s'.state.threads ==>
      && s'.orders == s.orders
    )
    && (tid in s.state.threads && tid in s'.state.threads ==>
      && tid in s.orders
      && s.orders[tid] == my_rank
      && s'.orders == s.orders
    )
  }

  predicate ThreadsOrdered(s: Variables, tid1: int, tid2: int)
  {
    tid1 in s.orders && tid2 in s.orders && s.orders[tid1] < s.orders[tid2] ==>
      && tid1 in s.state.threads
      && tid2 in s.state.threads
      && s.state.threads[tid1].lockHeld < s.state.threads[tid2].lockHeld
  }

  predicate LocksDistinct(s: Variables, tid1: int, tid2: int)
  {
    tid1 in s.state.threads && tid2 in s.state.threads && tid1 != tid2 ==>
        s.state.threads[tid1].lockHeld != s.state.threads[tid2].lockHeld
  }

  predicate Inv(s: Variables)
  {
    && (forall tid1, tid2 :: ThreadsOrdered(s, tid1, tid2))
    && (forall tid1, tid2 :: LocksDistinct(s, tid1, tid2))
  }

  lemma Commute(s: Variables, s1: Variables, s12: Variables,
      tid1: int, ui1: Abstract.UI, my_rank1: int,
      tid2: int, ui2: Abstract.UI, my_rank2: int)
  returns (s2: Variables)
  requires Inv(s)
  requires Inv(s1)
  requires Inv(s12)
  requires Next(s, s1, tid1, ui1, my_rank1)
  requires Next(s1, s12, tid2, ui2, my_rank2)
  requires my_rank1 > my_rank2
  requires tid1 != tid2
  requires !(
      && tid1 in s1.state.threads && s1.state.threads[tid1].lockHeld == 0
      && tid2 in s12.state.threads && s12.state.threads[tid2].lockHeld == 0
    )
  ensures Next(s, s2, tid2, ui2, my_rank2)
  ensures Next(s2, s12, tid1, ui1, my_rank1)
  {
    assert ThreadsOrdered(s, tid2, tid1);
    assert LocksDistinct(s, tid1, tid2);

    if Concrete.Advance(s1.state, s12.state, tid2, ui2) {
      var t := s.state.threads[tid2];
      assert t == s1.state.threads[tid2];
      assert s.state.board[t.lockHeld] == s1.state.board[t.lockHeld];

      var nextLock := t.lockHeld + 1;
      if s.state.board[t.lockHeld].stones == t.victim {
        // yay we found it!
        var board := s.state.board[t.lockHeld := s.state.board[t.lockHeld].(stones := t.victim + 1)];
        var threads := Concrete.MapRemove1(s.state.threads, tid2);
        var orders := Concrete.MapRemove1(s.orders, tid2);
        s2 := Variables(Concrete.State(board, threads), orders);

        assert ui2.Some?;
        assert ui2.value.victim == t.victim;
        assert ui2.value.outidx == Some(t.lockHeld);
        assert Concrete.Advance(s.state, s2.state, tid2, ui2);
        assert Next(s, s2, tid2, ui2, my_rank2);
      } else if |s.state.board| <= nextLock {
        var board := s.state.board;
        var threads := Concrete.MapRemove1(s.state.threads, tid2);
        var orders := Concrete.MapRemove1(s.orders, tid2);
        s2 := Variables(Concrete.State(board, threads), orders);

        assert Next(s, s2, tid2, ui2, my_rank2);
      } else if Concrete.LockFree(s.state, nextLock) {
        var t' := Concrete.Thread(nextLock, t.victim);
        var board := s.state.board;
        var threads := s.state.threads[tid2 := t'];
        var orders := s.orders;
        s2 := Variables(Concrete.State(board, threads), orders);

        assert Next(s, s2, tid2, ui2, my_rank2);
      } else {
        var board := s.state.board;
        var threads := s.state.threads;
        var orders := s.orders;
        s2 := Variables(Concrete.State(board, threads), orders);

        assert Next(s, s2, tid2, ui2, my_rank2);
      }
    } else {
      var victim :| Concrete.Start(s1.state, s12.state, victim, tid2, ui2);
      var board := s.state.board;
      var newThread := Concrete.Thread(0, victim);
      var threads := s.state.threads[tid2 := newThread];
      var orders := s.orders[tid2 := my_rank2];
      s2 := Variables(Concrete.State(board, threads), orders);

      forall id | id in s.state.threads
      ensures s.state.threads[id].lockHeld != 0
      {
        assert LocksDistinct(s, id, tid1);
        assert LocksDistinct(s, id, tid2);
        assert id != tid2;
        if id == tid1 {
          if s.state.threads[tid1].lockHeld == 0 {
            assert ThreadsOrdered(s12, tid2, tid1);
            assert tid1 in s1.state.threads;
            assert s1.state.threads[tid1].lockHeld == 0;
            assert tid2 in s12.state.threads;
            assert s12.state.threads[tid2].lockHeld == 0;
            assert false;
          }
          // Ordering is used here:
          //assert s12.state.threads[tid1].lockHeld
          //    > s12.state.threads[tid2].lockHeld;
          //assert s1.state.threads[tid1].lockHeld
          //    == s.state.threads[tid1].lockHeld;
        } else {
          assert s1.state.threads[id].lockHeld
              == s.state.threads[id].lockHeld;
        }
      }
      assert Concrete.Start(s.state, s2.state, victim, tid2, ui2);
      assert Next(s, s2, tid2, ui2, my_rank2);
    }

    assert Next(s2, s12, tid1, ui1, my_rank1);
  }
}

module TheoremProof {

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
