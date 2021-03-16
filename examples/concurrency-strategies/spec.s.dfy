// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"

module Abstract {
  import opened Options

  type View = seq<nat>

  datatype Op =
    | DonateOp(victim:nat, outidx: Option<nat>)
  type UI = Option<Op>

  function LeastIndexOf(view:View, victim:nat) : (idx:Option<nat>)
    ensures idx.None? ==> 
      forall j | 0 <= j < |view| :: view[j] != victim
    ensures idx.Some? ==>
      && idx.value < |view|
      && view[idx.value] == victim
      && forall j | 0 <= j < idx.value :: view[j] != victim
  {
    if |view| == 0 then None else (
      if view[0] == victim then Some(0) else (
        var t := LeastIndexOf(view[1..], victim);
        if t.Some? then (
          Some(t.value + 1)
        ) else (
          None
        )
      )
    )
  }

  function Donate(view:View, victim:nat) : (View, Option<nat>) {
    var outidx := LeastIndexOf(view, victim);
    var view' := (
      if outidx.None? then
        view
      else
        view[outidx.value := victim + 1]
    );
    (view', outidx)
  }

  datatype State = State(board:View)

  predicate DonateStep(s:State, s':State, victim:nat, ui:UI) {
    var (view',outidx) := Donate(s.board, victim);
    && s' == State(view')
    && ui == Some(DonateOp(victim, outidx))
  }

  predicate NoopStep(s:State, s':State) {
    s' == s
  }

  predicate Next(s:State, s':State, ui:UI) {
    || (exists victim :: DonateStep(s, s', victim, ui))
    || (NoopStep(s, s') && ui==None)
  }

}

//////////////////////////////////////////////////////////////////////////////

/*module Concrete {
  import Abstract
  import opened Options

  datatype Well = Well(stones: nat, ghost suffix: Abstract.View)

  datatype Thread = Thread(lockHeld: nat, victim:nat)
    // Thread's goal is to find a well containing victim stones, and add a stone to it.

  type Board = seq<Well>

  datatype State = State(board:Board, threads:set<Thread>)

  function View(board:Board, i:nat) : (v:seq<nat>)
    ensures |v| == |board| - i
    ensures forall j | 0<=j<|v| :: v[i] == board[j-i].stones
  {
    [board[i].stones] + View(board, i+1)
  }

  predicate Init(s: State) {
    && (forall i :: s.board[i].stones == 0)  // not necessary, just feels right
    && (forall i :: s.board[i].suffix == View(s.board, i))
    && s.threads == {}
  }

  predicate LockFree(s: State, lockId:nat) {
    forall t | t in s.threads :: t.lockHeld != lockId
  }

  predicate Start(s: State, s':State, victim:nat, ui:Abstract.UI) {
    var newThread := Thread(0, victim);
    && LockFree(s, 0)
    && s'.board == s.board
    && s'.threads == s.threads + {newThread}
    && var (suffix', outidx) := Abstract.Donate(s.board[0].suffix, victim);
    && ui == Some(Abstract.DonateOp(victim, outidx))
    && s'.board == s.board[0 := s.board[0].(suffix := suffix')]
  }

  predicate Advance(s: State, s':State, ui:Abstract.UI) {
    && ui == None
    && var t :| t in s.threads;
    && var nextLock := t.lockHeld + 1;
    && if s.board[t.lockHeld].stones == t.victim then
      // yay we found it!
      && s'.board == s.board[t.lockHeld := s.board[t.lockHeld].(stones := t.victim + 1)]
      && s'.threads == s.threads - {t}  // we're done! exit the runnable queue
    else if |s.board| <= nextLock then
      // Ran off end of list without finding victim.
      && s'.board == s.board
      && s'.threads == s.threads - {t}  // we're done! exit the runnable queue
    else if LockFree(s, nextLock) then
      var t' := Thread(nextLock, t.victim);
      var (suffix', outidx) := Abstract.Donate(s.board[nextLock].suffix, t.victim);
      && s'.board == s.board[nextLock := s.board[nextLock].(suffix := suffix')]
      && s'.threads == s.threads - {t} + {t'}
    else
      // Need to advance, but waiting on a lock
      && s' == s
  }

  predicate Next(s:State, s':State, ui:Abstract.UI) {
    || (exists victim :: Start(s, s', victim, ui))
    || Advance(s, s', ui)
  }

  function I(s:State) : (abs:Abstract.State) {
    Abstract.State(s.board[0].suffix)
  }

} // module Concrete
*/

/*module TheoremObligationDotS {
  import Abstract

  datatype MetaState<State, UI> = MetaState(state: State, ui: UI)
  type Behavior<State, UI> = seq<MetaState> // iseq would be better

  function Interpret<CState, AState>(b:Behavior<CState, Abstract.UI>, I:CState->AState) : (ab:Behavior<AState, Abstract.UI>)
    ensures forall i :: I(b[i].state) == ab[i].state
    ensures forall i :: b[i].ui == ab[i].ui
  {
    [MetaState(I[b[0].state], b[0].ui)] + Interpret(b[1:], I)
  }

  lemma Correctness(b:Behavior<Concrete.State>, I:CState->AState)
    requires Reachable(b, Concrete.Init, Concrete.Next)
    ensures var ab := Interpret(b, I); Reachable(ab, Abstract.Init, Abstract.Next)
  {
  }
} // module TheoremObligationDotS*/
