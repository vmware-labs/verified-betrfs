module Abstract {
  type View = seq<nat>
  datatype Option<V> = None | Some(value:V)

  datatype Op = DonateOp(victim:nat, outidx: Option<nat>)
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

  function Donate(view:View, victim:nat, ui:UI) : (View, Option<nat>) {
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
    var (view',outidx) := Donate(s.board, victim, ui);
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

module Concrete {

  datatype Well = Well(stones: nat /*, ghost suffix: View*/)

  datatype Thread = Thread(lockHeld: nat, victim:nat)
    // Thread's goal is to find a well containing victim stones, and add a stone to it.

  type Board = seq<Well>

  datatype State = State(board:Board, threads:set<Thread>)

  function View(board:Board, i:nat) : (v:seq<nat>)
    ensures |v| == |board| - i
    ensures forall j | 0<=j<|v| :: v[i] == board[j-i]
  {
    [board[i]] + View(board, i+1)
  }

  predicate Init(s: State) {
    && (forall i :: board[i].stones == 0)  // not necessary, just feels right
    && (forall i :: board[i].suffix == View(board, i))
    && threads == {}
  }

  predicate LockFree(s: State, lockId:nat) {
    forall t | t in s.threads :: t.lockHeld != lockId
  }

  predicate Start(s: State, s':State, victim:nat, ui:UI) {
    var newThread := Thread(0, victim);
    && LockFree(s, 0)
    && s'.board == s.board
    && s'.threads == s.threads + {newThread}
    && ui == None()
  }

  predicate Advance(s: State, s':State, ui:UI) {
    var t :| t in s.threads;
    var nextLock := t.lockHeld + 1;
    if s.board[lockHeld] == t.victim then
      // yay we found it!
      && s'.board == s.board[t.lockHeld := t.victim + 1]
      && s'.threads == s.threads - {t}  // we're done! exit the runnable queue
      && ui == Some(t.victim, Some(t.lockHeld))
    else if |s.board| <= nextLock then
      // Ran off end of list without finding victim.
      && s'.board == s.board
      && s'.threads == s.threads - {t}  // we're done! exit the runnable queue
      && ui == Some(t.victim, None())
    else if LockFree(s, nextLock) then
      var t' := Thread(nextLock, victim);
      && s'.board == s.board
      && s'.threads == s.threads - {t} + {t'}
      && ui == None()
    else
      // Need to advance, but waiting on a lock
      && s' == s
      && ui == None()
  }

  predicate Next(s:State, s':State, ui:UI) {
    || (exists victim :: Start(s, s', victim, ui))
    || Advance(s, s', ui)
  }

  function I(s:State) : (abs:Abstract.State) {
    s.board[0].suffix
  }

} // module Concrete

module TheoremObligationDotS {
  datatype MetaState<State> = MetaState(state: State, ui: UI)
  type Behavior<State> = iseq<MetaState>

  function Interpret<CState, AState>(b:Behavior<CState, UI>, I:CState->AState) : (ab:Behavior<AState, UI>)
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
} // module TheoremObligationDotS
