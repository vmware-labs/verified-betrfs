type View = seq<nat>

function LeastIndexOf(view:View, victim:nat) : (idx:Option<Nat>)
  ensures forall j::0<=j<i ==> view[j] != victim
  ensures i<|board| ==> view[i] == victim
{
...
}

function Donate(view:View, victim:nat) : (view':View, outidx: Option<nat>) {
  outidx := LeastIndexOf(view, victim);
  if idx.None? then
    view' == view
  else:
    view' == view[idx.value := victim + 1]
}


module Abstract {

datatype State = State(board:View)

predicate DonateStep(s:State, s':State, victim:nat, ui:UI, ui':UI) {
  var view',outidx := Donate(s, victim);
  && s' == view'
  && ui' == ui.append(victim, outidx)
}

predicate NoopStep(s:State, s':State) {
  s' == s
}

predicate Next(s:State, s':State, ui:UI, ui':UI) {
  || (exists victim, outidx :: DonateStep(s, s', victim, ui:UI, ui':UI)
  || (NoopStep(s, s') && ui'==ui)
}

}

//////////////////////////////////////////////////////////////////////////////

module Concrete {

datatype Well = Well(stones: nat, ghost suffix: View)

datatype Thread = Thread(lockHeld: nat, victim:nat)
  // Thread's goal is to find a well containing victim stones, and add a stone to it.

type Board = seq<Well>

datatype State = (board:Board, threads:set<Thread>)

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

predicate Start(s: State, s':State, victim:nat, ui:UI, ui':UI) {
  var newThread := Thread(0, victim);
  && LockFree(s, 0)
  && s'.board == s.board
  && s'.threads == s.threads + {newThread}
  && ui' == ui
}

predicate Advance(s: State, s':State, ui:UI, ui':UI) {
  var t :| t in s.threads;
  var nextLock := t.lockHeld + 1;
  if s.board[lockHeld] == t.victim then
    // yay we found it!
    && s'.board == s.board[t.lockHeld := t.victim + 1]
    && s'.threads == s.threads - {t}  // we're done! exit the runnable queue
    && ui' == ui.append(t.victim, Some(t.lockHeld))
  else if |s.board| <= nextLock then
    // Ran off end of list without finding victim.
    && s'.board == s.board
    && s'.threads == s.threads - {t}  // we're done! exit the runnable queue
    && ui' == ui.append(t.victim, None())
  else if LockFree(s, nextLock) then
    var t' := Thread(nextLock, victim);
    && s'.board == s.board
    && s'.threads == s.threads - {t} + {t'}
    && ui' == ui  // non-observable
  else
    // Need to advance, but waiting on a lock
    && s' = s
    && ui' == ui
}

predicate Next(s:State, s':State, ui:UI, ui':UI) {
  || (exists victim :: Start(s, s', victim, ui, ui'))
  || Advance(s, s', ui, ui)
}

function I(s:State) : (as:Abstract.State) {
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
