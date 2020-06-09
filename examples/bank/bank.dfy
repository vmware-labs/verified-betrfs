// Bank spec

module Bank {
  datatype variables = variables(accounts:seq<int>)

  predicate Init(s: variables)
  {
    forall i | 0 <= i < |s.accounts| :: s.accounts[i] == 0
  }

  predicate Transfer(s: variables, s': variables, from_account: int, to_account: int, amt: int)
  {
    && from_account != to_account
    && 0 <= to_account < |s.accounts|
    && 0 <= from_account < |s.accounts|
    && s'.accounts == s.accounts
          [from_account := s.accounts[from_account] - amt]
          [to_account := s.accounts[to_account] + amt]
  }

  datatype Step = TransferStep(from_account: int, to_account: int, amt: int)

  predicate NextStep(s: variables, s': variables, step: Step)
  {
    Transfer(s, s', step.from_account, step.to_account, step.amt)
  }

  predicate Next(s: variables, s': variables)
  {
    exists step :: NextStep(s, s', step)
  }

  // should follow from spec above
  //predicate Inv(s: variables)
  //{
   // sum(s.accounts) == 0
  //}
}

module BankImpl {
  // axiomatization of a mutex
  import Bank

  class LockHandler {
    predicate can_acquire()
    reads this
  }

  class Mutex {
    predicate is_acquired()
    reads this

    function value() : int
    reads this

    method acquire(lh: LockHandler)
    returns (v: int)
    requires lh.can_acquire()
    requires !is_acquired()
    modifies this
    ensures is_acquired()
    ensures value() == old(value())
    ensures v == old(value())

    method release(lh: LockHandler, v: int)
    requires is_acquired()
    modifies lh
    modifies this
    ensures !lh.can_acquire()
    ensures value() == v
  }

  // Implementation

  function mutex_values(ms: seq<Mutex>) : (res : seq<int>)
  reads ms
  ensures |res| == |ms|
  ensures forall i | 0 <= i < |res| :: res[i] == ms[i].value()
  {
    if ms == [] then [] else mutex_values(ms[..|ms|-1]) + [ms[|ms|-1].value()]
  }

  datatype state = state(accounts: seq<Mutex>)
  {
    function I() : Bank.variables
    reads accounts
    {
      Bank.variables(mutex_values(accounts))
    }
  }

  method transaction(s: state, lh: LockHandler, i: int, j: int, amt: int)
  requires lh.can_acquire()
  requires forall i, j | 0 <= i < |s.accounts| && 0 <= j < |s.accounts| && i != j
      :: s.accounts[i] != s.accounts[j]
  requires forall i | 0 <= i < |s.accounts| :: !s.accounts[i].is_acquired()
  requires i != j
  requires 0 <= i < |s.accounts|
  requires 0 <= j < |s.accounts|
  modifies lh
  modifies s.accounts
  ensures Bank.Next(old(s.I()), s.I())
  {
    var m1 := s.accounts[i];
    var m2 := s.accounts[j];

    var v1 := m1.acquire(lh);
    var v2 := m2.acquire(lh);

    v1 := v1 - amt;
    v2 := v2 + amt;

    m1.release(lh, v1);
    m2.release(lh, v2);

    assert Bank.NextStep(
        old(s.I()), s.I(),
        Bank.TransferStep(i, j, amt));
  }
}
