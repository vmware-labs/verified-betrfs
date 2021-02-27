// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

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

  type Mutex = int

  class LockHandler {
    // Starts true in any transition
    // Is set to false when a 'release' occurs
    predicate can_acquire()
    reads this

    predicate is_acquired(m: Mutex)
    reads this

    function value(m: Mutex) : int
    reads this

    method acquire(m: Mutex)
    returns (v: int)
    requires can_acquire()
    requires !is_acquired(m)
    modifies this
    ensures can_acquire()
    ensures is_acquired(m)
    ensures forall m' | m' != m :: is_acquired(m') == old(is_acquired(m'))
    ensures forall m' :: value(m') == old(value(m'))
    ensures v == value(m)

    method release(m: Mutex, v: int)
    requires is_acquired(m)
    modifies this
    ensures is_acquired(m)
    ensures forall m' | m' != m :: is_acquired(m') == old(is_acquired(m'))
    ensures value(m) == v
    ensures forall m' | m' != m :: value(m') == old(value(m'))
  }

  // Implementation

  function mutex_values(lh: LockHandler, ms: seq<Mutex>) : (res : seq<int>)
  reads lh
  ensures |res| == |ms|
  ensures forall i | 0 <= i < |res| :: res[i] == lh.value(ms[i])
  {
    if ms == [] then [] else
      mutex_values(lh, ms[..|ms|-1]) + [lh.value(ms[|ms|-1])]
  }

  datatype state = state(accounts: seq<Mutex>)

  function I(lh: LockHandler, s: state) : Bank.variables
  reads lh
  {
    Bank.variables(mutex_values(lh, s.accounts))
  }

  method transaction(s: state, lh: LockHandler, i: int, j: int, amt: int)
  requires lh.can_acquire()
  requires forall i, j | 0 <= i < |s.accounts| && 0 <= j < |s.accounts| && i != j
      :: s.accounts[i] != s.accounts[j]
  requires forall i | 0 <= i < |s.accounts| :: !lh.is_acquired(s.accounts[i])
  requires i != j
  requires 0 <= i < |s.accounts|
  requires 0 <= j < |s.accounts|
  modifies lh
  ensures Bank.Next(old(I(lh, s)), I(lh, s))
  {
    var m1 := s.accounts[i];
    var m2 := s.accounts[j];

    var v1 := lh.acquire(m1);
    var v2 := lh.acquire(m2);

    v1 := v1 - amt;
    v2 := v2 + amt;

    lh.release(m1, v1);
    lh.release(m2, v2);

    assert Bank.NextStep(
        old(I(lh, s)), I(lh, s),
        Bank.TransferStep(i, j, amt));
  }
}
