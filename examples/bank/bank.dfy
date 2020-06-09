// Bank spec

module Bank {
  datatype variables = variables(accounts:seq<int>)

  predicate Init(s: variables)
  {
    forall i :: s.accounts[i] == 0
  }

  predicate Transfer(s: variables, s’: variables, from_account: int, to_account: int, amt: int)
  {
    && from_account != to_account
    && 0 <= to_account < |s.accounts|
    && 0 <= from_account < |s.accounts|
    && s’.accounts == s.accounts
          [from_account := s.accounts[from_account] - amt]
          [to_account := s.accounts[to_account] + amt]
  }

  datatype Step = TransferStep(from_account: int, to_account: int, amt: int)

  predicate NextStep(s: variables, s’: variables, step: Step)
  {
    Transfer(s, s', step.from_account, step.to_account, step.amt)
  }

  predicate Next(s: variables, s’: variables)
  {
    exists step :: NextStep(s, s', step)
  }

  // should follow from spec above
  predicate Inv(k, s)
  {
    sum(s.accounts) == 0
  }
}

// SharedMemory axiomatization

module SharedMemory {
  type MutexId = int
  type Value = int

  datatype variables = variables(m: map<MutexId, Value>)

  /*datatype ReadOp = ReadOp(mid: MutexId, v: value)
  datatype WriteOp = WriteOp(mid: MutexId, v: value)

  datatype MemoryStep = MemoryStep(
    readOps: seq<ReadOp>
    writeOps: seq<WriteOp>
  )*/
}

abstract module SharedMemorySystem {
  import SharedMemory

  type FixedMemory

  datatype variables = variables(
    sharedMemory: SharedMemory.variables,
    fixedMemory: FixedMemory
    //threadStates
   )

  datatype Step = Step(ms: SharedMemory.MemoryStep)

  predicate ThreadNext(k: FixedMemory, s: SharedMemory.variables, s': SharedMemory.variables)

  predicate Next(s: variables, s': variables)
  {
    && s'.fixedMemory == s.fixedMemory
    && ThreadNext(s.fixedMemory, s.sharedMemory, s'.sharedMemory)
  }
}

// Implementation of thread transition for the SharedMemorySystem

module BankSharedMemorySystem refines SharedMemorySystem {
  import Bank

  type FixedMemory = seq<SharedMemory.LockId>

  function lookup_balances(
      s: seq<SharedMemory.LockId>,
      balances: map<SharedMemory.LockId, int>) : seq<int>
  {
    if s == [] then [] else
      lookup_balances(s[..|s|-1]) + balances[s[|s|-1]]
  }

  function I(k: FixedMemory, s: SharedMemory.variables)
  {
    lookup_balances(k, s.m)
  }

  predicate ThreadNextStep(k: FixedMemory, s: SharedMemory.variables, s': SharedMemory.variables, bs: Bank.Step)
  {
    Bank.Next(I(k, s), I(k, s'), bs)
  }

  predicate ThreadNext(k: FixedMemory, s: SharedMemory.variables, s': SharedMemory.variables)
  {
    exists step ::
      ThreadNextStep(k, s, s', step)
  }
}

module BankImpl {
  import opened SharedMemory

  class LockHandler {
    //function step() : MemoryStep
    //reads this

    function 
  }

  class Mutex {
    function id() : MutexId
    reads this

    predicate has()
    reads this

    method acquire(lh: LockHandler)
    returns (v: int)
    requires lh.step().writeOps == []
    requires !has()
    modifies lh
    modifies this
    ensures lh.step().readOps == old(lh.step()).readOps + [ReadOp(id(), v)]
    ensures lh.step().writeOps == old(lh.step()).writeOps
    ensures id() == old(id())
    ensures has()

    method release(lh: LockHandler, v: int)
    modifies lh
    requires has()
    ensures lh.step().readOps == old(lh.step()).readOps
    ensures lh.step().writeOps == old(lh.step()).writeOps + [WriteOp(id(), v)]
    ensures id() == old(id())
    ensures !has()
  }

  datatype state = state(accounts: seq<Mutex>)

  method transaction(s: state, lh: LockHandler)
  modifies lh
  modifies s.accounts
  requires lh.step().readOps == []
  requires lh.step().writesOps == []
  ensures Next(lh.step())
  {
  }
}
