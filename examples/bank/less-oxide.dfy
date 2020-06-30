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
}

module BankImpl {
  import Bank

  linear type Tracker

  // `in_intro(t)` is true when we only performed right-movers
  predicate in_intro(t: Tracker)

  // Using Dafny's `class` syntax in lieu of anything else.
  // For this example, I'm assuming we aren't using dynamic frame reasoning
  // though - instead I'm imagining we use Rust-style ownership to determine
  // mutability.

  class MutexDataPtr<V> {
    var value: V;
  }

  linear type MutexHandle<V> {
    linear p: MutexDataPtr<V>
  }

  linear class Mutex<V> {
    // Code isn't allowed to access this ptr, but proof can.
    // ghost var ptr: MutexDataPtr<V>; // read-only from the outside
    function Contents(): V

    ghost var has: bool;
 
    method acquire<V>(t: Tracker) mut // havocs Contents, has
    returns (handle: MutexHandle<V>, t': Tracker)
    requires in_intro(t) // acquire is right-mover
    ensures in_intro(t')
    ensures old(has)
    ensures handle.p == this.Contents()
    // ensures after_expiry(has)
    // ensures after_expiry(ptr) == before_expiry(p)

    // The `p: &mut MutexDataPtr` borrow has to expire before this
    // can be called.
    method release<V>(t: Tracker, linear handle: MutexHandle<V>) mut
    returns (t': Tracker)
    requires !has(m)
    ensures !in_intro(t') // release is left-mover
    ensures has(m')
    ensures this.Contents() == handle.p
  }

  function mutex_values(ms: seq<&Mutex>) : (res : seq<int>)
  reads lh
  ensures |res| == |ms|
  ensures forall i | 0 <= i < |res| :: res[i] == ms[i].value()
  {
    if ms == [] then [] else
      mutex_values(lh, ms[..|ms|-1]) + [ms[|ms|-1].value()]
  }

  datatype state = state(accounts: seq<&Mutex>)
  {
    function I() : Bank.variables
    {
      Bank.variables(mutex_values(accounts))
    }
  }

  method DoTransfer(s: state, lh: LockHandler, i: int, j: int, amt: int)
  requires 0 <= i < |s.accounts|
  requires 0 <= j < |s.accounts|
  requires i != j
  ensures Bank.Next(old(state.I()), state.I())
  {
    ghost var ptrBefore := s[i].ptr;

    var p1 := s[i].acquire();
    var p2 := s[j].acquire();

    // p1
    // this should be illegal: assert(s[i].ptr.value == 0)

    p1.value := p1.value - amt;
    p2.value := p1.value + amt;

    // p1 expires
    // p2 expires

    s[i].release();
    s[j].release();

    assert s[i].ptr.value == old(s[i].ptr.value) - amt;
    assert s[j].ptr.value == old(s[j].ptr.value) - amt;
    
    assert Bank.NextStep(
        old(state.I()), state.I(),
        Bank.TransferStep(i, j, amt));
  }
}
