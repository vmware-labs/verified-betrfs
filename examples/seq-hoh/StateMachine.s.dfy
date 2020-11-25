include "../concurrency-strategies/spec.s.dfy"

abstract module StateMachine {
  import opened Options

  type ThreadId = int

  type StateObject(!new,==)

  predicate transform(a: multiset<StateObject>, b: multiset<StateObject>)
  function donate_ticket(tid: ThreadId, victim: nat) : StateObject
  function donate_stub(tid: ThreadId, outidx: Option<nat>) : StateObject
  function init_ticket() : StateObject

  type Variables = multiset<StateObject>

  predicate Init(s: Variables)
  {
    s == multiset{init_ticket()}
  }

  predicate DonateStart(s: Variables, s': Variables,
      tid: ThreadId, victim: nat)
  {
    s' == s + multiset{donate_ticket(tid, victim)}
  }

  predicate DonateEnd(s: Variables, s': Variables,
      tid: ThreadId, outidx: Option<nat>)
  {
    s == s' + multiset{donate_stub(tid, outidx)}
  }

  predicate Next(s: Variables, s': Variables)
  {
		exists a, b, c ::
			s == a + c && s' == b + c
			&& transform(a, b)
  }
}
