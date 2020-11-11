include "../concurrency-strategies/spec.s.dfy"

module StateObjects {
  import opened Options

  // State: a sequence of integers a_1,...,a_n
  //
  // Input:
  //      victim: int
  // Output:
  //      outidx: int
  //
  // let i be smallest such that a_i = victim
  // if no such i exists:
  //    outidx := None
  // else:
  //    a_i := a_i + 1
  //    outidx := Some(i)

  type ThreadId = int

  function method len(): int { 20 }

  datatype StateObject =
     | StoneValue(i: nat, v: nat)
     | StoneLock(i: nat)
     | ThreadPos(tid: ThreadId, n: nat, victim: nat)
     | Ticket(tid: ThreadId, victim: nat)
     | Stub(tid: ThreadId, outidx: Option<nat>)

  predicate transform(a: multiset<StateObject>, b: multiset<StateObject>)
  {
    || (exists tid, victim ::
      && a == multiset{Ticket(tid, victim), StoneLock(0)}
      && b == multiset{ThreadPos(tid, 0, victim)}
     )
    || (exists tid, i:nat, victim, v ::
      && v != victim
      && i+1 < len()
      && a == multiset{ThreadPos(tid, i, victim), StoneLock(i+1), StoneValue(i, v)}
      && b == multiset{ThreadPos(tid, i+1, victim), StoneLock(i), StoneValue(i, v)}
     )
    || (exists tid, victim, v ::
      && v != victim
      && a == multiset{ThreadPos(tid, len()-1, victim), StoneValue(len()-1, v)}
      && b == multiset{Stub(tid, None), StoneLock(len()-1), StoneValue(len()-1, v)}
     )
    || (exists tid, i:nat, victim:nat ::
      && a == multiset{ThreadPos(tid, i, victim), StoneValue(i, victim)}
      && b == multiset{Stub(tid, Some(i)), StoneLock(i), StoneValue(i, victim+1)}
     )
  }

  type Variables = multiset<StateObject>

  predicate Init(s: Variables)
  {
    s == multiset{}
  }

  predicate DonateStart(s: Variables, s': Variables,
      tid: ThreadId, victim: nat)
  {
    s' == s + multiset{Ticket(tid, victim)}
  }

  predicate DonateEnd(s: Variables, s': Variables,
      tid: ThreadId, outidx: Option<nat>)
  {
    s == s' + multiset{Stub(tid, outidx)}
  }

  predicate Next(s: Variables, s': Variables)
  {
		exists a, b, c ::
			s == a + c && s' == b + c
			&& transform(a, b)
  }
}
