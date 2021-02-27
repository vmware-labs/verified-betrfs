// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../concurrency-strategies/spec.s.dfy"
include "StateMachine.s.dfy"

module WellStateObjects refines StateMachine {
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

  function method len(): int { 20 }

  datatype StateObject =
     | StoneValue(i: nat, v: nat)
     | StoneLock(i: nat)
     | ThreadPos(tid: ThreadId, n: nat, victim: nat)
     | Ticket(tid: ThreadId, victim: nat)
     | Stub(tid: ThreadId, outidx: Option<nat>)

  function donate_ticket(tid: ThreadId, victim: nat) : StateObject
  {
    Ticket(tid, victim)
  }

  function donate_stub(tid: ThreadId, outidx: Option<nat>) : StateObject
  {
    Stub(tid, outidx)
  }

  datatype Step =
    | StartStep(tid: ThreadId, victim: nat)
    | AdvanceStep(tid: ThreadId, i:nat, victim: nat, v: nat)
    | FailStep(tid: ThreadId, victim: nat, v: nat)
    | DoneStep(tid: ThreadId, i: nat, victim: nat)

  predicate transform_step(a: multiset<StateObject>, b: multiset<StateObject>,
      step: Step)
  {
    match step {
      case StartStep(tid, victim) => start(a, b, tid, victim)
      case AdvanceStep(tid, i, victim, v) => advance(a, b, tid, i, victim, v)
      case FailStep(tid, victim, v) => fail(a, b, tid, victim, v)
      case DoneStep(tid, i, victim) => done(a, b, tid, i, victim)
    }
  }

  predicate transform(a: multiset<StateObject>, b: multiset<StateObject>)
  {
    exists step :: transform_step(a, b, step)
  }

  predicate start(a: multiset<StateObject>, b: multiset<StateObject>,
      tid: ThreadId, victim: nat)
  {
    && a == multiset{Ticket(tid, victim), StoneLock(0)}
    && b == multiset{ThreadPos(tid, 0, victim)}
  }

  predicate advance(a: multiset<StateObject>, b: multiset<StateObject>,
      tid: ThreadId, i:nat, victim: nat, v: nat)
  {
    && v != victim
    && i+1 < len()
    && a == multiset{ThreadPos(tid, i, victim), StoneLock(i+1), StoneValue(i, v)}
    && b == multiset{ThreadPos(tid, i+1, victim), StoneLock(i), StoneValue(i, v)}
  }

  predicate fail(a: multiset<StateObject>, b: multiset<StateObject>,
      tid: ThreadId, victim: nat, v: nat)
  {
      && v != victim
      && a == multiset{ThreadPos(tid, len()-1, victim), StoneValue(len()-1, v)}
      && b == multiset{Stub(tid, None), StoneLock(len()-1), StoneValue(len()-1, v)}
  }

  predicate done(a: multiset<StateObject>, b: multiset<StateObject>,
      tid: ThreadId, i:nat, victim:nat)
  {
      && a == multiset{ThreadPos(tid, i, victim), StoneValue(i, victim)}
      && b == multiset{Stub(tid, Some(i)), StoneLock(i), StoneValue(i, victim+1)}
  }

  predicate Inv1(o: StateObject)
  {
    && (o.StoneValue? ==> 0 <= o.i < len())
    && (o.StoneLock? ==> 0 <= o.i < len())
    && (o.ThreadPos? ==> 0 <= o.n < len())
  }

  predicate Inv2(o: StateObject, p: StateObject)
  {
    && (o.StoneValue? && p.StoneValue? ==> o.i != p.i)
    && (o.StoneLock? && p.StoneLock? ==> o.i != p.i)
    && (o.StoneLock? && p.ThreadPos? ==> o.i != p.n)
    && (o.ThreadPos? && p.ThreadPos? ==> o.n != p.n)
  }

  predicate Inv(s: multiset<StateObject>)
  {
    && (forall o | o in s :: Inv1(o))
    && (forall o, p | multiset{o,p} <= s :: Inv2(o, p))
  }

  lemma StartPreservesInv(a: multiset<StateObject>, b: multiset<StateObject>,
      c: multiset<StateObject>, tid: ThreadId, victim: nat)
  requires Inv(a + c)
  requires start(a, b, tid, victim)
  ensures Inv(b + c)
  {
    var s := a + c;
    var s' := b + c;
    forall o, p | multiset{o,p} <= s'
    ensures Inv2(o, p)
    {
      if multiset{o, p} <= s {
        assert Inv2(o, p);
      } else if o in b && p in c {
        assert Inv2(Ticket(tid, victim), p);
        assert Inv2(StoneLock(0), p);
        assert Inv2(o, p);
      } else if o in c && p in b {
        assert Inv2(o, Ticket(tid, victim));
        assert Inv2(o, StoneLock(0));
        assert Inv2(Ticket(tid, victim), o);
        assert Inv2(StoneLock(0), o);
        assert Inv2(o, p);
      } else if multiset{o, p} <= b {
        assert Inv2(o, p);
      }
    }
    assert Inv(s');
  }

  lemma AdvancePreservesInv(a: multiset<StateObject>, b: multiset<StateObject>,
      c: multiset<StateObject>,
      tid: ThreadId, i:nat, victim: nat, v: nat)
  requires Inv(a + c)
  requires advance(a, b, tid, i, victim, v)
  ensures Inv(b + c)
  {
    var s := a + c;
    var s' := b + c;
    forall o, p | multiset{o,p} <= s'
    ensures Inv2(o, p)
    {
      if multiset{o, p} <= s {
        assert Inv2(o, p);
      } else if o in b && p in c {
        assert Inv2(ThreadPos(tid, i, victim), p);
        assert Inv2(StoneLock(i+1), p);
        assert Inv2(StoneValue(i, v), p);
        assert Inv2(p, ThreadPos(tid, i, victim));
        assert Inv2(p, StoneLock(i+1));
        assert Inv2(p, StoneValue(i, v));
        assert Inv2(o, p);
      } else if o in c && p in b {
        assert Inv2(ThreadPos(tid, i, victim), o);
        assert Inv2(StoneLock(i+1), o);
        assert Inv2(StoneValue(i, v), o);
        assert Inv2(o, ThreadPos(tid, i, victim));
        assert Inv2(o, StoneLock(i+1));
        assert Inv2(o, StoneValue(i, v));
        assert Inv2(o, p);
      } else if multiset{o, p} <= b {
        assert Inv2(o, p);
      }
    }
    assert Inv(s');

  }

  lemma FailPreservesInv(a: multiset<StateObject>, b: multiset<StateObject>,
      c: multiset<StateObject>,
      tid: ThreadId, victim: nat, v: nat)
  requires Inv(a + c)
  requires fail(a, b, tid, victim, v)
  ensures Inv(b + c)
  {
    var s := a + c;
    var s' := b + c;
    forall o, p | multiset{o,p} <= s'
    ensures Inv2(o, p)
    {
      if multiset{o, p} <= s {
        assert Inv2(o, p);
      } else if o in b && p in c {
        assert Inv2(ThreadPos(tid, len()-1, victim), p);
        assert Inv2(StoneValue(len()-1, v), p);
        assert Inv2(p, ThreadPos(tid, len()-1, victim));
        assert Inv2(p, StoneValue(len()-1, v));
        assert Inv2(o, p);
      } else if o in c && p in b {
        assert Inv2(ThreadPos(tid, len()-1, victim), o);
        assert Inv2(StoneValue(len()-1, v), o);
        assert Inv2(o, ThreadPos(tid, len()-1, victim));
        assert Inv2(o, StoneValue(len()-1, v));
        assert Inv2(o, p);
      } else if multiset{o, p} <= b {
        assert Inv2(o, p);
      }
    }
    assert Inv(s');
  }

  lemma DonePreservesInv(a: multiset<StateObject>, b: multiset<StateObject>,
      c: multiset<StateObject>,
      tid: ThreadId, i: nat, victim: nat)
  requires Inv(a + c)
  requires done(a, b, tid, i, victim)
  ensures Inv(b + c)
  {
    var s := a + c;
    var s' := b + c;
    forall o, p | multiset{o,p} <= s'
    ensures Inv2(o, p)
    {
      if multiset{o, p} <= s {
        assert Inv2(o, p);
      } else if o in b && p in c {
        assert Inv2(ThreadPos(tid, i, victim), p);
        assert Inv2(StoneValue(i, victim), p);
        assert Inv2(p, ThreadPos(tid, i, victim));
        assert Inv2(p, StoneValue(i, victim));
        assert Inv2(o, p);
      } else if o in c && p in b {
        assert Inv2(ThreadPos(tid, i, victim), o);
        assert Inv2(StoneValue(i, victim), o);
        assert Inv2(o, ThreadPos(tid, i, victim));
        assert Inv2(o, StoneValue(i, victim));
        assert Inv2(o, p);
      } else if multiset{o, p} <= b {
        assert Inv2(o, p);
      }
    }
    forall o | o in s'
    ensures Inv1(o)
    {
      if o in b {
        assert Inv1(StoneValue(i, victim));
        assert Inv1(o);
      } else {
        assert Inv1(o);
      }
    }
    assert Inv(s');
  }

  lemma NextPreservesInv(s: multiset<StateObject>, s': multiset<StateObject>)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
  {
		var a, b, c :|
			s == a + c && s' == b + c
			&& transform(a, b);
    var step :| transform_step(a, b, step);
    match step {
      case StartStep(tid, victim) => {
        StartPreservesInv(a, b, c, tid, victim);
      }
      case AdvanceStep(tid, i, victim, v) => {
        AdvancePreservesInv(a, b, c, tid, i, victim, v);
      }
      case FailStep(tid, victim, v) => {
        FailPreservesInv(a, b, c, tid, victim, v);
      }
      case DoneStep(tid, i, victim) => {
        DonePreservesInv(a, b, c, tid, i, victim);
      }
    }
  }
}
