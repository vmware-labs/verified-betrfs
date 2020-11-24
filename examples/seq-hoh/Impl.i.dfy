include "StateMachine.i.dfy"
include "Mutex.s.dfy"
include "ImplSpec.s.dfy"

module NumMutex refines AbstractMutex {
  import opened WellStateObjects

  type ConstType = nat

  linear datatype V = V(num: nat, linear r: StateObject, linear l: StateObject)

  type ValueType = V

  predicate Inv(k: ConstType, v: ValueType)
  {
    && v.r == StoneValue(k, v.num)
    && v.l == StoneLock(k)
  }
}

module DonateImpl refines DonateImplSpec {
  import opened SM = WellStateObjects
  import opened NumMutex

  method transform_init(tid: ThreadId, victim: nat,
      linear s1: StateObject,
      linear s2: StateObject)
  returns (
      linear t1: StateObject)
  requires s1 == Ticket(tid, victim)
  requires s2 == StoneLock(0)
  ensures t1 == ThreadPos(tid, 0, victim)
  {
    assert transform_step(multiset{s1, s2}, multiset{ThreadPos(tid, 0, victim)},
        StartStep(tid, victim));
    t1 := transform_2_1(s1, s2, ThreadPos(tid, 0, victim));
  }

  method transform_advance(
      tid: ThreadId, i: nat, victim: nat, v: nat,
      linear s1: StateObject,
      linear s2: StateObject,
      linear s3: StateObject)
  returns (
      linear t1: StateObject,
      linear t2: StateObject,
      linear t3: StateObject)
  requires v != victim
  requires i+1 < len()
  requires s1 == ThreadPos(tid, i, victim)
  requires s2 == StoneLock(i+1)
  requires s3 == StoneValue(i, v)
  ensures t1 == ThreadPos(tid, i+1, victim)
  ensures t2 == StoneLock(i)
  ensures t3 == StoneValue(i, v)
  {
    assert transform_step(multiset{s1, s2, s3}, multiset{ ThreadPos(tid, i+1, victim), StoneLock(i), StoneValue(i, v) }, AdvanceStep(tid, i, victim, v));
    t1, t2, t3 := transform_3_3(s1, s2, s3,
      ThreadPos(tid, i+1, victim),
      StoneLock(i),
      StoneValue(i, v));
  }

  method transform_fail(
      tid: ThreadId, victim: nat, v: nat,
      linear s1: StateObject,
      linear s2: StateObject)
  returns (
      linear t1: StateObject,
      linear t2: StateObject,
      linear t3: StateObject)
  requires v != victim
  requires s1 == ThreadPos(tid, len()-1, victim)
  requires s2 == StoneValue(len()-1, v)
  ensures t1 == Stub(tid, None)
  ensures t2 == StoneLock(len()-1)
  ensures t3 == StoneValue(len()-1, v)
  {
    assert transform_step(multiset{s1, s2}, multiset{ 
        Stub(tid, None),
        StoneLock(len()-1),
        StoneValue(len()-1, v)}, FailStep(tid, victim, v));
    t1, t2, t3 := transform_2_3(s1, s2,
        Stub(tid, None),
        StoneLock(len()-1),
        StoneValue(len()-1, v));
  }

  method transform_finish(
      tid: ThreadId, i: nat, victim: nat,
      linear s1: StateObject,
      linear s2: StateObject)
  returns (
      linear t1: StateObject,
      linear t2: StateObject,
      linear t3: StateObject)
  requires s1 == ThreadPos(tid, i, victim)
  requires s2 == StoneValue(i, victim)
  ensures t1 == Stub(tid, Some(i))
  ensures t2 == StoneLock(i)
  ensures t3 == StoneValue(i, victim+1)
  {
    assert transform_step(multiset{s1, s2}, multiset{ 
        Stub(tid, Some(i)),
        StoneLock(i),
        StoneValue(i, victim+1)}, DoneStep(tid, i, victim));
    t1, t2, t3 := transform_2_3(s1, s2,
        Stub(tid, Some(i)),
        StoneLock(i),
        StoneValue(i, victim+1));
  }

  type Object = seq<Mutex>

  predicate Inv(o: Object)
  {
    && |o| == len()
    && (forall i | 0 <= i < |o| :: o[i].constant() == i)
  }

  // TODO
  method init(linear ticket: StateObject)
  returns (self: Object)

  method donate(
    self: Object,
    victim: nat, linear ticket: StateObject)
  returns (outidx: Option<nat>, linear stub: StateObject)
  {
    linear var entry0 := acquire(self[0]);
    linear var V(num, r, l) := entry0;

    var tid := ticket.tid;
    linear var tstate := transform_init(tid, victim, ticket, l);

    var i := 0;

    var done := false;

    while i < len() - 1 && num != victim
    invariant 0 <= i < len()
    invariant tstate.ThreadPos?
    invariant tstate.tid == tid
    invariant tstate.n == i
    invariant tstate.victim == victim
    invariant r == StoneValue(i, num)
    decreases len() - i
    {
      linear var entry := acquire(self[i+1]);
      linear var V(num', r', l') := entry;
  
      tstate, l, r := transform_advance(tid, i, victim, num,
          tstate, l', r);

      release(self[i], V(num, r, l));

      r := r';
      i := i + 1;
      num := num';
    }

    if num == victim {
      stub, l, r := transform_finish(tid, i, victim, tstate, r);

      num := num + 1;

      release(self[i], V(num, r, l));

      outidx := Some(i);
    } else {
      stub, l, r := transform_fail(tid, victim, num,
          tstate, r);

      release(self[i], V(num, r, l));

      outidx := None;
    }

    assert stub == donate_stub(tid, outidx);
  }
}
