include "../../lib/Base/Option.s.dfy"

/*module PseudoCivl {
  class Env {
    method do_yield()
    modifies this
  }

  class Mutex<V> {
    function has() 
  }
}*/

module PseudoCivl {
  import opened Options

  linear datatype RightPhase = RightPhase // TODO make opaque
  linear datatype LeftPhase = LeftPhase // TODO make opaque
  linear datatype Tid = Tid // TODO make opaque

  class Mutex<V> {
    function {:axiom} lock() : Option<Tid>
    reads this

    function {:axiom} value() : V
    reads this

    // right-mover
    method {:axiom} Acq(shared tid:Tid, shared r:RightPhase)
    modifies this
    ensures old(lock()) == None
    ensures lock() == Some(tid)

    // left-mover
    method {:axiom} Rel(shared tid:Tid, shared l:LeftPhase)
    modifies this
    requires lock() == Some(tid)
    ensures lock() == None

    method {:axiom} Read(shared tid:Tid) returns (v: V)
    requires lock() == Some(tid)
    ensures v == value()

    method {:axiom} Write(shared tid:Tid, v: V)
    modifies this
    requires lock() == Some(tid)
    ensures v == value()
  }

  function arbitrary_objects(): set<object>

  method do_yield(linear l:LeftPhase)
  returns (linear r:RightPhase)
  modifies arbitrary_objects()
  //modifies all Mutex objects / all objects? // ?
  //modifies *

  method shift_phase(linear r:RightPhase)
  returns (linear l:LeftPhase)
}

/*module ExampleUsage {
  method stuff(m: Mutex<int>, linear tid: TID, linear r:RightPhase) {
    {
      m.Acq(tid, r)
      var l := shift_phase(r);
      m.Rel(tid, l)
    }

    r := yield(l);

    {
      m.Acq(tid, r)
      var l := shift_phase(r);
      m.Rel(tid, l)
    }
  }

  function I(s: seq<Entry>) : LocalConcurrentLinearHashTable.SharedVariables

  method LockAdvance(s: seq<Entry>, linear tid: TID, localThreadState: LocalThreadState)
  ensures LocalConcurrentLinearHashTable.InsertAdvance(old(I(s)), old(localThreadState), I(s), localThreadState)
  {
    s[localThreadState.currentSlot].Acquire();

    // do some work with s[i]

    s[localThreadState.currentSlot].Release();

    localThreadState.currentSlot += 1;
  }
}*/
