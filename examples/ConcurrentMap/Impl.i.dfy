include "PseudoCivl.dfy"
include "ConcurrentLinearHashTable.i.dfy"

module Impl {
  import opened PseudoCivl
  import L = LocalConcurrentLinearHashTable
  import ConcurrentMap

  type SharedState = seq<Mutex<L.Item>>
  type ThreadState = L.ThreadState

  type Key = ConcurrentMap.Key
  type Value = ConcurrentMap.Value

  // Spec

  datatype QueryPlace = Start | Mid(key: Key) | End(key: Key, value: Value)
  linear datatype QueryTransitionTracker =
      QueryTransitionTracker(x: int) // TODO make opaque
  {
    function place() : QueryPlace
  }

  method transfer_QueryInit(
        linear tt: QueryTransitionTracker,
        linear source: Source<L.SharedVariables, L.ThreadState>,
        ghost g': L.SharedVariables,
        l': L.ThreadState,
        key: Key
  )
  returns (
      linear tt' : QueryTransitionTracker,
      linear source' : Source<L.SharedVariables, L.ThreadState>
  ) 
  requires L.QueryInit(source.global(), g', source.local(), l', key)
  requires tt.place() == Start
  ensures tt.place() == Mid(key)
  ensures source'.global() == g'
  ensures source'.local() == l'

  predicate Inv(
    s: SharedState,
    source: Source<L.SharedVariables, L.ThreadState>)
  reads s
  {
    I(s) == source.global()
  }

  // Impl

  function values_of_mutexes(s: seq<Mutex<L.Item>>) : (res : seq<L.Item>)
  ensures |res| == |s|
  reads s
  {
    if s == [] then [] else values_of_mutexes(s[..|s|-1]) + [s[|s|-1].value()]
  }

  function I(s: SharedState) : L.SharedVariables
  reads s
  {
    L.SharedVariables(
      values_of_mutexes(s)
    )
  }

  method query(
    s: SharedState,
    key: Key,
    shared tid: Tid,
    linear p: Phase,
    linear source: Source<L.SharedVariables, L.ThreadState>,
    linear tt: QueryTransitionTracker)
  returns (res: Value,
    linear p': Phase,
    linear source': Source<L.SharedVariables, L.ThreadState>,
    linear tt': QueryTransitionTracker)
  requires tt.place() == Start
  requires Inv(s, source)
  requires source.local() == L.Idle

  modifies s
  modifies arbitrary_objects()
  requires |s| > 0
  {
    var slot := L.SlotForKey(|s|, key);

    assert L.QueryInit(old(I(s)), I(s), L.Idle, ThreadState.Query(key, slot), key);
    linear var tt1, source1 := transfer_QueryInit(tt, source, I(s), ThreadState.Query(key, slot), key);

    assert Inv(s, source1);
    assert source1.local() == ThreadState.Query(key, slot);
    assert tt1.place() == Mid(key);
    
    linear var p1 := do_yield(p);

    res, p', source', tt' := query_loop(s, key, slot, tid, p1, source1, tt1);
  }

  method query_loop(s: SharedState, key: Key, slot: L.Slot, shared tid: Tid, linear p: Phase,
    linear source: Source<L.SharedVariables, L.ThreadState>,
    linear tt: QueryTransitionTracker)
  returns (res: Value, linear p': Phase,
    linear source': Source<L.SharedVariables, L.ThreadState>,
    linear tt': QueryTransitionTracker)
  requires p.is_rising()
  modifies s
  modifies arbitrary_objects()
  requires 0 <= slot.slot <= |s|
  decreases |s| - slot.slot
  {
    linear var p1;
    linear var p2;

    if slot.slot == |s| {
      assume false;
      p' := p;
      source' := source;
      tt' := tt;
    } else {
      p1 := s[slot.slot].Acq(tid, p);

      var entry := s[slot.slot].Read(tid);

      p2 := s[slot.slot].Rel(tid, p1);

      if entry.Empty? {
        assume false;
        p' := p2;
        source' := source;
        tt' := tt;
      } else if entry.key == key {
        if entry.Tombstone? {
          assume false;
          p' := p2;
          source' := source;
          tt' := tt;
        } else {
          p' := p2;
          source' := source;
          tt' := tt;
          res := entry.value;
        }
      } else {
        var slot' := L.Slot(slot.slot + 1);
        linear var r' := do_yield(p2);
        res, p', source', tt' := query_loop(s, key, slot', tid, r', source, tt);
      }
    }
  }
}
