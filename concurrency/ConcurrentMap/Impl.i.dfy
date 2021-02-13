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

  method {:axiom} transfer_QueryInit(
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

  method {:axiom} transfer_QueryAdvance(
        linear tt: QueryTransitionTracker,
        linear source: Source<L.SharedVariables, L.ThreadState>,
        ghost g': L.SharedVariables,
        l': L.ThreadState
  )
  returns (
      linear tt' : QueryTransitionTracker,
      linear source' : Source<L.SharedVariables, L.ThreadState>
  ) 
  requires L.QueryAdvance(source.global(), g', source.local(), l')
  ensures tt'.place() == tt.place()
  ensures source'.global() == g'
  ensures source'.local() == l'

  method {:axiom} transfer_QueryComplete(
        linear tt: QueryTransitionTracker,
        linear source: Source<L.SharedVariables, L.ThreadState>,
        ghost g': L.SharedVariables,
        l': L.ThreadState,
        value: Value
  )
  returns (
      linear tt' : QueryTransitionTracker,
      linear source' : Source<L.SharedVariables, L.ThreadState>
  ) 
  requires L.QueryComplete(source.global(), g', source.local(), l', value)
  requires tt.place().Mid?
  ensures tt'.place() == End(tt.place().key, value)
  ensures source'.global() == g'
  ensures source'.local() == l'

  //datatype Global<V> = IsGlobal(x: int) // TODO make opaque
  //{
  //  state() : V
  //}

  predicate Inv(
    s: SharedState,
    source: Source<L.SharedVariables, L.ThreadState>)
  reads s
  {
    I(s) == source.global()
  }

  method do_yield_inv(
    s: SharedState,
    linear p:Phase,
    linear source: Source<L.SharedVariables, L.ThreadState>
  )
  returns (
    linear p': Phase,
    linear source': Source<L.SharedVariables, L.ThreadState>
  )
  requires Inv(s, source)
  modifies arbitrary_objects()
  ensures p'.is_rising()
  ensures Inv(s, source')
  ensures source'.local() == source.local()

  // Impl

  function {:opaque} values_of_mutexes(s: seq<Mutex<L.Item>>) : (res : seq<L.Item>)
  ensures |res| == |s|
  ensures forall i | 0 <= i < |res| :: res[i] == s[i].value()
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
  requires |s| > 0

  modifies s
  modifies arbitrary_objects()

  ensures tt'.place() == End(key, res)
  {
    var slot := L.SlotForKey(|s|, key);

    assert L.QueryInit(old(I(s)), I(s), L.Idle, ThreadState.Query(key, slot), key);
    linear var tt1, source1 := transfer_QueryInit(tt, source, I(s), ThreadState.Query(key, slot), key);

    assert Inv(s, source1);
    assert source1.local() == ThreadState.Query(key, slot);
    assert tt1.place() == Mid(key);
    
    res, p', source', tt' := query_loop(s, key, slot, tid, p, source1, tt1);
  }

  method query_loop(s: SharedState, key: Key, slot: L.Slot, shared tid: Tid, linear p: Phase,
    linear source: Source<L.SharedVariables, L.ThreadState>,
    linear tt: QueryTransitionTracker)
  returns (res: Value, linear p': Phase,
    linear source': Source<L.SharedVariables, L.ThreadState>,
    linear tt': QueryTransitionTracker)
  requires p.is_rising()
  requires Inv(s, source)
  requires source.local() == ThreadState.Query(key, slot)
  requires tt.place() == Mid(key)
  requires 0 <= slot.slot <= |s|
  modifies s
  modifies arbitrary_objects()
  ensures tt'.place() == End(key, res)
  decreases |s| - slot.slot
  {
    linear var p1;
    linear var p2;
    linear var tt1;
    linear var source1;

    if slot.slot == |s| {
      assume false;
      p' := p;
      source' := source;
      tt' := tt;
    } else {
      p1 := s[slot.slot].Acq(tid, p);

      var entry := s[slot.slot].Read(tid);

      assert entry == I(s).table[slot.slot];

      p2 := s[slot.slot].Rel(tid, p1);

      assert entry == I(s).table[slot.slot];

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
          res := entry.value;

          tt', source' := transfer_QueryComplete(
            tt,
            source,
            I(s),
            L.Idle,
            res);
        }
      } else {
        assume slot.slot + 1 < |s|;

        var slot' := L.Slot(slot.slot + 1);

        assert L.QueryAdvance(old(I(s)), I(s), ThreadState.Query(key, slot), ThreadState.Query(key, slot'));
        tt1, source1 := transfer_QueryAdvance(
          tt,
          source,
          I(s),
          ThreadState.Query(key, slot'));

        assert Inv(s, source1);
        assert source1.local() == ThreadState.Query(key, slot');
        assert tt1.place() == Mid(key);

        linear var r', source2 := do_yield_inv(s, p2, source1);

        res, p', source', tt' := query_loop(s, key, slot', tid, r', source2, tt1);
      }
    }
  }
}
