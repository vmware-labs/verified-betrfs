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

  method query(s: SharedState, key: Key, shared tid: Tid, linear r: RightPhase)
  returns (res: Value, linear l: LeftPhase)
  requires |s| > 0
  {
    var slot := L.SlotForKey(|s|, key);
    res, l := query_loop(s, key, slot, tid, r);
  }

  method query_loop(s: SharedState, key: Key, slot: L.Slot, shared tid: Tid, linear r: RightPhase)
  returns (res: Value, linear l_out: LeftPhase)
  requires 0 <= slot.slot <= |s|
  {
    if slot.slot == |s| {
      assume false;
    } else {
      s[slot.slot].Acq(tid, r);

      var entry := s[slot.slot].Read(tid);

      linear var l := shift_phase(r);
      s[slot.slot].Rel(tid, l);

      if entry.Empty? {
        assume false;
        l_out := l;
      } else if entry.key == key {
        if entry.Tombstone? {
          assume false;
          l_out := l;
        } else {
          l_out := l;
          res := entry.value;
        }
      } else {
        var slot' := L.Slot(slot.slot + 1);
        linear var r' := do_yield(l);
        res, l_out := query_loop(s, key, slot', tid, r');
      }
    }
  }
}
