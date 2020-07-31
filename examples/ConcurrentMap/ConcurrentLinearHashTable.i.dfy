include "../../lib/Base/sequences.i.dfy"
include "ConcurrentMap.i.dfy"

module ConcurrentLinearHashTable {
  import opened Sequences
  import ConcurrentMap

  type Key = ConcurrentMap.Key
  type Value = ConcurrentMap.Value

  datatype Slot = Slot(ghost slot: nat)
  predicate ValidSlot(elementsLength: nat, slot: Slot)
  {
    slot.slot < elementsLength
  }

  function SlotForKey(elementsLength: nat, key: Key): (result: Slot)
  requires 0 < elementsLength
  ensures ValidSlot(elementsLength, result)
  //  {
  //    var h := hash64(key);
  //    Slot((h as nat) % elementsLength)
  //  }

  datatype Item = Empty | Entry(key: Key, value: Value) | Tombstone(key: Key)

  datatype ThreadState =
    | Insert(key: Key, value: Value, slot:Slot)
    //| Remove(key: Key, slot:Slot)
    | Query(key: Key, slot:Slot)
    | Idle

  predicate WFThreadState(elementsLength:nat, t:ThreadState)
  {
    match t
      case Insert(_, _, slot) => ValidSlot(elementsLength, slot)
      //case Remove(_, slot) => ValidSlot(elementsLength, slot)
      case Query(_, slot) => ValidSlot(elementsLength, slot)
      case Idle => true
  }

  datatype Variables = Variables(table:seq<Item>, threads:seq<ThreadState>)
  predicate ValidThreadId(s:Variables, tid:nat)
  {
    tid < |s.threads|
  }

  predicate WFVariables(s:Variables)
  {
    && 0 < |s.table|
    && (forall tid | ValidThreadId(s, tid) :: WFThreadState(|s.table|, s.threads[tid]))
  }

  predicate InsertInit(s:Variables, s':Variables, tid:nat, key:Key, value:Value) {
    && WFVariables(s)
    && ValidThreadId(s, tid)
    && s.threads[tid].Idle?
    && s' == s.(threads := s.threads[tid := Insert(key, value, SlotForKey(|s.table|, key))])
  }

  predicate InsertAdvance(s:Variables, s':Variables, tid:nat) {
    && WFVariables(s)
    && ValidThreadId(s, tid)
    && var t := s.threads[tid];
    && t.Insert?
    && !s.table[t.slot.slot].Empty?
    && s.table[t.slot.slot].key != t.key
    && t.slot.slot < |s.table|-1  // Can't roll around end of table
    && s' == s.(threads := s.threads[tid := t.(slot := Slot(t.slot.slot+1))])
  }

  predicate InsertComplete(s:Variables, s':Variables, tid:nat) {
    && WFVariables(s)
    && ValidThreadId(s, tid)
    && var t := s.threads[tid];
    && t.Insert?
    && (s.table[t.slot.slot].Empty? || s.table[t.slot.slot].key == t.key)
    && s' == s.(threads := s.threads[tid := Idle], table := s.table[t.slot.slot := Entry(t.key, t.value)])
  }


  predicate QueryInit(s:Variables, s':Variables, tid:nat, key:Key) {
    && WFVariables(s)
    && ValidThreadId(s, tid)
    && s.threads[tid].Idle?
    && s' == s.(threads := s.threads[tid := Query(key, SlotForKey(|s.table|, key))])
  }

  predicate QueryAdvance(s:Variables, s':Variables, tid:nat) {
    && WFVariables(s)
    && ValidThreadId(s, tid)
    && var t := s.threads[tid];
    && t.Query?
    && !s.table[t.slot.slot].Empty?
    && s.table[t.slot.slot].key != t.key
    && t.slot.slot < |s.table|-1  // Can't roll around end of table TODO
    && s' == s.(threads := s.threads[tid := t.(slot := Slot(t.slot.slot+1))])
  }

  // TODO Success-only result; need to return None
  predicate QueryComplete(s:Variables, s':Variables, tid:nat, value:Value) {
    && WFVariables(s)
    && ValidThreadId(s, tid)
    && var t := s.threads[tid];
    && t.Query?
    && s.table[t.slot.slot] == Entry(t.key, value)
    && s' == s.(threads := s.threads[tid := Idle])
  }

  predicate Init(s:Variables) {
    && |s.table| >0
    && (forall si | 0<=si<|s.table| :: s.table[si].Empty?)
    && (forall tid | 0 <= tid < |s.threads| :: s.threads[tid].Idle?)
  }

  datatype Step =
    | InsertInitStep(key:Key, value:Value, tid:nat)
    | InsertAdvanceStep(tid:nat)
    | InsertCompleteStep(tid:nat)
    | QueryInitStep(key:Key, tid:nat)
    | QueryAdvanceStep(tid:nat)
    | QueryCompleteStep(tid:nat, value:Value)

  predicate NextStep(s:Variables, s':Variables, step:Step) {
    match step
      case InsertInitStep(key, value, tid) => InsertInit(s, s', tid, key, value)
      case InsertAdvanceStep(tid) => InsertAdvance(s, s', tid)
      case InsertCompleteStep(tid) => InsertComplete(s, s', tid)
      case QueryInitStep(key, tid) => QueryInit(s, s', tid, key)
      case QueryAdvanceStep(tid) => QueryAdvance(s, s', tid)
      case QueryCompleteStep(tid, value) => QueryComplete(s, s', tid, value)
  }

  predicate Next(s:Variables, s':Variables) {
    exists step:Step :: NextStep(s, s', step)
  }

  function ITable(table:seq<Item>) : (m:map<Key,Value>)
    ensures forall slot | ValidSlot(|table|, slot) && table[slot.slot].Entry?  :: table[slot.slot].key in m
  {
    if |table|==0
      then map[]
    else
      var last := Last(table);
      if last.Entry?
        then ITable(DropLast(table))[last.key := last.value]
        else ITable(DropLast(table))
  }

  predicate KeySlot(table:seq<Item>, slot:Slot)
  {
    && ValidSlot(|table|, slot)
    && !table[slot.slot].Empty?
  }

  predicate UniqueKeys(table:seq<Item>)
  {
    (forall i, j | && KeySlot(table, i) && KeySlot(table, j) && table[i.slot].key == table[j.slot].key
      :: i == j)
  }

  predicate ReachableForKey(table:seq<Item>, key:Key, end /* exclusive */ :Slot)
  {
    && 0<|table|
    && ValidSlot(|table|, end)
    && var start := SlotForKey(|table|, key);
    && start.slot <= end.slot
    && (forall i:Slot | start.slot<=i.slot<end.slot :: !table[i.slot].Empty? && table[i.slot].key!=key)
  }

  predicate ReachableInv(table:seq<Item>)
  {
    (forall i | KeySlot(table, i) :: ReachableForKey(table, table[i.slot].key, i))
  }

  predicate TableInv(table:seq<Item>)
  {
    && UniqueKeys(table)
    && ReachableInv(table)
  }

  predicate ThreadInv(s:Variables, t:ThreadState)
  {
    !t.Idle? ==> ReachableForKey(s.table, t.key, t.slot)
  }

  predicate Inv(s:Variables)
  {
    && TableInv(s.table)
    && (forall tid | ValidThreadId(s, tid) :: ThreadInv(s, s.threads[tid]))
  }

  lemma InitInv(s:Variables)
  requires Init(s)
  ensures Inv(s)
  {
  }

  lemma NextInv(s:Variables, s':Variables)
  requires Next(s, s')
  requires Inv(s)
  ensures Inv(s')
  {
  }

  lemma InsertInitInterpretation(s:Variables, s':Variables, tid:nat, key:Key, value:Value)
    requires Inv(s)
    requires InsertInit(s, s', tid, key, value)
    ensures Inv(s')
    ensures ITable(s'.table) == ITable(s.table)
  {
  }

  lemma InsertAdvanceInterpretation(s:Variables, s':Variables, tid:nat)
    requires Inv(s)
    requires InsertAdvance(s, s', tid)
    ensures Inv(s')
    ensures ITable(s'.table) == ITable(s.table)
  {
  }

  lemma PointInterpretationForwards(table: seq<Item>, i: Slot)
    requires UniqueKeys(table)
    requires KeySlot(table, i)
    requires table[i.slot].Entry?
    ensures table[i.slot].key in ITable(table) && ITable(table)[table[i.slot].key] == table[i.slot].value
  {
    if |table| == i.slot + 1 {
    } else {
      PointInterpretationForwards(DropLast(table), i);
      if Last(table).Entry? {
        assert KeySlot(table, Slot(|table|-1));
      }
    }
  }

  lemma PointInterpretationBackwards(table: seq<Item>)
    requires UniqueKeys(table)
    ensures forall k | k in ITable(table) :: exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k])
  {
    if |table| == 0 {
    } else {
      PointInterpretationBackwards(DropLast(table));
      var prem := ITable(DropLast(table));
      var m := ITable(table);
      forall k | k in ITable(table)
      ensures exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k])
      {
        var l := Last(table);
        if (l.Entry? || l.Tombstone?) && k == l.key {
          var i := Slot(|table| - 1);
          assert KeySlot(table, i);
          assert table[i.slot] == Entry(k, ITable(table)[k]);
        } else {
          assert exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k]);
        }
      }
    }
  }

  lemma PointInterpretation(table: seq<Item>)
    requires UniqueKeys(table)
    ensures forall i | KeySlot(table, i) && table[i.slot].Entry? :: table[i.slot].key in ITable(table) && ITable(table)[table[i.slot].key] == table[i.slot].value
    ensures forall k | k in ITable(table) :: exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k])
  {
    forall i | KeySlot(table, i) && table[i.slot].Entry?
      ensures table[i.slot].key in ITable(table) && ITable(table)[table[i.slot].key] == table[i.slot].value
    {
      PointInterpretationForwards(table, i);
    }
    PointInterpretationBackwards(table);
  }

  lemma InsertCompleteInterpretation(s:Variables, s':Variables, tid:nat)
    requires Inv(s)
    requires InsertComplete(s, s', tid)
    ensures Inv(s')
    ensures ITable(s'.table) == ITable(s.table)[s.threads[tid].key := s.threads[tid].value]
  {
    PointInterpretation(s.table);
    PointInterpretation(s'.table);
  }

  lemma QueryInitInterpretation(s:Variables, s':Variables, tid:nat, key: Key)
    requires Inv(s)
    requires QueryInit(s, s', tid, key)
    ensures Inv(s')
    ensures ITable(s'.table) == ITable(s.table)
  {
  }

  lemma QueryAdvanceInterpretation(s:Variables, s':Variables, tid:nat)
    requires Inv(s)
    requires QueryAdvance(s, s', tid)
    ensures Inv(s')
    ensures ITable(s'.table) == ITable(s.table)
  {
  }

  lemma QueryCompleteInterpretation(s:Variables, s':Variables, tid:nat, value: Value)
    requires Inv(s)
    requires QueryComplete(s, s', tid, value)
    ensures Inv(s')
    ensures ITable(s'.table) == ITable(s.table)
  {
  }

  function IThread(t: ThreadState) : ConcurrentMap.Req
  requires t != Idle
  {
    match t {
      case Insert(key, value, slot) => ConcurrentMap.ReqInsert(key, value)
      case Query(key, slot) => ConcurrentMap.ReqQuery(key)
    }
  }

  function I(s: Variables): ConcurrentMap.Variables
  {
    ConcurrentMap.Variables(
      ITable(s.table),
      map tid:nat | 0 <= tid < |s.threads| && s.threads[tid] != Idle
          :: IThread(s.threads[tid])
    ) 
  }
}
